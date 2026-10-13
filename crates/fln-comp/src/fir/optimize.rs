//! Verdict-preserving FIR simplification before FLBC lowering (bead
//! `fln-golem-ordinary-loops-fbj6`).
//!
//! Ingress lowers a `match` through its matcher function, whose alternatives
//! arrive as closures, and recursion through a closure over the function
//! itself. Run as written, one step of `go (n + 1) acc => go n (acc + n)`
//! allocates four closures and executes eighteen instructions. The pin's
//! compiler never builds that shape: it inlines matchers before its IR exists
//! and calls a known function directly. These rewrites do the same to FIR:
//!
//! - a saturated `Apply` of a closure built in the same function, directly or
//!   through partial applications, becomes a direct `Call`;
//! - a call to a small function that is not recursive is replaced by the
//!   callee's body: in tail position for any callee shape, elsewhere when the
//!   callee is one block;
//! - a returned call followed only by unread work that runs no code moves
//!   after that work, so it becomes a tail call;
//! - a binding that only allocates and whose value nobody reads is dropped.
//!
//! Nothing here merges or drops a computation: every call, intrinsic and
//! projection the program as written performs still runs, once per time it
//! was written to run. Sharing repeated pure work, as the pin's LCNF `cse`
//! does, or dropping unread pure work, as its `elimDead` does, would change
//! the engine's evaluation counts, which its tests pin.
//!
//! Every operation that can run user code, fail, or touch the world survives
//! in its original order, so a program answers, refuses and prints exactly as
//! written; it executes fewer instructions and needs fewer frames, so it can
//! finish under a step or frame ceiling the unoptimized program exceeds.
//! Merging two values into one is sound only where no operation consumes a
//! value, so a function is rewritten only when every operand it passes is
//! borrowed or scalar, and a callee is absorbed only under the same rule.
//! The result is validated again; on a validation error the caller keeps the
//! program as written.

use super::{
    Block, BlockId, EffectClass, Function, FunctionId, Operation, Program, Terminator,
    ValidatedProgram, ValidationError, ValidationLimits, ValueId, validate,
};
use crate::flbc::ArgumentOwnership;
use std::collections::{BTreeMap, BTreeSet};

/// Rewrite rounds per function. Each round exposes the next link of a
/// closure-passing chain (matcher, then alternative, then recursive call).
const ROUNDS: usize = 8;
/// A callee is absorbed only when it is at most this large...
const INLINE_BINDINGS: usize = 48;
const INLINE_BLOCKS: usize = 8;
/// ...only while the caller stays below this many bindings...
const CALLER_BINDINGS: usize = 1_024;
/// ...and at most this many times per function and round, never absorbing a
/// function twice into one block in a round, so recursion cannot unroll.
const ABSORPTIONS_PER_ROUND: usize = 16;

/// Simplify every function of `program`, then validate the result.
pub fn optimize(
    program: &ValidatedProgram,
    limits: ValidationLimits,
) -> Result<ValidatedProgram, ValidationError> {
    let mut work = program.program.clone();
    // Absorbing copies a body, so it never adds a call-graph edge the original
    // lacked; the cycles found here are all the cycles there will be.
    let recursive = recursive_functions(&work);
    for index in 0..work.functions.len() {
        if !function_is_plain(&work, &work.functions[index]) {
            continue;
        }
        let mut function = work.functions[index].clone();
        for _ in 0..ROUNDS {
            let mut changed = direct_calls(&work, &mut function);
            changed |= inline_calls(&work, &recursive, &mut function);
            changed |= expose_tail_calls(&work, &mut function);
            changed |= drop_dead(&work, &mut function);
            if !changed {
                break;
            }
        }
        renumber(&mut function);
        work.functions[index] = function;
    }
    validate(work, limits)
}

const fn plain(ownership: ArgumentOwnership) -> bool {
    !ownership.consumes()
}

fn function_at(program: &Program, id: FunctionId) -> Option<&Function> {
    id.index().and_then(|index| program.functions.get(index))
}

/// No operand of `function`, and no parameter, is ever consumed: every value
/// stays readable for the whole activation, so one value may stand for two.
fn function_is_plain(program: &Program, function: &Function) -> bool {
    function.parameter_ownership.iter().copied().all(plain)
        && function
            .blocks
            .iter()
            .flat_map(|block| &block.bindings)
            .all(|binding| match &binding.operation {
                Operation::Intrinsic { intrinsic, .. } => intrinsic
                    .index()
                    .and_then(|index| program.intrinsics.get(index))
                    .is_some_and(|declaration| {
                        declaration.argument_ownership.iter().copied().all(plain)
                    }),
                Operation::Call { function, .. } => function_at(program, *function)
                    .is_some_and(|callee| callee.parameter_ownership.iter().copied().all(plain)),
                Operation::Closure {
                    capture_ownership, ..
                } => capture_ownership.iter().copied().all(plain),
                Operation::Apply {
                    argument_ownership, ..
                } => argument_ownership.iter().copied().all(plain),
                _ => true,
            })
}

fn binding_count(function: &Function) -> usize {
    function
        .blocks
        .iter()
        .map(|block| block.bindings.len())
        .sum()
}

/// A closure value whose target and leading arguments are known statically:
/// a `Closure` binding, or a partial application of one.
#[derive(Clone)]
struct KnownCallable {
    target: FunctionId,
    prefix: Vec<ValueId>,
}

fn known_callables(program: &Program, function: &Function) -> BTreeMap<ValueId, KnownCallable> {
    let mut known = BTreeMap::new();
    // Bindings may sit in table order after their uses' blocks, so iterate
    // until the map stops growing; each pass adds at least one entry or ends.
    loop {
        let before = known.len();
        for binding in function.blocks.iter().flat_map(|block| &block.bindings) {
            if known.contains_key(&binding.id) {
                continue;
            }
            let entry = match &binding.operation {
                Operation::Closure {
                    function: target,
                    captures,
                    ..
                } => Some(KnownCallable {
                    target: *target,
                    prefix: captures.clone(),
                }),
                Operation::Apply { closure, args, .. } => {
                    known.get(closure).and_then(|inner: &KnownCallable| {
                        let arity = function_at(program, inner.target)?.parameters.len();
                        let prefix: Vec<ValueId> =
                            inner.prefix.iter().chain(args).copied().collect();
                        (prefix.len() < arity).then_some(KnownCallable {
                            target: inner.target,
                            prefix,
                        })
                    })
                }
                _ => None,
            };
            if let Some(entry) = entry {
                known.insert(binding.id, entry);
            }
        }
        if known.len() == before {
            return known;
        }
    }
}

/// A saturated `Apply` of a known callable becomes the direct `Call` it
/// performs: same target, same arguments, same result contract (FIR validation
/// binds a closure signature to its target's parameters and result).
fn direct_calls(program: &Program, function: &mut Function) -> bool {
    let known = known_callables(program, function);
    let mut changed = false;
    for binding in function
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.bindings)
    {
        let Operation::Apply { closure, args, .. } = &binding.operation else {
            continue;
        };
        let Some(callable) = known.get(closure) else {
            continue;
        };
        let Some(callee) = function_at(program, callable.target) else {
            continue;
        };
        if callable.prefix.len() + args.len() != callee.parameters.len()
            || !callee.parameter_ownership.iter().copied().all(plain)
        {
            continue;
        }
        let args = callable.prefix.iter().chain(args).copied().collect();
        binding.operation = Operation::Call {
            function: callable.target,
            args,
        };
        changed = true;
    }
    changed
}

/// The callee body, with parameters replaced by `args` and every binding given
/// a fresh id from `next_value`. Block ids are left as the callee's own.
fn instantiate(callee: &Function, args: &[ValueId], next_value: &mut u32) -> Vec<Block> {
    let mut map: BTreeMap<ValueId, ValueId> = BTreeMap::new();
    for (index, arg) in args.iter().enumerate() {
        if let Ok(raw) = u32::try_from(index) {
            map.insert(ValueId::new(raw), *arg);
        }
    }
    for binding in callee.blocks.iter().flat_map(|block| &block.bindings) {
        map.insert(binding.id, ValueId::new(*next_value));
        *next_value = next_value.saturating_add(1);
    }
    let rename = |value: ValueId| map.get(&value).copied().unwrap_or(value);
    callee
        .blocks
        .iter()
        .map(|block| {
            let mut block = block.clone();
            for binding in &mut block.bindings {
                binding.id = rename(binding.id);
                rename_operation(&mut binding.operation, &rename);
            }
            rename_terminator(&mut block.terminator, &rename);
            block
        })
        .collect()
}

/// Functions on a cycle of direct calls and closure constructions. Absorbing
/// one would unroll its recursion into the caller; it is called instead.
fn recursive_functions(program: &Program) -> BTreeSet<FunctionId> {
    let edges: Vec<Vec<usize>> = program
        .functions
        .iter()
        .map(|function| {
            let mut targets: Vec<usize> = function
                .blocks
                .iter()
                .flat_map(|block| &block.bindings)
                .filter_map(|binding| match &binding.operation {
                    Operation::Call { function, .. } | Operation::Closure { function, .. } => {
                        function.index()
                    }
                    _ => None,
                })
                .filter(|target| *target < program.functions.len())
                .collect();
            targets.sort_unstable();
            targets.dedup();
            targets
        })
        .collect();
    // Iterative Tarjan: a node is recursive when its component has two nodes
    // or it has an edge to itself.
    let count = edges.len();
    let mut index_of = vec![usize::MAX; count];
    let mut low = vec![0usize; count];
    let mut on_stack = vec![false; count];
    let mut stack = Vec::new();
    let mut next_index = 0usize;
    let mut recursive = BTreeSet::new();
    for root in 0..count {
        if index_of[root] != usize::MAX {
            continue;
        }
        let mut frames: Vec<(usize, usize)> = vec![(root, 0)];
        index_of[root] = next_index;
        low[root] = next_index;
        next_index += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&mut (node, ref mut edge)) = frames.last_mut() {
            if let Some(&target) = edges[node].get(*edge) {
                *edge += 1;
                if index_of[target] == usize::MAX {
                    index_of[target] = next_index;
                    low[target] = next_index;
                    next_index += 1;
                    stack.push(target);
                    on_stack[target] = true;
                    frames.push((target, 0));
                } else if on_stack[target] {
                    low[node] = low[node].min(index_of[target]);
                }
                continue;
            }
            frames.pop();
            if let Some(&(parent, _)) = frames.last() {
                low[parent] = low[parent].min(low[node]);
            }
            if low[node] == index_of[node] {
                let mut component = Vec::new();
                while let Some(member) = stack.pop() {
                    on_stack[member] = false;
                    component.push(member);
                    if member == node {
                        break;
                    }
                }
                let cyclic = component.len() > 1 || edges[node].contains(&node);
                if cyclic {
                    for member in component {
                        if let Ok(raw) = u32::try_from(member) {
                            recursive.insert(FunctionId::new(raw));
                        }
                    }
                }
            }
        }
    }
    recursive
}

fn absorbable(
    program: &Program,
    recursive: &BTreeSet<FunctionId>,
    caller: &Function,
    target: FunctionId,
) -> Option<Function> {
    if target == caller.id || recursive.contains(&target) {
        return None;
    }
    let callee = function_at(program, target)?;
    (callee.blocks.len() <= INLINE_BLOCKS
        && binding_count(callee) <= INLINE_BINDINGS
        && function_is_plain(program, callee))
    .then(|| callee.clone())
}

fn next_value_id(function: &Function) -> u32 {
    let parameters = u32::try_from(function.parameters.len()).unwrap_or(u32::MAX);
    function
        .blocks
        .iter()
        .flat_map(|block| &block.bindings)
        .map(|binding| binding.id.get().saturating_add(1))
        .max()
        .unwrap_or(0)
        .max(parameters)
}

fn targets_entry(blocks: &[Block]) -> bool {
    blocks.iter().any(|block| match block.terminator {
        Terminator::Jump { target } => target.get() == 0,
        Terminator::BranchZero { zero, nonzero, .. } => zero.get() == 0 || nonzero.get() == 0,
        Terminator::Return { .. } | Terminator::Panic { .. } => false,
    })
}

/// Replace one call per block by the callee's body: a tail call by any small
/// callee, any other call by a single-block callee ending in `Return`.
fn inline_calls(
    program: &Program,
    recursive: &BTreeSet<FunctionId>,
    function: &mut Function,
) -> bool {
    let mut changed = false;
    let mut block_index = 0;
    let mut absorptions = 0;
    let mut absorbed: BTreeSet<(usize, FunctionId)> = BTreeSet::new();
    while block_index < function.blocks.len() {
        if binding_count(function) >= CALLER_BINDINGS || absorptions >= ABSORPTIONS_PER_ROUND {
            break;
        }
        let block = &function.blocks[block_index];
        let tail = match (block.bindings.last(), &block.terminator) {
            (Some(binding), Terminator::Return { value }) if *value == binding.id => {
                Some(binding.id)
            }
            _ => None,
        };
        let candidate = block
            .bindings
            .iter()
            .enumerate()
            .find_map(|(position, binding)| {
                let Operation::Call {
                    function: target,
                    args,
                } = &binding.operation
                else {
                    return None;
                };
                if absorbed.contains(&(block_index, *target)) {
                    return None;
                }
                let callee = absorbable(program, recursive, function, *target)?;
                let in_tail = tail == Some(binding.id)
                    && callee.result == function.result
                    && callee.result_ownership == function.result_ownership;
                let single = callee.blocks.len() == 1
                    && matches!(callee.blocks[0].terminator, Terminator::Return { .. });
                // Validated FIR never targets an entry block; refuse rather than
                // misplace one should that ever change.
                ((in_tail || single) && !targets_entry(&callee.blocks))
                    .then(|| (position, args.clone(), callee, in_tail))
            });
        let Some((position, args, callee, in_tail)) = candidate else {
            block_index += 1;
            continue;
        };
        let Ok(base) = u32::try_from(function.blocks.len()) else {
            break;
        };
        absorbed.insert((block_index, callee.id));
        absorptions += 1;
        let mut next_value = next_value_id(function);
        let mut body = instantiate(&callee, &args, &mut next_value);
        let entry = body.remove(0);
        let returned = match entry.terminator {
            Terminator::Return { value } => Some(value),
            _ => None,
        };
        if !in_tail && returned.is_none() {
            block_index += 1;
            continue;
        }
        let caller = &mut function.blocks[block_index];
        let call = caller.bindings.remove(position);
        let rest = caller.bindings.split_off(position);
        caller.bindings.extend(entry.bindings);
        if in_tail {
            // The call was the block's last binding, so `rest` is empty. The
            // callee's entry continues this block and its other blocks follow
            // the caller's; FIR gives an entry block no predecessors, so no
            // callee edge needs the entry as a separate block.
            let offset = |target: BlockId| BlockId::new(base + target.get().saturating_sub(1));
            let mut terminator = entry.terminator;
            retarget(&mut terminator, &offset);
            caller.terminator = terminator;
            for (index, mut block) in body.into_iter().enumerate() {
                retarget(&mut block.terminator, &offset);
                block.id = BlockId::new(base + u32::try_from(index).unwrap_or(u32::MAX));
                function.blocks.push(block);
            }
        } else if let Some(value) = returned {
            caller.bindings.extend(rest);
            let rename = |id: ValueId| if id == call.id { value } else { id };
            rename_function(function, &rename);
        }
        changed = true;
        // Revisit this block: the absorbed body may itself end in a call.
    }
    changed
}

/// Pure `Nat` primitives that run no code and are total on `Nat`.
const MOVABLE_INTRINSICS: [&str; 8] = [
    "extern:Nat.add",
    "extern:Nat.beq",
    "extern:Nat.ble",
    "extern:Nat.decEq",
    "extern:Nat.decLe",
    "extern:Nat.decLt",
    "extern:Nat.pred",
    "extern:Nat.sub",
];

/// Whether `operation` runs no code and touches nothing but its operands, so
/// it may run before a call instead of after it.
fn movable(program: &Program, operation: &Operation) -> bool {
    match operation {
        Operation::Unit
        | Operation::Bool(_)
        | Operation::Nat(_)
        | Operation::NatBig(_)
        | Operation::String(_)
        | Operation::Alias(_)
        | Operation::Box(_)
        | Operation::Unbox { .. }
        | Operation::Ctor { .. }
        | Operation::CtorTest { .. }
        | Operation::Array { .. }
        | Operation::Closure { .. } => true,
        Operation::Intrinsic { intrinsic, .. } => intrinsic
            .index()
            .and_then(|index| program.intrinsics.get(index))
            .is_some_and(|declaration| {
                declaration.effect == EffectClass::Pure
                    && MOVABLE_INTRINSICS.contains(&declaration.row.as_str())
            }),
        _ => false,
    }
}

/// A call whose value its block returns, followed only by unread work that
/// runs no code and reads nothing the call produced, moves after that work:
/// the call then ends its block and lowers to a tail call. The work still runs,
/// once, in the same block, so every evaluation count stays as written.
///
/// Ingress leaves exactly this shape in every structural `succ` case, where the
/// rebuilt `k + 1` follows the recursive call; it is what kept such a loop one
/// frame deeper per iteration. The one ordering change: a `Nat.add` whose
/// magnitude check fails now stops before the call rather than after it,
/// which differs only when that call itself panics or stops first.
fn expose_tail_calls(program: &Program, function: &mut Function) -> bool {
    let mut changed = false;
    for block in &mut function.blocks {
        let Terminator::Return { value } = block.terminator else {
            continue;
        };
        let Some(position) = block
            .bindings
            .iter()
            .position(|binding| binding.id == value)
        else {
            continue;
        };
        if position + 1 == block.bindings.len()
            || !matches!(
                block.bindings[position].operation,
                Operation::Call { .. } | Operation::Apply { .. }
            )
        {
            continue;
        }
        // A returning block has no successors, so its trailing values can be
        // read only by one another; none may read the call's.
        let trailing_is_movable = block.bindings[position + 1..].iter().all(|binding| {
            movable(program, &binding.operation)
                && binding.operation.reads().all(|read| read != value)
        });
        if trailing_is_movable {
            let call = block.bindings.remove(position);
            block.bindings.push(call);
            changed = true;
        }
    }
    changed
}

/// Drop bindings that run no code, cannot fail, and are never read: literals,
/// copies, aggregates and closures only allocate, and so does a partial
/// application of a known closure. Every call, intrinsic, projection,
/// checkpoint and any other `Apply` stays, even when unread: each is work the
/// program as written performs, and the engine's evaluation-count tests hold
/// it to performing it.
fn drop_dead(program: &Program, function: &mut Function) -> bool {
    let mut changed = false;
    loop {
        // `known_callables` admits an `Apply` only when it supplies fewer
        // arguments than its known target takes: it allocates and runs nothing.
        let partial: BTreeSet<ValueId> = known_callables(program, function).into_keys().collect();
        let mut uses: BTreeMap<ValueId, usize> = BTreeMap::new();
        for block in &function.blocks {
            for binding in &block.bindings {
                for value in binding.operation.reads() {
                    *uses.entry(value).or_default() += 1;
                }
            }
            for value in block.terminator.reads() {
                *uses.entry(*value).or_default() += 1;
            }
        }
        let mut removed = false;
        for block in &mut function.blocks {
            block.bindings.retain(|binding| {
                let dead = !uses.contains_key(&binding.id)
                    && match &binding.operation {
                        Operation::Unit
                        | Operation::Bool(_)
                        | Operation::Nat(_)
                        | Operation::NatBig(_)
                        | Operation::String(_)
                        | Operation::Alias(_)
                        | Operation::Box(_)
                        | Operation::Unbox { .. }
                        | Operation::Ctor { .. }
                        | Operation::CtorTest { .. }
                        | Operation::Array { .. }
                        | Operation::Closure { .. } => true,
                        Operation::Apply { .. } => partial.contains(&binding.id),
                        _ => false,
                    };
                if dead {
                    removed = true;
                }
                !dead
            });
        }
        if !removed {
            return changed;
        }
        changed = true;
    }
}

fn rename_operation(operation: &mut Operation, rename: &impl Fn(ValueId) -> ValueId) {
    match operation {
        Operation::Unit
        | Operation::Bool(_)
        | Operation::Nat(_)
        | Operation::NatBig(_)
        | Operation::String(_)
        | Operation::CheckSystem { .. } => {}
        Operation::Alias(value)
        | Operation::Box(value)
        | Operation::Unbox { value, .. }
        | Operation::CtorTest { value, .. }
        | Operation::Project { value, .. }
        | Operation::CheckSystemValue { module_name: value } => *value = rename(*value),
        Operation::Ctor { fields: values, .. }
        | Operation::Array { items: values }
        | Operation::Intrinsic { args: values, .. }
        | Operation::Call { args: values, .. }
        | Operation::Closure {
            captures: values, ..
        } => {
            for value in values {
                *value = rename(*value);
            }
        }
        Operation::Apply { closure, args, .. } => {
            *closure = rename(*closure);
            for value in args {
                *value = rename(*value);
            }
        }
    }
}

fn rename_terminator(terminator: &mut Terminator, rename: &impl Fn(ValueId) -> ValueId) {
    match terminator {
        Terminator::Jump { .. } => {}
        Terminator::BranchZero { condition, .. } => *condition = rename(*condition),
        Terminator::Return { value } | Terminator::Panic { message: value } => {
            *value = rename(*value);
        }
    }
}

fn retarget(terminator: &mut Terminator, offset: &impl Fn(BlockId) -> BlockId) {
    match terminator {
        Terminator::Jump { target } => *target = offset(*target),
        Terminator::BranchZero { zero, nonzero, .. } => {
            *zero = offset(*zero);
            *nonzero = offset(*nonzero);
        }
        Terminator::Return { .. } | Terminator::Panic { .. } => {}
    }
}

fn rename_function(function: &mut Function, rename: &impl Fn(ValueId) -> ValueId) {
    for block in &mut function.blocks {
        for binding in &mut block.bindings {
            rename_operation(&mut binding.operation, rename);
        }
        rename_terminator(&mut block.terminator, rename);
    }
}

/// Restore canonical numbering: parameters first, then bindings in
/// block-table order; blocks keep their table positions.
fn renumber(function: &mut Function) {
    let mut map: BTreeMap<ValueId, ValueId> = BTreeMap::new();
    let mut next = u32::try_from(function.parameters.len()).unwrap_or(u32::MAX);
    for binding in function
        .blocks
        .iter_mut()
        .flat_map(|block| &mut block.bindings)
    {
        map.insert(binding.id, ValueId::new(next));
        binding.id = ValueId::new(next);
        next = next.saturating_add(1);
    }
    let rename = |value: ValueId| map.get(&value).copied().unwrap_or(value);
    rename_function(function, &rename);
    for (position, block) in function.blocks.iter_mut().enumerate() {
        block.id = BlockId::new(u32::try_from(position).unwrap_or(u32::MAX));
    }
}
