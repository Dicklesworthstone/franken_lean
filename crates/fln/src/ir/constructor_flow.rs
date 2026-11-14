//! Conservative constructor domains for private direct-call parameters.
//!
//! FIR's `Constructor` carrier deliberately forgets the source family. Recover
//! only facts proved by actual producers and calls: a case test is not evidence
//! of exhaustiveness. Every parameter of an address-taken function stays unknown
//! because an escaping closure can receive arguments outside this program.
//!
//! The monotone analysis visits every syntactic block, without guessing branch
//! reachability. Bottom means no flow has arrived yet, not an impossible runtime
//! value. Neither bottom nor unknown becomes a restriction in the exporter.

use super::{Budget, CompileError, ConstructorTags, InternalConstructors, Result, fir, invariant};

#[cfg(test)]
mod tests;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Target {
    function: usize,
    remaining: usize,
}

enum Fact {
    Bottom,
    Unknown,
    Constructors(ConstructorTags),
    Closures(Vec<Target>),
}

impl Fact {
    fn copy(&self, meter: &mut Budget) -> Result<Self> {
        meter.charge(1)?;
        Ok(match self {
            Self::Bottom => Self::Bottom,
            Self::Unknown => Self::Unknown,
            Self::Constructors(tags) => Self::Constructors(*tags),
            Self::Closures(targets) => {
                meter.charge(targets.len())?;
                let mut result = Vec::new();
                result
                    .try_reserve_exact(targets.len())
                    .map_err(|_| CompileError::Allocation)?;
                result.extend_from_slice(targets);
                Self::Closures(result)
            }
        })
    }

    fn join(&mut self, incoming: &Self, meter: &mut Budget) -> Result<bool> {
        meter.charge(1)?;
        if matches!(self, Self::Unknown) || matches!(incoming, Self::Bottom) {
            return Ok(false);
        }
        if matches!(incoming, Self::Unknown) {
            *self = Self::Unknown;
            return Ok(true);
        }
        if matches!(self, Self::Bottom) {
            *self = incoming.copy(meter)?;
            return Ok(true);
        }
        match (self, incoming) {
            (Self::Constructors(tags), Self::Constructors(other)) => {
                let before = *tags;
                for (word, other) in tags.0.iter_mut().zip(other.0) {
                    *word |= other;
                }
                Ok(*tags != before)
            }
            (Self::Closures(targets), Self::Closures(other)) => {
                let mut changed = false;
                for target in other {
                    // Insertion shifts the tail; charge the whole current set
                    // as well as the lookup rather than hiding quadratic work.
                    meter.charge(targets.len().saturating_add(1))?;
                    if let Err(index) = targets.binary_search(target) {
                        targets
                            .try_reserve(1)
                            .map_err(|_| CompileError::Allocation)?;
                        targets.insert(index, *target);
                        changed = true;
                    }
                }
                Ok(changed)
            }
            (slot, _) => {
                // Validation prevents mixed carriers. Staying unknown is still
                // conservative if a future representation admits such a join.
                *slot = Self::Unknown;
                Ok(true)
            }
        }
    }
}

struct FunctionFacts {
    values: Vec<Fact>,
    result: Fact,
}

fn value(
    functions: &[FunctionFacts],
    function: usize,
    value: fir::ValueId,
    meter: &mut Budget,
) -> Result<Fact> {
    functions
        .get(function)
        .and_then(|function| function.values.get(value.get() as usize))
        .ok_or_else(|| invariant("constructor flow value"))?
        .copy(meter)
}

fn result(functions: &[FunctionFacts], function: usize, meter: &mut Budget) -> Result<Fact> {
    functions
        .get(function)
        .ok_or_else(|| invariant("constructor flow callee"))?
        .result
        .copy(meter)
}

fn operation(
    program: &fir::ValidatedProgram,
    constructors: &InternalConstructors,
    functions: &mut [FunctionFacts],
    caller: usize,
    operation: &fir::Operation,
    changed: &mut bool,
    meter: &mut Budget,
) -> Result<Fact> {
    meter.charge(1)?;
    match operation {
        fir::Operation::Ctor { constructor, .. } => {
            let declaration = program
                .constructors()
                .get(constructor.get() as usize)
                .ok_or_else(|| invariant("constructor flow layout"))?;
            let fields =
                u16::try_from(declaration.fields.len()).map_err(|_| CompileError::Limit)?;
            let tag = constructors.tag(declaration.tag, fields)?;
            Ok(Fact::Constructors(ConstructorTags::singleton(tag)))
        }
        fir::Operation::Alias(source) => value(functions, caller, *source, meter),
        fir::Operation::Closure {
            function, captures, ..
        } => {
            let target = function.get() as usize;
            let remaining = program
                .functions()
                .get(target)
                .ok_or_else(|| invariant("constructor flow closure target"))?
                .parameters
                .len()
                .checked_sub(captures.len())
                .ok_or_else(|| invariant("constructor flow capture arity"))?;
            let mut targets = Vec::new();
            targets
                .try_reserve_exact(1)
                .map_err(|_| CompileError::Allocation)?;
            targets.push(Target {
                function: target,
                remaining,
            });
            Ok(Fact::Closures(targets))
        }
        fir::Operation::Call { function, args } => {
            let callee = function.get() as usize;
            if program
                .functions()
                .get(callee)
                .is_none_or(|function| function.parameters.len() != args.len())
            {
                return Err(invariant("constructor flow call arity"));
            }
            for (index, argument) in args.iter().enumerate() {
                let argument = value(functions, caller, *argument, meter)?;
                let parameter = functions
                    .get_mut(callee)
                    .and_then(|function| function.values.get_mut(index))
                    .ok_or_else(|| invariant("constructor flow parameter"))?;
                *changed |= parameter.join(&argument, meter)?;
            }
            result(functions, callee, meter)
        }
        fir::Operation::Apply { closure, args, .. } => {
            match value(functions, caller, *closure, meter)? {
                Fact::Bottom => Ok(Fact::Bottom),
                Fact::Closures(targets) => {
                    let mut applied = Fact::Bottom;
                    for target in targets {
                        meter.charge(1)?;
                        // Only a fully saturated literal target supplies a
                        // result fact. Partial and staged overapplication keep
                        // their existing unconstrained export behavior.
                        if target.remaining != args.len() {
                            return Ok(Fact::Unknown);
                        }
                        let returned = result(functions, target.function, meter)?;
                        applied.join(&returned, meter)?;
                    }
                    Ok(applied)
                }
                _ => Ok(Fact::Unknown),
            }
        }
        // In particular, projections, ABI casts, intrinsics and effects grant
        // no constructor-family or closure-target evidence.
        _ => Ok(Fact::Unknown),
    }
}

pub(super) fn parameters(
    program: &fir::ValidatedProgram,
    constructors: &InternalConstructors,
    meter: &mut Budget,
) -> Result<Vec<Vec<ConstructorTags>>> {
    meter.charge(program.functions().len())?;
    let mut exposed = Vec::new();
    exposed
        .try_reserve_exact(program.functions().len())
        .map_err(|_| CompileError::Allocation)?;
    exposed.resize(program.functions().len(), false);
    *exposed
        .get_mut(program.entry().get() as usize)
        .ok_or_else(|| invariant("constructor flow entry"))? = true;
    for function in program.functions() {
        for binding in function.blocks.iter().flat_map(|block| &block.bindings) {
            meter.charge(1)?;
            if let fir::Operation::Closure { function, .. } = binding.operation {
                *exposed
                    .get_mut(function.get() as usize)
                    .ok_or_else(|| invariant("constructor flow exposed target"))? = true;
            }
        }
    }
    let mut functions = Vec::new();
    functions
        .try_reserve_exact(program.functions().len())
        .map_err(|_| CompileError::Allocation)?;
    for function in program.functions() {
        // FIR validation requires dense, canonical ValueIds: parameters first,
        // then bindings in block-table order. Calls preserve FunctionIds when
        // FIR lowers to FLBC, so the exported rows use that same table index.
        let mut count = function.parameters.len();
        for block in &function.blocks {
            meter.charge(1)?;
            count = count
                .checked_add(block.bindings.len())
                .ok_or(CompileError::Limit)?;
        }
        meter.charge(count)?;
        let mut values = Vec::new();
        values
            .try_reserve_exact(count)
            .map_err(|_| CompileError::Allocation)?;
        values.resize_with(count, || Fact::Bottom);
        for (index, ty) in function.parameters.iter().enumerate() {
            if exposed[function.id.get() as usize]
                || !matches!(ty, fir::ValueType::Constructor | fir::ValueType::Closure(_))
            {
                values[index] = Fact::Unknown;
            }
        }
        functions.push(FunctionFacts {
            values,
            result: Fact::Bottom,
        });
    }
    loop {
        let mut changed = false;
        for function in program.functions() {
            meter.charge(1)?;
            let caller = function.id.get() as usize;
            for block in &function.blocks {
                meter.charge(1)?;
                for binding in &block.bindings {
                    let produced = operation(
                        program,
                        constructors,
                        &mut functions,
                        caller,
                        &binding.operation,
                        &mut changed,
                        meter,
                    )?;
                    let destination = functions
                        .get_mut(caller)
                        .and_then(|function| function.values.get_mut(binding.id.get() as usize))
                        .ok_or_else(|| invariant("constructor flow destination"))?;
                    changed |= destination.join(&produced, meter)?;
                }
                if let fir::Terminator::Return { value: returned } = block.terminator {
                    let returned = value(&functions, caller, returned, meter)?;
                    changed |= functions[caller].result.join(&returned, meter)?;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let mut masks = Vec::new();
    masks
        .try_reserve_exact(functions.len())
        .map_err(|_| CompileError::Allocation)?;
    for (function, facts) in program.functions().iter().zip(functions) {
        meter.charge(function.parameters.len().saturating_add(1))?;
        let mut parameters = Vec::new();
        parameters
            .try_reserve_exact(function.parameters.len())
            .map_err(|_| CompileError::Allocation)?;
        for (index, ty) in function.parameters.iter().enumerate() {
            parameters.push(match (&facts.values[index], ty) {
                (Fact::Constructors(tags), fir::ValueType::Constructor) if !tags.is_empty() => {
                    *tags
                }
                _ => ConstructorTags::default(),
            });
        }
        masks.push(parameters);
    }
    Ok(masks)
}
