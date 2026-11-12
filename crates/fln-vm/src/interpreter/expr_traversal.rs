//! Callback-driven Expr search and replacement. User callbacks run in ordinary
//! Golem frames; the host only advances a bounded iterative traversal. Checked
//! views preserve original object identities and the pin's sharing-sensitive
//! memoization, while all reconstruction stays inside the converter membrane.

use std::collections::{HashMap, HashSet};

use super::{
    ApplyPlan, ArgumentOwnership, FunctionId, Obj, PreparedApply, ValidatedProgram, VmRefusal,
    exact_owned_args, finish_apply, plan_apply, type_mismatch,
};
use fln_core::expr::{ExprNode, MAX_LOOSE_BVAR_RANGE};
use fln_core::level::MAX_LEVEL_DEPTH;
use fln_rt::convert::{CheckedExpr, Conversion, ConvertError};

const MAX_TRAVERSAL_WORK: usize = 1_000_000;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum Intrinsic {
    Replace,
    Find,
    FindExt,
}

impl Intrinsic {
    pub(super) fn for_row(row: &str) -> Option<Self> {
        Some(match row {
            "extern:Lean.Expr.replaceImpl" => Self::Replace,
            "extern:Lean.Expr.findImpl?" => Self::Find,
            "extern:Lean.Expr.findExtImpl?" => Self::FindExt,
            _ => return None,
        })
    }

    fn operation(self) -> &'static str {
        match self {
            Self::Replace => "Expr.replaceImpl",
            Self::Find => "Expr.findImpl?",
            Self::FindExt => "Expr.findExtImpl?",
        }
    }
}

#[derive(Debug)]
pub(super) enum Failure {
    Refused(VmRefusal),
    Resource {
        resource: &'static str,
        allowed: u64,
        observed: u64,
    },
}

impl From<VmRefusal> for Failure {
    fn from(value: VmRefusal) -> Self {
        Self::Refused(value)
    }
}

impl From<ConvertError> for Failure {
    fn from(value: ConvertError) -> Self {
        match value {
            ConvertError::NodeBudgetExhausted {
                visited, budget, ..
            } => Self::Resource {
                resource: "expression traversal projection/rebuild nodes",
                allowed: budget as u64,
                observed: visited as u64,
            },
            ConvertError::ByteBudgetExhausted {
                visited, budget, ..
            } => Self::Resource {
                resource: "expression traversal projection/rebuild bytes",
                allowed: budget as u64,
                observed: visited as u64,
            },
            ConvertError::NativeOverflow { family: "level" } => Self::Resource {
                resource: "universe level depth",
                allowed: u64::from(MAX_LEVEL_DEPTH),
                observed: u64::from(MAX_LEVEL_DEPTH) + 1,
            },
            ConvertError::NativeOverflow { .. } => Self::Resource {
                resource: "expression loose bound variable range",
                allowed: u64::from(MAX_LOOSE_BVAR_RANGE),
                observed: u64::MAX,
            },
            _ => Self::Refused(VmRefusal::InvalidCtorObject),
        }
    }
}

pub(super) struct State {
    intrinsic: Intrinsic,
    callback: Obj,
    // Keep every original node alive while identity tokens index the memo.
    // Replacement results can otherwise release the last ancestor of a node.
    _root: CheckedExpr,
    conversion: Conversion,
    tasks: Vec<Task>,
    pending: Option<CheckedExpr>,
    results: Vec<CheckedExpr>,
    replacements: HashMap<usize, CheckedExpr>,
    checked_outputs: HashMap<usize, CheckedExpr>,
    visited: HashSet<usize>,
    work: usize,
    allowed: usize,
}

enum Task {
    Visit(CheckedExpr),
    // findExt visits an application head and its arguments, but never invokes
    // the callback on the intermediate applications in the function spine.
    Spine(CheckedExpr),
    Rebuild { original: CheckedExpr, base: usize },
}

pub(super) enum Step {
    Complete(Obj),
    Call {
        function: FunctionId,
        args: Vec<Obj>,
        state: Box<State>,
    },
}

pub(super) fn start(
    program: &ValidatedProgram,
    intrinsic: Intrinsic,
    row: &str,
    args: Vec<Obj>,
) -> Result<Step, Failure> {
    start_bounded(program, intrinsic, row, args, MAX_TRAVERSAL_WORK)
}

fn start_bounded(
    program: &ValidatedProgram,
    intrinsic: Intrinsic,
    row: &str,
    args: Vec<Obj>,
    allowed: usize,
) -> Result<Step, Failure> {
    let [callback, input] = exact_owned_args::<2>(row, args)?;
    callback_plan(program, &callback)?;
    let allowed = allowed.min(MAX_TRAVERSAL_WORK);
    let mut conversion = Conversion::with_node_budget(allowed);
    let root = conversion.check_expr(&input)?;
    advance(
        program,
        Box::new(State {
            intrinsic,
            callback,
            tasks: vec![Task::Visit(root.clone())],
            _root: root,
            conversion,
            pending: None,
            results: Vec::new(),
            replacements: HashMap::new(),
            checked_outputs: HashMap::new(),
            visited: HashSet::new(),
            work: 0,
            allowed,
        }),
    )
}

pub(super) fn resume(
    program: &ValidatedProgram,
    mut state: Box<State>,
    value: Obj,
) -> Result<Step, Failure> {
    let current = state.pending.take().ok_or(VmRefusal::InvalidCtorObject)?;
    match state.intrinsic {
        Intrinsic::Replace => match replacement(&value, state.intrinsic.operation())? {
            Some(value) => {
                // Returning the original node is already checked. All other
                // distinct callback results cross the same aggregate bounded
                // membrane. Retaining checked outputs prevents identity reuse
                // and avoids repeatedly projecting a shared captured result.
                let key = value.identity_token();
                let result = if key == current.object().identity_token() {
                    current.clone()
                } else if let Some(result) = state.checked_outputs.get(&key) {
                    result.clone()
                } else {
                    state.conversion.check_expr(&value)?
                };
                state.checked_outputs.insert(key, result.clone());
                state.save_replacement(current, result);
            }
            None => {
                let children = current.children()?;
                if children.is_empty() {
                    state.save_replacement(current.clone(), current);
                } else {
                    let base = state.results.len();
                    state.tasks.push(Task::Rebuild {
                        original: current,
                        base,
                    });
                    state
                        .tasks
                        .extend(children.into_iter().rev().map(Task::Visit));
                }
            }
        },
        Intrinsic::Find | Intrinsic::FindExt => {
            let decision = find_decision(&value, state.intrinsic)?;
            if decision == FindDecision::Found {
                return Ok(Step::Complete(Obj::mk_ctor(
                    1,
                    vec![current.object().clone_ref()],
                    &[],
                )));
            }
            if decision == FindDecision::Visit {
                let mut children = current.children()?;
                if state.intrinsic == Intrinsic::FindExt
                    && matches!(current.expression().node(), ExprNode::App { .. })
                {
                    let argument = children.pop().ok_or(VmRefusal::InvalidCtorObject)?;
                    let function = children.pop().ok_or(VmRefusal::InvalidCtorObject)?;
                    state.tasks.push(Task::Visit(argument));
                    state.tasks.push(Task::Spine(function));
                } else {
                    state
                        .tasks
                        .extend(children.into_iter().rev().map(Task::Visit));
                }
            }
        }
    }
    advance(program, state)
}

impl State {
    fn charge(&mut self) -> Result<(), Failure> {
        self.work = self.work.saturating_add(1);
        if self.work > self.allowed {
            return Err(Failure::Resource {
                resource: "expression traversal work",
                allowed: self.allowed as u64,
                observed: self.work as u64,
            });
        }
        Ok(())
    }

    fn save_replacement(&mut self, original: CheckedExpr, result: CheckedExpr) {
        self.replacements
            .insert(original.object().identity_token(), result.clone());
        self.results.push(result);
    }
}

fn advance(program: &ValidatedProgram, mut state: Box<State>) -> Result<Step, Failure> {
    while let Some(task) = state.tasks.pop() {
        state.charge()?;
        let current = match task {
            Task::Rebuild { original, base } => {
                if base > state.results.len() {
                    return Err(VmRefusal::InvalidCtorObject.into());
                }
                let children = state.results.split_off(base);
                let result = state.conversion.rebuild_expr(&original, &children)?;
                state.save_replacement(original, result);
                continue;
            }
            Task::Spine(current) => {
                if matches!(current.expression().node(), ExprNode::App { .. }) {
                    let mut children = current.children()?;
                    let argument = children.pop().ok_or(VmRefusal::InvalidCtorObject)?;
                    let function = children.pop().ok_or(VmRefusal::InvalidCtorObject)?;
                    state.tasks.push(Task::Visit(argument));
                    state.tasks.push(Task::Spine(function));
                } else {
                    state.tasks.push(Task::Visit(current));
                }
                continue;
            }
            Task::Visit(current) => current,
        };
        let key = current.object().identity_token();
        if state.intrinsic == Intrinsic::Replace {
            if let Some(result) = state.replacements.get(&key).cloned() {
                state.results.push(result);
                continue;
            }
        } else if !matches!(
            current.expression().node(),
            ExprNode::BVar { .. } | ExprNode::Const { .. } | ExprNode::Sort { .. }
        ) && !state.visited.insert(key)
        {
            // The pin calls predicates at every BVar/Const/Sort occurrence;
            // other shared nodes are visited once. Repeated identity implies
            // sharing in this retained immutable input graph.
            continue;
        }
        let plan = callback_plan(program, &state.callback)?;
        let args = vec![current.object().clone_ref()];
        state.pending = Some(current);
        match finish_apply(plan, args, None) {
            PreparedApply::Call { function, args, .. } => {
                return Ok(Step::Call {
                    function,
                    args,
                    state,
                });
            }
            PreparedApply::Partial { .. } => {
                unreachable!("the traversal callback consumes exactly one argument")
            }
        }
    }
    if state.intrinsic == Intrinsic::Replace {
        if state.results.len() != 1 {
            return Err(VmRefusal::InvalidCtorObject.into());
        }
        Ok(Step::Complete(state.results[0].object().clone_ref()))
    } else {
        Ok(Step::Complete(Obj::mk_nat(0)))
    }
}

fn callback_plan(program: &ValidatedProgram, callback: &Obj) -> Result<ApplyPlan, VmRefusal> {
    let plan = plan_apply(program, callback, 1, None, None)?;
    if plan.required != 1 {
        return Err(VmRefusal::MalformedClosure {
            reason: "Expr traversal callback requires exactly one remaining argument",
        });
    }
    let function = program
        .function(plan.function)
        .ok_or(VmRefusal::MalformedClosure {
            reason: "target function is absent",
        })?;
    for (argument, expected) in function.parameter_ownership[..plan.captures.len()]
        .iter()
        .copied()
        .enumerate()
    {
        if expected == ArgumentOwnership::Unique {
            return Err(VmRefusal::ApplyOwnershipMismatch {
                function: plan.function,
                argument,
                expected,
                actual: ArgumentOwnership::Borrowed,
            });
        }
    }
    let expected = function.parameter_ownership[plan.captures.len()];
    if matches!(
        expected,
        ArgumentOwnership::Scalar | ArgumentOwnership::Unique
    ) {
        return Err(VmRefusal::ApplyOwnershipMismatch {
            function: plan.function,
            argument: 0,
            expected,
            actual: ArgumentOwnership::Borrowed,
        });
    }
    Ok(plan)
}

fn replacement(value: &Obj, operation: &'static str) -> Result<Option<Obj>, VmRefusal> {
    if value.is_scalar() && value.unbox() == 0 {
        return Ok(None);
    }
    if !value.is_scalar()
        && value.obj_tag() == 1
        && value.header().other == 1
        && value.byte_size() == 16
    {
        return value
            .try_ctor_child(0)
            .map(Some)
            .ok_or(VmRefusal::InvalidCtorObject);
    }
    Err(type_mismatch(
        operation,
        0,
        "Option Expr callback result",
        value,
    ))
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum FindDecision {
    Found,
    Visit,
    Done,
}

fn find_decision(value: &Obj, intrinsic: Intrinsic) -> Result<FindDecision, VmRefusal> {
    if value.is_scalar() {
        match (intrinsic, value.unbox()) {
            (Intrinsic::Find, 0) | (Intrinsic::FindExt, 1) => return Ok(FindDecision::Visit),
            (Intrinsic::Find, 1) | (Intrinsic::FindExt, 0) => return Ok(FindDecision::Found),
            (Intrinsic::FindExt, 2) => return Ok(FindDecision::Done),
            _ => {}
        }
    }
    Err(type_mismatch(
        intrinsic.operation(),
        0,
        if intrinsic == Intrinsic::Find {
            "Bool callback result"
        } else {
            "FindStep callback result"
        },
        value,
    ))
}

#[cfg(test)]
mod tests;
