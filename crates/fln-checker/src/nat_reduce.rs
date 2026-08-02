//! Checker-owned KR-313 natural-literal expression reduction.
//!
//! The reducer recognizes the pinned operation table directly over checker wire
//! arenas, gates slow-conversion use on a closed candidate pair, normalizes
//! operands with checker WHNF, and delegates arithmetic only to this crate's
//! independent [`crate::numeric`] substrate. Nested arithmetic uses explicit heap
//! frames; no operation depth is represented by the Rust call stack.
//!
//! This is not a general normalizer. Native and String reduction, recursors,
//! typing, declaration admission, and consensus remain outside this module.

use crate::numeric::{
    self, NatBudget, NatComparison, NatFault, NatOperation, NatOutcome, NatProgress, NatRefusal,
    NatStop, NatValue,
};
use crate::term::TermBudget;
use crate::whnf::{
    WhnfBudget, WhnfContext, WhnfFault, WhnfOutcome, WhnfRefusal, WhnfStop, whnf_core_at_with,
    whnf_delta_step_at_with,
};
use crate::wire::{
    ExprId, ExprNode, NamePart, WireExpr, WireName, expression_owned_units, level_owned_units,
    usize_units,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatReductionOperation {
    Successor,
    Add,
    Subtract,
    Multiply,
    Divide,
    Modulo,
    Gcd,
    Power,
    Equal,
    LessEqual,
    BitAnd,
    BitOr,
    BitXor,
    ShiftLeft,
    ShiftRight,
}

impl NatReductionOperation {
    const fn arity(self) -> u8 {
        match self {
            NatReductionOperation::Successor => 1,
            NatReductionOperation::Add
            | NatReductionOperation::Subtract
            | NatReductionOperation::Multiply
            | NatReductionOperation::Divide
            | NatReductionOperation::Modulo
            | NatReductionOperation::Gcd
            | NatReductionOperation::Power
            | NatReductionOperation::Equal
            | NatReductionOperation::LessEqual
            | NatReductionOperation::BitAnd
            | NatReductionOperation::BitOr
            | NatReductionOperation::BitXor
            | NatReductionOperation::ShiftLeft
            | NatReductionOperation::ShiftRight => 2,
        }
    }

    const fn numeric(self) -> Option<NatOperation> {
        match self {
            NatReductionOperation::Successor
            | NatReductionOperation::Equal
            | NatReductionOperation::LessEqual => None,
            NatReductionOperation::Add => Some(NatOperation::Add),
            NatReductionOperation::Subtract => Some(NatOperation::Subtract),
            NatReductionOperation::Multiply => Some(NatOperation::Multiply),
            NatReductionOperation::Divide => Some(NatOperation::Divide),
            NatReductionOperation::Modulo => Some(NatOperation::Modulo),
            NatReductionOperation::Gcd => Some(NatOperation::Gcd),
            NatReductionOperation::Power => Some(NatOperation::Power),
            NatReductionOperation::BitAnd => Some(NatOperation::BitAnd),
            NatReductionOperation::BitOr => Some(NatOperation::BitOr),
            NatReductionOperation::BitXor => Some(NatOperation::BitXor),
            NatReductionOperation::ShiftLeft => Some(NatOperation::ShiftLeft),
            NatReductionOperation::ShiftRight => Some(NatOperation::ShiftRight),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NatReductionBudget {
    pub max_steps: u64,
    pub max_work_items: u64,
    pub max_generated_arenas: u64,
    pub max_materialized_arena_nodes: u64,
    pub max_materialized_owned_units: u64,
    pub max_output_units: u64,
    pub whnf: WhnfBudget,
    pub numeric: NatBudget,
}

impl NatReductionBudget {
    #[allow(clippy::too_many_arguments)]
    pub const fn new(
        max_steps: u64,
        max_work_items: u64,
        max_generated_arenas: u64,
        max_materialized_arena_nodes: u64,
        max_materialized_owned_units: u64,
        max_output_units: u64,
        whnf: WhnfBudget,
        numeric: NatBudget,
    ) -> NatReductionBudget {
        NatReductionBudget {
            max_steps,
            max_work_items,
            max_generated_arenas,
            max_materialized_arena_nodes,
            max_materialized_owned_units,
            max_output_units,
            whnf,
            numeric,
        }
    }

    pub const fn unlimited() -> NatReductionBudget {
        NatReductionBudget::new(
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            WhnfBudget::unlimited(),
            NatBudget::unlimited(),
        )
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct NatReductionProgress {
    pub steps: u64,
    pub work_items: u64,
    pub generated_arenas: u64,
    pub whnf_steps: u64,
    pub whnf_reductions: u64,
    pub delta_unfolds: u64,
    pub numeric_steps: u64,
    pub numeric_materialized_limbs: u64,
    pub numeric_reductions: u64,
    pub materialized_arena_nodes: u64,
    pub materialized_owned_units: u64,
    pub output_units: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatReductionLimit {
    Steps,
    WorkItems,
    GeneratedArenas,
    MaterializedArenaNodes,
    MaterializedOwnedUnits,
    OutputUnits,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatReductionInput {
    Candidate,
    Companion,
    Generated { index: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatReductionOperand {
    First,
    Second,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatReductionPhase {
    OperandCore,
    OperandDelta,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NatReductionAllocation {
    ClosedWalk,
    EvaluationFrames,
    GeneratedArenas,
    LiteralLimbs,
    OutputNodes,
    BoolNameParts,
    BoolNameText,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatNotReduced {
    HeadNotConstant,
    HeadHasLevels,
    UnknownHead,
    Arity {
        operation: NatReductionOperation,
        expected: u8,
        actual: u64,
    },
    OpenPair {
        input: NatReductionInput,
    },
    OperandNotNatural {
        operand: NatReductionOperand,
    },
    PowExponentAbovePinCap {
        cap: u64,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatReductionRefusal {
    Whnf {
        phase: NatReductionPhase,
        refusal: WhnfRefusal,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatReductionStop {
    Resource {
        limit: NatReductionLimit,
        allowed: u64,
        observed: u64,
        at: usize,
        progress: NatReductionProgress,
    },
    Cancelled {
        at: usize,
        polls: u64,
        progress: NatReductionProgress,
    },
    AllocationFailed {
        allocation: NatReductionAllocation,
        requested: u64,
        progress: NatReductionProgress,
    },
    OutputSizeOverflow {
        progress: NatReductionProgress,
    },
    Whnf {
        phase: NatReductionPhase,
        stop: WhnfStop,
        progress: NatReductionProgress,
    },
    Numeric {
        operation: NatReductionOperation,
        stop: NatStop,
        progress: NatReductionProgress,
    },
}

impl NatReductionStop {
    pub const fn progress(&self) -> NatReductionProgress {
        match self {
            NatReductionStop::Resource { progress, .. }
            | NatReductionStop::Cancelled { progress, .. }
            | NatReductionStop::AllocationFailed { progress, .. }
            | NatReductionStop::OutputSizeOverflow { progress }
            | NatReductionStop::Whnf { progress, .. }
            | NatReductionStop::Numeric { progress, .. } => *progress,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatReductionFault {
    MissingGeneratedArena {
        index: usize,
    },
    MissingExpression {
        input: NatReductionInput,
        index: usize,
    },
    NonBackwardExpressionReference {
        input: NatReductionInput,
        parent: usize,
        child: usize,
    },
    NonCanonicalNatLiteral {
        input: NatReductionInput,
        index: usize,
    },
    Whnf {
        phase: NatReductionPhase,
        fault: WhnfFault,
    },
    Numeric {
        operation: NatReductionOperation,
        fault: NatFault,
    },
    ValueStack {
        operation: NatReductionOperation,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NatReductionResult {
    pub term: WireExpr,
    pub operation: NatReductionOperation,
    pub progress: NatReductionProgress,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NatReductionOutcome {
    Reduced(NatReductionResult),
    NotReduced {
        reason: NatNotReduced,
        progress: NatReductionProgress,
    },
    Refused {
        refusal: NatReductionRefusal,
        progress: NatReductionProgress,
    },
    Inconclusive(NatReductionStop),
    InternalFault(NatReductionFault),
}

enum Halt {
    Refusal {
        refusal: Box<NatReductionRefusal>,
        progress: NatReductionProgress,
    },
    Stop(Box<NatReductionStop>),
    Fault(NatReductionFault),
}

impl Halt {
    fn stop(stop: NatReductionStop) -> Halt {
        Halt::Stop(Box::new(stop))
    }
}

#[derive(Clone, Copy)]
enum ArenaSource {
    Candidate,
    Generated(usize),
}

impl ArenaSource {
    const fn input(self) -> NatReductionInput {
        match self {
            ArenaSource::Candidate => NatReductionInput::Candidate,
            ArenaSource::Generated(index) => NatReductionInput::Generated { index },
        }
    }
}

#[derive(Clone, Copy)]
struct Cursor {
    source: ArenaSource,
    root: ExprId,
}

#[derive(Clone, Copy)]
struct Parsed {
    operation: NatReductionOperation,
    operands: [Option<ExprId>; 2],
}

struct EvalFrame {
    cursor: Cursor,
    operation: NatReductionOperation,
    operands: [Option<ExprId>; 2],
    values: [Option<NatValue>; 2],
    next_operand: u8,
    top_level: bool,
}

enum EvalState {
    Seek {
        cursor: Cursor,
        core_normalized: bool,
    },
    ForceDelta(Cursor),
    Natural(NatValue),
    NonNatural,
}

enum Executed {
    Natural(NatValue),
    Boolean(bool),
    PowCap(u64),
}

struct MaterializationAdmission {
    arena_nodes: u64,
    owned_units: u64,
}

struct Control<'a> {
    budget: NatReductionBudget,
    progress: NatReductionProgress,
    polls: u64,
    cancelled: &'a mut dyn FnMut() -> bool,
}

impl<'a> Control<'a> {
    fn new(budget: NatReductionBudget, cancelled: &'a mut dyn FnMut() -> bool) -> Control<'a> {
        Control {
            budget,
            progress: NatReductionProgress::default(),
            polls: 0,
            cancelled,
        }
    }

    fn poll(&mut self, at: usize) -> Result<(), Halt> {
        self.polls = self.polls.saturating_add(1);
        if (self.cancelled)() {
            return Err(Halt::stop(NatReductionStop::Cancelled {
                at,
                polls: self.polls,
                progress: self.progress,
            }));
        }
        Ok(())
    }

    fn step(&mut self, at: usize) -> Result<(), Halt> {
        self.poll(at)?;
        let observed = self.progress.steps.saturating_add(1);
        if observed > self.budget.max_steps {
            return Err(Halt::stop(NatReductionStop::Resource {
                limit: NatReductionLimit::Steps,
                allowed: self.budget.max_steps,
                observed,
                at,
                progress: self.progress,
            }));
        }
        self.progress.steps = observed;
        Ok(())
    }

    fn push_work<T>(
        &mut self,
        stack: &mut Vec<T>,
        value: T,
        at: usize,
        allocation: NatReductionAllocation,
    ) -> Result<(), Halt> {
        self.poll(at)?;
        let observed = self.progress.work_items.saturating_add(1);
        if observed > self.budget.max_work_items {
            return Err(Halt::stop(NatReductionStop::Resource {
                limit: NatReductionLimit::WorkItems,
                allowed: self.budget.max_work_items,
                observed,
                at,
                progress: self.progress,
            }));
        }
        stack.try_reserve(1).map_err(|_| {
            Halt::stop(NatReductionStop::AllocationFailed {
                allocation,
                requested: 1,
                progress: self.progress,
            })
        })?;
        stack.push(value);
        self.progress.work_items = observed;
        Ok(())
    }

    fn prepare_materialization(
        &mut self,
        arena_nodes: u64,
        owned_units: u64,
        at: usize,
    ) -> Result<MaterializationAdmission, Halt> {
        self.poll(at)?;
        let observed_nodes = self
            .progress
            .materialized_arena_nodes
            .checked_add(arena_nodes)
            .ok_or(Halt::stop(NatReductionStop::OutputSizeOverflow {
                progress: self.progress,
            }))?;
        if observed_nodes > self.budget.max_materialized_arena_nodes {
            return Err(Halt::stop(NatReductionStop::Resource {
                limit: NatReductionLimit::MaterializedArenaNodes,
                allowed: self.budget.max_materialized_arena_nodes,
                observed: observed_nodes,
                at,
                progress: self.progress,
            }));
        }
        let observed_units = self
            .progress
            .materialized_owned_units
            .checked_add(owned_units)
            .ok_or(Halt::stop(NatReductionStop::OutputSizeOverflow {
                progress: self.progress,
            }))?;
        if observed_units > self.budget.max_materialized_owned_units {
            return Err(Halt::stop(NatReductionStop::Resource {
                limit: NatReductionLimit::MaterializedOwnedUnits,
                allowed: self.budget.max_materialized_owned_units,
                observed: observed_units,
                at,
                progress: self.progress,
            }));
        }
        Ok(MaterializationAdmission {
            arena_nodes: observed_nodes,
            owned_units: observed_units,
        })
    }

    fn commit_materialization(&mut self, admission: MaterializationAdmission) {
        self.progress.materialized_arena_nodes = admission.arena_nodes;
        self.progress.materialized_owned_units = admission.owned_units;
    }

    fn retain_generated(
        &mut self,
        generated: &mut Vec<WireExpr>,
        term: WireExpr,
        at: usize,
    ) -> Result<Cursor, Halt> {
        let arena_nodes = usize_units(term.nodes().len())
            .checked_add(usize_units(term.levels().len()))
            .ok_or(Halt::stop(NatReductionStop::OutputSizeOverflow {
                progress: self.progress,
            }))?;
        let owned_units = term
            .nodes()
            .iter()
            .fold(0_u64, |units, node| {
                units.saturating_add(expression_owned_units(node))
            })
            .saturating_add(term.levels().iter().fold(0_u64, |units, node| {
                units.saturating_add(level_owned_units(node))
            }));
        let admission = self.prepare_materialization(arena_nodes, owned_units, at)?;
        let observed = self.progress.generated_arenas.saturating_add(1);
        if observed > self.budget.max_generated_arenas {
            return Err(Halt::stop(NatReductionStop::Resource {
                limit: NatReductionLimit::GeneratedArenas,
                allowed: self.budget.max_generated_arenas,
                observed,
                at,
                progress: self.progress,
            }));
        }
        generated.try_reserve(1).map_err(|_| {
            Halt::stop(NatReductionStop::AllocationFailed {
                allocation: NatReductionAllocation::GeneratedArenas,
                requested: 1,
                progress: self.progress,
            })
        })?;
        let root = term.root();
        let index = generated.len();
        generated.push(term);
        self.commit_materialization(admission);
        self.progress.generated_arenas = observed;
        Ok(Cursor {
            source: ArenaSource::Generated(index),
            root,
        })
    }

    fn remaining_whnf(&self) -> WhnfBudget {
        WhnfBudget::new(
            self.budget
                .whnf
                .max_steps
                .saturating_sub(self.progress.whnf_steps),
            self.budget
                .whnf
                .max_reductions
                .saturating_sub(self.progress.whnf_reductions),
            self.budget.whnf.materialization,
        )
    }

    fn absorb_whnf(&mut self, result: &crate::whnf::WhnfResult) {
        self.progress.whnf_steps = self.progress.whnf_steps.saturating_add(result.steps);
        self.progress.whnf_reductions = self
            .progress
            .whnf_reductions
            .saturating_add(result.reductions);
        self.progress.delta_unfolds = self
            .progress
            .delta_unfolds
            .saturating_add(result.delta_reductions);
    }

    fn remaining_numeric(&self) -> NatBudget {
        NatBudget::new(
            self.budget
                .numeric
                .max_steps
                .saturating_sub(self.progress.numeric_steps),
            self.budget
                .numeric
                .max_materialized_limbs
                .saturating_sub(self.progress.numeric_materialized_limbs),
        )
    }

    fn absorb_numeric(&mut self, progress: NatProgress) {
        self.progress.numeric_steps = self.progress.numeric_steps.saturating_add(progress.steps);
        self.progress.numeric_materialized_limbs = self
            .progress
            .numeric_materialized_limbs
            .saturating_add(progress.materialized_limbs);
    }

    fn output(&mut self, units: u64, at: usize) -> Result<(), Halt> {
        self.poll(at)?;
        let observed = self
            .progress
            .output_units
            .checked_add(units)
            .ok_or(Halt::stop(NatReductionStop::OutputSizeOverflow {
                progress: self.progress,
            }))?;
        if observed > self.budget.max_output_units {
            return Err(Halt::stop(NatReductionStop::Resource {
                limit: NatReductionLimit::OutputUnits,
                allowed: self.budget.max_output_units,
                observed,
                at,
                progress: self.progress,
            }));
        }
        self.progress.output_units = observed;
        Ok(())
    }
}

fn text_name(name: &WireName, namespace: &str, leaf: &str) -> bool {
    matches!(
        name.parts(),
        [NamePart::Text(actual_namespace), NamePart::Text(actual_leaf)]
            if actual_namespace == namespace && actual_leaf == leaf
    )
}

fn operation_for_name(name: &WireName) -> Option<NatReductionOperation> {
    let [NamePart::Text(namespace), NamePart::Text(leaf)] = name.parts() else {
        return None;
    };
    if namespace != "Nat" {
        return None;
    }
    match leaf.as_str() {
        "succ" => Some(NatReductionOperation::Successor),
        "add" => Some(NatReductionOperation::Add),
        "sub" => Some(NatReductionOperation::Subtract),
        "mul" => Some(NatReductionOperation::Multiply),
        "div" => Some(NatReductionOperation::Divide),
        "mod" => Some(NatReductionOperation::Modulo),
        "gcd" => Some(NatReductionOperation::Gcd),
        "pow" => Some(NatReductionOperation::Power),
        "beq" => Some(NatReductionOperation::Equal),
        "ble" => Some(NatReductionOperation::LessEqual),
        "land" => Some(NatReductionOperation::BitAnd),
        "lor" => Some(NatReductionOperation::BitOr),
        "xor" => Some(NatReductionOperation::BitXor),
        "shiftLeft" => Some(NatReductionOperation::ShiftLeft),
        "shiftRight" => Some(NatReductionOperation::ShiftRight),
        _ => None,
    }
}

fn parse_application(
    term: &WireExpr,
    input: NatReductionInput,
    root: ExprId,
    control: &mut Control<'_>,
) -> Result<Result<Parsed, NatNotReduced>, Halt> {
    let mut current = root;
    let mut outer_operands = [None, None];
    let mut argument_count = 0_u64;
    loop {
        control.step(current.index())?;
        let node = term
            .node(current)
            .ok_or(Halt::Fault(NatReductionFault::MissingExpression {
                input,
                index: current.index(),
            }))?;
        let ExprNode::Apply { function, argument } = node else {
            break;
        };
        validate_child(input, current, *function)?;
        validate_child(input, current, *argument)?;
        if argument_count < 2 {
            outer_operands[argument_count as usize] = Some(*argument);
        }
        argument_count = argument_count.saturating_add(1);
        current = *function;
    }

    control.step(current.index())?;
    let head = term
        .node(current)
        .ok_or(Halt::Fault(NatReductionFault::MissingExpression {
            input,
            index: current.index(),
        }))?;
    let ExprNode::Constant { name, levels } = head else {
        return Ok(Err(NatNotReduced::HeadNotConstant));
    };
    let Some(operation) = operation_for_name(name) else {
        return Ok(Err(NatNotReduced::UnknownHead));
    };
    if !levels.is_empty() {
        return Ok(Err(NatNotReduced::HeadHasLevels));
    }
    if argument_count != u64::from(operation.arity()) {
        return Ok(Err(NatNotReduced::Arity {
            operation,
            expected: operation.arity(),
            actual: argument_count,
        }));
    }
    let operands = match operation.arity() {
        1 => [outer_operands[0], None],
        2 => [outer_operands[1], outer_operands[0]],
        _ => return Err(Halt::Fault(NatReductionFault::ValueStack { operation })),
    };
    Ok(Ok(Parsed {
        operation,
        operands,
    }))
}

fn parse_application_unmetered(term: &WireExpr, root: ExprId) -> Option<Parsed> {
    let mut current = root;
    let mut outer_operands = [None, None];
    let mut argument_count = 0_u64;
    while let ExprNode::Apply { function, argument } = term.node(current)? {
        if function.index() >= current.index() || argument.index() >= current.index() {
            return None;
        }
        if argument_count < 2 {
            outer_operands[argument_count as usize] = Some(*argument);
        }
        argument_count = argument_count.saturating_add(1);
        current = *function;
    }
    let ExprNode::Constant { name, levels } = term.node(current)? else {
        return None;
    };
    let operation = operation_for_name(name)?;
    if !levels.is_empty() || argument_count != u64::from(operation.arity()) {
        return None;
    }
    Some(Parsed {
        operation,
        operands: match operation.arity() {
            1 => [outer_operands[0], None],
            2 => [outer_operands[1], outer_operands[0]],
            _ => return None,
        },
    })
}

pub(crate) fn is_potential_nat_reduction(term: &WireExpr, root: ExprId) -> bool {
    parse_application_unmetered(term, root).is_some()
}

fn validate_child(input: NatReductionInput, parent: ExprId, child: ExprId) -> Result<(), Halt> {
    if child.index() >= parent.index() {
        return Err(Halt::Fault(
            NatReductionFault::NonBackwardExpressionReference {
                input,
                parent: parent.index(),
                child: child.index(),
            },
        ));
    }
    Ok(())
}

fn push_child(
    stack: &mut Vec<ExprId>,
    child: ExprId,
    parent: ExprId,
    input: NatReductionInput,
    control: &mut Control<'_>,
) -> Result<(), Halt> {
    validate_child(input, parent, child)?;
    control.push_work(
        stack,
        child,
        parent.index(),
        NatReductionAllocation::ClosedWalk,
    )
}

fn is_closed(
    term: &WireExpr,
    input: NatReductionInput,
    root: ExprId,
    control: &mut Control<'_>,
) -> Result<bool, Halt> {
    let mut pending = Vec::new();
    control.push_work(
        &mut pending,
        root,
        root.index(),
        NatReductionAllocation::ClosedWalk,
    )?;
    while let Some(current) = pending.pop() {
        control.step(current.index())?;
        let node = term
            .node(current)
            .ok_or(Halt::Fault(NatReductionFault::MissingExpression {
                input,
                index: current.index(),
            }))?;
        match node {
            ExprNode::Free { .. } => return Ok(false),
            ExprNode::Bound { .. }
            | ExprNode::Meta { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Constant { .. }
            | ExprNode::StringLiteral(_) => {}
            ExprNode::NatLiteral { limbs_le } => {
                if limbs_le.last() == Some(&0) {
                    return Err(Halt::Fault(NatReductionFault::NonCanonicalNatLiteral {
                        input,
                        index: current.index(),
                    }));
                }
            }
            ExprNode::Apply { function, argument } => {
                push_child(&mut pending, *function, current, input, control)?;
                push_child(&mut pending, *argument, current, input, control)?;
            }
            ExprNode::Lambda {
                binder_type, body, ..
            }
            | ExprNode::Forall {
                binder_type, body, ..
            } => {
                push_child(&mut pending, *binder_type, current, input, control)?;
                push_child(&mut pending, *body, current, input, control)?;
            }
            ExprNode::Let {
                type_, value, body, ..
            } => {
                push_child(&mut pending, *type_, current, input, control)?;
                push_child(&mut pending, *value, current, input, control)?;
                push_child(&mut pending, *body, current, input, control)?;
            }
            ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                push_child(&mut pending, *expression, current, input, control)?;
            }
        }
    }
    Ok(true)
}

fn source_term<'a>(
    source: ArenaSource,
    candidate: &'a WireExpr,
    generated: &'a [WireExpr],
) -> Result<&'a WireExpr, Halt> {
    match source {
        ArenaSource::Candidate => Ok(candidate),
        ArenaSource::Generated(index) => {
            generated
                .get(index)
                .ok_or(Halt::Fault(NatReductionFault::MissingGeneratedArena {
                    index,
                }))
        }
    }
}

fn direct_natural(
    cursor: Cursor,
    candidate: &WireExpr,
    generated: &[WireExpr],
    control: &mut Control<'_>,
) -> Result<Option<NatValue>, Halt> {
    let term = source_term(cursor.source, candidate, generated)?;
    let input = cursor.source.input();
    control.step(cursor.root.index())?;
    let node = term
        .node(cursor.root)
        .ok_or(Halt::Fault(NatReductionFault::MissingExpression {
            input,
            index: cursor.root.index(),
        }))?;
    match node {
        ExprNode::NatLiteral { limbs_le } => {
            if limbs_le.last() == Some(&0) {
                return Err(Halt::Fault(NatReductionFault::NonCanonicalNatLiteral {
                    input,
                    index: cursor.root.index(),
                }));
            }
            let owned_units = usize_units(limbs_le.len());
            let admission = control.prepare_materialization(0, owned_units, cursor.root.index())?;
            let mut copied = Vec::new();
            copied.try_reserve_exact(limbs_le.len()).map_err(|_| {
                Halt::stop(NatReductionStop::AllocationFailed {
                    allocation: NatReductionAllocation::LiteralLimbs,
                    requested: owned_units,
                    progress: control.progress,
                })
            })?;
            for limb in limbs_le {
                control.step(cursor.root.index())?;
                copied.push(*limb);
            }
            let value = NatValue::from_limbs_le(copied).map_err(|_| {
                Halt::Fault(NatReductionFault::NonCanonicalNatLiteral {
                    input,
                    index: cursor.root.index(),
                })
            })?;
            control.commit_materialization(admission);
            Ok(Some(value))
        }
        ExprNode::Constant { name, levels }
            if levels.is_empty() && text_name(name, "Nat", "zero") =>
        {
            Ok(Some(NatValue::zero()))
        }
        _ => Ok(None),
    }
}

fn normalize_cursor(
    cursor: Cursor,
    phase: NatReductionPhase,
    candidate: &WireExpr,
    generated: &mut Vec<WireExpr>,
    context: &WhnfContext,
    control: &mut Control<'_>,
) -> Result<(Cursor, bool), Halt> {
    let outcome = {
        let term = source_term(cursor.source, candidate, generated)?;
        let budget = control.remaining_whnf();
        match phase {
            NatReductionPhase::OperandCore => {
                whnf_core_at_with(term, cursor.root, context, budget, control.cancelled)
            }
            NatReductionPhase::OperandDelta => {
                whnf_delta_step_at_with(term, cursor.root, context, budget, control.cancelled)
            }
        }
    };
    match outcome {
        WhnfOutcome::Complete(result) => {
            let changed = match phase {
                NatReductionPhase::OperandCore => result.reductions != 0,
                NatReductionPhase::OperandDelta => result.delta_reductions != 0,
            };
            control.absorb_whnf(&result);
            let next = control.retain_generated(generated, result.term, cursor.root.index())?;
            Ok((next, changed))
        }
        WhnfOutcome::Refused(refusal) => Err(Halt::Refusal {
            refusal: Box::new(NatReductionRefusal::Whnf { phase, refusal }),
            progress: control.progress,
        }),
        WhnfOutcome::Inconclusive(stop) => Err(Halt::stop(NatReductionStop::Whnf {
            phase,
            stop,
            progress: control.progress,
        })),
        WhnfOutcome::InternalFault(fault) => {
            Err(Halt::Fault(NatReductionFault::Whnf { phase, fault }))
        }
    }
}

fn nat_stop_progress(stop: &NatStop) -> NatProgress {
    match stop {
        NatStop::Resource { progress, .. }
        | NatStop::Cancelled { progress, .. }
        | NatStop::OutputSizeOverflow { progress, .. }
        | NatStop::AllocationFailed { progress, .. } => *progress,
    }
}

fn execute_successor(value: &NatValue, control: &mut Control<'_>) -> Result<Executed, Halt> {
    let operation = NatReductionOperation::Successor;
    let budget = control.remaining_numeric();
    let outcome = numeric::successor_with(value, budget, || (control.cancelled)());
    match outcome {
        NatOutcome::Complete(result) => {
            control.absorb_numeric(result.progress);
            control.progress.numeric_reductions =
                control.progress.numeric_reductions.saturating_add(1);
            Ok(Executed::Natural(result.value))
        }
        NatOutcome::Refused { refusal, progress } => {
            control.absorb_numeric(progress);
            match refusal {
                NatRefusal::PowExponentAbovePinCap { cap } => Ok(Executed::PowCap(cap)),
            }
        }
        NatOutcome::Inconclusive(stop) => {
            control.absorb_numeric(nat_stop_progress(&stop));
            Err(Halt::stop(NatReductionStop::Numeric {
                operation,
                stop,
                progress: control.progress,
            }))
        }
        NatOutcome::InternalFault(fault) => {
            Err(Halt::Fault(NatReductionFault::Numeric { operation, fault }))
        }
    }
}

fn execute_binary(
    operation: NatReductionOperation,
    left: &NatValue,
    right: &NatValue,
    control: &mut Control<'_>,
) -> Result<Executed, Halt> {
    if matches!(
        operation,
        NatReductionOperation::Equal | NatReductionOperation::LessEqual
    ) {
        let budget = control.remaining_numeric();
        let outcome = numeric::compare_with(left, right, budget, || (control.cancelled)());
        return match outcome {
            NatOutcome::Complete(result) => {
                control.absorb_numeric(result.progress);
                control.progress.numeric_reductions =
                    control.progress.numeric_reductions.saturating_add(1);
                Ok(Executed::Boolean(match operation {
                    NatReductionOperation::Equal => result.value == NatComparison::Equal,
                    NatReductionOperation::LessEqual => result.value != NatComparison::Greater,
                    _ => false,
                }))
            }
            NatOutcome::Refused { refusal, progress } => {
                control.absorb_numeric(progress);
                match refusal {
                    NatRefusal::PowExponentAbovePinCap { cap } => Ok(Executed::PowCap(cap)),
                }
            }
            NatOutcome::Inconclusive(stop) => {
                control.absorb_numeric(nat_stop_progress(&stop));
                Err(Halt::stop(NatReductionStop::Numeric {
                    operation,
                    stop,
                    progress: control.progress,
                }))
            }
            NatOutcome::InternalFault(fault) => {
                Err(Halt::Fault(NatReductionFault::Numeric { operation, fault }))
            }
        };
    }

    let numeric_operation = operation
        .numeric()
        .ok_or(Halt::Fault(NatReductionFault::ValueStack { operation }))?;
    let budget = control.remaining_numeric();
    let outcome = numeric::binary_with(numeric_operation, left, right, budget, || {
        (control.cancelled)()
    });
    match outcome {
        NatOutcome::Complete(result) => {
            control.absorb_numeric(result.progress);
            control.progress.numeric_reductions =
                control.progress.numeric_reductions.saturating_add(1);
            Ok(Executed::Natural(result.value))
        }
        NatOutcome::Refused { refusal, progress } => {
            control.absorb_numeric(progress);
            match refusal {
                NatRefusal::PowExponentAbovePinCap { cap } => Ok(Executed::PowCap(cap)),
            }
        }
        NatOutcome::Inconclusive(stop) => {
            control.absorb_numeric(nat_stop_progress(&stop));
            Err(Halt::stop(NatReductionStop::Numeric {
                operation,
                stop,
                progress: control.progress,
            }))
        }
        NatOutcome::InternalFault(fault) => {
            Err(Halt::Fault(NatReductionFault::Numeric { operation, fault }))
        }
    }
}

fn execute_frame(frame: &mut EvalFrame, control: &mut Control<'_>) -> Result<Executed, Halt> {
    match frame.operation.arity() {
        1 => {
            let value =
                frame.values[0]
                    .take()
                    .ok_or(Halt::Fault(NatReductionFault::ValueStack {
                        operation: frame.operation,
                    }))?;
            execute_successor(&value, control)
        }
        2 => {
            let left =
                frame.values[0]
                    .take()
                    .ok_or(Halt::Fault(NatReductionFault::ValueStack {
                        operation: frame.operation,
                    }))?;
            let right =
                frame.values[1]
                    .take()
                    .ok_or(Halt::Fault(NatReductionFault::ValueStack {
                        operation: frame.operation,
                    }))?;
            execute_binary(frame.operation, &left, &right, control)
        }
        _ => Err(Halt::Fault(NatReductionFault::ValueStack {
            operation: frame.operation,
        })),
    }
}

fn bool_name(value: bool, control: &mut Control<'_>) -> Result<WireName, Halt> {
    let leaf = if value { "true" } else { "false" };
    let units = 2_u64
        .saturating_add(usize_units("Bool".len()))
        .saturating_add(usize_units(leaf.len()));
    control.output(units, 0)?;
    let mut parts = Vec::new();
    parts.try_reserve_exact(2).map_err(|_| {
        Halt::stop(NatReductionStop::AllocationFailed {
            allocation: NatReductionAllocation::BoolNameParts,
            requested: 2,
            progress: control.progress,
        })
    })?;
    for text in ["Bool", leaf] {
        let mut owned = String::new();
        owned.try_reserve_exact(text.len()).map_err(|_| {
            Halt::stop(NatReductionStop::AllocationFailed {
                allocation: NatReductionAllocation::BoolNameText,
                requested: usize_units(text.len()),
                progress: control.progress,
            })
        })?;
        owned.push_str(text);
        parts.push(NamePart::Text(owned));
    }
    Ok(WireName::from_parts(parts))
}

fn output_term(
    executed: Executed,
    operation: NatReductionOperation,
    control: &mut Control<'_>,
) -> Result<WireExpr, Halt> {
    let node = match executed {
        Executed::Natural(value) => {
            let units = 1_u64.saturating_add(usize_units(value.limbs_le().len()));
            control.output(units, 0)?;
            ExprNode::NatLiteral {
                limbs_le: value.into_limbs_le(),
            }
        }
        Executed::Boolean(value) => {
            control.output(1, 0)?;
            ExprNode::Constant {
                name: bool_name(value, control)?,
                levels: Vec::new(),
            }
        }
        Executed::PowCap(_) => {
            return Err(Halt::Fault(NatReductionFault::ValueStack { operation }));
        }
    };
    let mut nodes = Vec::new();
    nodes.try_reserve_exact(1).map_err(|_| {
        Halt::stop(NatReductionStop::AllocationFailed {
            allocation: NatReductionAllocation::OutputNodes,
            requested: 1,
            progress: control.progress,
        })
    })?;
    nodes.push(node);
    let root = ExprId::from_index(0).ok_or(Halt::stop(NatReductionStop::OutputSizeOverflow {
        progress: control.progress,
    }))?;
    Ok(WireExpr::from_parts(nodes, Vec::new(), root))
}

fn frame_from(parsed: Parsed, cursor: Cursor, top_level: bool) -> Result<EvalFrame, Halt> {
    if parsed.operands[0].is_none()
        || (parsed.operation.arity() == 2 && parsed.operands[1].is_none())
    {
        return Err(Halt::Fault(NatReductionFault::ValueStack {
            operation: parsed.operation,
        }));
    }
    Ok(EvalFrame {
        cursor,
        operation: parsed.operation,
        operands: parsed.operands,
        values: [None, None],
        next_operand: 0,
        top_level,
    })
}

fn current_operand(frame: &EvalFrame) -> Result<Cursor, Halt> {
    let operand = frame.operands[usize::from(frame.next_operand)].ok_or(Halt::Fault(
        NatReductionFault::ValueStack {
            operation: frame.operation,
        },
    ))?;
    Ok(Cursor {
        source: frame.cursor.source,
        root: operand,
    })
}

fn operand_identity(index: u8) -> NatReductionOperand {
    if index == 0 {
        NatReductionOperand::First
    } else {
        NatReductionOperand::Second
    }
}

fn reduce_inner(
    candidate: &WireExpr,
    candidate_root: ExprId,
    companion: &WireExpr,
    companion_root: ExprId,
    context: &WhnfContext,
    budget: NatReductionBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<NatReductionOutcome, Halt> {
    let mut control = Control::new(budget, cancelled);
    let parsed = match parse_application(
        candidate,
        NatReductionInput::Candidate,
        candidate_root,
        &mut control,
    )? {
        Ok(parsed) => parsed,
        Err(reason) => {
            return Ok(NatReductionOutcome::NotReduced {
                reason,
                progress: control.progress,
            });
        }
    };

    if !is_closed(
        candidate,
        NatReductionInput::Candidate,
        candidate_root,
        &mut control,
    )? {
        return Ok(NatReductionOutcome::NotReduced {
            reason: NatNotReduced::OpenPair {
                input: NatReductionInput::Candidate,
            },
            progress: control.progress,
        });
    }
    if !is_closed(
        companion,
        NatReductionInput::Companion,
        companion_root,
        &mut control,
    )? {
        return Ok(NatReductionOutcome::NotReduced {
            reason: NatNotReduced::OpenPair {
                input: NatReductionInput::Companion,
            },
            progress: control.progress,
        });
    }

    let top_cursor = Cursor {
        source: ArenaSource::Candidate,
        root: candidate_root,
    };
    let mut frames = Vec::new();
    let top_frame = frame_from(parsed, top_cursor, true)?;
    let first = current_operand(&top_frame)?;
    control.push_work(
        &mut frames,
        top_frame,
        candidate_root.index(),
        NatReductionAllocation::EvaluationFrames,
    )?;
    let mut state = EvalState::Seek {
        cursor: first,
        core_normalized: false,
    };
    let mut generated = Vec::new();
    let mut context_validated = false;

    loop {
        state = match state {
            EvalState::Seek {
                cursor,
                core_normalized,
            } => {
                if context_validated
                    && let Some(value) =
                        direct_natural(cursor, candidate, &generated, &mut control)?
                {
                    EvalState::Natural(value)
                } else {
                    let nested = {
                        let term = source_term(cursor.source, candidate, &generated)?;
                        parse_application_unmetered(term, cursor.root)
                    };
                    if let Some(parsed) = nested {
                        let frame = frame_from(parsed, cursor, false)?;
                        let first = current_operand(&frame)?;
                        control.push_work(
                            &mut frames,
                            frame,
                            cursor.root.index(),
                            NatReductionAllocation::EvaluationFrames,
                        )?;
                        EvalState::Seek {
                            cursor: first,
                            core_normalized: false,
                        }
                    } else if !core_normalized {
                        let (next, _) = normalize_cursor(
                            cursor,
                            NatReductionPhase::OperandCore,
                            candidate,
                            &mut generated,
                            context,
                            &mut control,
                        )?;
                        context_validated = true;
                        EvalState::Seek {
                            cursor: next,
                            core_normalized: true,
                        }
                    } else if let Some(value) =
                        direct_natural(cursor, candidate, &generated, &mut control)?
                    {
                        EvalState::Natural(value)
                    } else {
                        EvalState::ForceDelta(cursor)
                    }
                }
            }
            EvalState::ForceDelta(cursor) => {
                let (next, changed) = normalize_cursor(
                    cursor,
                    NatReductionPhase::OperandDelta,
                    candidate,
                    &mut generated,
                    context,
                    &mut control,
                )?;
                context_validated = true;
                if changed {
                    EvalState::Seek {
                        cursor: next,
                        core_normalized: false,
                    }
                } else {
                    EvalState::NonNatural
                }
            }
            EvalState::Natural(value) => {
                let frame =
                    frames
                        .last_mut()
                        .ok_or(Halt::Fault(NatReductionFault::ValueStack {
                            operation: parsed.operation,
                        }))?;
                frame.values[usize::from(frame.next_operand)] = Some(value);
                if frame.next_operand + 1 < frame.operation.arity() {
                    frame.next_operand += 1;
                    EvalState::Seek {
                        cursor: current_operand(frame)?,
                        core_normalized: false,
                    }
                } else {
                    let mut frame =
                        frames
                            .pop()
                            .ok_or(Halt::Fault(NatReductionFault::ValueStack {
                                operation: parsed.operation,
                            }))?;
                    let executed = execute_frame(&mut frame, &mut control)?;
                    match executed {
                        Executed::Natural(value) if frame.top_level => {
                            let term = output_term(
                                Executed::Natural(value),
                                frame.operation,
                                &mut control,
                            )?;
                            return Ok(NatReductionOutcome::Reduced(NatReductionResult {
                                term,
                                operation: frame.operation,
                                progress: control.progress,
                            }));
                        }
                        Executed::Boolean(value) if frame.top_level => {
                            let term = output_term(
                                Executed::Boolean(value),
                                frame.operation,
                                &mut control,
                            )?;
                            return Ok(NatReductionOutcome::Reduced(NatReductionResult {
                                term,
                                operation: frame.operation,
                                progress: control.progress,
                            }));
                        }
                        Executed::PowCap(cap) => {
                            return Ok(NatReductionOutcome::NotReduced {
                                reason: NatNotReduced::PowExponentAbovePinCap { cap },
                                progress: control.progress,
                            });
                        }
                        Executed::Natural(value) => EvalState::Natural(value),
                        Executed::Boolean(_) => EvalState::NonNatural,
                    }
                }
            }
            EvalState::NonNatural => {
                let frame = frames
                    .pop()
                    .ok_or(Halt::Fault(NatReductionFault::ValueStack {
                        operation: parsed.operation,
                    }))?;
                if frame.top_level {
                    return Ok(NatReductionOutcome::NotReduced {
                        reason: NatNotReduced::OperandNotNatural {
                            operand: operand_identity(frame.next_operand),
                        },
                        progress: control.progress,
                    });
                }
                EvalState::ForceDelta(frame.cursor)
            }
        };
    }
}

pub fn reduce_nat(
    candidate: &WireExpr,
    companion: &WireExpr,
    context: &WhnfContext,
    budget: NatReductionBudget,
) -> NatReductionOutcome {
    reduce_nat_with(candidate, companion, context, budget, || false)
}

pub fn reduce_nat_with(
    candidate: &WireExpr,
    companion: &WireExpr,
    context: &WhnfContext,
    budget: NatReductionBudget,
    mut cancelled: impl FnMut() -> bool,
) -> NatReductionOutcome {
    reduce_nat_at_with(
        candidate,
        candidate.root(),
        companion,
        companion.root(),
        context,
        budget,
        &mut cancelled,
    )
}

pub(crate) fn reduce_nat_at_with(
    candidate: &WireExpr,
    candidate_root: ExprId,
    companion: &WireExpr,
    companion_root: ExprId,
    context: &WhnfContext,
    budget: NatReductionBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> NatReductionOutcome {
    match reduce_inner(
        candidate,
        candidate_root,
        companion,
        companion_root,
        context,
        budget,
        cancelled,
    ) {
        Ok(outcome) => outcome,
        Err(Halt::Refusal { refusal, progress }) => NatReductionOutcome::Refused {
            refusal: *refusal,
            progress,
        },
        Err(Halt::Stop(stop)) => NatReductionOutcome::Inconclusive(*stop),
        Err(Halt::Fault(fault)) => NatReductionOutcome::InternalFault(fault),
    }
}
