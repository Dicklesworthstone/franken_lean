//! Resource-counted definitional equality over checker-owned arenas.
//!
//! The KR-300 through KR-303 quick front end proves structural congruence,
//! treats metadata as transparent, ignores binder presentation, and compares
//! `Sort` levels with this checker's independent universe relation. Deferred
//! pairs continue through a slow worklist that first takes a no-delta weak head,
//! checks KR-308 Nat successor offsets, and applies KR-313 Nat reduction. Ordinary
//! queries require a closed pair; the pin's exact eager query may first normalize
//! open operands. It then unfolds safe definition heads one step at a time in
//! descending definitional-height order. At the exact `String.ofList` comparison gate,
//! Unicode String literals expand through the checker-owned KR-314 reducer.
//! Once both heads are stable, the exact `fun x => f x` KR-312 subset contracts
//! through virtual binders, including leading telescopes and nested eta-expanded functions, when `f`
//! does not depend on any of the removed binders. Pi-driven eta,
//! typing, proof irrelevance, recursors, and native computation still produce
//! a typed deferral. A deferral is not a rejection and this module is not a
//! declaration-admission authority.

mod spine;

use std::collections::{BTreeMap, BTreeSet};

use crate::environment::ReducibilityHint;
use crate::term::{TermBudget, TermOutcome, TermStop, copy_compact_subterm_with};

use crate::nat_reduce::{
    NatReductionBudget, NatReductionFault, NatReductionOutcome, NatReductionProgress,
    NatReductionQuery, NatReductionRefusal, NatReductionScope, NatReductionStop,
    is_potential_nat_reduction, reduce_nat_at_with,
};
use crate::numeric::NatBudget;
use crate::string_reduce::{
    StringExpansionBudget, StringExpansionFault, StringExpansionOutcome, StringExpansionProgress,
    StringExpansionStop, expand_string_literal_with,
};
use crate::universe::{UniverseError, level_roots_equal};
use crate::whnf::{
    WhnfBudget, WhnfContext, WhnfFault, WhnfOutcome, WhnfRefusal, WhnfStop, whnf_at_with,
    whnf_core_at_with, whnf_delta_step_at_with,
};
use crate::wire::{
    ExprId, ExprNode, MAX_BVAR_INDEX, NamePart, WireExpr, WireName, expression_owned_units,
    level_owned_units, usize_units,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuickDefEqBudget {
    pub max_comparisons: u64,
    pub max_level_arena_nodes: u64,
}

impl QuickDefEqBudget {
    pub const fn new(max_comparisons: u64, max_level_arena_nodes: u64) -> QuickDefEqBudget {
        QuickDefEqBudget {
            max_comparisons,
            max_level_arena_nodes,
        }
    }

    pub const fn unlimited() -> QuickDefEqBudget {
        QuickDefEqBudget::new(u64::MAX, u64::MAX)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuickDefEqLimit {
    Comparisons,
    LevelArenaNodes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuickDefEqStop {
    Resource {
        limit: QuickDefEqLimit,
        allowed: u64,
        observed: u64,
        completed_comparisons: u64,
    },
    Cancelled {
        polls: u64,
        completed_comparisons: u64,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuickDefEqSide {
    Left,
    Right,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuickDefEqFault {
    MissingExpression {
        side: QuickDefEqSide,
        index: usize,
    },
    NonBackwardExpressionReference {
        side: QuickDefEqSide,
        parent: usize,
        child: usize,
    },
    Universe {
        left: usize,
        right: usize,
        error: UniverseError,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpressionClass {
    Bound,
    Free,
    Meta,
    Sort,
    Constant,
    Apply,
    Lambda,
    Forall,
    Let,
    NatLiteral,
    StringLiteral,
    Metadata,
    Projection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuickDefEqDeferred {
    pub left: usize,
    pub right: usize,
    pub left_class: ExpressionClass,
    pub right_class: ExpressionClass,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuickDefEqMismatch {
    SortLevels { left: usize, right: usize },
    NatLiterals { left: usize, right: usize },
    StringLiterals { left: usize, right: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuickDefEqResult {
    pub comparisons: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuickDefEqOutcome {
    Equal(QuickDefEqResult),
    NotEqual {
        mismatch: QuickDefEqMismatch,
        completed_comparisons: u64,
    },
    Deferred {
        need: QuickDefEqDeferred,
        completed_comparisons: u64,
    },
    Inconclusive(QuickDefEqStop),
    InternalFault(QuickDefEqFault),
}

/// Aggregate bounds for one conversion query.
///
/// The quick and WHNF budgets retain their own meanings. The slow bounds apply
/// across the entire query rather than resetting for each stuck subterm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefEqBudget {
    pub quick: QuickDefEqBudget,
    pub max_slow_comparisons: u64,
    pub max_normalizations: u64,
    pub max_materialized_arena_nodes: u64,
    pub max_materialized_owned_units: u64,
    pub whnf: WhnfBudget,
    pub nat: NatReductionBudget,
    pub string: StringExpansionBudget,
}

impl DefEqBudget {
    pub const fn new(
        quick: QuickDefEqBudget,
        max_slow_comparisons: u64,
        max_normalizations: u64,
        max_materialized_arena_nodes: u64,
        max_materialized_owned_units: u64,
        whnf: WhnfBudget,
    ) -> DefEqBudget {
        DefEqBudget {
            quick,
            max_slow_comparisons,
            max_normalizations,
            max_materialized_arena_nodes,
            max_materialized_owned_units,
            whnf,
            nat: NatReductionBudget::new(
                max_slow_comparisons,
                max_materialized_arena_nodes,
                max_normalizations,
                max_materialized_arena_nodes,
                max_materialized_owned_units,
                max_materialized_owned_units,
                whnf,
                NatBudget::new(max_slow_comparisons, max_materialized_owned_units),
            ),
            string: StringExpansionBudget::new(
                max_slow_comparisons,
                max_materialized_arena_nodes,
                max_materialized_arena_nodes,
                max_materialized_owned_units,
            ),
        }
    }

    pub const fn with_nat(mut self, nat: NatReductionBudget) -> DefEqBudget {
        self.nat = nat;
        self
    }

    pub const fn with_string(mut self, string: StringExpansionBudget) -> DefEqBudget {
        self.string = string;
        self
    }

    pub const fn unlimited() -> DefEqBudget {
        DefEqBudget::new(
            QuickDefEqBudget::unlimited(),
            u64::MAX,
            u64::MAX,
            u64::MAX,
            u64::MAX,
            WhnfBudget::unlimited(),
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefEqLimit {
    SlowComparisons,
    BoundIndex,
    Normalizations,
    MaterializedArenaNodes,
    MaterializedOwnedUnits,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DefEqSide {
    Left,
    Right,
}

/// A diagnostic location in an original arena (`generation == 0`) or in a
/// materialized WHNF result (`generation > 0`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefEqLocation {
    pub side: DefEqSide,
    pub generation: u64,
    pub index: usize,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DefEqProgress {
    pub quick_comparisons: u64,
    pub slow_comparisons: u64,
    pub normalizations: u64,
    pub whnf_steps: u64,
    pub whnf_reductions: u64,
    pub delta_unfolds: u64,
    pub nat_offset_steps: u64,
    pub nat_offset_limb_steps: u64,
    pub nat_reduction_steps: u64,
    pub nat_work_items: u64,
    pub nat_generated_arenas: u64,
    pub nat_numeric_steps: u64,
    pub nat_numeric_materialized_limbs: u64,
    pub nat_reductions: u64,
    pub nat_output_units: u64,
    pub string_steps: u64,
    pub string_code_points: u64,
    pub string_generated_arenas: u64,
    pub string_arena_nodes: u64,
    pub string_owned_units: u64,
    pub materialized_arena_nodes: u64,
    pub materialized_owned_units: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefEqDeferred {
    pub left: DefEqLocation,
    pub right: DefEqLocation,
    pub left_class: ExpressionClass,
    pub right_class: ExpressionClass,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefEqMismatch {
    SortLevels {
        left: DefEqLocation,
        right: DefEqLocation,
    },
    NatLiterals {
        left: DefEqLocation,
        right: DefEqLocation,
    },
    StringLiterals {
        left: DefEqLocation,
        right: DefEqLocation,
    },
    NatOffsets {
        left: DefEqLocation,
        right: DefEqLocation,
    },
    StringExpansion {
        left: DefEqLocation,
        right: DefEqLocation,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefEqStop {
    Quick(QuickDefEqStop),
    Resource {
        limit: DefEqLimit,
        allowed: u64,
        observed: u64,
        progress: DefEqProgress,
    },
    Cancelled {
        polls: u64,
        progress: DefEqProgress,
    },
    Whnf {
        side: DefEqSide,
        stop: WhnfStop,
        progress: DefEqProgress,
    },
    NatReduction {
        side: DefEqSide,
        stop: NatReductionStop,
        progress: DefEqProgress,
    },
    StringExpansion {
        side: DefEqSide,
        stop: StringExpansionStop,
        progress: DefEqProgress,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefEqFault {
    Quick(QuickDefEqFault),
    MissingGeneratedArena {
        side: DefEqSide,
        generation: u64,
    },
    MissingExpression {
        location: DefEqLocation,
    },
    NonBackwardExpressionReference {
        parent: DefEqLocation,
        child: usize,
    },
    Universe {
        left: DefEqLocation,
        right: DefEqLocation,
        error: UniverseError,
    },
    NonCanonicalNatLiteral {
        location: DefEqLocation,
    },
    Whnf {
        side: DefEqSide,
        fault: WhnfFault,
    },
    NatReduction {
        side: DefEqSide,
        fault: NatReductionFault,
    },
    StringExpansion {
        side: DefEqSide,
        fault: StringExpansionFault,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DefEqOutcome {
    Equal(DefEqProgress),
    NotEqual {
        mismatch: DefEqMismatch,
        progress: DefEqProgress,
    },
    Deferred {
        need: DefEqDeferred,
        progress: DefEqProgress,
    },
    Refused {
        side: DefEqSide,
        refusal: WhnfRefusal,
        progress: DefEqProgress,
    },
    Inconclusive(DefEqStop),
    InternalFault(DefEqFault),
}

enum Halt {
    Stop(QuickDefEqStop),
    Fault(QuickDefEqFault),
}

struct Control {
    budget: QuickDefEqBudget,
    comparisons: u64,
    polls: u64,
}

impl Control {
    fn new(budget: QuickDefEqBudget) -> Control {
        Control {
            budget,
            comparisons: 0,
            polls: 0,
        }
    }

    fn poll(&mut self, cancelled: &mut dyn FnMut() -> bool) -> Result<(), Halt> {
        self.polls = self.polls.saturating_add(1);
        if cancelled() {
            return Err(Halt::Stop(QuickDefEqStop::Cancelled {
                polls: self.polls,
                completed_comparisons: self.comparisons,
            }));
        }
        Ok(())
    }

    fn admit_levels(
        &mut self,
        left: &WireExpr,
        right: &WireExpr,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<(), Halt> {
        self.poll(cancelled)?;
        let observed =
            usize_units(left.levels().len()).saturating_add(usize_units(right.levels().len()));
        if observed > self.budget.max_level_arena_nodes {
            return Err(Halt::Stop(QuickDefEqStop::Resource {
                limit: QuickDefEqLimit::LevelArenaNodes,
                allowed: self.budget.max_level_arena_nodes,
                observed,
                completed_comparisons: self.comparisons,
            }));
        }
        Ok(())
    }

    fn comparison(&mut self, cancelled: &mut dyn FnMut() -> bool) -> Result<(), Halt> {
        self.poll(cancelled)?;
        let observed = self.comparisons.saturating_add(1);
        if observed > self.budget.max_comparisons {
            return Err(Halt::Stop(QuickDefEqStop::Resource {
                limit: QuickDefEqLimit::Comparisons,
                allowed: self.budget.max_comparisons,
                observed,
                completed_comparisons: self.comparisons,
            }));
        }
        self.comparisons = observed;
        Ok(())
    }
}

fn expression_class(node: &ExprNode) -> ExpressionClass {
    match node {
        ExprNode::Bound { .. } => ExpressionClass::Bound,
        ExprNode::Free { .. } => ExpressionClass::Free,
        ExprNode::Meta { .. } => ExpressionClass::Meta,
        ExprNode::Sort { .. } => ExpressionClass::Sort,
        ExprNode::Constant { .. } => ExpressionClass::Constant,
        ExprNode::Apply { .. } => ExpressionClass::Apply,
        ExprNode::Lambda { .. } => ExpressionClass::Lambda,
        ExprNode::Forall { .. } => ExpressionClass::Forall,
        ExprNode::Let { .. } => ExpressionClass::Let,
        ExprNode::NatLiteral { .. } => ExpressionClass::NatLiteral,
        ExprNode::StringLiteral(_) => ExpressionClass::StringLiteral,
        ExprNode::Metadata { .. } => ExpressionClass::Metadata,
        ExprNode::Projection { .. } => ExpressionClass::Projection,
    }
}

fn node(term: &WireExpr, id: ExprId, side: QuickDefEqSide) -> Result<&ExprNode, Halt> {
    term.node(id)
        .ok_or(Halt::Fault(QuickDefEqFault::MissingExpression {
            side,
            index: id.index(),
        }))
}

fn validate_child(side: QuickDefEqSide, parent: ExprId, child: ExprId) -> Result<(), Halt> {
    if child.index() >= parent.index() {
        return Err(Halt::Fault(
            QuickDefEqFault::NonBackwardExpressionReference {
                side,
                parent: parent.index(),
                child: child.index(),
            },
        ));
    }
    Ok(())
}

fn outcome(result: Result<QuickDefEqOutcome, Halt>) -> QuickDefEqOutcome {
    match result {
        Ok(outcome) => outcome,
        Err(Halt::Stop(stop)) => QuickDefEqOutcome::Inconclusive(stop),
        Err(Halt::Fault(fault)) => QuickDefEqOutcome::InternalFault(fault),
    }
}

fn run(
    left: &WireExpr,
    right: &WireExpr,
    budget: QuickDefEqBudget,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<QuickDefEqOutcome, Halt> {
    let mut control = Control::new(budget);
    control.admit_levels(left, right, cancelled)?;
    let mut pending = vec![(left.root(), right.root())];
    let mut seen = BTreeSet::new();

    while let Some((left_id, right_id)) = pending.pop() {
        if !seen.insert((left_id, right_id)) {
            continue;
        }
        control.comparison(cancelled)?;
        let left_node = node(left, left_id, QuickDefEqSide::Left)?;
        let right_node = node(right, right_id, QuickDefEqSide::Right)?;

        let mut push_pair = |left_child: ExprId, right_child: ExprId| -> Result<(), Halt> {
            validate_child(QuickDefEqSide::Left, left_id, left_child)?;
            validate_child(QuickDefEqSide::Right, right_id, right_child)?;
            pending.push((left_child, right_child));
            Ok(())
        };

        match (left_node, right_node) {
            (
                ExprNode::Metadata {
                    expression: left_expression,
                    ..
                },
                ExprNode::Metadata {
                    expression: right_expression,
                    ..
                },
            ) => {
                push_pair(*left_expression, *right_expression)?;
                continue;
            }
            (
                ExprNode::Metadata {
                    expression: left_expression,
                    ..
                },
                _,
            ) => {
                validate_child(QuickDefEqSide::Left, left_id, *left_expression)?;
                pending.push((*left_expression, right_id));
                continue;
            }
            (
                _,
                ExprNode::Metadata {
                    expression: right_expression,
                    ..
                },
            ) => {
                validate_child(QuickDefEqSide::Right, right_id, *right_expression)?;
                pending.push((left_id, *right_expression));
                continue;
            }
            _ => {}
        }

        match (left_node, right_node) {
            (ExprNode::Bound { index: left }, ExprNode::Bound { index: right })
                if left == right => {}
            (ExprNode::Free { name: left }, ExprNode::Free { name: right }) if left == right => {}
            (ExprNode::Meta { name: left }, ExprNode::Meta { name: right }) if left == right => {}
            (ExprNode::Sort { level: left_level }, ExprNode::Sort { level: right_level }) => {
                let equal =
                    level_roots_equal(left.levels(), *left_level, right.levels(), *right_level)
                        .map_err(|error| {
                            Halt::Fault(QuickDefEqFault::Universe {
                                left: left_level.index(),
                                right: right_level.index(),
                                error,
                            })
                        })?;
                if !equal {
                    return Ok(QuickDefEqOutcome::NotEqual {
                        mismatch: QuickDefEqMismatch::SortLevels {
                            left: left_id.index(),
                            right: right_id.index(),
                        },
                        completed_comparisons: control.comparisons,
                    });
                }
            }
            (
                ExprNode::Constant {
                    name: left_name,
                    levels: left_levels,
                },
                ExprNode::Constant {
                    name: right_name,
                    levels: right_levels,
                },
            ) if left_name == right_name && left_levels.len() == right_levels.len() => {
                for (left_level, right_level) in left_levels.iter().zip(right_levels) {
                    let equal =
                        level_roots_equal(left.levels(), *left_level, right.levels(), *right_level)
                            .map_err(|error| {
                                Halt::Fault(QuickDefEqFault::Universe {
                                    left: left_level.index(),
                                    right: right_level.index(),
                                    error,
                                })
                            })?;
                    if !equal {
                        return Ok(QuickDefEqOutcome::Deferred {
                            need: QuickDefEqDeferred {
                                left: left_id.index(),
                                right: right_id.index(),
                                left_class: ExpressionClass::Constant,
                                right_class: ExpressionClass::Constant,
                            },
                            completed_comparisons: control.comparisons,
                        });
                    }
                }
            }
            (
                ExprNode::Apply {
                    function: left_function,
                    argument: left_argument,
                },
                ExprNode::Apply {
                    function: right_function,
                    argument: right_argument,
                },
            ) => {
                push_pair(*left_argument, *right_argument)?;
                push_pair(*left_function, *right_function)?;
            }
            (
                ExprNode::Lambda {
                    binder_type: left_type,
                    body: left_body,
                    ..
                },
                ExprNode::Lambda {
                    binder_type: right_type,
                    body: right_body,
                    ..
                },
            )
            | (
                ExprNode::Forall {
                    binder_type: left_type,
                    body: left_body,
                    ..
                },
                ExprNode::Forall {
                    binder_type: right_type,
                    body: right_body,
                    ..
                },
            ) => {
                push_pair(*left_body, *right_body)?;
                push_pair(*left_type, *right_type)?;
            }
            (
                ExprNode::Let {
                    type_: left_type,
                    value: left_value,
                    body: left_body,
                    ..
                },
                ExprNode::Let {
                    type_: right_type,
                    value: right_value,
                    body: right_body,
                    ..
                },
            ) => {
                push_pair(*left_body, *right_body)?;
                push_pair(*left_value, *right_value)?;
                push_pair(*left_type, *right_type)?;
            }
            (
                ExprNode::NatLiteral {
                    limbs_le: left_limbs,
                },
                ExprNode::NatLiteral {
                    limbs_le: right_limbs,
                },
            ) => {
                if left_limbs != right_limbs {
                    return Ok(QuickDefEqOutcome::NotEqual {
                        mismatch: QuickDefEqMismatch::NatLiterals {
                            left: left_id.index(),
                            right: right_id.index(),
                        },
                        completed_comparisons: control.comparisons,
                    });
                }
            }
            (ExprNode::StringLiteral(left_value), ExprNode::StringLiteral(right_value)) => {
                if left_value != right_value {
                    return Ok(QuickDefEqOutcome::NotEqual {
                        mismatch: QuickDefEqMismatch::StringLiterals {
                            left: left_id.index(),
                            right: right_id.index(),
                        },
                        completed_comparisons: control.comparisons,
                    });
                }
            }
            (
                ExprNode::Projection {
                    structure_name: left_structure,
                    index: left_index,
                    expression: left_expression,
                },
                ExprNode::Projection {
                    structure_name: right_structure,
                    index: right_index,
                    expression: right_expression,
                },
            ) if left_structure == right_structure && left_index == right_index => {
                push_pair(*left_expression, *right_expression)?;
            }
            _ => {
                return Ok(QuickDefEqOutcome::Deferred {
                    need: QuickDefEqDeferred {
                        left: left_id.index(),
                        right: right_id.index(),
                        left_class: expression_class(left_node),
                        right_class: expression_class(right_node),
                    },
                    completed_comparisons: control.comparisons,
                });
            }
        }
    }

    Ok(QuickDefEqOutcome::Equal(QuickDefEqResult {
        comparisons: control.comparisons,
    }))
}

/// Run the checker-owned KR-300 through KR-303 quick phase.
pub fn quick_def_eq(
    left: &WireExpr,
    right: &WireExpr,
    budget: QuickDefEqBudget,
) -> QuickDefEqOutcome {
    quick_def_eq_with(left, right, budget, || false)
}

/// Run the quick phase with cooperative cancellation.
pub fn quick_def_eq_with(
    left: &WireExpr,
    right: &WireExpr,
    budget: QuickDefEqBudget,
    mut cancelled: impl FnMut() -> bool,
) -> QuickDefEqOutcome {
    outcome(run(left, right, budget, &mut cancelled))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum DefEqSource {
    Original(DefEqSide),
    Generated { index: usize, side: DefEqSide },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct DefEqTerm {
    source: DefEqSource,
    root: ExprId,
}

impl DefEqTerm {
    const fn original(side: DefEqSide, root: ExprId) -> DefEqTerm {
        DefEqTerm {
            source: DefEqSource::Original(side),
            root,
        }
    }

    const fn side(self) -> DefEqSide {
        match self.source {
            DefEqSource::Original(side) | DefEqSource::Generated { side, .. } => side,
        }
    }

    fn location(self) -> DefEqLocation {
        let generation = match self.source {
            DefEqSource::Original(_) => 0,
            DefEqSource::Generated { index, .. } => usize_units(index).saturating_add(1),
        };
        DefEqLocation {
            side: self.side(),
            generation,
            index: self.root.index(),
        }
    }
}

enum SlowHalt {
    Stop(Box<DefEqStop>),
    Refusal {
        side: DefEqSide,
        refusal: Box<WhnfRefusal>,
        progress: Box<DefEqProgress>,
    },
    Fault(DefEqFault),
}

struct SlowControl {
    budget: DefEqBudget,
    progress: DefEqProgress,
    polls: u64,
    spines: BTreeMap<DefEqTerm, spine::Demand>,
}

struct OffsetMaterialization {
    arena_nodes: u64,
    owned_units: u64,
}

impl SlowControl {
    fn new(budget: DefEqBudget, quick_comparisons: u64) -> SlowControl {
        SlowControl {
            budget,
            progress: DefEqProgress {
                quick_comparisons,
                ..DefEqProgress::default()
            },
            polls: 0,
            spines: BTreeMap::new(),
        }
    }

    fn poll(&mut self, cancelled: &mut dyn FnMut() -> bool) -> Result<(), SlowHalt> {
        self.polls = self.polls.saturating_add(1);
        if cancelled() {
            return Err(SlowHalt::Stop(Box::new(DefEqStop::Cancelled {
                polls: self.polls,
                progress: self.progress,
            })));
        }
        Ok(())
    }

    fn comparison(&mut self, cancelled: &mut dyn FnMut() -> bool) -> Result<(), SlowHalt> {
        self.poll(cancelled)?;
        let observed = self.progress.slow_comparisons.saturating_add(1);
        if observed > self.budget.max_slow_comparisons {
            return Err(SlowHalt::Stop(Box::new(DefEqStop::Resource {
                limit: DefEqLimit::SlowComparisons,
                allowed: self.budget.max_slow_comparisons,
                observed,
                progress: self.progress,
            })));
        }
        self.progress.slow_comparisons = observed;
        Ok(())
    }

    fn bound_index(&self, observed: u64) -> SlowHalt {
        SlowHalt::Stop(Box::new(DefEqStop::Resource {
            limit: DefEqLimit::BoundIndex,
            allowed: u64::from(MAX_BVAR_INDEX),
            observed,
            progress: self.progress,
        }))
    }

    fn nat_offset_step(&mut self) {
        self.progress.nat_offset_steps = self.progress.nat_offset_steps.saturating_add(1);
    }

    fn nat_offset_limb(&mut self, cancelled: &mut dyn FnMut() -> bool) -> Result<(), SlowHalt> {
        self.comparison(cancelled)?;
        self.progress.nat_offset_limb_steps = self.progress.nat_offset_limb_steps.saturating_add(1);
        Ok(())
    }

    fn prepare_offset_materialization(
        &mut self,
        arena_nodes: u64,
        owned_units: u64,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<OffsetMaterialization, SlowHalt> {
        self.poll(cancelled)?;
        let observed_nodes = self
            .progress
            .materialized_arena_nodes
            .saturating_add(arena_nodes);
        if observed_nodes > self.budget.max_materialized_arena_nodes {
            return Err(SlowHalt::Stop(Box::new(DefEqStop::Resource {
                limit: DefEqLimit::MaterializedArenaNodes,
                allowed: self.budget.max_materialized_arena_nodes,
                observed: observed_nodes,
                progress: self.progress,
            })));
        }
        let observed_units = self
            .progress
            .materialized_owned_units
            .saturating_add(owned_units);
        if observed_units > self.budget.max_materialized_owned_units {
            return Err(SlowHalt::Stop(Box::new(DefEqStop::Resource {
                limit: DefEqLimit::MaterializedOwnedUnits,
                allowed: self.budget.max_materialized_owned_units,
                observed: observed_units,
                progress: self.progress,
            })));
        }
        Ok(OffsetMaterialization {
            arena_nodes: observed_nodes,
            owned_units: observed_units,
        })
    }

    fn commit_offset_materialization(&mut self, admission: OffsetMaterialization) {
        self.progress.materialized_arena_nodes = admission.arena_nodes;
        self.progress.materialized_owned_units = admission.owned_units;
    }

    fn remaining_string_budget(&self) -> StringExpansionBudget {
        let mut budget = self.budget.string;
        budget.max_steps = budget.max_steps.saturating_sub(self.progress.string_steps);
        budget.max_code_points = budget
            .max_code_points
            .saturating_sub(self.progress.string_code_points);
        budget.max_arena_nodes = budget
            .max_arena_nodes
            .saturating_sub(self.progress.string_arena_nodes)
            .min(
                self.budget
                    .max_materialized_arena_nodes
                    .saturating_sub(self.progress.materialized_arena_nodes),
            );
        budget.max_owned_units = budget
            .max_owned_units
            .saturating_sub(self.progress.string_owned_units)
            .min(
                self.budget
                    .max_materialized_owned_units
                    .saturating_sub(self.progress.materialized_owned_units),
            );
        budget
    }

    fn absorb_string(&mut self, progress: StringExpansionProgress) {
        self.progress.string_steps = self.progress.string_steps.saturating_add(progress.steps);
        self.progress.string_code_points = self
            .progress
            .string_code_points
            .saturating_add(progress.code_points);
        self.progress.string_generated_arenas = self
            .progress
            .string_generated_arenas
            .saturating_add(progress.generated_arenas);
        self.progress.string_arena_nodes = self
            .progress
            .string_arena_nodes
            .saturating_add(progress.arena_nodes);
        self.progress.string_owned_units = self
            .progress
            .string_owned_units
            .saturating_add(progress.owned_units);
        self.progress.materialized_arena_nodes = self
            .progress
            .materialized_arena_nodes
            .saturating_add(progress.arena_nodes);
        self.progress.materialized_owned_units = self
            .progress
            .materialized_owned_units
            .saturating_add(progress.owned_units);
    }

    fn begin_normalization(
        &mut self,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<WhnfBudget, SlowHalt> {
        self.poll(cancelled)?;
        let observed = self.progress.normalizations.saturating_add(1);
        if observed > self.budget.max_normalizations {
            return Err(SlowHalt::Stop(Box::new(DefEqStop::Resource {
                limit: DefEqLimit::Normalizations,
                allowed: self.budget.max_normalizations,
                observed,
                progress: self.progress,
            })));
        }
        self.progress.normalizations = observed;
        Ok(WhnfBudget::new(
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
        .with_string(self.remaining_string_budget()))
    }

    fn absorb_whnf(
        &mut self,
        result: &crate::whnf::WhnfResult,
        cancelled: &mut dyn FnMut() -> bool,
    ) -> Result<(), SlowHalt> {
        self.absorb_string(result.string_progress);
        self.progress.whnf_steps = self.progress.whnf_steps.saturating_add(result.steps);
        self.progress.whnf_reductions = self
            .progress
            .whnf_reductions
            .saturating_add(result.reductions);
        self.progress.delta_unfolds = self
            .progress
            .delta_unfolds
            .saturating_add(result.delta_reductions);
        self.poll(cancelled)?;
        let produced = usize_units(result.term.nodes().len())
            .saturating_add(usize_units(result.term.levels().len()));
        let observed = self
            .progress
            .materialized_arena_nodes
            .saturating_add(produced);
        if observed > self.budget.max_materialized_arena_nodes {
            return Err(SlowHalt::Stop(Box::new(DefEqStop::Resource {
                limit: DefEqLimit::MaterializedArenaNodes,
                allowed: self.budget.max_materialized_arena_nodes,
                observed,
                progress: self.progress,
            })));
        }
        self.progress.materialized_arena_nodes = observed;
        let produced_units = result
            .term
            .nodes()
            .iter()
            .fold(0_u64, |units, node| {
                units.saturating_add(expression_owned_units(node))
            })
            .saturating_add(result.term.levels().iter().fold(0_u64, |units, node| {
                units.saturating_add(level_owned_units(node))
            }));
        let observed = self
            .progress
            .materialized_owned_units
            .saturating_add(produced_units);
        if observed > self.budget.max_materialized_owned_units {
            return Err(SlowHalt::Stop(Box::new(DefEqStop::Resource {
                limit: DefEqLimit::MaterializedOwnedUnits,
                allowed: self.budget.max_materialized_owned_units,
                observed,
                progress: self.progress,
            })));
        }
        self.progress.materialized_owned_units = observed;
        Ok(())
    }

    fn remaining_nat_budget(&self) -> NatReductionBudget {
        let mut budget = self.budget.nat;
        budget.max_steps = budget
            .max_steps
            .saturating_sub(self.progress.nat_reduction_steps);
        budget.max_work_items = budget
            .max_work_items
            .saturating_sub(self.progress.nat_work_items);
        budget.max_generated_arenas = budget
            .max_generated_arenas
            .saturating_sub(self.progress.nat_generated_arenas)
            .min(
                self.budget
                    .max_normalizations
                    .saturating_sub(self.progress.normalizations),
            );
        budget.max_materialized_arena_nodes = budget
            .max_materialized_arena_nodes
            .saturating_sub(self.progress.materialized_arena_nodes)
            .min(
                self.budget
                    .max_materialized_arena_nodes
                    .saturating_sub(self.progress.materialized_arena_nodes),
            );
        budget.max_materialized_owned_units = budget
            .max_materialized_owned_units
            .saturating_sub(self.progress.materialized_owned_units)
            .min(
                self.budget
                    .max_materialized_owned_units
                    .saturating_sub(self.progress.materialized_owned_units),
            );
        budget.max_output_units = budget
            .max_output_units
            .saturating_sub(self.progress.nat_output_units);
        budget.whnf.max_steps = budget
            .whnf
            .max_steps
            .saturating_sub(self.progress.whnf_steps);
        budget.whnf.max_reductions = budget
            .whnf
            .max_reductions
            .saturating_sub(self.progress.whnf_reductions);
        budget.numeric.max_steps = budget
            .numeric
            .max_steps
            .saturating_sub(self.progress.nat_numeric_steps);
        budget.numeric.max_materialized_limbs = budget
            .numeric
            .max_materialized_limbs
            .saturating_sub(self.progress.nat_numeric_materialized_limbs);
        budget
    }

    fn absorb_nat(&mut self, progress: NatReductionProgress) {
        self.progress.nat_reduction_steps = self
            .progress
            .nat_reduction_steps
            .saturating_add(progress.steps);
        self.progress.nat_work_items = self
            .progress
            .nat_work_items
            .saturating_add(progress.work_items);
        self.progress.nat_generated_arenas = self
            .progress
            .nat_generated_arenas
            .saturating_add(progress.generated_arenas);
        self.progress.normalizations = self
            .progress
            .normalizations
            .saturating_add(progress.generated_arenas);
        self.progress.whnf_steps = self.progress.whnf_steps.saturating_add(progress.whnf_steps);
        self.progress.whnf_reductions = self
            .progress
            .whnf_reductions
            .saturating_add(progress.whnf_reductions);
        self.progress.delta_unfolds = self
            .progress
            .delta_unfolds
            .saturating_add(progress.delta_unfolds);
        self.progress.nat_numeric_steps = self
            .progress
            .nat_numeric_steps
            .saturating_add(progress.numeric_steps);
        self.progress.nat_numeric_materialized_limbs = self
            .progress
            .nat_numeric_materialized_limbs
            .saturating_add(progress.numeric_materialized_limbs);
        self.progress.nat_reductions = self
            .progress
            .nat_reductions
            .saturating_add(progress.numeric_reductions);
        self.progress.materialized_arena_nodes = self
            .progress
            .materialized_arena_nodes
            .saturating_add(progress.materialized_arena_nodes);
        self.progress.materialized_owned_units = self
            .progress
            .materialized_owned_units
            .saturating_add(progress.materialized_owned_units);
        self.progress.nat_output_units = self
            .progress
            .nat_output_units
            .saturating_add(progress.output_units);
    }

    fn remaining_defeq_budget(&self) -> DefEqBudget {
        let mut budget = self.budget;
        budget.max_slow_comparisons = self
            .budget
            .max_slow_comparisons
            .saturating_sub(self.progress.slow_comparisons);
        budget.max_normalizations = self
            .budget
            .max_normalizations
            .saturating_sub(self.progress.normalizations);
        budget.max_materialized_arena_nodes = self
            .budget
            .max_materialized_arena_nodes
            .saturating_sub(self.progress.materialized_arena_nodes);
        budget.max_materialized_owned_units = self
            .budget
            .max_materialized_owned_units
            .saturating_sub(self.progress.materialized_owned_units);
        budget.quick.max_comparisons = self
            .budget
            .quick
            .max_comparisons
            .saturating_sub(self.progress.quick_comparisons);
        budget.whnf.max_steps = self
            .budget
            .whnf
            .max_steps
            .saturating_sub(self.progress.whnf_steps);
        budget.whnf.max_reductions = self
            .budget
            .whnf
            .max_reductions
            .saturating_sub(self.progress.whnf_reductions);
        budget
    }

    fn absorb_defeq_progress(&mut self, progress: &DefEqProgress) {
        self.progress.quick_comparisons = self
            .progress
            .quick_comparisons
            .saturating_add(progress.quick_comparisons);
        self.progress.slow_comparisons = self
            .progress
            .slow_comparisons
            .saturating_add(progress.slow_comparisons);
        self.progress.normalizations = self
            .progress
            .normalizations
            .saturating_add(progress.normalizations);
        self.progress.whnf_steps = self.progress.whnf_steps.saturating_add(progress.whnf_steps);
        self.progress.whnf_reductions = self
            .progress
            .whnf_reductions
            .saturating_add(progress.whnf_reductions);
        self.progress.delta_unfolds = self
            .progress
            .delta_unfolds
            .saturating_add(progress.delta_unfolds);
        self.progress.nat_offset_steps = self
            .progress
            .nat_offset_steps
            .saturating_add(progress.nat_offset_steps);
        self.progress.nat_offset_limb_steps = self
            .progress
            .nat_offset_limb_steps
            .saturating_add(progress.nat_offset_limb_steps);
        self.progress.nat_reduction_steps = self
            .progress
            .nat_reduction_steps
            .saturating_add(progress.nat_reduction_steps);
        self.progress.nat_work_items = self
            .progress
            .nat_work_items
            .saturating_add(progress.nat_work_items);
        self.progress.nat_generated_arenas = self
            .progress
            .nat_generated_arenas
            .saturating_add(progress.nat_generated_arenas);
        self.progress.nat_numeric_steps = self
            .progress
            .nat_numeric_steps
            .saturating_add(progress.nat_numeric_steps);
        self.progress.nat_numeric_materialized_limbs = self
            .progress
            .nat_numeric_materialized_limbs
            .saturating_add(progress.nat_numeric_materialized_limbs);
        self.progress.nat_reductions = self
            .progress
            .nat_reductions
            .saturating_add(progress.nat_reductions);
        self.progress.nat_output_units = self
            .progress
            .nat_output_units
            .saturating_add(progress.nat_output_units);
        self.progress.string_steps = self
            .progress
            .string_steps
            .saturating_add(progress.string_steps);
        self.progress.string_code_points = self
            .progress
            .string_code_points
            .saturating_add(progress.string_code_points);
        self.progress.string_generated_arenas = self
            .progress
            .string_generated_arenas
            .saturating_add(progress.string_generated_arenas);
        self.progress.string_arena_nodes = self
            .progress
            .string_arena_nodes
            .saturating_add(progress.string_arena_nodes);
        self.progress.string_owned_units = self
            .progress
            .string_owned_units
            .saturating_add(progress.string_owned_units);
        self.progress.materialized_arena_nodes = self
            .progress
            .materialized_arena_nodes
            .saturating_add(progress.materialized_arena_nodes);
        self.progress.materialized_owned_units = self
            .progress
            .materialized_owned_units
            .saturating_add(progress.materialized_owned_units);
    }
}

fn source_term<'a>(
    reference: DefEqTerm,
    left: &'a WireExpr,
    right: &'a WireExpr,
    generated: &'a [WireExpr],
) -> Result<&'a WireExpr, SlowHalt> {
    match reference.source {
        DefEqSource::Original(DefEqSide::Left) => Ok(left),
        DefEqSource::Original(DefEqSide::Right) => Ok(right),
        DefEqSource::Generated { index, side } => {
            generated
                .get(index)
                .ok_or(SlowHalt::Fault(DefEqFault::MissingGeneratedArena {
                    side,
                    generation: usize_units(index).saturating_add(1),
                }))
        }
    }
}

#[derive(Clone, Copy)]
struct TermSources<'a> {
    left: &'a WireExpr,
    right: &'a WireExpr,
    generated: &'a [WireExpr],
}

impl<'a> TermSources<'a> {
    fn new(left: &'a WireExpr, right: &'a WireExpr, generated: &'a [WireExpr]) -> TermSources<'a> {
        TermSources {
            left,
            right,
            generated,
        }
    }

    fn source(self, reference: DefEqTerm) -> Result<&'a WireExpr, SlowHalt> {
        source_term(reference, self.left, self.right, self.generated)
    }
}

fn slow_node<'a>(
    reference: DefEqTerm,
    left: &'a WireExpr,
    right: &'a WireExpr,
    generated: &'a [WireExpr],
) -> Result<(&'a WireExpr, &'a ExprNode), SlowHalt> {
    let term = source_term(reference, left, right, generated)?;
    let node = term
        .node(reference.root)
        .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
            location: reference.location(),
        }))?;
    Ok((term, node))
}

fn child(parent: DefEqTerm, child: ExprId) -> Result<DefEqTerm, SlowHalt> {
    if child.index() >= parent.root.index() {
        return Err(SlowHalt::Fault(
            DefEqFault::NonBackwardExpressionReference {
                parent: parent.location(),
                child: child.index(),
            },
        ));
    }
    Ok(DefEqTerm {
        source: parent.source,
        root: child,
    })
}

enum PairAction {
    Done,
    Push1((DefEqTerm, DefEqTerm)),
    Push2((DefEqTerm, DefEqTerm), (DefEqTerm, DefEqTerm)),
    NotEqual(DefEqMismatch),
    Normalize(DefEqDeferred),
}

fn defer_pair(
    left: DefEqTerm,
    right: DefEqTerm,
    left_node: &ExprNode,
    right_node: &ExprNode,
) -> PairAction {
    PairAction::Normalize(DefEqDeferred {
        left: left.location(),
        right: right.location(),
        left_class: expression_class(left_node),
        right_class: expression_class(right_node),
    })
}

/// Dump the surviving pair of a typed deferral under FLN_CHECKER_TRACE. The
/// `DefEqDeferred` need references the GENERATED arenas, which are dropped
/// before any caller-side hook could print them, so an item-126-class
/// deferral is invisible at the surface without this dump.
fn trace_unresolved(
    need: &DefEqDeferred,
    left_reference: DefEqTerm,
    right_reference: DefEqTerm,
    left: &WireExpr,
    right: &WireExpr,
    generated: &[WireExpr],
) {
    if std::env::var_os("FLN_CHECKER_TRACE").is_none() {
        return;
    }
    let sources = TermSources::new(left, right, generated);
    eprintln!(
        "fln-checker: defeq unresolved need left={:?} right={:?}",
        need.left, need.right
    );
    if let Ok(term) = sources.source(left_reference) {
        eprintln!(
            "fln-checker: defeq unresolved LEFT root={} arena: {:?}",
            left_reference.root.index(),
            term.nodes()
        );
    }
    if let Ok(term) = sources.source(right_reference) {
        eprintln!(
            "fln-checker: defeq unresolved RIGHT root={} arena: {:?}",
            right_reference.root.index(),
            term.nodes()
        );
    }
}

fn compare_pair(
    left_reference: DefEqTerm,
    right_reference: DefEqTerm,
    sources: TermSources<'_>,
    context: &WhnfContext,
    after_core: bool,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<PairAction, SlowHalt> {
    let (left_term, left_node) = slow_node(
        left_reference,
        sources.left,
        sources.right,
        sources.generated,
    )?;
    let (right_term, right_node) = slow_node(
        right_reference,
        sources.left,
        sources.right,
        sources.generated,
    )?;

    match (left_node, right_node) {
        (
            ExprNode::Metadata {
                expression: left_expression,
                ..
            },
            ExprNode::Metadata {
                expression: right_expression,
                ..
            },
        ) => {
            return Ok(PairAction::Push1((
                child(left_reference, *left_expression)?,
                child(right_reference, *right_expression)?,
            )));
        }
        (
            ExprNode::Metadata {
                expression: left_expression,
                ..
            },
            _,
        ) => {
            return Ok(PairAction::Push1((
                child(left_reference, *left_expression)?,
                right_reference,
            )));
        }
        (
            _,
            ExprNode::Metadata {
                expression: right_expression,
                ..
            },
        ) => {
            return Ok(PairAction::Push1((
                left_reference,
                child(right_reference, *right_expression)?,
            )));
        }
        _ => {}
    }

    match (left_node, right_node) {
        (ExprNode::Bound { index: left }, ExprNode::Bound { index: right }) if left == right => {
            Ok(PairAction::Done)
        }
        (ExprNode::Free { name: left }, ExprNode::Free { name: right }) if left == right => {
            Ok(PairAction::Done)
        }
        (ExprNode::Meta { name: left }, ExprNode::Meta { name: right }) if left == right => {
            Ok(PairAction::Done)
        }
        (ExprNode::Sort { level: left_level }, ExprNode::Sort { level: right_level }) => {
            let equal = level_roots_equal(
                left_term.levels(),
                *left_level,
                right_term.levels(),
                *right_level,
            )
            .map_err(|error| {
                SlowHalt::Fault(DefEqFault::Universe {
                    left: left_reference.location(),
                    right: right_reference.location(),
                    error,
                })
            })?;
            if equal {
                Ok(PairAction::Done)
            } else {
                Ok(PairAction::NotEqual(DefEqMismatch::SortLevels {
                    left: left_reference.location(),
                    right: right_reference.location(),
                }))
            }
        }
        (
            ExprNode::Constant {
                name: left_name,
                levels: left_levels,
            },
            ExprNode::Constant {
                name: right_name,
                levels: right_levels,
            },
        ) if left_name == right_name && left_levels.len() == right_levels.len() => {
            for (left_level, right_level) in left_levels.iter().zip(right_levels) {
                let equal = level_roots_equal(
                    left_term.levels(),
                    *left_level,
                    right_term.levels(),
                    *right_level,
                )
                .map_err(|error| {
                    SlowHalt::Fault(DefEqFault::Universe {
                        left: left_reference.location(),
                        right: right_reference.location(),
                        error,
                    })
                })?;
                if !equal {
                    return Ok(defer_pair(
                        left_reference,
                        right_reference,
                        left_node,
                        right_node,
                    ));
                }
            }
            Ok(PairAction::Done)
        }
        (
            ExprNode::Apply {
                function: left_function,
                argument: left_argument,
            },
            ExprNode::Apply {
                function: right_function,
                argument: right_argument,
            },
        ) => {
            if control.spine_head_reduces(
                left_reference,
                sources,
                context,
                !after_core,
                cancelled,
            )? || control.spine_head_reduces(
                right_reference,
                sources,
                context,
                !after_core,
                cancelled,
            )? {
                return Ok(defer_pair(
                    left_reference,
                    right_reference,
                    left_node,
                    right_node,
                ));
            }
            Ok(PairAction::Push2(
                (
                    child(left_reference, *left_function)?,
                    child(right_reference, *right_function)?,
                ),
                (
                    child(left_reference, *left_argument)?,
                    child(right_reference, *right_argument)?,
                ),
            ))
        }
        (
            ExprNode::Lambda {
                binder_type: left_type,
                body: left_body,
                ..
            },
            ExprNode::Lambda {
                binder_type: right_type,
                body: right_body,
                ..
            },
        )
        | (
            ExprNode::Forall {
                binder_type: left_type,
                body: left_body,
                ..
            },
            ExprNode::Forall {
                binder_type: right_type,
                body: right_body,
                ..
            },
        ) => Ok(PairAction::Push2(
            (
                child(left_reference, *left_type)?,
                child(right_reference, *right_type)?,
            ),
            (
                child(left_reference, *left_body)?,
                child(right_reference, *right_body)?,
            ),
        )),
        (ExprNode::Let { .. }, ExprNode::Let { .. }) => Ok(defer_pair(
            left_reference,
            right_reference,
            left_node,
            right_node,
        )),
        (
            ExprNode::NatLiteral {
                limbs_le: left_limbs,
            },
            ExprNode::NatLiteral {
                limbs_le: right_limbs,
            },
        ) => {
            if left_limbs == right_limbs {
                Ok(PairAction::Done)
            } else {
                Ok(PairAction::NotEqual(DefEqMismatch::NatLiterals {
                    left: left_reference.location(),
                    right: right_reference.location(),
                }))
            }
        }
        (ExprNode::StringLiteral(left_value), ExprNode::StringLiteral(right_value)) => {
            if left_value == right_value {
                Ok(PairAction::Done)
            } else {
                Ok(PairAction::NotEqual(DefEqMismatch::StringLiterals {
                    left: left_reference.location(),
                    right: right_reference.location(),
                }))
            }
        }
        (
            ExprNode::Projection {
                structure_name: left_structure,
                index: left_index,
                expression: left_expression,
            },
            ExprNode::Projection {
                structure_name: right_structure,
                index: right_index,
                expression: right_expression,
            },
        ) if left_structure == right_structure && left_index == right_index => {
            Ok(PairAction::Push1((
                child(left_reference, *left_expression)?,
                child(right_reference, *right_expression)?,
            )))
        }
        _ => Ok(defer_pair(
            left_reference,
            right_reference,
            left_node,
            right_node,
        )),
    }
}

fn wire_name_is_two(name: &WireName, namespace: &str, leaf: &str) -> bool {
    matches!(
        name.parts(),
        [NamePart::Text(actual_namespace), NamePart::Text(actual_leaf)]
            if actual_namespace == namespace && actual_leaf == leaf
    )
}

#[derive(Clone, Copy)]
enum NatOffsetShape {
    Zero,
    Successor(NatPredecessor),
    Other,
}

#[derive(Clone, Copy)]
enum NatPredecessor {
    Symbolic(DefEqTerm),
    Literal(DefEqTerm),
}

enum NatOffsetAction {
    NoMatch,
    Equal,
    NotEqual(DefEqMismatch),
    Peel(DefEqTerm, DefEqTerm),
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum NatOffsetContext {
    Fresh,
    PairedPeel,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum StringComparisonContext {
    Ordinary,
    MatchedExpansion,
}

fn nat_offset_shape(
    reference: DefEqTerm,
    sources: TermSources<'_>,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<NatOffsetShape, SlowHalt> {
    control.comparison(cancelled)?;
    let term = sources.source(reference)?;
    let node = term
        .node(reference.root)
        .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
            location: reference.location(),
        }))?;
    match node {
        ExprNode::NatLiteral { limbs_le } => {
            if limbs_le.is_empty() {
                Ok(NatOffsetShape::Zero)
            } else if limbs_le.last() == Some(&0) {
                Err(SlowHalt::Fault(DefEqFault::NonCanonicalNatLiteral {
                    location: reference.location(),
                }))
            } else {
                Ok(NatOffsetShape::Successor(NatPredecessor::Literal(
                    reference,
                )))
            }
        }
        ExprNode::Constant { name, levels }
            if levels.is_empty() && wire_name_is_two(name, "Nat", "zero") =>
        {
            Ok(NatOffsetShape::Zero)
        }
        ExprNode::Apply { function, argument } => {
            let function_reference = child(reference, *function)?;
            let function_node =
                term.node(*function)
                    .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
                        location: function_reference.location(),
                    }))?;
            if matches!(
                function_node,
                ExprNode::Constant { name, levels }
                    if levels.is_empty() && wire_name_is_two(name, "Nat", "succ")
            ) {
                Ok(NatOffsetShape::Successor(NatPredecessor::Symbolic(child(
                    reference, *argument,
                )?)))
            } else {
                Ok(NatOffsetShape::Other)
            }
        }
        ExprNode::Bound { .. }
        | ExprNode::Free { .. }
        | ExprNode::Meta { .. }
        | ExprNode::Sort { .. }
        | ExprNode::Constant { .. }
        | ExprNode::Lambda { .. }
        | ExprNode::Forall { .. }
        | ExprNode::Let { .. }
        | ExprNode::StringLiteral(_)
        | ExprNode::Metadata { .. }
        | ExprNode::Projection { .. } => Ok(NatOffsetShape::Other),
    }
}

fn materialize_nat_literal_predecessor(
    reference: DefEqTerm,
    sources: TermSources<'_>,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<WireExpr, SlowHalt> {
    let term = sources.source(reference)?;
    let node = term
        .node(reference.root)
        .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
            location: reference.location(),
        }))?;
    let ExprNode::NatLiteral { limbs_le } = node else {
        return Err(SlowHalt::Fault(DefEqFault::NonCanonicalNatLiteral {
            location: reference.location(),
        }));
    };
    if limbs_le.is_empty() || limbs_le.last() == Some(&0) {
        return Err(SlowHalt::Fault(DefEqFault::NonCanonicalNatLiteral {
            location: reference.location(),
        }));
    }

    let mut first_nonzero = None;
    for (index, limb) in limbs_le.iter().enumerate() {
        control.nat_offset_limb(cancelled)?;
        if *limb != 0 {
            first_nonzero = Some(index);
            break;
        }
    }
    let first_nonzero =
        first_nonzero.ok_or(SlowHalt::Fault(DefEqFault::NonCanonicalNatLiteral {
            location: reference.location(),
        }))?;
    let last = limbs_le.len() - 1;
    let output_len = if first_nonzero == last && limbs_le[last] == 1 {
        last
    } else {
        limbs_le.len()
    };
    let admission = control.prepare_offset_materialization(
        1,
        1_u64.saturating_add(usize_units(output_len)),
        cancelled,
    )?;

    let mut predecessor = Vec::with_capacity(output_len);
    for (index, limb) in limbs_le.iter().copied().take(output_len).enumerate() {
        control.nat_offset_limb(cancelled)?;
        predecessor.push(if index < first_nonzero {
            u64::MAX
        } else if index == first_nonzero {
            limb - 1
        } else {
            limb
        });
    }
    let root =
        ExprId::from_index(0).ok_or(SlowHalt::Fault(DefEqFault::NonCanonicalNatLiteral {
            location: reference.location(),
        }))?;
    control.commit_offset_materialization(admission);
    Ok(WireExpr::from_parts(
        vec![ExprNode::NatLiteral {
            limbs_le: predecessor,
        }],
        Vec::new(),
        root,
    ))
}

fn resolve_nat_predecessor(
    predecessor: NatPredecessor,
    side: DefEqSide,
    left: &WireExpr,
    right: &WireExpr,
    generated: &mut Vec<WireExpr>,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<DefEqTerm, SlowHalt> {
    match predecessor {
        NatPredecessor::Symbolic(reference) => Ok(reference),
        NatPredecessor::Literal(reference) => {
            let predecessor = materialize_nat_literal_predecessor(
                reference,
                TermSources::new(left, right, generated),
                control,
                cancelled,
            )?;
            Ok(retain_generated(generated, side, predecessor))
        }
    }
}

fn nat_offset_action(
    references: (DefEqTerm, DefEqTerm),
    left: &WireExpr,
    right: &WireExpr,
    generated: &mut Vec<WireExpr>,
    offset_context: NatOffsetContext,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<NatOffsetAction, SlowHalt> {
    let (left_reference, right_reference) = references;
    let left_shape = nat_offset_shape(
        left_reference,
        TermSources::new(left, right, generated),
        control,
        cancelled,
    )?;
    let right_shape = nat_offset_shape(
        right_reference,
        TermSources::new(left, right, generated),
        control,
        cancelled,
    )?;
    match (left_shape, right_shape) {
        (NatOffsetShape::Zero, NatOffsetShape::Zero) => Ok(NatOffsetAction::Equal),
        (NatOffsetShape::Zero, NatOffsetShape::Successor(_))
        | (NatOffsetShape::Successor(_), NatOffsetShape::Zero)
            if offset_context == NatOffsetContext::PairedPeel =>
        {
            Ok(NatOffsetAction::NotEqual(DefEqMismatch::NatOffsets {
                left: left_reference.location(),
                right: right_reference.location(),
            }))
        }
        (
            NatOffsetShape::Successor(left_predecessor),
            NatOffsetShape::Successor(right_predecessor),
        ) => {
            control.nat_offset_step();
            let next_left = resolve_nat_predecessor(
                left_predecessor,
                DefEqSide::Left,
                left,
                right,
                generated,
                control,
                cancelled,
            )?;
            let next_right = resolve_nat_predecessor(
                right_predecessor,
                DefEqSide::Right,
                left,
                right,
                generated,
                control,
                cancelled,
            )?;
            Ok(NatOffsetAction::Peel(next_left, next_right))
        }
        _ => Ok(NatOffsetAction::NoMatch),
    }
}

fn definition_height(
    reference: DefEqTerm,
    sources: TermSources<'_>,
    context: &WhnfContext,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Option<u32>, SlowHalt> {
    let term = sources.source(reference)?;
    let mut current = reference;
    loop {
        control.comparison(cancelled)?;
        let node =
            term.node(current.root)
                .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
                    location: current.location(),
                }))?;
        match node {
            ExprNode::Apply { function, .. } => {
                current = child(current, *function)?;
            }
            ExprNode::Metadata { expression, .. } | ExprNode::Projection { expression, .. } => {
                // A stuck projection demands its major premise. Its next
                // delta step is the definition at that premise's head, not
                // the projection node itself. WHNF still checks the structure,
                // constructor and field before reducing the projection.
                current = child(current, *expression)?;
            }
            ExprNode::Constant { name, .. } => {
                return Ok(context
                    .constants()
                    .find(name)
                    .and_then(|constant| constant.delta_body())
                    .map(|definition| definition.hint().delta_height()));
            }
            ExprNode::Bound { .. }
            | ExprNode::Free { .. }
            | ExprNode::Meta { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lambda { .. }
            | ExprNode::Forall { .. }
            | ExprNode::Let { .. }
            | ExprNode::NatLiteral { .. }
            | ExprNode::StringLiteral(_) => return Ok(None),
        }
    }
}

#[derive(Clone, Copy)]
enum NormalizationMode {
    Core,
    DeltaStep,
}

fn normalize(
    reference: DefEqTerm,
    sources: TermSources<'_>,
    context: &WhnfContext,
    mode: NormalizationMode,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<crate::whnf::WhnfResult, SlowHalt> {
    let budget = control.begin_normalization(cancelled)?;
    let term = sources.source(reference)?;
    let outcome = match mode {
        NormalizationMode::Core => {
            whnf_core_at_with(term, reference.root, context, budget, cancelled)
        }
        NormalizationMode::DeltaStep => {
            whnf_delta_step_at_with(term, reference.root, context, budget, cancelled)
        }
    };
    match outcome {
        WhnfOutcome::Complete(result) => {
            control.absorb_whnf(&result, cancelled)?;
            Ok(result)
        }
        WhnfOutcome::Refused(refusal) => Err(SlowHalt::Refusal {
            side: reference.side(),
            refusal: Box::new(refusal),
            progress: Box::new(control.progress),
        }),
        WhnfOutcome::Inconclusive(stop) => Err(SlowHalt::Stop(Box::new(DefEqStop::Whnf {
            side: reference.side(),
            stop,
            progress: control.progress,
        }))),
        WhnfOutcome::InternalFault(fault) => Err(SlowHalt::Fault(DefEqFault::Whnf {
            side: reference.side(),
            fault,
        })),
    }
}

fn reduce_nat_candidate(
    reference: DefEqTerm,
    companion_reference: DefEqTerm,
    sources: TermSources<'_>,
    context: &WhnfContext,
    scope: NatReductionScope,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Option<WireExpr>, SlowHalt> {
    let candidate = sources.source(reference)?;
    if !is_potential_nat_reduction(candidate, reference.root) {
        return Ok(None);
    }
    let companion = sources.source(companion_reference)?;
    let budget = control.remaining_nat_budget();
    match reduce_nat_at_with(
        NatReductionQuery::new(
            candidate,
            reference.root,
            companion,
            companion_reference.root,
            context,
        ),
        budget,
        scope,
        cancelled,
    ) {
        NatReductionOutcome::Reduced(result) => {
            control.absorb_nat(result.progress);
            Ok(Some(result.term))
        }
        NatReductionOutcome::NotReduced { progress, .. } => {
            control.absorb_nat(progress);
            Ok(None)
        }
        NatReductionOutcome::Refused {
            refusal: NatReductionRefusal::Whnf { refusal, .. },
            progress,
        } => {
            control.absorb_nat(progress);
            Err(SlowHalt::Refusal {
                side: reference.side(),
                refusal: Box::new(refusal),
                progress: Box::new(control.progress),
            })
        }
        NatReductionOutcome::Inconclusive(stop) => {
            let progress = stop.progress();
            control.absorb_nat(progress);
            Err(SlowHalt::Stop(Box::new(DefEqStop::NatReduction {
                side: reference.side(),
                stop,
                progress: control.progress,
            })))
        }
        NatReductionOutcome::InternalFault(fault) => {
            Err(SlowHalt::Fault(DefEqFault::NatReduction {
                side: reference.side(),
                fault,
            }))
        }
    }
}

fn string_literal_value<'a>(
    reference: DefEqTerm,
    sources: TermSources<'a>,
) -> Result<Option<&'a str>, SlowHalt> {
    let term = sources.source(reference)?;
    let node = term
        .node(reference.root)
        .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
            location: reference.location(),
        }))?;
    Ok(match node {
        ExprNode::StringLiteral(value) => Some(value.as_str()),
        _ => None,
    })
}

fn is_exact_string_of_list(
    reference: DefEqTerm,
    sources: TermSources<'_>,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<bool, SlowHalt> {
    control.comparison(cancelled)?;
    let term = sources.source(reference)?;
    let node = term
        .node(reference.root)
        .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
            location: reference.location(),
        }))?;
    let ExprNode::Apply { function, argument } = node else {
        return Ok(false);
    };
    let function_reference = child(reference, *function)?;
    let _ = child(reference, *argument)?;
    control.comparison(cancelled)?;
    let function_node =
        term.node(*function)
            .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
                location: function_reference.location(),
            }))?;
    Ok(matches!(
        function_node,
        ExprNode::Constant { name, levels }
            if levels.is_empty() && wire_name_is_two(name, "String", "ofList")
    ))
}

fn expand_string_candidate(
    reference: DefEqTerm,
    value: &str,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<WireExpr, SlowHalt> {
    let budget = control.remaining_string_budget();
    match expand_string_literal_with(value, budget, cancelled) {
        StringExpansionOutcome::Expanded(result) => {
            control.absorb_string(result.progress);
            Ok(result.term)
        }
        StringExpansionOutcome::Inconclusive(stop) => {
            control.absorb_string(stop.progress());
            Err(SlowHalt::Stop(Box::new(DefEqStop::StringExpansion {
                side: reference.side(),
                stop,
                progress: control.progress,
            })))
        }
        StringExpansionOutcome::InternalFault { fault, progress } => {
            control.absorb_string(progress);
            Err(SlowHalt::Fault(DefEqFault::StringExpansion {
                side: reference.side(),
                fault,
            }))
        }
    }
}

fn string_expansion(
    left_reference: DefEqTerm,
    right_reference: DefEqTerm,
    sources: TermSources<'_>,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Option<(DefEqSide, WireExpr)>, SlowHalt> {
    if let Some(value) = string_literal_value(left_reference, sources)?
        && is_exact_string_of_list(right_reference, sources, control, cancelled)?
    {
        let term = expand_string_candidate(left_reference, value, control, cancelled)?;
        return Ok(Some((DefEqSide::Left, term)));
    }
    if let Some(value) = string_literal_value(right_reference, sources)?
        && is_exact_string_of_list(left_reference, sources, control, cancelled)?
    {
        let term = expand_string_candidate(right_reference, value, control, cancelled)?;
        return Ok(Some((DefEqSide::Right, term)));
    }
    Ok(None)
}

fn virtual_binder_bound_equal(
    inside_index: u32,
    outside_index: u32,
    cutoff: u64,
    removed: u64,
    control: &SlowControl,
) -> Result<bool, SlowHalt> {
    let outside = u64::from(outside_index);
    if outside < cutoff {
        return Ok(inside_index == outside_index);
    }
    let observed = outside.saturating_add(removed);
    if observed > u64::from(MAX_BVAR_INDEX) {
        return Err(control.bound_index(observed));
    }
    Ok(u64::from(inside_index) == observed)
}

fn eta_structurally_equal(
    inside: DefEqTerm,
    outside: DefEqTerm,
    removed: u64,
    sources: TermSources<'_>,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<bool, SlowHalt> {
    let mut pending = vec![(inside, outside, 0_u64)];
    let mut seen = BTreeSet::new();

    while let Some((inside_reference, outside_reference, cutoff)) = pending.pop() {
        if !seen.insert((inside_reference, outside_reference, cutoff)) {
            continue;
        }
        control.comparison(cancelled)?;
        let inside_term = sources.source(inside_reference)?;
        let inside_node = inside_term
            .node(inside_reference.root)
            .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
                location: inside_reference.location(),
            }))?;
        let outside_term = sources.source(outside_reference)?;
        let outside_node = outside_term
            .node(outside_reference.root)
            .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
                location: outside_reference.location(),
            }))?;

        match (inside_node, outside_node) {
            (
                ExprNode::Metadata {
                    expression: inside_expression,
                    ..
                },
                ExprNode::Metadata {
                    expression: outside_expression,
                    ..
                },
            ) => {
                pending.push((
                    child(inside_reference, *inside_expression)?,
                    child(outside_reference, *outside_expression)?,
                    cutoff,
                ));
                continue;
            }
            (
                ExprNode::Metadata {
                    expression: inside_expression,
                    ..
                },
                _,
            ) => {
                pending.push((
                    child(inside_reference, *inside_expression)?,
                    outside_reference,
                    cutoff,
                ));
                continue;
            }
            (
                _,
                ExprNode::Metadata {
                    expression: outside_expression,
                    ..
                },
            ) => {
                pending.push((
                    inside_reference,
                    child(outside_reference, *outside_expression)?,
                    cutoff,
                ));
                continue;
            }
            _ => {}
        }

        match (inside_node, outside_node) {
            (
                ExprNode::Bound {
                    index: inside_index,
                },
                ExprNode::Bound {
                    index: outside_index,
                },
            ) => {
                if !virtual_binder_bound_equal(
                    *inside_index,
                    *outside_index,
                    cutoff,
                    removed,
                    control,
                )? {
                    return Ok(false);
                }
            }
            (ExprNode::Free { name: inside }, ExprNode::Free { name: outside })
            | (ExprNode::Meta { name: inside }, ExprNode::Meta { name: outside }) => {
                if inside != outside {
                    return Ok(false);
                }
            }
            (
                ExprNode::Sort {
                    level: inside_level,
                },
                ExprNode::Sort {
                    level: outside_level,
                },
            ) => {
                if !level_roots_equal(
                    inside_term.levels(),
                    *inside_level,
                    outside_term.levels(),
                    *outside_level,
                )
                .map_err(|error| {
                    SlowHalt::Fault(DefEqFault::Universe {
                        left: inside_reference.location(),
                        right: outside_reference.location(),
                        error,
                    })
                })? {
                    return Ok(false);
                }
            }
            (
                ExprNode::Constant {
                    name: inside_name,
                    levels: inside_levels,
                },
                ExprNode::Constant {
                    name: outside_name,
                    levels: outside_levels,
                },
            ) => {
                if inside_name != outside_name || inside_levels.len() != outside_levels.len() {
                    return Ok(false);
                }
                for (inside_level, outside_level) in inside_levels.iter().zip(outside_levels) {
                    if !level_roots_equal(
                        inside_term.levels(),
                        *inside_level,
                        outside_term.levels(),
                        *outside_level,
                    )
                    .map_err(|error| {
                        SlowHalt::Fault(DefEqFault::Universe {
                            left: inside_reference.location(),
                            right: outside_reference.location(),
                            error,
                        })
                    })? {
                        return Ok(false);
                    }
                }
            }
            (
                ExprNode::Apply {
                    function: inside_function,
                    argument: inside_argument,
                },
                ExprNode::Apply {
                    function: outside_function,
                    argument: outside_argument,
                },
            ) => {
                pending.push((
                    child(inside_reference, *inside_argument)?,
                    child(outside_reference, *outside_argument)?,
                    cutoff,
                ));
                pending.push((
                    child(inside_reference, *inside_function)?,
                    child(outside_reference, *outside_function)?,
                    cutoff,
                ));
            }
            (
                ExprNode::Lambda {
                    binder_type: inside_type,
                    body: inside_body,
                    ..
                },
                ExprNode::Lambda {
                    binder_type: outside_type,
                    body: outside_body,
                    ..
                },
            )
            | (
                ExprNode::Forall {
                    binder_type: inside_type,
                    body: inside_body,
                    ..
                },
                ExprNode::Forall {
                    binder_type: outside_type,
                    body: outside_body,
                    ..
                },
            ) => {
                pending.push((
                    child(inside_reference, *inside_body)?,
                    child(outside_reference, *outside_body)?,
                    cutoff.saturating_add(1),
                ));
                pending.push((
                    child(inside_reference, *inside_type)?,
                    child(outside_reference, *outside_type)?,
                    cutoff,
                ));
            }
            (
                ExprNode::Let {
                    type_: inside_type,
                    value: inside_value,
                    body: inside_body,
                    ..
                },
                ExprNode::Let {
                    type_: outside_type,
                    value: outside_value,
                    body: outside_body,
                    ..
                },
            ) => {
                pending.push((
                    child(inside_reference, *inside_body)?,
                    child(outside_reference, *outside_body)?,
                    cutoff.saturating_add(1),
                ));
                pending.push((
                    child(inside_reference, *inside_value)?,
                    child(outside_reference, *outside_value)?,
                    cutoff,
                ));
                pending.push((
                    child(inside_reference, *inside_type)?,
                    child(outside_reference, *outside_type)?,
                    cutoff,
                ));
            }
            (
                ExprNode::NatLiteral {
                    limbs_le: inside_limbs,
                },
                ExprNode::NatLiteral {
                    limbs_le: outside_limbs,
                },
            ) => {
                if inside_limbs != outside_limbs {
                    return Ok(false);
                }
            }
            (ExprNode::StringLiteral(inside), ExprNode::StringLiteral(outside)) => {
                if inside != outside {
                    return Ok(false);
                }
            }
            (
                ExprNode::Projection {
                    structure_name: inside_structure,
                    index: inside_index,
                    expression: inside_expression,
                },
                ExprNode::Projection {
                    structure_name: outside_structure,
                    index: outside_index,
                    expression: outside_expression,
                },
            ) => {
                if inside_structure != outside_structure || inside_index != outside_index {
                    return Ok(false);
                }
                pending.push((
                    child(inside_reference, *inside_expression)?,
                    child(outside_reference, *outside_expression)?,
                    cutoff,
                ));
            }
            _ => return Ok(false),
        }
    }

    Ok(true)
}

/// Remove metadata while charging each examined node. This is used only by
/// exact eta recognition; it neither weak-head reduces nor invents a type.
fn eta_visible(
    mut term: DefEqTerm,
    sources: TermSources<'_>,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<DefEqTerm, SlowHalt> {
    loop {
        control.comparison(cancelled)?;
        let arena = sources.source(term)?;
        match arena
            .node(term.root)
            .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
                location: term.location(),
            }))? {
            ExprNode::Metadata { expression, .. } => term = child(term, *expression)?,
            _ => return Ok(term),
        }
    }
}

fn eta_candidate(
    (mut lambda, mut body): (DefEqTerm, ExprId),
    outside: DefEqTerm,
    (left, right): (&WireExpr, &WireExpr),
    generated: &mut Vec<WireExpr>,
    context: &WhnfContext,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<bool, SlowHalt> {
    let mut removed = 0u64;
    loop {
        let sources = TermSources::new(left, right, generated);
        let mut inside = eta_visible(child(lambda, body)?, sources, control, cancelled)?;

        let sources = TermSources::new(left, right, generated);
        let has_delta_head =
            definition_height(inside, sources, context, control, cancelled)?.is_some();
        if has_delta_head {
            let sources = TermSources::new(left, right, generated);
            let inside_term = sources.source(inside)?;
            let budget = control.begin_normalization(cancelled)?;
            match whnf_at_with(inside_term, inside.root, context, budget, cancelled) {
                WhnfOutcome::Complete(result) => {
                    control.absorb_whnf(&result, cancelled)?;
                    if result.reductions != 0 {
                        inside = retain_generated(generated, lambda.side(), result.term);
                    }
                }
                WhnfOutcome::Refused(refusal) => {
                    return Err(SlowHalt::Refusal {
                        side: inside.side(),
                        refusal: Box::new(refusal),
                        progress: Box::new(control.progress),
                    });
                }
                WhnfOutcome::Inconclusive(stop) => {
                    return Err(SlowHalt::Stop(Box::new(DefEqStop::Whnf {
                        side: inside.side(),
                        stop,
                        progress: control.progress,
                    })));
                }
                WhnfOutcome::InternalFault(fault) => {
                    return Err(SlowHalt::Fault(DefEqFault::Whnf {
                        side: inside.side(),
                        fault,
                    }));
                }
            }
        }

        let mut width = 1u64;
        let sources = TermSources::new(left, right, generated);
        let mut binder_types = Vec::new();
        if let Some(ExprNode::Lambda { binder_type, .. }) =
            sources.source(lambda)?.node(lambda.root)
        {
            binder_types.push(child(lambda, *binder_type)?);
        }
        while let Some(ExprNode::Lambda {
            binder_type, body, ..
        }) = sources.source(inside)?.node(inside.root)
        {
            binder_types.push(child(inside, *binder_type)?);
            width = width
                .checked_add(1)
                .ok_or_else(|| control.bound_index(u64::MAX))?;
            inside = eta_visible(child(inside, *body)?, sources, control, cancelled)?;
        }
        let sources = TermSources::new(left, right, generated);
        let has_delta_head =
            definition_height(inside, sources, context, control, cancelled)?.is_some();
        if has_delta_head {
            let sources = TermSources::new(left, right, generated);
            let inside_term = sources.source(inside)?;
            let budget = control.begin_normalization(cancelled)?;
            match whnf_at_with(inside_term, inside.root, context, budget, cancelled) {
                WhnfOutcome::Complete(result) => {
                    control.absorb_whnf(&result, cancelled)?;
                    if result.reductions != 0 {
                        inside = retain_generated(generated, lambda.side(), result.term);
                    }
                }
                WhnfOutcome::Refused(refusal) => {
                    return Err(SlowHalt::Refusal {
                        side: inside.side(),
                        refusal: Box::new(refusal),
                        progress: Box::new(control.progress),
                    });
                }
                WhnfOutcome::Inconclusive(stop) => {
                    return Err(SlowHalt::Stop(Box::new(DefEqStop::Whnf {
                        side: inside.side(),
                        stop,
                        progress: control.progress,
                    })));
                }
                WhnfOutcome::InternalFault(fault) => {
                    return Err(SlowHalt::Fault(DefEqFault::Whnf {
                        side: inside.side(),
                        fault,
                    }));
                }
            }
        }
        for index in 0..width {
            let sources = TermSources::new(left, right, generated);
            let term = sources.source(inside)?;
            let Some(ExprNode::Apply { function, argument }) = term.node(inside.root) else {
                return Ok(false);
            };
            let argument = eta_visible(child(inside, *argument)?, sources, control, cancelled)?;
            let sources = TermSources::new(left, right, generated);
            let argument_term = sources.source(argument)?;
            let is_matched = if let Some(ExprNode::Bound { index: actual }) =
                argument_term.node(argument.root)
            {
                u64::from(*actual) == index
            } else {
                let budget = control.begin_normalization(cancelled)?;
                match whnf_at_with(argument_term, argument.root, context, budget, cancelled) {
                    WhnfOutcome::Complete(result) => {
                        control.absorb_whnf(&result, cancelled)?;
                        let matched_bound = matches!(
                            result.term.node(result.term.root()),
                            Some(ExprNode::Bound { index: actual }) if u64::from(*actual) == index
                        );
                        if matched_bound {
                            true
                        } else {
                            let binder_idx = width as usize - 1 - index as usize;
                            let unit_like = if let Some(&bt) = binder_types.get(binder_idx) {
                                unit_like_inductive_for_binder(
                                    bt, sources, context, control, cancelled,
                                )?
                            } else {
                                None
                            };
                            if let Some((_induct_name, ctor_name)) = unit_like {
                                let mut arg_head = result.term.root();
                                while let Some(node) = result.term.node(arg_head) {
                                    match node {
                                        ExprNode::Apply { function, .. } => arg_head = *function,
                                        ExprNode::Metadata { expression, .. } => {
                                            arg_head = *expression
                                        }
                                        _ => break,
                                    }
                                }
                                matches!(
                                    result.term.node(arg_head),
                                    Some(ExprNode::Constant { name, .. }) if name == &ctor_name
                                )
                            } else {
                                false
                            }
                        }
                    }
                    WhnfOutcome::Refused(refusal) => {
                        return Err(SlowHalt::Refusal {
                            side: argument.side(),
                            refusal: Box::new(refusal),
                            progress: Box::new(control.progress),
                        });
                    }
                    WhnfOutcome::Inconclusive(stop) => {
                        return Err(SlowHalt::Stop(Box::new(DefEqStop::Whnf {
                            side: argument.side(),
                            stop,
                            progress: control.progress,
                        })));
                    }
                    WhnfOutcome::InternalFault(fault) => {
                        return Err(SlowHalt::Fault(DefEqFault::Whnf {
                            side: argument.side(),
                            fault,
                        }));
                    }
                }
            };
            if !is_matched {
                return Ok(false);
            }
            inside = eta_visible(child(inside, *function)?, sources, control, cancelled)?;
        }
        removed = removed
            .checked_add(width)
            .ok_or_else(|| control.bound_index(u64::MAX))?;
        let sources = TermSources::new(left, right, generated);
        if let Some(ExprNode::Lambda { body: inner, .. }) =
            sources.source(inside)?.node(inside.root)
        {
            lambda = inside;
            body = *inner;
            continue;
        }

        let sources = TermSources::new(left, right, generated);
        return eta_structurally_equal(inside, outside, removed, sources, control, cancelled);
    }
}

fn exact_function_eta(
    left_reference: DefEqTerm,
    right_reference: DefEqTerm,
    (left, right): (&WireExpr, &WireExpr),
    generated: &mut Vec<WireExpr>,
    context: &WhnfContext,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<bool, SlowHalt> {
    control.comparison(cancelled)?;
    let sources = TermSources::new(left, right, generated);
    let left_term = sources.source(left_reference)?;
    let left_node = left_term.node(left_reference.root).ok_or(SlowHalt::Fault(
        DefEqFault::MissingExpression {
            location: left_reference.location(),
        },
    ))?;
    let right_term = sources.source(right_reference)?;
    let right_node = right_term
        .node(right_reference.root)
        .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
            location: right_reference.location(),
        }))?;

    match (left_node, right_node) {
        (ExprNode::Lambda { body, .. }, node) if !matches!(node, ExprNode::Lambda { .. }) => {
            eta_candidate(
                (left_reference, *body),
                right_reference,
                (left, right),
                generated,
                context,
                control,
                cancelled,
            )
        }
        (node, ExprNode::Lambda { body, .. }) if !matches!(node, ExprNode::Lambda { .. }) => {
            eta_candidate(
                (right_reference, *body),
                left_reference,
                (left, right),
                generated,
                context,
                control,
                cancelled,
            )
        }
        _ => Ok(false),
    }
}

fn is_non_rec_structure(
    constants: &crate::environment::ConstantEnvironment,
    name: &WireName,
) -> bool {
    let Some(decl) = constants.find(name) else {
        return false;
    };
    let Some(induct) = decl.inductive_metadata() else {
        return false;
    };
    induct.constructors().len() == 1 && induct.num_indices() == 0 && !induct.is_recursive()
}

fn unit_like_inductive_for_binder(
    binder: DefEqTerm,
    sources: TermSources<'_>,
    context: &WhnfContext,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Option<(WireName, WireName)>, SlowHalt> {
    let budget = control.begin_normalization(cancelled)?;
    let term = sources.source(binder)?;
    let norm = match whnf_at_with(term, binder.root, context, budget, cancelled) {
        WhnfOutcome::Complete(result) => {
            control.absorb_whnf(&result, cancelled)?;
            result.term
        }
        WhnfOutcome::Refused(refusal) => {
            return Err(SlowHalt::Refusal {
                side: binder.side(),
                refusal: Box::new(refusal),
                progress: Box::new(control.progress),
            });
        }
        WhnfOutcome::Inconclusive(stop) => {
            return Err(SlowHalt::Stop(Box::new(DefEqStop::Whnf {
                side: binder.side(),
                stop,
                progress: control.progress,
            })));
        }
        WhnfOutcome::InternalFault(fault) => {
            return Err(SlowHalt::Fault(DefEqFault::Whnf {
                side: binder.side(),
                fault,
            }));
        }
    };
    let mut head = norm.root();
    while let Some(node) = norm.node(head) {
        match node {
            ExprNode::Metadata { expression, .. } => head = *expression,
            ExprNode::Apply { function, .. } => head = *function,
            _ => break,
        }
    }
    let Some(ExprNode::Constant { name, .. }) = norm.node(head) else {
        return Ok(None);
    };
    let constants = context.constants();
    if !is_non_rec_structure(constants, name) {
        return Ok(None);
    }
    let Some(decl) = constants.find(name) else {
        return Ok(None);
    };
    let Some(induct) = decl.inductive_metadata() else {
        return Ok(None);
    };
    let Some(ctor_name) = induct.constructors().first() else {
        return Ok(None);
    };
    let Some(ctor_decl) = constants.find(ctor_name) else {
        return Ok(None);
    };
    let Some(ctor) = ctor_decl.constructor_metadata() else {
        return Ok(None);
    };
    if ctor.num_fields() == 0 {
        return Ok(Some((name.clone(), ctor_name.clone())));
    }
    Ok(None)
}

fn collect_constructor_spine(
    term: DefEqTerm,
    sources: TermSources<'_>,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<(DefEqTerm, Vec<DefEqTerm>), SlowHalt> {
    let mut args = Vec::new();
    let mut cur = eta_visible(term, sources, control, cancelled)?;
    loop {
        control.comparison(cancelled)?;
        let arena = sources.source(cur)?;
        let node = arena
            .node(cur.root)
            .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
                location: cur.location(),
            }))?;
        match node {
            ExprNode::Apply { function, argument } => {
                args.push(child(cur, *argument)?);
                cur = eta_visible(child(cur, *function)?, sources, control, cancelled)?;
            }
            ExprNode::Metadata { expression, .. } => {
                cur = child(cur, *expression)?;
            }
            _ => break,
        }
    }
    args.reverse();
    Ok((cur, args))
}

struct StructureEtaMatch {
    s_on_left: bool,
    fields: Vec<(DefEqTerm, WireExpr)>,
}

struct ConstructorCandidate {
    induct_name: WireName,
    num_params: usize,
    num_fields: usize,
}

fn candidate_constructor(
    term: DefEqTerm,
    sources: TermSources<'_>,
    context: &WhnfContext,
) -> Result<Option<ConstructorCandidate>, SlowHalt> {
    let mut cur = term;
    loop {
        let arena = sources.source(cur)?;
        let node = arena
            .node(cur.root)
            .ok_or(SlowHalt::Fault(DefEqFault::MissingExpression {
                location: cur.location(),
            }))?;
        match node {
            ExprNode::Apply { function, .. } => {
                cur = child(cur, *function)?;
            }
            ExprNode::Metadata { expression, .. } => {
                cur = child(cur, *expression)?;
            }
            ExprNode::Constant {
                name: ctor_name, ..
            } => {
                let Some(decl) = context.constants().find(ctor_name) else {
                    return Ok(None);
                };
                let Some(ctor) = decl.constructor_metadata() else {
                    return Ok(None);
                };
                let induct_name = ctor.inductive().clone();
                let num_params = match usize::try_from(ctor.num_parameters()) {
                    Ok(n) => n,
                    Err(_) => return Ok(None),
                };
                let num_fields = match usize::try_from(ctor.num_fields()) {
                    Ok(n) => n,
                    Err(_) => return Ok(None),
                };
                if num_fields == 0 {
                    return Ok(None);
                }
                if !is_non_rec_structure(context.constants(), &induct_name) {
                    return Ok(None);
                }
                return Ok(Some(ConstructorCandidate {
                    induct_name,
                    num_params,
                    num_fields,
                }));
            }
            _ => return Ok(None),
        }
    }
}

fn try_structure_eta_candidate(
    s: DefEqTerm,
    t: DefEqTerm,
    s_on_left: bool,
    sources: TermSources<'_>,
    context: &WhnfContext,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Option<StructureEtaMatch>, SlowHalt> {
    let Some(candidate) = candidate_constructor(s, sources, context)? else {
        return Ok(None);
    };
    let (_head, spine_args) = collect_constructor_spine(s, sources, control, cancelled)?;
    let expected_args = match candidate.num_params.checked_add(candidate.num_fields) {
        Some(sum) => sum,
        None => return Ok(None),
    };
    if spine_args.len() != expected_args {
        return Ok(None);
    }

    let t_visible = eta_visible(t, sources, control, cancelled)?;
    let t_arena = sources.source(t_visible)?;
    let copied_t = match copy_compact_subterm_with(
        t_arena,
        t_visible.root,
        TermBudget::unlimited(),
        cancelled,
    ) {
        TermOutcome::Complete(term) => term,
        TermOutcome::Inconclusive(stop) => {
            return Err(SlowHalt::Stop(Box::new(match stop {
                TermStop::Cancelled { polls, .. } => DefEqStop::Cancelled {
                    polls: control.polls.saturating_add(polls),
                    progress: control.progress,
                },
                TermStop::Resource {
                    allowed, observed, ..
                } => DefEqStop::Resource {
                    limit: DefEqLimit::MaterializedArenaNodes,
                    allowed,
                    observed,
                    progress: control.progress,
                },
            })));
        }
        TermOutcome::InternalFault(_) => {
            return Err(SlowHalt::Fault(DefEqFault::MissingExpression {
                location: t.location(),
            }));
        }
    };

    let mut fields = Vec::with_capacity(candidate.num_fields);
    for i in 0..candidate.num_fields {
        let s_field = spine_args[candidate.num_params + i];
        let mut nodes = copied_t.nodes().to_vec();
        let proj_root = ExprId::from_index(nodes.len()).ok_or(SlowHalt::Fault(
            DefEqFault::MissingExpression {
                location: t.location(),
            },
        ))?;
        nodes.push(ExprNode::Projection {
            structure_name: candidate.induct_name.clone(),
            index: i as u64,
            expression: copied_t.root(),
        });
        let proj_expr = WireExpr::from_parts(nodes, copied_t.levels().to_vec(), proj_root);
        let arena_nodes = proj_expr.nodes().len() as u64;
        let owned_units = proj_expr
            .nodes()
            .iter()
            .map(expression_owned_units)
            .chain(proj_expr.levels().iter().map(level_owned_units))
            .sum::<u64>();
        let admission =
            control.prepare_offset_materialization(arena_nodes, owned_units, cancelled)?;
        control.commit_offset_materialization(admission);
        fields.push((s_field, proj_expr));
    }
    Ok(Some(StructureEtaMatch { s_on_left, fields }))
}

fn exact_structure_eta(
    left_reference: DefEqTerm,
    right_reference: DefEqTerm,
    sources: TermSources<'_>,
    context: &WhnfContext,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<Option<StructureEtaMatch>, SlowHalt> {
    if let Some(matched) = try_structure_eta_candidate(
        left_reference,
        right_reference,
        true,
        sources,
        context,
        control,
        cancelled,
    )? {
        return Ok(Some(matched));
    }
    try_structure_eta_candidate(
        right_reference,
        left_reference,
        false,
        sources,
        context,
        control,
        cancelled,
    )
}

fn retain_generated(generated: &mut Vec<WireExpr>, side: DefEqSide, term: WireExpr) -> DefEqTerm {
    let root = term.root();
    let index = generated.len();
    generated.push(term);
    DefEqTerm {
        source: DefEqSource::Generated { index, side },
        root,
    }
}

fn unresolved_pair(
    need: DefEqDeferred,
    left: DefEqTerm,
    right: DefEqTerm,
    string_context: StringComparisonContext,
    progress: DefEqProgress,
) -> DefEqOutcome {
    match string_context {
        StringComparisonContext::Ordinary => DefEqOutcome::Deferred { need, progress },
        StringComparisonContext::MatchedExpansion => DefEqOutcome::NotEqual {
            mismatch: DefEqMismatch::StringExpansion {
                left: left.location(),
                right: right.location(),
            },
            progress,
        },
    }
}

fn materialize_subterm_wire(
    term: DefEqTerm,
    sources: TermSources<'_>,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<WireExpr, SlowHalt> {
    let visible = eta_visible(term, sources, control, cancelled)?;
    let arena = sources.source(visible)?;
    match copy_compact_subterm_with(arena, visible.root, TermBudget::unlimited(), cancelled) {
        TermOutcome::Complete(wire) => Ok(wire),
        TermOutcome::Inconclusive(stop) => Err(SlowHalt::Stop(Box::new(match stop {
            TermStop::Cancelled { polls, .. } => DefEqStop::Cancelled {
                polls: control.polls.saturating_add(polls),
                progress: control.progress,
            },
            TermStop::Resource {
                allowed, observed, ..
            } => DefEqStop::Resource {
                limit: DefEqLimit::MaterializedArenaNodes,
                allowed,
                observed,
                progress: control.progress,
            },
        }))),
        TermOutcome::InternalFault(_) => Err(SlowHalt::Fault(DefEqFault::MissingExpression {
            location: term.location(),
        })),
    }
}

/// Upstream Lean 4 / K1 equal-regular-definition shortcut:
/// Before unfolding two applications of the SAME regular definition,
/// check whether all arguments are definitionally equal.
/// If all arguments are defeq, congruence proves definitional equality
/// directly, skipping delta reduction. If argument checking fails,
/// this returns `Ok(false)` and lazy delta continues with normal height ordering.
#[allow(clippy::too_many_arguments)]
fn regular_same_head_apps_def_eq(
    left_reference: DefEqTerm,
    right_reference: DefEqTerm,
    left: &WireExpr,
    right: &WireExpr,
    generated: &[WireExpr],
    context: &WhnfContext,
    nat_scope: NatReductionScope,
    control: &mut SlowControl,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<bool, SlowHalt> {
    let sources = TermSources::new(left, right, generated);
    let (left_head, left_args) =
        collect_constructor_spine(left_reference, sources, control, cancelled)?;
    if left_args.is_empty() {
        return Ok(false);
    }
    let sources = TermSources::new(left, right, generated);
    let (right_head, right_args) =
        collect_constructor_spine(right_reference, sources, control, cancelled)?;
    if left_args.len() != right_args.len() {
        return Ok(false);
    }

    let sources = TermSources::new(left, right, generated);
    let left_arena = sources.source(left_head)?;
    let right_arena = sources.source(right_head)?;
    let (
        Some(ExprNode::Constant {
            name: left_name,
            levels: left_levels,
        }),
        Some(ExprNode::Constant {
            name: right_name,
            levels: right_levels,
        }),
    ) = (
        left_arena.node(left_head.root),
        right_arena.node(right_head.root),
    )
    else {
        return Ok(false);
    };

    if left_name != right_name || left_levels.len() != right_levels.len() {
        return Ok(false);
    }

    for (left_level, right_level) in left_levels.iter().zip(right_levels) {
        let equal = level_roots_equal(
            left_arena.levels(),
            *left_level,
            right_arena.levels(),
            *right_level,
        )
        .map_err(|error| {
            SlowHalt::Fault(DefEqFault::Universe {
                left: left_reference.location(),
                right: right_reference.location(),
                error,
            })
        })?;
        if !equal {
            return Ok(false);
        }
    }

    let is_regular = context
        .constants()
        .find(left_name)
        .and_then(|constant| constant.delta_body())
        .map(|definition| matches!(definition.hint(), ReducibilityHint::Regular(_)))
        .unwrap_or(false);

    if !is_regular {
        return Ok(false);
    }

    for (&left_arg, &right_arg) in left_args.iter().zip(&right_args) {
        let sources = TermSources::new(left, right, generated);
        let left_wire = materialize_subterm_wire(left_arg, sources, control, cancelled)?;
        let sources = TermSources::new(left, right, generated);
        let right_wire = materialize_subterm_wire(right_arg, sources, control, cancelled)?;

        let sub_budget = control.remaining_defeq_budget();
        let outcome = def_eq_scoped_with(
            &left_wire,
            &right_wire,
            context,
            sub_budget,
            nat_scope,
            cancelled,
        );
        match outcome {
            DefEqOutcome::Equal(progress) => {
                control.absorb_defeq_progress(&progress);
            }
            DefEqOutcome::NotEqual { progress, .. } | DefEqOutcome::Deferred { progress, .. } => {
                control.absorb_defeq_progress(&progress);
                return Ok(false);
            }
            DefEqOutcome::Inconclusive(stop) => {
                return Err(SlowHalt::Stop(Box::new(stop)));
            }
            DefEqOutcome::Refused {
                side,
                refusal,
                progress,
            } => {
                return Err(SlowHalt::Refusal {
                    side,
                    refusal: Box::new(refusal),
                    progress: Box::new(progress),
                });
            }
            DefEqOutcome::InternalFault(fault) => {
                return Err(SlowHalt::Fault(fault));
            }
        }
    }

    Ok(true)
}

fn run_slow(
    left: &WireExpr,
    right: &WireExpr,
    context: &WhnfContext,
    budget: DefEqBudget,
    quick_comparisons: u64,
    nat_scope: NatReductionScope,
    cancelled: &mut dyn FnMut() -> bool,
) -> Result<DefEqOutcome, SlowHalt> {
    let mut control = SlowControl::new(budget, quick_comparisons);
    let mut generated = Vec::new();
    let mut pending = vec![(
        DefEqTerm::original(DefEqSide::Left, left.root()),
        DefEqTerm::original(DefEqSide::Right, right.root()),
        NatOffsetContext::Fresh,
        StringComparisonContext::Ordinary,
    )];
    let mut seen = BTreeSet::new();

    while let Some((left_reference, right_reference, offset_context, string_context)) =
        pending.pop()
    {
        if !seen.insert((
            left_reference,
            right_reference,
            offset_context,
            string_context,
        )) {
            continue;
        }
        control.comparison(cancelled)?;
        match compare_pair(
            left_reference,
            right_reference,
            TermSources::new(left, right, &generated),
            context,
            false,
            &mut control,
            cancelled,
        )? {
            PairAction::Done => {}
            PairAction::Push1((next_left, next_right)) => {
                pending.push((next_left, next_right, offset_context, string_context));
            }
            PairAction::Push2(first, second) => {
                pending.push((second.0, second.1, offset_context, string_context));
                pending.push((first.0, first.1, offset_context, string_context));
            }
            PairAction::NotEqual(mismatch) => {
                return Ok(DefEqOutcome::NotEqual {
                    mismatch,
                    progress: control.progress,
                });
            }
            PairAction::Normalize(need) => {
                match nat_offset_action(
                    (left_reference, right_reference),
                    left,
                    right,
                    &mut generated,
                    offset_context,
                    &mut control,
                    cancelled,
                )? {
                    NatOffsetAction::NoMatch => {}
                    NatOffsetAction::Equal => continue,
                    NatOffsetAction::NotEqual(mismatch) => {
                        return Ok(DefEqOutcome::NotEqual {
                            mismatch,
                            progress: control.progress,
                        });
                    }
                    NatOffsetAction::Peel(next_left, next_right) => {
                        pending.push((
                            next_left,
                            next_right,
                            NatOffsetContext::PairedPeel,
                            string_context,
                        ));
                        continue;
                    }
                }

                let left_result = normalize(
                    left_reference,
                    TermSources::new(left, right, &generated),
                    context,
                    NormalizationMode::Core,
                    &mut control,
                    cancelled,
                )?;
                let right_result = normalize(
                    right_reference,
                    TermSources::new(left, right, &generated),
                    context,
                    NormalizationMode::Core,
                    &mut control,
                    cancelled,
                )?;
                // When both weak heads reduce to identical standalone expressions
                // (e.g. beta-redexes in generated noConfusion principles reducing
                // to identical noConfusionType applications), reflexivity decides
                // the pair immediately without redundant delta unfolding.
                if left_result.reductions != 0
                    && right_result.reductions != 0
                    && left_result.term == right_result.term
                {
                    continue;
                }
                // Auxiliary K-gate reductions count as work, but a failed gate
                // can leave the compared term unchanged. Do not resubmit that
                // same pair forever merely because the gate spent reductions.
                // The zero-shift structural comparison is metered by this query.
                let mut next_left = left_reference;
                let mut next_right = right_reference;
                for (reference, result, next) in [
                    (left_reference, left_result, &mut next_left),
                    (right_reference, right_result, &mut next_right),
                ] {
                    if result.reductions != 0 {
                        let candidate =
                            retain_generated(&mut generated, reference.side(), result.term);
                        if !result.has_auxiliary_work
                            || !eta_structurally_equal(
                                candidate,
                                reference,
                                0,
                                TermSources::new(left, right, &generated),
                                &mut control,
                                cancelled,
                            )?
                        {
                            *next = candidate;
                        }
                    }
                }
                if next_left != left_reference || next_right != right_reference {
                    pending.push((next_left, next_right, offset_context, string_context));
                    continue;
                }

                // A saturated recursor must keep its major until iota has
                // had an opportunity to fire. If both weak heads stayed stuck,
                // congruence is still a valid sufficient proof; do not turn
                // equal arguments beneath a neutral recursor into a deferral.
                if let PairAction::Push2(first, second) = compare_pair(
                    left_reference,
                    right_reference,
                    TermSources::new(left, right, &generated),
                    context,
                    true,
                    &mut control,
                    cancelled,
                )? {
                    pending.push((second.0, second.1, offset_context, string_context));
                    pending.push((first.0, first.1, offset_context, string_context));
                    continue;
                }

                if let Some((side, term)) = string_expansion(
                    left_reference,
                    right_reference,
                    TermSources::new(left, right, &generated),
                    &mut control,
                    cancelled,
                )? {
                    match side {
                        DefEqSide::Left => {
                            let next_left = retain_generated(&mut generated, DefEqSide::Left, term);
                            pending.push((
                                next_left,
                                right_reference,
                                offset_context,
                                StringComparisonContext::MatchedExpansion,
                            ));
                        }
                        DefEqSide::Right => {
                            let next_right =
                                retain_generated(&mut generated, DefEqSide::Right, term);
                            pending.push((
                                left_reference,
                                next_right,
                                offset_context,
                                StringComparisonContext::MatchedExpansion,
                            ));
                        }
                    }
                    continue;
                }

                let left_is_nat = {
                    let term = TermSources::new(left, right, &generated).source(left_reference)?;
                    is_potential_nat_reduction(term, left_reference.root)
                };
                let right_is_nat = {
                    let term = TermSources::new(left, right, &generated).source(right_reference)?;
                    is_potential_nat_reduction(term, right_reference.root)
                };
                // The pin's `lazy_delta_reduction` tries `reduce_nat` on the
                // left and then the right before *every* delta step, whatever
                // the other side's definition height. Deferring it while the
                // companion can still unfold lets height order delta-unfold a
                // closed `Nat.add`/`Nat.sub`/`Nat.pow` application itself, which
                // walks its structural recursion over the literal's magnitude
                // (`Char.toUpper._proof_1`, `2^32` fuel) instead of evaluating it.
                if left_is_nat
                    && let Some(term) = reduce_nat_candidate(
                        left_reference,
                        right_reference,
                        TermSources::new(left, right, &generated),
                        context,
                        nat_scope,
                        &mut control,
                        cancelled,
                    )?
                {
                    let next_left = retain_generated(&mut generated, DefEqSide::Left, term);
                    pending.push((next_left, right_reference, offset_context, string_context));
                    continue;
                }
                if right_is_nat
                    && let Some(term) = reduce_nat_candidate(
                        right_reference,
                        left_reference,
                        TermSources::new(left, right, &generated),
                        context,
                        nat_scope,
                        &mut control,
                        cancelled,
                    )?
                {
                    let next_right = retain_generated(&mut generated, DefEqSide::Right, term);
                    pending.push((left_reference, next_right, offset_context, string_context));
                    continue;
                }

                let left_height = definition_height(
                    left_reference,
                    TermSources::new(left, right, &generated),
                    context,
                    &mut control,
                    cancelled,
                )?;
                let right_height = definition_height(
                    right_reference,
                    TermSources::new(left, right, &generated),
                    context,
                    &mut control,
                    cancelled,
                )?;
                let (unfold_left, unfold_right) = match (left_height, right_height) {
                    (None, None) => {
                        if exact_function_eta(
                            left_reference,
                            right_reference,
                            (left, right),
                            &mut generated,
                            context,
                            &mut control,
                            cancelled,
                        )? {
                            continue;
                        }
                        if let Some(matched) = exact_structure_eta(
                            left_reference,
                            right_reference,
                            TermSources::new(left, right, &generated),
                            context,
                            &mut control,
                            cancelled,
                        )? {
                            let projected_side = if matched.s_on_left {
                                DefEqSide::Right
                            } else {
                                DefEqSide::Left
                            };
                            for (s_field, proj_expr) in matched.fields.into_iter().rev() {
                                let proj_term =
                                    retain_generated(&mut generated, projected_side, proj_expr);
                                let (next_left, next_right) = if matched.s_on_left {
                                    (s_field, proj_term)
                                } else {
                                    (proj_term, s_field)
                                };
                                pending.push((
                                    next_left,
                                    next_right,
                                    offset_context,
                                    string_context,
                                ));
                            }
                            continue;
                        }
                        trace_unresolved(
                            &need,
                            left_reference,
                            right_reference,
                            left,
                            right,
                            &generated,
                        );
                        return Ok(unresolved_pair(
                            need,
                            left_reference,
                            right_reference,
                            string_context,
                            control.progress,
                        ));
                    }
                    (Some(_), None) => (true, false),
                    (None, Some(_)) => (false, true),
                    (Some(left_height), Some(right_height)) => {
                        if left_height == right_height
                            && regular_same_head_apps_def_eq(
                                left_reference,
                                right_reference,
                                left,
                                right,
                                &generated,
                                context,
                                nat_scope,
                                &mut control,
                                cancelled,
                            )?
                        {
                            continue;
                        }
                        (left_height >= right_height, right_height >= left_height)
                    }
                };

                let mut next_left = left_reference;
                let mut next_right = right_reference;
                if unfold_left {
                    let result = normalize(
                        left_reference,
                        TermSources::new(left, right, &generated),
                        context,
                        NormalizationMode::DeltaStep,
                        &mut control,
                        cancelled,
                    )?;
                    if result.delta_reductions == 0 {
                        trace_unresolved(
                            &need,
                            left_reference,
                            right_reference,
                            left,
                            right,
                            &generated,
                        );
                        return Ok(unresolved_pair(
                            need,
                            left_reference,
                            right_reference,
                            string_context,
                            control.progress,
                        ));
                    }
                    next_left = retain_generated(&mut generated, DefEqSide::Left, result.term);
                }
                if unfold_right {
                    let result = normalize(
                        right_reference,
                        TermSources::new(left, right, &generated),
                        context,
                        NormalizationMode::DeltaStep,
                        &mut control,
                        cancelled,
                    )?;
                    if result.delta_reductions == 0 {
                        trace_unresolved(
                            &need,
                            left_reference,
                            right_reference,
                            left,
                            right,
                            &generated,
                        );
                        return Ok(unresolved_pair(
                            need,
                            left_reference,
                            right_reference,
                            string_context,
                            control.progress,
                        ));
                    }
                    next_right = retain_generated(&mut generated, DefEqSide::Right, result.term);
                }
                pending.push((next_left, next_right, offset_context, string_context));
            }
        }
    }

    Ok(DefEqOutcome::Equal(control.progress))
}

fn slow_outcome(result: Result<DefEqOutcome, SlowHalt>) -> DefEqOutcome {
    match result {
        Ok(outcome) => outcome,
        Err(SlowHalt::Stop(stop)) => DefEqOutcome::Inconclusive(*stop),
        Err(SlowHalt::Refusal {
            side,
            refusal,
            progress,
        }) => DefEqOutcome::Refused {
            side,
            refusal: *refusal,
            progress: *progress,
        },
        Err(SlowHalt::Fault(fault)) => DefEqOutcome::InternalFault(fault),
    }
}

fn original_location(side: DefEqSide, index: usize) -> DefEqLocation {
    DefEqLocation {
        side,
        generation: 0,
        index,
    }
}

fn map_quick_mismatch(mismatch: QuickDefEqMismatch) -> DefEqMismatch {
    match mismatch {
        QuickDefEqMismatch::SortLevels { left, right } => DefEqMismatch::SortLevels {
            left: original_location(DefEqSide::Left, left),
            right: original_location(DefEqSide::Right, right),
        },
        QuickDefEqMismatch::NatLiterals { left, right } => DefEqMismatch::NatLiterals {
            left: original_location(DefEqSide::Left, left),
            right: original_location(DefEqSide::Right, right),
        },
        QuickDefEqMismatch::StringLiterals { left, right } => DefEqMismatch::StringLiterals {
            left: original_location(DefEqSide::Left, left),
            right: original_location(DefEqSide::Right, right),
        },
    }
}

/// Run the counted quick phase followed by height-ordered slow conversion.
pub fn def_eq(
    left: &WireExpr,
    right: &WireExpr,
    context: &WhnfContext,
    budget: DefEqBudget,
) -> DefEqOutcome {
    def_eq_with(left, right, context, budget, || false)
}

/// Run conversion with cooperative cancellation shared by every phase.
pub fn def_eq_with(
    left: &WireExpr,
    right: &WireExpr,
    context: &WhnfContext,
    budget: DefEqBudget,
    mut cancelled: impl FnMut() -> bool,
) -> DefEqOutcome {
    def_eq_scoped_with(
        left,
        right,
        context,
        budget,
        NatReductionScope::ClosedPair,
        &mut cancelled,
    )
}

/// The pin's query-local `m_eager_reduce` conversion. This differs from
/// ordinary conversion only by allowing KR-313 to try WHNF on open Nat
/// operands; unresolved free variables still leave the pair deferred.
pub(crate) fn def_eq_eager_with(
    left: &WireExpr,
    right: &WireExpr,
    context: &WhnfContext,
    budget: DefEqBudget,
    mut cancelled: impl FnMut() -> bool,
) -> DefEqOutcome {
    def_eq_scoped_with(
        left,
        right,
        context,
        budget,
        NatReductionScope::EagerOpenPair,
        &mut cancelled,
    )
}

fn def_eq_scoped_with(
    left: &WireExpr,
    right: &WireExpr,
    context: &WhnfContext,
    budget: DefEqBudget,
    nat_scope: NatReductionScope,
    cancelled: &mut dyn FnMut() -> bool,
) -> DefEqOutcome {
    match quick_def_eq_with(left, right, budget.quick, &mut *cancelled) {
        QuickDefEqOutcome::Equal(result) => DefEqOutcome::Equal(DefEqProgress {
            quick_comparisons: result.comparisons,
            ..DefEqProgress::default()
        }),
        QuickDefEqOutcome::NotEqual {
            mismatch,
            completed_comparisons,
        } => {
            // Quick congruence can discover different literal arguments under
            // a function that erases them. Only a root atomic mismatch is a
            // final negative verdict; nested mismatches need actual conversion.
            if matches!(
                (left.node(left.root()), right.node(right.root())),
                (Some(ExprNode::Sort { .. }), Some(ExprNode::Sort { .. }))
                    | (
                        Some(ExprNode::NatLiteral { .. }),
                        Some(ExprNode::NatLiteral { .. })
                    )
                    | (
                        Some(ExprNode::StringLiteral(_)),
                        Some(ExprNode::StringLiteral(_))
                    )
            ) {
                DefEqOutcome::NotEqual {
                    mismatch: map_quick_mismatch(mismatch),
                    progress: DefEqProgress {
                        quick_comparisons: completed_comparisons,
                        ..DefEqProgress::default()
                    },
                }
            } else {
                slow_outcome(run_slow(
                    left,
                    right,
                    context,
                    budget,
                    completed_comparisons,
                    nat_scope,
                    cancelled,
                ))
            }
        }
        QuickDefEqOutcome::Deferred {
            completed_comparisons,
            ..
        } => slow_outcome(run_slow(
            left,
            right,
            context,
            budget,
            completed_comparisons,
            nat_scope,
            cancelled,
        )),
        QuickDefEqOutcome::Inconclusive(stop) => DefEqOutcome::Inconclusive(DefEqStop::Quick(stop)),
        QuickDefEqOutcome::InternalFault(fault) => {
            DefEqOutcome::InternalFault(DefEqFault::Quick(fault))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::ExprId;

    #[test]
    fn private_arena_corruption_is_an_internal_fault() {
        let root = ExprId::from_index(0).expect("zero expression index");
        let term = WireExpr::from_parts(
            vec![ExprNode::Apply {
                function: root,
                argument: root,
            }],
            Vec::new(),
            root,
        );
        assert_eq!(
            quick_def_eq(&term, &term, QuickDefEqBudget::unlimited()),
            QuickDefEqOutcome::InternalFault(QuickDefEqFault::NonBackwardExpressionReference {
                side: QuickDefEqSide::Left,
                parent: 0,
                child: 0,
            })
        );
        assert_eq!(
            def_eq(
                &term,
                &term,
                &WhnfContext::default(),
                DefEqBudget::unlimited(),
            ),
            DefEqOutcome::InternalFault(DefEqFault::Quick(
                QuickDefEqFault::NonBackwardExpressionReference {
                    side: QuickDefEqSide::Left,
                    parent: 0,
                    child: 0,
                }
            ))
        );
    }

    #[test]
    fn a_noncanonical_private_nat_literal_faults_before_offset_materialization() {
        let root = ExprId::from_index(0).expect("zero expression index");
        let noncanonical = WireExpr::from_parts(
            vec![ExprNode::NatLiteral { limbs_le: vec![0] }],
            Vec::new(),
            root,
        );
        let other = WireExpr::from_parts(
            vec![ExprNode::Constant {
                name: WireName::default(),
                levels: Vec::new(),
            }],
            Vec::new(),
            root,
        );
        assert_eq!(
            def_eq(
                &noncanonical,
                &other,
                &WhnfContext::default(),
                DefEqBudget::unlimited(),
            ),
            DefEqOutcome::InternalFault(DefEqFault::NonCanonicalNatLiteral {
                location: DefEqLocation {
                    side: DefEqSide::Left,
                    generation: 0,
                    index: 0,
                },
            })
        );
    }
}
