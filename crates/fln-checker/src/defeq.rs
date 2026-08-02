//! Resource-counted quick definitional equality over checker-owned arenas.
//!
//! This is deliberately only the KR-300 through KR-303 front end. It proves
//! reflexive structural congruence, treats metadata as transparent, ignores
//! binder presentation, and compares `Sort` levels with this checker's
//! independent universe relation. It returns a typed deferral whenever a
//! conclusion could depend on weak-head reduction, delta, eta, proof
//! irrelevance, recursors, native computation, literal expansion, or typing
//! information. A deferral is not a rejection and this module is not a
//! declaration-admission authority.

use std::collections::BTreeSet;

use crate::universe::{UniverseError, level_roots_equal};
use crate::wire::{ExprId, ExprNode, WireExpr, usize_units};

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
    }
}
