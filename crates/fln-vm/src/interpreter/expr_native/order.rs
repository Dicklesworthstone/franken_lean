//! Pinned C++ expression order (`library/expr_lt.cpp`), including its distinct
//! name order (`util/name.cpp`) and metadata order (`util/kvmap.cpp`).
//! Every recursive comparison is a tail step; equality uses the existing
//! bounded pair walk before it can select the next child.

use std::cmp::Ordering;

use super::{Expr, ExprNode, IntrinsicFailure, Level, WorkBudget, check_equality_pairs};
use fln_core::level::LevelView;
use fln_core::name::{LeafView, Name};
use fln_core::options::{DataValue, KVMap};

pub(super) fn less_than(
    mut left: &Expr,
    mut right: &Expr,
    use_hash: bool,
    budget: &mut WorkBudget,
) -> Result<bool, IntrinsicFailure> {
    loop {
        budget.visit()?;
        if left.allocation_identity() == right.allocation_identity() {
            return Ok(false);
        }
        let kinds = expr_kind(left.node()).cmp(&expr_kind(right.node()));
        if kinds != Ordering::Equal {
            return Ok(kinds == Ordering::Less);
        }
        if use_hash && left.hash() != right.hash() {
            return Ok(left.hash() < right.hash());
        }
        // The pin's operator== is alpha equality, not Expr.equal: binder
        // names and binder-info cannot select an earlier child here.
        match (left.node(), right.node()) {
            (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) => return Ok(a < b),
            (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) => {
                return Ok(name_cmp(&a.0, &b.0, budget)? == Ordering::Less);
            }
            (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) => {
                return Ok(name_cmp(&a.0, &b.0, budget)? == Ordering::Less);
            }
            (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) => {
                return level_less_than(a, b, use_hash, budget);
            }
            (
                ExprNode::Const {
                    name: a,
                    levels: al,
                },
                ExprNode::Const {
                    name: b,
                    levels: bl,
                },
            ) => {
                let names = name_cmp(a, b, budget)?;
                if names != Ordering::Equal {
                    return Ok(names == Ordering::Less);
                }
                for (a, b) in al.iter().zip(bl) {
                    if !level_equal(a, b, budget)? {
                        return level_less_than(a, b, use_hash, budget);
                    }
                }
                return Ok(al.len() < bl.len());
            }
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                (left, right) = if alpha_equal(af, bf, budget)? {
                    (aa, ba)
                } else {
                    (af, bf)
                };
            }
            (
                ExprNode::Lam {
                    binder_type: at,
                    body: ab,
                    ..
                },
                ExprNode::Lam {
                    binder_type: bt,
                    body: bb,
                    ..
                },
            )
            | (
                ExprNode::ForallE {
                    binder_type: at,
                    body: ab,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: bt,
                    body: bb,
                    ..
                },
            ) => {
                (left, right) = if alpha_equal(at, bt, budget)? {
                    (ab, bb)
                } else {
                    (at, bt)
                };
            }
            (
                ExprNode::LetE {
                    type_: at,
                    value: av,
                    body: ab,
                    non_dep: an,
                    ..
                },
                ExprNode::LetE {
                    type_: bt,
                    value: bv,
                    body: bb,
                    non_dep: bn,
                    ..
                },
            ) => {
                if an != bn {
                    return Ok(an < bn);
                }
                (left, right) = if !alpha_equal(at, bt, budget)? {
                    (at, bt)
                } else if !alpha_equal(av, bv, budget)? {
                    (av, bv)
                } else {
                    (ab, bb)
                };
            }
            (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) => {
                return Ok(a.lt(b));
            }
            (ExprNode::MData { data: ad, expr: ae }, ExprNode::MData { data: bd, expr: be }) => {
                if alpha_equal(ae, be, budget)? {
                    return metadata_less_than(ad, bd, budget);
                }
                (left, right) = (ae, be);
            }
            (
                ExprNode::Proj {
                    struct_name: an,
                    idx: ai,
                    expr: ae,
                },
                ExprNode::Proj {
                    struct_name: bn,
                    idx: bi,
                    expr: be,
                },
            ) => {
                if alpha_equal(ae, be, budget)? {
                    let names = name_cmp(an, bn, budget)?;
                    return Ok(if names == Ordering::Equal {
                        ai < bi
                    } else {
                        names == Ordering::Less
                    });
                }
                (left, right) = (ae, be);
            }
            _ => unreachable!("both expressions have the same constructor"),
        }
    }
}

fn alpha_equal(
    left: &Expr,
    right: &Expr,
    budget: &mut WorkBudget,
) -> Result<bool, IntrinsicFailure> {
    check_equality_pairs(left, right, budget)?;
    Ok(left.is_alpha_equiv(right))
}

fn level_equal(
    left: &Level,
    right: &Level,
    budget: &mut WorkBudget,
) -> Result<bool, IntrinsicFailure> {
    budget.level_pairs(left, right)?;
    Ok(left == right)
}

pub(super) fn level_less_than(
    mut left: &Level,
    mut right: &Level,
    use_hash: bool,
    budget: &mut WorkBudget,
) -> Result<bool, IntrinsicFailure> {
    loop {
        budget.visit()?;
        if left.allocation_identity() == right.allocation_identity() {
            return Ok(false);
        }
        // kernel/level.cpp orders depth before constructor, unlike Expr.
        if left.data().depth() != right.data().depth() {
            return Ok(left.data().depth() < right.data().depth());
        }
        let kinds = level_kind(left.view()).cmp(&level_kind(right.view()));
        if kinds != Ordering::Equal {
            return Ok(kinds == Ordering::Less);
        }
        if use_hash && left.hash() != right.hash() {
            return Ok(left.hash() < right.hash());
        }
        match (left.view(), right.view()) {
            (LevelView::Zero, LevelView::Zero) => return Ok(false),
            (LevelView::Param(a), LevelView::Param(b)) => {
                return Ok(name_cmp(a, b, budget)? == Ordering::Less);
            }
            (LevelView::MVar(a), LevelView::MVar(b)) => {
                return Ok(name_cmp(&a.0, &b.0, budget)? == Ordering::Less);
            }
            (LevelView::Succ(a), LevelView::Succ(b)) => (left, right) = (a, b),
            (LevelView::Max(al, ar), LevelView::Max(bl, br))
            | (LevelView::IMax(al, ar), LevelView::IMax(bl, br)) => {
                (left, right) = if level_equal(al, bl, budget)? {
                    (ar, br)
                } else {
                    (al, bl)
                };
            }
            _ => unreachable!("both levels have the same constructor"),
        }
    }
}

fn expr_kind(node: &ExprNode) -> u8 {
    match node {
        ExprNode::BVar { .. } => 0,
        ExprNode::FVar { .. } => 1,
        ExprNode::MVar { .. } => 2,
        ExprNode::Sort { .. } => 3,
        ExprNode::Const { .. } => 4,
        ExprNode::App { .. } => 5,
        ExprNode::Lam { .. } => 6,
        ExprNode::ForallE { .. } => 7,
        ExprNode::LetE { .. } => 8,
        ExprNode::Lit { .. } => 9,
        ExprNode::MData { .. } => 10,
        ExprNode::Proj { .. } => 11,
    }
}

fn level_kind(level: LevelView<'_>) -> u8 {
    match level {
        LevelView::Zero => 0,
        LevelView::Succ(_) => 1,
        LevelView::Max(..) => 2,
        LevelView::IMax(..) => 3,
        LevelView::Param(_) => 4,
        LevelView::MVar(_) => 5,
    }
}

fn name_components(name: &Name, budget: &mut WorkBudget) -> Result<Vec<Name>, IntrinsicFailure> {
    let mut parts = Vec::new();
    let mut current = name.clone();
    while !current.is_anonymous() {
        budget.visit()?;
        let parent = current.parent();
        parts.push(current);
        current = parent;
    }
    Ok(parts)
}

fn name_cmp(
    left: &Name,
    right: &Name,
    budget: &mut WorkBudget,
) -> Result<Ordering, IntrinsicFailure> {
    // util/name.cpp compares root-to-leaf components. Name::Ord implements
    // Lean Name.cmp, whose leaf-constructor precedence is a different order.
    let left = name_components(left, budget)?;
    let right = name_components(right, budget)?;
    for (a, b) in left.iter().rev().zip(right.iter().rev()) {
        let order = match (a.leaf_view(), b.leaf_view()) {
            (LeafView::Num(a), LeafView::Num(b)) => a.cmp(&b),
            (LeafView::Str(a), LeafView::Str(b)) => a.cmp(b),
            (LeafView::Num(_), LeafView::Str(_)) => Ordering::Less,
            (LeafView::Str(_), LeafView::Num(_)) => Ordering::Greater,
            _ => unreachable!("anonymous is excluded from the component lists"),
        };
        if order != Ordering::Equal {
            return Ok(order);
        }
    }
    Ok(left.len().cmp(&right.len()))
}

fn metadata_less_than(
    left: &KVMap,
    right: &KVMap,
    budget: &mut WorkBudget,
) -> Result<bool, IntrinsicFailure> {
    for ((ak, av), (bk, bv)) in left.entries().iter().zip(right.entries()) {
        budget.visit()?;
        let names = name_cmp(ak, bk, budget)?;
        let order = if names == Ordering::Equal {
            data_value_cmp(av, bv, budget)?
        } else {
            names
        };
        if order != Ordering::Equal {
            return Ok(order == Ordering::Less);
        }
    }
    Ok(left.len() < right.len())
}

fn data_value_cmp(
    left: &DataValue,
    right: &DataValue,
    budget: &mut WorkBudget,
) -> Result<Ordering, IntrinsicFailure> {
    let kinds = data_value_kind(left).cmp(&data_value_kind(right));
    if kinds != Ordering::Equal {
        return Ok(kinds);
    }
    Ok(match (left, right) {
        (DataValue::OfString(a), DataValue::OfString(b)) => a.cmp(b),
        (DataValue::OfBool(a), DataValue::OfBool(b)) => a.cmp(b),
        (DataValue::OfName(a), DataValue::OfName(b)) => name_cmp(a, b, budget)?,
        (DataValue::OfNat(a), DataValue::OfNat(b)) => a.cmp(b),
        // The pin has no less-than case for equal-tag Int/Syntax and returns
        // false in both directions. list_ref continues to the
        // next entry even if those payloads are structurally unequal.
        (DataValue::OfInt(_), DataValue::OfInt(_))
        | (DataValue::OfSyntax(_), DataValue::OfSyntax(_)) => Ordering::Equal,
        _ => unreachable!("both data values have the same constructor"),
    })
}

fn data_value_kind(value: &DataValue) -> u8 {
    match value {
        DataValue::OfString(_) => 0,
        DataValue::OfBool(_) => 1,
        DataValue::OfName(_) => 2,
        DataValue::OfNat(_) => 3,
        DataValue::OfInt(_) => 4,
        DataValue::OfSyntax(_) => 5,
    }
}
