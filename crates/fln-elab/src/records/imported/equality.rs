//! Exact, bounded comparisons for imported structure interfaces.
//!
//! Allocation identity is only a local fast path. Unequal independently decoded
//! nodes still receive the same structural comparison, including binder names,
//! metadata, universes and declaration flags.
use super::{RecordError, tick};
use fln_core::expr::{Expr, ExprNode, Literal};
use fln_core::level::{Level, LevelView};
use fln_core::name::{LeafView, Name};
use fln_core::options::{DataValue, KVMap};
use fln_env::constants::ConstantInfo;
use std::collections::HashSet;

fn charge(left: &mut usize, count: usize) -> Result<(), RecordError> {
    *left = left.checked_sub(count).ok_or(RecordError::ResourceLimit)?;
    Ok(())
}

fn name(left: &Name, right: &Name, remaining: &mut usize) -> Result<bool, RecordError> {
    for root in [left, right] {
        let mut current = root.clone();
        loop {
            tick(remaining)?;
            match current.leaf_view() {
                LeafView::Anonymous => break,
                LeafView::Str(value) => charge(remaining, value.len())?,
                LeafView::Num(_) => {}
            }
            current = current.parent();
        }
    }
    Ok(left == right)
}

fn names(left: &[Name], right: &[Name], remaining: &mut usize) -> Result<bool, RecordError> {
    tick(remaining)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for (left, right) in left.iter().zip(right) {
        if !name(left, right, remaining)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn level(left: &Level, right: &Level, remaining: &mut usize) -> Result<bool, RecordError> {
    let mut pending = vec![(left, right)];
    let mut seen = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        tick(remaining)?;
        if left.data() != right.data() {
            return Ok(false);
        }
        if std::ptr::eq(left, right)
            || !seen.insert((std::ptr::from_ref(left), std::ptr::from_ref(right)))
        {
            continue;
        }
        match (left.view(), right.view()) {
            (LevelView::Zero, LevelView::Zero) => {}
            (LevelView::Succ(a), LevelView::Succ(b)) => pending.push((a, b)),
            (LevelView::Max(a, b), LevelView::Max(c, d))
            | (LevelView::IMax(a, b), LevelView::IMax(c, d)) => {
                pending.push((b, d));
                pending.push((a, c));
            }
            (LevelView::Param(a), LevelView::Param(b)) if name(a, b, remaining)? => {}
            (LevelView::MVar(a), LevelView::MVar(b)) if name(&a.0, &b.0, remaining)? => {}
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn metadata(left: &KVMap, right: &KVMap, remaining: &mut usize) -> Result<bool, RecordError> {
    tick(remaining)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for ((a_name, a), (b_name, b)) in left.entries().iter().zip(right.entries()) {
        if !name(a_name, b_name, remaining)? {
            return Ok(false);
        }
        let equal = match (a, b) {
            (DataValue::OfName(a), DataValue::OfName(b)) => name(a, b, remaining)?,
            (DataValue::OfString(a), DataValue::OfString(b)) => {
                charge(remaining, a.len().saturating_add(b.len()))?;
                a == b
            }
            _ => {
                tick(remaining)?;
                a == b
            }
        };
        if !equal {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn expression(
    left: &Expr,
    right: &Expr,
    remaining: &mut usize,
) -> Result<bool, RecordError> {
    let mut pending = vec![(left, right)];
    let mut seen = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        tick(remaining)?;
        if left.data() != right.data() {
            return Ok(false);
        }
        let pair = (left.allocation_identity(), right.allocation_identity());
        if pair.0 == pair.1 || !seen.insert(pair) {
            continue;
        }
        match (left.node(), right.node()) {
            (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
            (ExprNode::FVar { id: a }, ExprNode::FVar { id: b })
                if name(&a.0, &b.0, remaining)? => {}
            (ExprNode::MVar { id: a }, ExprNode::MVar { id: b })
                if name(&a.0, &b.0, remaining)? => {}
            (ExprNode::Sort { level: a }, ExprNode::Sort { level: b })
                if level(a, b, remaining)? => {}
            (
                ExprNode::Const {
                    name: a,
                    levels: a_levels,
                },
                ExprNode::Const {
                    name: b,
                    levels: b_levels,
                },
            ) => {
                if !name(a, b, remaining)? || a_levels.len() != b_levels.len() {
                    return Ok(false);
                }
                for (a, b) in a_levels.iter().zip(b_levels) {
                    if !level(a, b, remaining)? {
                        return Ok(false);
                    }
                }
            }
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                pending.push((aa, ba));
                pending.push((af, bf));
            }
            (
                ExprNode::Lam {
                    binder_name: an,
                    binder_type: at,
                    body: ab,
                    binder_info: ai,
                },
                ExprNode::Lam {
                    binder_name: bn,
                    binder_type: bt,
                    body: bb,
                    binder_info: bi,
                },
            )
            | (
                ExprNode::ForallE {
                    binder_name: an,
                    binder_type: at,
                    body: ab,
                    binder_info: ai,
                },
                ExprNode::ForallE {
                    binder_name: bn,
                    binder_type: bt,
                    body: bb,
                    binder_info: bi,
                },
            ) => {
                if ai != bi || !name(an, bn, remaining)? {
                    return Ok(false);
                }
                pending.push((ab, bb));
                pending.push((at, bt));
            }
            (
                ExprNode::LetE {
                    decl_name: an,
                    type_: at,
                    value: av,
                    body: ab,
                    non_dep: ad,
                },
                ExprNode::LetE {
                    decl_name: bn,
                    type_: bt,
                    value: bv,
                    body: bb,
                    non_dep: bd,
                },
            ) => {
                if ad != bd || !name(an, bn, remaining)? {
                    return Ok(false);
                }
                pending.push((ab, bb));
                pending.push((av, bv));
                pending.push((at, bt));
            }
            (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) => {
                let size = |value: &Literal| match value {
                    Literal::Nat(value) => value.limbs_le().len(),
                    Literal::Str(value) => value.len(),
                };
                charge(remaining, size(a).saturating_add(size(b)))?;
                if a != b {
                    return Ok(false);
                }
            }
            (ExprNode::MData { data: a, expr: ae }, ExprNode::MData { data: b, expr: be }) => {
                if !metadata(a, b, remaining)? {
                    return Ok(false);
                }
                pending.push((ae, be));
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
                if ai != bi || !name(an, bn, remaining)? {
                    return Ok(false);
                }
                pending.push((ae, be));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// Compare a structure family, constructor or generated projection exactly.
/// This is an observation, never an admission path. The source importer uses it
/// to bind metadata to its checked module without unmetered ConstantInfo walks.
pub fn same_interface(
    left: &ConstantInfo,
    right: &ConstantInfo,
    remaining: &mut usize,
) -> Result<bool, RecordError> {
    tick(remaining)?;
    let (a, b) = (left.constant_val(), right.constant_val());
    if !name(&a.name, &b.name, remaining)?
        || !names(&a.level_params, &b.level_params, remaining)?
        || !expression(&a.type_, &b.type_, remaining)?
    {
        return Ok(false);
    }
    let equal = match (left, right) {
        (ConstantInfo::Induct(a), ConstantInfo::Induct(b)) => {
            a.num_params == b.num_params
                && a.num_indices == b.num_indices
                && a.num_nested == b.num_nested
                && a.is_rec == b.is_rec
                && a.is_unsafe == b.is_unsafe
                && a.is_reflexive == b.is_reflexive
                && names(&a.all, &b.all, remaining)?
                && names(&a.ctors, &b.ctors, remaining)?
        }
        (ConstantInfo::Ctor(a), ConstantInfo::Ctor(b)) => {
            a.cidx == b.cidx
                && a.num_params == b.num_params
                && a.num_fields == b.num_fields
                && a.is_unsafe == b.is_unsafe
                && name(&a.induct, &b.induct, remaining)?
        }
        (ConstantInfo::Defn(a), ConstantInfo::Defn(b)) => {
            a.hints == b.hints
                && a.safety == b.safety
                && names(&a.all, &b.all, remaining)?
                && expression(&a.value, &b.value, remaining)?
        }
        (ConstantInfo::Thm(a), ConstantInfo::Thm(b)) => {
            names(&a.all, &b.all, remaining)? && expression(&a.value, &b.value, remaining)?
        }
        _ => false,
    };
    Ok(equal)
}
