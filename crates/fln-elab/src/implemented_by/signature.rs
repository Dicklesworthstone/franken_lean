//! The pin compares types using Expr.eqv after simultaneous universe renaming.
//! Binder labels/info are ignored; metadata, let non-dependency, constants and
//! universe syntax remain significant. No reduction or equivalence proof is
//! used: implemented_by deliberately changes only executable semantics.
use super::*;
use fln_core::expr::{Expr, ExprNode};
use fln_core::level::Level;

pub(super) fn validate<E: From<ImplementedByError>>(
    env: &Environment,
    declaration: &Name,
    implementation: &Name,
    spend: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<(), E> {
    spend(1)?;
    if declaration == implementation {
        return Err(ImplementedByError::SelfImplementation(declaration.clone()).into());
    }
    let source = env
        .find(declaration)
        .ok_or_else(|| ImplementedByError::UnknownDeclaration(declaration.clone()))?
        .constant_val();
    let target = env
        .find(implementation)
        .ok_or_else(|| ImplementedByError::UnknownDeclaration(implementation.clone()))?
        .constant_val();
    let mismatch = || ImplementedByError::InvalidSignature {
        declaration: declaration.clone(),
        implementation: implementation.clone(),
    };
    if source.level_params.len() != target.level_params.len() {
        return Err(mismatch().into());
    }
    spend(source.level_params.len())?;
    let mut levels = Vec::new();
    levels
        .try_reserve_exact(source.level_params.len())
        .map_err(|_| ImplementedByError::Limit)?;
    levels.extend(source.level_params.iter().cloned().map(Level::param));
    let target_type = crate::universe::parameters::instantiate(
        || spend(1),
        || mismatch().into(),
        &target.type_,
        &target.level_params,
        &levels,
    )?;
    if !equivalent(&source.type_, &target_type, spend)? {
        return Err(mismatch().into());
    }
    Ok(())
}

fn equivalent<E: From<ImplementedByError>>(
    source: &Expr,
    target: &Expr,
    spend: &mut impl FnMut(usize) -> Result<(), E>,
) -> Result<bool, E> {
    let mut pending = vec![(source, target)];
    let mut seen = HashSet::new();
    while let Some((left, right)) = pending.pop() {
        spend(1)?;
        let key = (left.allocation_identity(), right.allocation_identity());
        if key.0 == key.1 || seen.contains(&key) {
            continue;
        }
        seen.try_reserve(1).map_err(|_| ImplementedByError::Limit)?;
        seen.insert(key);
        pending
            .try_reserve(3)
            .map_err(|_| ImplementedByError::Limit)?;
        match (left.node(), right.node()) {
            (ExprNode::BVar { idx: a }, ExprNode::BVar { idx: b }) if a == b => {}
            (ExprNode::FVar { id: a }, ExprNode::FVar { id: b }) if a == b => {}
            (ExprNode::MVar { id: a }, ExprNode::MVar { id: b }) if a == b => {}
            (ExprNode::Sort { level: a }, ExprNode::Sort { level: b }) if a == b => {}
            (ExprNode::Lit { literal: a }, ExprNode::Lit { literal: b }) if a == b => {}
            (
                ExprNode::Const {
                    name: a,
                    levels: al,
                },
                ExprNode::Const {
                    name: b,
                    levels: bl,
                },
            ) if a == b && al == bl => {}
            (ExprNode::App { f: af, a: aa }, ExprNode::App { f: bf, a: ba }) => {
                pending.push((af, bf));
                pending.push((aa, ba));
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
                pending.push((at, bt));
                pending.push((ab, bb));
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
            ) if an == bn => {
                pending.push((at, bt));
                pending.push((av, bv));
                pending.push((ab, bb));
            }
            (ExprNode::MData { data: ad, expr: ae }, ExprNode::MData { data: bd, expr: be })
                if ad == bd =>
            {
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
            ) if an == bn && ai == bi => {
                pending.push((ae, be));
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}
