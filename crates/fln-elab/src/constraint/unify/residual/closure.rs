//! Close a validated local telescope without rewalking every inner binding.
//!
//! The dependency walk in `prepare_value_check` has already instantiated and
//! ordered every local and residual. Abstract each original field against its
//! prefix once, then assemble the same lambda/forall/let telescope that repeated
//! single-variable abstraction produces. No local or kernel check is omitted.

use super::super::{Meter, UnificationDeferred, UnificationError};
use crate::lctx::LocalContext;
use fln_core::expr::{Expr, ExprNode, FVarId};
use std::collections::HashMap;

pub(super) fn close(
    value: Expr,
    type_: Expr,
    telescope: &LocalContext,
    meter: &mut Meter<'_>,
) -> Result<(Expr, Expr), UnificationError> {
    let mut positions = HashMap::new();
    for (index, local) in telescope.decls().iter().enumerate() {
        meter.node()?;
        if local.index != index || positions.insert(local.id.clone(), index).is_some() {
            return Err(UnificationError::Deferred(
                UnificationDeferred::InvalidLocalContext,
            ));
        }
    }
    let mut value = abstract_prefix(&value, &positions, telescope.len(), meter)?;
    let mut type_ = abstract_prefix(&type_, &positions, telescope.len(), meter)?;
    for (index, local) in telescope.decls().iter().enumerate().rev() {
        meter.node()?;
        let domain = abstract_prefix(&local.type_, &positions, index, meter)?;
        if let Some(local_value) = &local.value {
            let local_value = abstract_prefix(local_value, &positions, index, meter)?;
            value = Expr::let_e(
                local.user_name.clone(),
                domain.clone(),
                local_value.clone(),
                value,
                false,
            );
            type_ = Expr::let_e(local.user_name.clone(), domain, local_value, type_, false);
        } else {
            value = Expr::lam(
                local.user_name.clone(),
                domain.clone(),
                value,
                local.binder_info,
            );
            type_ = Expr::forall_e(local.user_name.clone(), domain, type_, local.binder_info);
        }
    }
    Ok((value, type_))
}

/// The borrowed root pins every source identity. A cache is local to this one
/// prefix; binder depth remains part of its key because a shared DAG node may
/// appear both outside and underneath a lambda. Existing bound variables and
/// free variables outside the prefix are unchanged, just as in `abstract_fvar`.
fn abstract_prefix(
    expr: &Expr,
    positions: &HashMap<FVarId, usize>,
    prefix: usize,
    meter: &mut Meter<'_>,
) -> Result<Expr, UnificationError> {
    let mut done: HashMap<(usize, u32), Expr> = HashMap::new();
    let mut pending = vec![(expr, 0_u32, false)];
    while let Some((current, depth, exit)) = pending.pop() {
        meter.tick()?;
        let key = (current.allocation_identity(), depth);
        if done.contains_key(&key) {
            continue;
        }
        if !exit {
            meter.node()?;
            if !current.has_fvar() {
                done.insert(key, current.clone());
                continue;
            }
            pending.push((current, depth, true));
            match current.node() {
                ExprNode::App { f, a } => {
                    pending.push((a, depth, false));
                    pending.push((f, depth, false));
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    let inner = depth
                        .checked_add(1)
                        .ok_or(UnificationError::ExpressionScope)?;
                    pending.push((body, inner, false));
                    pending.push((binder_type, depth, false));
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    let inner = depth
                        .checked_add(1)
                        .ok_or(UnificationError::ExpressionScope)?;
                    pending.push((body, inner, false));
                    pending.push((value, depth, false));
                    pending.push((type_, depth, false));
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                    pending.push((expr, depth, false));
                }
                ExprNode::BVar { .. }
                | ExprNode::FVar { .. }
                | ExprNode::MVar { .. }
                | ExprNode::Sort { .. }
                | ExprNode::Const { .. }
                | ExprNode::Lit { .. } => {}
            }
            continue;
        }
        let child = |expr: &Expr, depth| {
            done.get(&(expr.allocation_identity(), depth))
                .cloned()
                .ok_or(UnificationError::ExpressionScope)
        };
        let abstracted = match current.node() {
            ExprNode::FVar { id } => {
                if let Some(&position) = positions.get(id).filter(|&&position| position < prefix) {
                    let index = u32::try_from(prefix - 1 - position)
                        .ok()
                        .and_then(|index| index.checked_add(depth))
                        .ok_or(UnificationError::ExpressionScope)?;
                    Expr::bvar(index).map_err(|_| UnificationError::ExpressionScope)?
                } else {
                    current.clone()
                }
            }
            ExprNode::BVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Const { .. }
            | ExprNode::Lit { .. } => current.clone(),
            ExprNode::App { f, a } => Expr::app(child(f, depth)?, child(a, depth)?),
            ExprNode::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::lam(
                binder_name.clone(),
                child(binder_type, depth)?,
                child(
                    body,
                    depth
                        .checked_add(1)
                        .ok_or(UnificationError::ExpressionScope)?,
                )?,
                *binder_info,
            ),
            ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => Expr::forall_e(
                binder_name.clone(),
                child(binder_type, depth)?,
                child(
                    body,
                    depth
                        .checked_add(1)
                        .ok_or(UnificationError::ExpressionScope)?,
                )?,
                *binder_info,
            ),
            ExprNode::LetE {
                decl_name,
                type_,
                value,
                body,
                non_dep,
            } => Expr::let_e(
                decl_name.clone(),
                child(type_, depth)?,
                child(value, depth)?,
                child(
                    body,
                    depth
                        .checked_add(1)
                        .ok_or(UnificationError::ExpressionScope)?,
                )?,
                *non_dep,
            ),
            ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr, depth)?),
            ExprNode::Proj {
                struct_name,
                idx,
                expr,
            } => Expr::proj(struct_name.clone(), *idx, child(expr, depth)?),
        };
        done.insert(key, abstracted);
    }
    done.remove(&(expr.allocation_identity(), 0))
        .ok_or(UnificationError::ExpressionScope)
}

#[cfg(test)]
mod tests;
