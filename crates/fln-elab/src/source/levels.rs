//! Capture-preserving universe parameter instantiation for source constants.
use super::{Context, SourceInferenceError, failure};
use crate::NatDefinitionElabError;
use fln_core::expr::{Expr, ExprNode};
use fln_core::level::{Level, LevelView};
use fln_core::name::Name;
use std::collections::HashMap;

impl Context {
    pub(super) fn instantiate_params(
        &mut self,
        expr: &Expr,
        params: &[Name],
        levels: &[Level],
    ) -> Result<Expr, NatDefinitionElabError> {
        if params.len() != levels.len() {
            return Err(failure(SourceInferenceError::Scope));
        }
        if !expr.has_level_param() || params.is_empty() {
            return Ok(expr.clone());
        }
        let substitutions: HashMap<_, _> = params.iter().zip(levels).collect();
        if substitutions.len() != params.len() {
            return Err(failure(SourceInferenceError::Scope));
        }
        let mut done = HashMap::<usize, Expr>::new();
        let mut level_done = HashMap::<*const Level, Level>::new();
        let mut pending = vec![(expr, false)];
        while let Some((current, exit)) = pending.pop() {
            self.tick()?;
            let id = current.allocation_identity();
            if done.contains_key(&id) {
                continue;
            }
            if !current.has_level_param() {
                done.insert(id, current.clone());
                continue;
            }
            if !exit {
                pending.push((current, true));
                match current.node() {
                    ExprNode::App { f, a } => {
                        pending.push((a, false));
                        pending.push((f, false));
                    }
                    ExprNode::Lam {
                        binder_type, body, ..
                    }
                    | ExprNode::ForallE {
                        binder_type, body, ..
                    } => {
                        pending.push((body, false));
                        pending.push((binder_type, false));
                    }
                    ExprNode::LetE {
                        type_, value, body, ..
                    } => {
                        pending.push((body, false));
                        pending.push((value, false));
                        pending.push((type_, false));
                    }
                    ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                        pending.push((expr, false))
                    }
                    _ => {}
                }
                continue;
            }
            let child = |expr: &Expr| done[&expr.allocation_identity()].clone();
            let value = match current.node() {
                ExprNode::Sort { level } => Expr::sort(self.instantiate_param_level(
                    level,
                    &substitutions,
                    &mut level_done,
                )?),
                ExprNode::Const { name, levels } => {
                    let mut result = Vec::new();
                    for level in levels {
                        result.push(self.instantiate_param_level(
                            level,
                            &substitutions,
                            &mut level_done,
                        )?);
                    }
                    Expr::const_(name.clone(), result)
                }
                ExprNode::App { f, a } => Expr::app(child(f), child(a)),
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    binder_name.clone(),
                    child(binder_type),
                    child(body),
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(
                    binder_name.clone(),
                    child(binder_type),
                    child(body),
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
                    child(type_),
                    child(value),
                    child(body),
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => Expr::mdata(data.clone(), child(expr)),
                ExprNode::Proj {
                    struct_name,
                    idx,
                    expr,
                } => Expr::proj(struct_name.clone(), *idx, child(expr)),
                _ => current.clone(),
            };
            done.insert(id, value);
        }
        Ok(done[&expr.allocation_identity()].clone())
    }

    fn instantiate_param_level(
        &mut self,
        level: &Level,
        substitutions: &HashMap<&Name, &Level>,
        done: &mut HashMap<*const Level, Level>,
    ) -> Result<Level, NatDefinitionElabError> {
        let mut pending = vec![(level, false)];
        while let Some((current, exit)) = pending.pop() {
            self.tick()?;
            let id = std::ptr::from_ref(current);
            if done.contains_key(&id) {
                continue;
            }
            if !current.has_param() {
                done.insert(id, current.clone());
                continue;
            }
            if !exit {
                pending.push((current, true));
                match current.view() {
                    LevelView::Succ(inner) => pending.push((inner, false)),
                    LevelView::Max(left, right) | LevelView::IMax(left, right) => {
                        pending.push((right, false));
                        pending.push((left, false));
                    }
                    _ => {}
                }
                continue;
            }
            let child = |level: &Level| done[&std::ptr::from_ref(level)].clone();
            let result = match current.view() {
                LevelView::Param(name) => substitutions
                    .get(name)
                    .map_or_else(|| current.clone(), |level| (*level).clone()),
                LevelView::Succ(inner) => child(inner)
                    .succ()
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                LevelView::Max(left, right) => Level::max(child(left), child(right))
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                LevelView::IMax(left, right) => Level::imax(child(left), child(right))
                    .map_err(|_| failure(SourceInferenceError::Scope))?,
                _ => current.clone(),
            };
            done.insert(id, result);
        }
        Ok(done[&std::ptr::from_ref(level)].clone())
    }
}
