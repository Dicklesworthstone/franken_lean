//! Recover a literal lambda hidden by value-only administrative bindings.
//!
//! This does not eta-expand a computed callback. A successful result removes
//! only identity lets and unused variable/literal aliases; every application,
//! projection, used alias, and other strict initializer remains a stage boundary.
use super::*;

impl Preparation<'_> {
    pub(in crate::runtime) fn administrative_callable_value(
        &mut self,
        input: &Expr,
    ) -> Result<Expr, IngressError> {
        if !matches!(input.node(), ExprNode::Lam { .. }) {
            return Ok(input.clone());
        }
        let mut value = input.clone();
        let mut binders = Vec::new();
        let mut changed = false;
        while let ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } = value.node()
        {
            self.producer_depth(binders.len().saturating_add(1))?;
            reserve(&mut binders, self.limits.max_context_depth)?;
            binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            value = if matches!(body.node(), ExprNode::LetE { .. } | ExprNode::MData { .. })
                && let Some(literal) = self.administrative_callable_gap(body)?
            {
                changed = true;
                literal
            } else {
                body.clone()
            };
        }
        if !changed {
            return Ok(input.clone());
        }
        for (name, type_, info) in binders.into_iter().rev() {
            self.tick()?;
            value = Expr::lam(name, type_, value, info);
        }
        Ok(value)
    }

    pub(in crate::runtime) fn administrative_callable_gap(
        &mut self,
        input: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        enum Work {
            Visit(Expr, usize),
            Let(Name, Expr, bool),
        }
        let mut work = vec![Work::Visit(input.clone(), 0)];
        let mut values = Vec::new();
        while let Some(task) = work.pop() {
            self.tick()?;
            let value = match task {
                Work::Visit(expr, depth) => match expr.node() {
                    ExprNode::MData { expr, .. } => {
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Visit(expr.clone(), depth));
                        continue;
                    }
                    ExprNode::LetE {
                        decl_name,
                        type_,
                        value,
                        body,
                        non_dep,
                    } => {
                        let nested = depth.saturating_add(1);
                        self.producer_depth(nested)?;
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Let(decl_name.clone(), type_.clone(), *non_dep));
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Visit(body.clone(), nested));
                        reserve(&mut work, self.limits.max_nodes)?;
                        work.push(Work::Visit(value.clone(), depth));
                        continue;
                    }
                    // A lambda is already a value. In particular, never walk
                    // its body to call a global or search for a later lambda.
                    _ => expr,
                },
                Work::Let(name, type_, non_dep) => {
                    let body = pop(&mut values)?;
                    let value = pop(&mut values)?;
                    if matches!(body.node(), ExprNode::BVar { idx: 0 }) {
                        // The initializer is evaluated once at this very
                        // position, even if it is an actual computation.
                        value
                    } else if matches!(value.node(), ExprNode::BVar { .. } | ExprNode::Lit { .. })
                        && self.administrative_local_absent(&body)?
                    {
                        // Absence includes checked type annotations, so
                        // removing this slot also preserves dependent scopes.
                        self.substitution(&body, &value)?
                    } else {
                        Expr::let_e(name, type_, value, body, non_dep)
                    }
                }
            };
            reserve(&mut values, self.limits.max_nodes)?;
            values.push(value);
        }
        if values.len() != 1 {
            return Err(unsupported("administrative callback result stack"));
        }
        let result = pop(&mut values)?;
        // If any genuine work remains between the lambda stages, retain the
        // complete original input, including its checked type anchors.
        Ok(matches!(result.node(), ExprNode::Lam { .. }).then_some(result))
    }

    fn administrative_local_absent(&mut self, body: &Expr) -> Result<bool, IngressError> {
        let mut pending = vec![(body.clone(), 0usize)];
        while let Some((expr, depth)) = pending.pop() {
            self.tick()?;
            let height = expr.approx_depth();
            if usize::try_from(expr.loose_bvar_range()).is_ok_and(|range| range <= depth)
                && height < u8::MAX
                && depth.checked_add(usize::from(height)).is_some_and(|end| {
                    end <= self.limits.max_context_depth && u32::try_from(end).is_ok()
                })
            {
                continue;
            }
            let limit = self.limits.max_nodes;
            let mut push = |expr: &Expr, depth| -> Result<(), IngressError> {
                reserve(&mut pending, limit)?;
                pending.push((expr.clone(), depth));
                Ok(())
            };
            match expr.node() {
                ExprNode::BVar { idx } if usize::try_from(*idx).ok() == Some(depth) => {
                    return Ok(false);
                }
                ExprNode::App { f, a } => {
                    push(a, depth)?;
                    push(f, depth)?;
                }
                ExprNode::Lam {
                    binder_type, body, ..
                }
                | ExprNode::ForallE {
                    binder_type, body, ..
                } => {
                    let nested = depth.saturating_add(1);
                    self.producer_depth(nested)?;
                    push(body, nested)?;
                    push(binder_type, depth)?;
                }
                ExprNode::LetE {
                    type_, value, body, ..
                } => {
                    let nested = depth.saturating_add(1);
                    self.producer_depth(nested)?;
                    push(body, nested)?;
                    push(value, depth)?;
                    push(type_, depth)?;
                }
                ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => push(expr, depth)?,
                _ => {}
            }
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests;
