//! Equality transport after admission. Concrete layout changes remain refused;
//! a checked Type equality can cross the private boxed carrier while retaining
//! the concrete payload and result interfaces. No proof is executed, and
//! ordinary endpoint/payload evaluation is retained in source order.
mod quotient;

use super::*;

fn application(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

impl Preparation<'_> {
    fn check_equality_family(&mut self) -> Result<(), IngressError> {
        if self.equality_family_checked {
            return Ok(());
        }
        if !crate::source_intrinsics::equality_family_matches(
            self.environment,
            &mut self.visited,
            self.limits,
        )? {
            return Err(unsupported("noncanonical equality family"));
        }
        self.equality_family_checked = true;
        Ok(())
    }

    /// Preserve the supplied, nondependent argument interface of a transport
    /// whose enclosing checked Type-index branch returns the boxed carrier.
    fn boxed_applied_transport_type(
        &mut self,
        mut before: Expr,
        mut after: Expr,
        arguments: usize,
    ) -> Result<Option<Expr>, IngressError> {
        let Some(mut result) = self.value_types.boxed.clone() else {
            return Ok(None);
        };
        let mut domains = Vec::new();
        for _ in 0..arguments {
            self.tick()?;
            let (
                ExprNode::ForallE {
                    binder_type: ad,
                    body: ab,
                    ..
                },
                ExprNode::ForallE {
                    binder_name,
                    binder_type: ed,
                    body: eb,
                    binder_info,
                },
            ) = (before.node(), after.node())
            else {
                return Ok(None);
            };
            if ad != ed || ab.has_loose_bvar(0) || eb.has_loose_bvar(0) {
                return Ok(None);
            }
            reserve(&mut domains, self.limits.max_context_depth)?;
            domains.push((binder_name.clone(), ed.clone(), *binder_info));
            before = ab.clone();
            after = eb.clone();
        }
        if self.value_type(&before)?.is_none() || self.value_type(&after)?.is_none() {
            return Ok(None);
        }
        for (name, domain, info) in domains.into_iter().rev() {
            self.tick()?;
            result = Expr::forall_e(name, domain, result, info);
        }
        Ok(Some(result))
    }

    /// Called only by a scheduler-owned boxed branch. Leading strict bindings
    /// retain their order; no initializer is substituted or dropped.
    pub(super) fn boxed_equality_transport(
        &mut self,
        value: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let mut value = value.clone();
        let mut prefix = Vec::new();
        loop {
            self.tick()?;
            match value.node() {
                ExprNode::MData { expr, .. } => value = expr.clone(),
                ExprNode::LetE {
                    decl_name,
                    type_,
                    value: init,
                    body,
                    non_dep,
                } => {
                    reserve(&mut prefix, self.limits.max_context_depth)?;
                    prefix.push((decl_name.clone(), type_.clone(), init.clone(), *non_dep));
                    value = body.clone();
                }
                _ => break,
            }
        }
        let (head, args) = self.spine(&value)?;
        let Some(mut value) = self.equality_transport_result(&head, &args, true)? else {
            return Ok(None);
        };
        for (name, type_, init, non_dep) in prefix.into_iter().rev() {
            self.tick()?;
            value = Expr::let_e(name, type_, init, value, non_dep);
        }
        Ok(Some(value))
    }

    /// A checked Type refinement can change the result of an otherwise
    /// identical, nondependent function telescope to or from the boxed carrier.
    /// Argument interfaces and value-dependent result types stay unchanged.
    fn boxed_result_refinement(
        &mut self,
        mut before: &Expr,
        mut after: &Expr,
    ) -> Result<bool, IngressError> {
        let Some(boxed) = self.value_types.boxed.clone() else {
            return Ok(false);
        };
        loop {
            self.tick()?;
            if before == &boxed || after == &boxed {
                return Ok(true);
            }
            let (
                ExprNode::ForallE {
                    binder_type: before_domain,
                    body: before_body,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: after_domain,
                    body: after_body,
                    ..
                },
            ) = (before.node(), after.node())
            else {
                return Ok(false);
            };
            if before_domain != after_domain
                || before_body.has_loose_bvar(0)
                || after_body.has_loose_bvar(0)
            {
                return Ok(false);
            }
            before = before_body;
            after = after_body;
        }
    }

    pub(super) fn equality_transport(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        self.equality_transport_result(head, args, false)
    }

    fn equality_transport_result(
        &mut self,
        head: &Expr,
        args: &[Expr],
        boxed_result: bool,
    ) -> Result<Option<Expr>, IngressError> {
        // Quotient construction/elimination is another post-admission
        // representation transport. Keep it before ordinary callable ingress.
        if !boxed_result && let Some(value) = self.quotient_operation(head, args)? {
            return Ok(Some(value));
        }
        let ExprNode::Const {
            name: callee,
            levels,
        } = head.node()
        else {
            return Ok(None);
        };
        if callee != &name("Eq.rec") || levels.len() != 2 || args.len() < 6 {
            return Ok(None);
        }
        self.check_equality_family()?;
        let refl = application(
            Expr::const_(name("Eq.refl"), vec![levels[1].clone()]),
            [args[0].clone(), args[1].clone()],
        );
        let before = application(args[2].clone(), [args[1].clone(), refl]);
        let after = application(args[2].clone(), [args[4].clone(), args[5].clone()]);
        let before = self.erase_runtime_type(&before)?;
        let mut after = self.erase_runtime_type(&after)?;
        let carrier = self.erase_runtime_type(&args[0])?;
        let static_endpoints = self.type_parameter(&carrier)?;
        if boxed_result {
            if !static_endpoints {
                return Ok(None);
            }
            let Some(type_) =
                self.boxed_applied_transport_type(before.clone(), after, args.len() - 6)?
            else {
                return Ok(None);
            };
            after = type_;
        }
        let boxed_refinement =
            before != after && static_endpoints && self.boxed_result_refinement(&before, &after)?;
        if before != after && !boxed_refinement {
            return Err(unsupported("representation-dependent equality transport"));
        }
        let result = self
            .value_type(&after)?
            .ok_or_else(|| unsupported("equality transport result representation"))?;
        let payload_type = if before == after {
            result
        } else {
            self.value_type(&before)?
                .ok_or_else(|| unsupported("equality transport payload representation"))?
        };
        if !static_endpoints && self.value_type(&carrier)?.is_none() {
            return Err(unsupported("equality transport carrier representation"));
        }
        // Constructing a literal lambda is inert. A fully supplied cast of one
        // can expose its beta spine directly, without inventing an annotation
        // for a curried source lambda interrupted by strict lets.
        let mut arity = 0usize;
        let mut codomain = &after;
        while let ExprNode::ForallE { body, .. } = codomain.node() {
            self.tick()?;
            arity = arity
                .checked_add(1)
                .ok_or_else(|| unsupported("transport arity"))?;
            codomain = body;
        }
        if before == after
            && matches!(args[3].node(), ExprNode::Lam { .. })
            && args.len() - 6 >= arity
        {
            let depth = if static_endpoints { 0 } else { 2 };
            if depth as usize > self.limits.max_context_depth {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ContextDepth,
                    limit: self.limits.max_context_depth,
                    observed: depth as usize,
                });
            }
            let mut applied = self.lift(&args[3], depth)?;
            for argument in &args[6..] {
                self.tick()?;
                applied = Expr::app(applied, self.lift(argument, depth)?);
            }
            if !static_endpoints {
                applied = Expr::let_e(
                    Name::anonymous(),
                    self.lift(&carrier, 1)?,
                    self.lift(&args[4], 1)?,
                    applied,
                    false,
                );
                applied = Expr::let_e(Name::anonymous(), carrier, args[1].clone(), applied, false);
            }
            return Ok(Some(applied));
        }
        let payload = self.typed_callable_result(args[3].clone(), before.clone(), payload_type)?;
        let payload = if boxed_refinement {
            self.adapt_erased_field(&payload, &before, &after)?
        } else {
            payload
        };
        let bindings = if static_endpoints {
            vec![(after, payload)]
        } else {
            vec![
                (carrier.clone(), args[1].clone()),
                (after, payload),
                (carrier, args[4].clone()),
            ]
        };
        if bindings.len() > self.limits.max_context_depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: self.limits.max_context_depth,
                observed: bindings.len(),
            });
        }
        let depth = u32::try_from(bindings.len()).map_err(|_| unsupported("transport scope"))?;
        let mut value = Expr::bvar(if static_endpoints { 0 } else { 1 })
            .map_err(|_| unsupported("transport scope"))?;
        for argument in &args[6..] {
            self.tick()?;
            value = Expr::app(value, self.lift(argument, depth)?);
        }
        for (index, (type_, init)) in bindings.into_iter().enumerate().rev() {
            self.tick()?;
            let index = u32::try_from(index).map_err(|_| unsupported("transport scope"))?;
            value = Expr::let_e(
                Name::anonymous(),
                self.lift(&type_, index)?,
                self.lift(&init, index)?,
                value,
                false,
            );
        }
        Ok(Some(value))
    }
}

#[cfg(test)]
mod tests;
