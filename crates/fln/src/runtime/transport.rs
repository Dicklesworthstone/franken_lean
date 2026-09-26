//! Equality transport after admission. A cast may disappear only when both
//! logical endpoints erase to the same executable type. No proof is executed,
//! and ordinary endpoint/payload evaluation is retained in source order.
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
        let Declaration::Inductive(block) = fln_elab::seed::eq_seed_declaration() else {
            return Err(unsupported("equality seed"));
        };
        for expected in &block.types {
            self.tick()?;
            if !matches!(self.environment.find(&expected.base.name),
                Some(ConstantInfo::Induct(actual)) if actual == expected)
            {
                return Err(unsupported("noncanonical equality family"));
            }
        }
        for expected in &block.ctors {
            self.tick()?;
            if !matches!(self.environment.find(&expected.base.name),
                Some(ConstantInfo::Ctor(actual)) if actual == expected)
            {
                return Err(unsupported("noncanonical equality constructor"));
            }
        }
        for expected in &block.recursors {
            self.tick()?;
            if !matches!(self.environment.find(&expected.base.name),
                Some(ConstantInfo::Rec(actual)) if actual == expected)
            {
                return Err(unsupported("noncanonical equality recursor"));
            }
        }
        self.equality_family_checked = true;
        Ok(())
    }

    pub(super) fn equality_transport(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        // Quotient construction/elimination is another post-admission
        // representation transport. Keep it before ordinary callable ingress.
        if let Some(value) = self.quotient_operation(head, args)? {
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
        let after = self.erase_runtime_type(&after)?;
        if before != after {
            return Err(unsupported("representation-dependent equality transport"));
        }
        let result = self
            .value_type(&after)?
            .ok_or_else(|| unsupported("equality transport result representation"))?;
        let carrier = self.erase_runtime_type(&args[0])?;
        let static_endpoints = self.type_parameter(&carrier)?;
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
        if matches!(args[3].node(), ExprNode::Lam { .. }) && args.len() - 6 >= arity {
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
        let payload = self.typed_callable_result(args[3].clone(), after.clone(), result)?;
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