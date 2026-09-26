//! Quotient representatives use their carrier's runtime representation. This
//! is post-admission erasure, not quotient normalization in either checker.
//! Respectfulness evidence is checked before this pass and never executed.
use super::*;

impl Preparation<'_> {
    fn check_quotient_family(&mut self) -> Result<(), IngressError> {
        let Declaration::Quotient(expected) = fln_elab::seed::quotient_seed_declaration() else {
            return Err(unsupported("quotient seed"));
        };
        for expected in expected {
            self.tick()?;
            if !matches!(self.environment.find(&expected.base.name),
                Some(ConstantInfo::Quot(actual)) if actual == &expected)
            {
                return Err(unsupported("noncanonical quotient family"));
            }
        }
        Ok(())
    }

    /// Called by the existing heap-backed type-erasure worklist. Return the
    /// carrier as another work item, rather than recursively discovering its
    /// representation here. The relation is static metadata, never traversed.
    pub(in crate::runtime) fn quotient_carrier(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if !matches!(head.node(), ExprNode::Const { name: n, levels }
            if n == &name("Quot") && levels.len() == 1)
            || args.len() != 2
        {
            return Ok(None);
        }
        self.check_quotient_family()?;
        Ok(Some(args[0].clone()))
    }

    /// Fully supplied primitives retain the ordinary evaluation order of
    /// runtime operands. In particular, the function is computed before the
    /// representative, and neither is substituted, duplicated or discarded.
    /// Unsupplied static parameters and proof-only primitives are not values.
    pub(super) fn quotient_operation(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name: n, levels } = head.node() else {
            return Ok(None);
        };
        let constructor = n == &name("Quot.mk") && levels.len() == 1 && args.len() == 3;
        let lift = n == &name("Quot.lift") && levels.len() == 2 && args.len() == 6;
        if !constructor && !lift {
            return Ok(None);
        }
        self.check_quotient_family()?;
        let carrier = self.erase_runtime_type(&args[0])?;
        let carrier_value = self
            .value_type(&carrier)?
            .ok_or_else(|| unsupported("quotient carrier representation"))?;
        if constructor {
            return self
                .typed_callable_result(args[2].clone(), carrier, carrier_value)
                .map(Some);
        }
        let result = self.erase_runtime_type(&args[2])?;
        let result_value = self
            .value_type(&result)?
            .ok_or_else(|| unsupported("quotient result representation"))?;
        if carrier.has_loose_bvars() || result.has_loose_bvars() {
            return Err(unsupported("dependent quotient representation"));
        }
        let depth = 2 + usize::from(matches!(result_value, ValueType::Closure(_)));
        if self.limits.max_context_depth < depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: self.limits.max_context_depth,
                observed: depth,
            });
        }
        let function_type = Expr::forall_e(
            Name::anonymous(),
            carrier.clone(),
            self.lift(&result, 1)?,
            BinderInfo::Default,
        );
        let function = self.annotate_callable_tail(&args[3], &function_type)?;
        let representative = self.lift(&args[5], 1)?;
        let function_ref = Expr::bvar(1).map_err(|_| unsupported("quotient function scope"))?;
        let value_ref = Expr::bvar(0).map_err(|_| unsupported("quotient value scope"))?;
        let applied = self.typed_callable_result(
            Expr::app(function_ref, value_ref),
            result,
            result_value,
        )?;
        let body = Expr::let_e(Name::anonymous(), carrier, representative, applied, false);
        Ok(Some(Expr::let_e(
            Name::anonymous(),
            function_type,
            function,
            body,
            false,
        )))
    }
}

#[cfg(test)]
mod tests;
