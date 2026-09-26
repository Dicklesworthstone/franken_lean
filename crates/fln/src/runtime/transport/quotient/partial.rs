//! Residual primitive functions keep source proof slots and strict captures.
//! Types are derived from the admitted primitive, not hand-written ABI guesses.
use super::*;

impl Preparation<'_> {
    fn quotient_residual_type(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Expr, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Err(unsupported("quotient residual head"));
        };
        let Some(ConstantInfo::Quot(info)) = self.environment.find(name) else {
            return Err(unsupported("quotient residual declaration"));
        };
        let mut type_ = self.universe_instance(&info.base.type_, &info.base.level_params, levels)?;
        for argument in args {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE { body, .. } = normal.node() else {
                return Err(unsupported("quotient residual telescope"));
            };
            type_ = self.substitution(body, argument)?;
        }
        self.erase_runtime_type(&type_)
    }

    pub(super) fn partial_quotient(
        &mut self,
        head: &Expr,
        args: &[Expr],
        constructor: bool,
        carrier: Expr,
    ) -> Result<Expr, IngressError> {
        let arity: usize = if constructor { 3 } else { 6 };
        let missing = arity
            .checked_sub(args.len())
            .filter(|&count| count != 0)
            .ok_or_else(|| unsupported("quotient residual arity"))?;
        let captured = usize::from(!constructor && args.len() >= 4);
        let type_ = self.quotient_residual_type(head, args)?;
        let mut remaining = type_.clone();
        let mut domains = Vec::new();
        for _ in 0..missing {
            self.tick()?;
            let normal = self.type_head(&remaining)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = normal.node()
            else {
                return Err(unsupported("quotient residual parameter"));
            };
            if binder_type.has_loose_bvars()
                || body.has_loose_bvars()
                || self.value_type(binder_type)?.is_none()
            {
                return Err(unsupported("quotient residual representation"));
            }
            reserve(&mut domains, self.limits.max_context_depth)?;
            domains.push((binder_name.clone(), binder_type.clone(), *binder_info));
            remaining = body.clone();
        }
        let result_value = self
            .value_type(&remaining)?
            .ok_or_else(|| unsupported("quotient residual result"))?;
        let depth = missing + captured + 1 + usize::from(matches!(result_value, ValueType::Closure(_)));
        if depth > self.limits.max_context_depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: self.limits.max_context_depth,
                observed: depth,
            });
        }
        let representative = Expr::bvar(0).map_err(|_| unsupported("quotient residual scope"))?;
        let mut value = if constructor {
            representative
        } else {
            // A supplied f lives outside every missing binder. Otherwise f
            // is the first missing binder, followed by the proof slot and q.
            let index = if captured != 0 { missing } else { missing - 1 };
            let index = u32::try_from(index).map_err(|_| unsupported("quotient residual scope"))?;
            Expr::app(
                Expr::bvar(index).map_err(|_| unsupported("quotient residual scope"))?,
                representative,
            )
        };
        for (name, domain, info) in domains.into_iter().rev() {
            self.tick()?;
            value = Expr::lam(name, domain, value, info);
        }
        value = self.annotate_callable_tail(&value, &type_)?;
        let interface = self
            .value_type(&type_)?
            .ok_or_else(|| unsupported("quotient residual interface"))?;
        value = self.typed_callable_result(value, type_, interface)?;
        if captured != 0 {
            let result = self.erase_runtime_type(&args[2])?;
            let function_type = Expr::forall_e(
                Name::anonymous(),
                carrier,
                self.lift(&result, 1)?,
                BinderInfo::Default,
            );
            let function = self.annotate_callable_tail(&args[3], &function_type)?;
            // Computing a partial lift computes f now, even when the residual
            // function is ignored. Only the later representative is deferred.
            value = Expr::let_e(Name::anonymous(), function_type, function, value, false);
        }
        Ok(value)
    }
}
