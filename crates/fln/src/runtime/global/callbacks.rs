//! Specialize a known staged callback at a checked call site rather than cast
//! it to a flat ABI. Literal lambdas are values: only their syntax is copied.
//! Every other supplied operand keeps one strict binding in source order.
use super::*;

fn literal_lambda(expr: &Expr) -> Option<&Expr> {
    matches!(expr.node(), ExprNode::Lam { .. }).then_some(expr)
}

impl Preparation<'_> {
    fn staged_callback(&mut self, input: &Expr, type_: &Expr) -> Result<bool, IngressError> {
        let Some(mut value) = literal_lambda(input) else {
            return Ok(false);
        };
        let mut type_ = self.normalize_type(type_)?;
        let mut depth = 0usize;
        loop {
            self.tick()?;
            if let ExprNode::MData { expr, .. } = value.node() {
                value = expr;
                continue;
            }
            let (ExprNode::Lam { body, .. }, ExprNode::ForallE { body: result, .. }) =
                (value.node(), type_.node())
            else {
                return Ok(depth != 0 && matches!(type_.node(), ExprNode::ForallE { .. }));
            };
            depth = depth.saturating_add(1);
            self.producer_depth(depth)?;
            value = body;
            type_ = result.clone();
        }
    }

    /// This is a bounded higher-order specialization, not a general closure
    /// conversion between different interfaces. An opaque/dynamic callback is
    /// never reinterpreted, and a strict callback-producing operand is not
    /// treated as an inert lambda. The normal FIR checker still sees every call.
    pub(super) fn specialize_staged_callback(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if args.is_empty() {
            return Ok(None);
        }
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let definition = match self.environment.find(name) {
            Some(ConstantInfo::Defn(definition))
                if definition.safety == DefinitionSafety::Safe =>
            {
                Some(definition.clone())
            }
            Some(_) => None,
            None => self.specialized_definition(name),
        };
        let Some(mut definition) = definition else {
            return Ok(None);
        };
        if definition.base.level_params.len() != levels.len()
            || levels.iter().any(|level| level.has_mvar() || level.has_param())
        {
            return Ok(None);
        }
        if args.len() > self.limits.max_application_args {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ApplicationArguments,
                limit: self.limits.max_application_args,
                observed: args.len(),
            });
        }
        let mut literal = false;
        for argument in args {
            self.tick()?;
            if literal_lambda(argument).is_some() {
                literal = true;
                break;
            }
        }
        if !literal {
            return Ok(None);
        }
        definition.base.type_ = self.universe_instance(
            &definition.base.type_,
            &definition.base.level_params,
            levels,
        )?;
        definition.value = self.universe_instance(
            &definition.value,
            &definition.base.level_params,
            levels,
        )?;
        definition.base.level_params.clear();
        // Detect against original source types first. Ordinary flat callbacks
        // keep the existing catalog path and need no body/layout preparation.
        let mut type_ = definition.base.type_.clone();
        let mut value = definition.value.clone();
        let mut selected = false;
        for argument in args {
            self.tick()?;
            while let ExprNode::MData { expr, .. } = value.node() {
                self.tick()?;
                value = expr.clone();
            }
            let normal = self.type_head(&type_)?;
            let (
                ExprNode::Lam { body: next, .. },
                ExprNode::ForallE {
                    binder_type, body, ..
                },
            ) = (value.node(), normal.node())
            else {
                break;
            };
            selected |= self.staged_callback(argument, binder_type)?;
            type_ = self.substitution(body, argument)?;
            value = next.clone();
        }
        if !selected {
            return Ok(None);
        }
        let definition = self.normalize_definition_signature(&definition)?;
        self.inline_callback_arguments(definition, args)
    }

    fn inline_callback_arguments(
        &mut self,
        definition: DefinitionVal,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let mut value = definition.value;
        let mut type_ = definition.base.type_;
        let mut bindings = Vec::new();
        let mut consumed = 0;
        for argument in args {
            self.tick()?;
            while let ExprNode::MData { expr, .. } = value.node() {
                self.tick()?;
                value = expr.clone();
            }
            let normal = self.type_head(&type_)?;
            let (
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    ..
                },
                ExprNode::ForallE {
                    binder_type: domain,
                    body: result,
                    ..
                },
            ) = (value.node(), normal.node())
            else {
                break;
            };
            // No representation is guessed for a genuinely dependent runtime
            // parameter or a type argument not handled by monomorphization.
            if self.normalize_type(binder_type)? != self.normalize_type(domain)?
                || domain.has_loose_bvars()
                || result.has_loose_bvars()
                || self.value_type(domain)?.is_none()
            {
                return Ok(None);
            }
            let offset = self.producer_depth(bindings.len())?;
            let argument = self.lift(argument, offset)?;
            if let Some(lambda) = literal_lambda(&argument) {
                // Captures already name runtime values, not initializer code.
                // The charged capture-avoiding substitution adjusts both the
                // removed parameter and all retained strict argument slots.
                value = self.substitution(body, lambda)?;
                type_ = self.substitution(result, lambda)?;
            } else {
                self.producer_depth(bindings.len().saturating_add(1))?;
                reserve(&mut bindings, self.limits.max_context_depth)?;
                bindings.push(Binder {
                    name: binder_name.clone(),
                    domain: domain.clone(),
                    value: argument,
                });
                value = body.clone();
                type_ = result.clone();
            }
            consumed += 1;
        }
        if consumed < args.len() {
            let Some(applied) =
                self.apply_producer(value, type_, &args[consumed..], bindings.len())?
            else {
                return Ok(None);
            };
            value = applied;
        } else {
            value = self.annotate_execution_value(value, type_.clone())?;
            let Some(result) = self.value_type(&type_)? else {
                return Ok(None);
            };
            // A partially applied consumer still needs the actual remaining
            // lambda registered as a value, inside the retained arguments.
            value = self.typed_callable_result(value, type_, result)?;
        }
        for binding in bindings.into_iter().rev() {
            self.tick()?;
            value = Expr::let_e(binding.name, binding.domain, binding.value, value, false);
        }
        Ok(Some(value))
    }
}

#[cfg(test)]
mod tests;
