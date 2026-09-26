//! Lower global function producers through the existing typed local-closure
//! path. Ordinary globals retain their flat ABI. A shorter executable lambda
//! spine is not eta-expanded across its strict, closure-producing body.
mod applications;
mod callbacks;

use super::*;

struct Binder {
    name: Name,
    domain: Expr,
    value: Expr,
}

fn variable(index: usize) -> Result<Expr, IngressError> {
    let index = u32::try_from(index).map_err(|_| unsupported("global producer scope"))?;
    Expr::bvar(index).map_err(|_| unsupported("global producer scope"))
}

impl Preparation<'_> {
    fn producer_depth(&mut self, depth: usize) -> Result<u32, IngressError> {
        self.tick()?;
        if depth > self.limits.max_context_depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: self.limits.max_context_depth,
                observed: depth,
            });
        }
        u32::try_from(depth).map_err(|_| unsupported("global producer depth"))
    }

    /// Keep the original outer lambda spine for the command's own annotation,
    /// but annotate a computed callback at the end of its strict let telescope.
    /// This also handles a zero-argument definition whose value is a let/call.
    pub(super) fn annotate_execution_value(
        &mut self,
        value: Expr,
        type_: Expr,
    ) -> Result<Expr, IngressError> {
        if matches!(value.node(), ExprNode::Lam { .. }) {
            return self.annotate_callable_tail(&value, &type_);
        }
        let Some(result @ ValueType::Closure(_)) = self.value_type(&type_)? else {
            return Ok(value);
        };
        self.typed_callable_result(value, type_, result)
    }

    /// Specialize known staged callbacks before considering a global producer.
    /// Only safe, ground definitions enter either path. No body is executed to
    /// find its type or its stage boundary. Copied bodies remain compiler input,
    /// never logical declarations or alternate admission authority.
    pub(super) fn global_producer(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        if let Some(specialized) = self.specialize_staged_callback(head, args)? {
            return Ok(Some(specialized));
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
        // Cheap syntactic exclusion avoids cloning/preparing an ordinary fully
        // lambda-bound function at every scalar call. Normalize the remaining
        // type only; never unfold the body to manufacture another lambda.
        let mut remaining = definition.base.type_.clone();
        let mut body = definition.value.clone();
        let mut prefix = 0usize;
        while let ExprNode::Lam { body: inner, .. } = body.node() {
            self.producer_depth(prefix.saturating_add(1))?;
            let normal = self.type_head(&remaining)?;
            let ExprNode::ForallE { body: result, .. } = normal.node() else {
                return Ok(None);
            };
            remaining = result.clone();
            body = inner.clone();
            prefix = prefix
                .checked_add(1)
                .ok_or_else(|| unsupported("global producer arity"))?;
        }
        let remaining = self.type_head(&remaining)?;
        if !matches!(remaining.node(), ExprNode::ForallE { .. }) {
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
        let definition = self.normalize_definition_signature(&definition)?;
        let mut type_ = definition.base.type_.clone();
        if !matches!(self.value_type(&type_)?, Some(ValueType::Closure(_))) {
            return Ok(None);
        }
        let mut value = definition.value;
        let mut bindings = Vec::new();
        let consumed = args.len().min(prefix);
        for argument in &args[..consumed] {
            self.tick()?;
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
            ) = (value.node(), type_.node())
            else {
                return Ok(None);
            };
            if binder_type != domain || domain.has_loose_bvars() || result.has_loose_bvars() {
                return Ok(None);
            }
            let offset = self.producer_depth(bindings.len())?;
            reserve(&mut bindings, self.limits.max_context_depth)?;
            bindings.push(Binder {
                name: binder_name.clone(),
                domain: domain.clone(),
                value: self.lift(argument, offset)?,
            });
            // Replacing each leading lambda with a let preserves its de Bruijn
            // slot. Runtime operands are not substituted, dropped or duplicated.
            value = body.clone();
            type_ = result.clone();
        }
        if args.len() <= prefix {
            let callback = self
                .value_type(&type_)?
                .ok_or_else(|| unsupported("global producer result representation"))?;
            value = self.typed_callable_result(value, type_, callback)?;
        } else {
            let Some(applied) =
                self.apply_producer(value, type_, &args[prefix..], bindings.len())?
            else {
                return Ok(None);
            };
            value = applied;
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
