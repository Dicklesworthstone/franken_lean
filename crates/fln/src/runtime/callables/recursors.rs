//! First-class recursors with a supplied static parameter/motive prefix.
//!
//! This is post-admission calling-form elaboration, not a new recursor engine.
//! The generated body saturates the original recursor and must pass the same
//! family-specific lowering, closure conversion and FIR/FLBC validators as a
//! direct call. A declaration, motive or runtime layout is never guessed.
use super::*;

// Literal lambdas have no initializer action. Keeping their syntax also lets
// the ordinary recursor lowering recognize an unused induction hypothesis.
// All other supplied runtime arguments are evaluated once, in source order,
// before returning the closure. A call returning a lambda is not a literal.
enum Argument {
    Inline(Expr),
    Capture(usize),
}

fn variable(index: usize) -> Result<Expr, IngressError> {
    let index = u32::try_from(index).map_err(|_| unsupported("partial recursor scope"))?;
    Expr::bvar(index).map_err(|_| unsupported("partial recursor scope"))
}

impl Preparation<'_> {
    pub(super) fn partially_applied_recursor(
        &mut self,
        head: &Expr,
        args: &[Expr],
    ) -> Result<Option<Expr>, IngressError> {
        let ExprNode::Const { name, levels } = head.node() else {
            return Ok(None);
        };
        let Some(ConstantInfo::Rec(rec)) = self.environment.find(name) else {
            return Ok(None);
        };
        if rec.is_unsafe
            || rec.num_motives == 0
            || rec.all.is_empty()
            || levels.len() != rec.base.level_params.len()
            || levels
                .iter()
                .any(|level| level.has_mvar() || level.has_param())
        {
            return Ok(None);
        }
        let prefix = (rec.num_params as usize)
            .checked_add(rec.num_motives as usize)
            .ok_or_else(|| unsupported("partial recursor arity"))?;
        let arity = prefix
            .checked_add(rec.num_minors as usize)
            .and_then(|n| n.checked_add(rec.num_indices as usize))
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| unsupported("partial recursor arity"))?;
        // A runtime closure cannot invent the type parameters or the motive
        // which determine its representation. Fully applied calls stay on the
        // existing path; this strict inequality also prevents rewrite loops.
        if args.len() < prefix || args.len() >= arity {
            return Ok(None);
        }
        if arity > self.limits.max_application_args {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ApplicationArguments,
                limit: self.limits.max_application_args,
                observed: arity,
            });
        }
        let mut type_ = self.universe_instance(&rec.base.type_, &rec.base.level_params, levels)?;
        let mut arguments = Vec::new();
        let mut captures = Vec::new();
        for (index, argument) in args.iter().enumerate() {
            self.tick()?;
            let normal = self.type_head(&type_)?;
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                ..
            } = normal.node()
            else {
                return Ok(None);
            };
            let value = if index < prefix {
                Argument::Inline(argument.clone())
            } else {
                let domain = self.erase_runtime_type(binder_type)?;
                if domain.has_loose_bvars() || self.value_type(&domain)?.is_none() {
                    return Ok(None);
                }
                if matches!(argument.node(), ExprNode::Lam { .. }) {
                    Argument::Inline(argument.clone())
                } else {
                    reserve(&mut captures, self.limits.max_context_depth)?;
                    let id = captures.len();
                    captures.push((binder_name.clone(), domain, argument.clone()));
                    Argument::Capture(id)
                }
            };
            reserve(&mut arguments, self.limits.max_application_args)?;
            arguments.push(value);
            // Recover the next logical domain from the real argument. No
            // dummy scalar may determine a dependent layout or callback type.
            type_ = self.substitution(body, argument)?;
        }
        let missing = arity - args.len();
        let depth = captures
            .len()
            .checked_add(missing)
            .ok_or_else(|| unsupported("partial recursor depth"))?;
        // Charge the combined generated context before discovering its callable
        // graph or allocating its missing-binder telescope, not each half alone.
        if depth > self.limits.max_context_depth {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::ContextDepth,
                limit: self.limits.max_context_depth,
                observed: depth,
            });
        }
        let callback_type = self.erase_runtime_type(&type_)?;
        if !matches!(
            self.value_type(&callback_type)?,
            Some(ValueType::Closure(_))
        ) {
            return Ok(None);
        }
        let mut binders = Vec::new();
        let mut remaining = callback_type.clone();
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
                return Ok(None);
            };
            // Index dependence may disappear under the checked uniform-layout
            // erasure. Dependence which survives it is not a callable interface.
            if binder_type.has_loose_bvars()
                || body.has_loose_bvars()
                || self.value_type(binder_type)?.is_none()
            {
                return Ok(None);
            }
            reserve(&mut binders, self.limits.max_context_depth)?;
            binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
            remaining = body.clone();
        }
        let lift = u32::try_from(depth).map_err(|_| unsupported("partial recursor depth"))?;
        let mut value = head.clone();
        for argument in arguments {
            self.tick()?;
            let argument = match argument {
                Argument::Inline(expr) => self.lift(&expr, lift)?,
                Argument::Capture(index) => variable(depth - index - 1)?,
            };
            value = Expr::app(value, argument);
        }
        for index in (0..missing).rev() {
            self.tick()?;
            value = Expr::app(value, variable(index)?);
        }
        // Only missing recursor arguments become lambda binders. In particular
        // do not eta-expand across an eliminator's function-valued result and
        // postpone work which belongs to that return stage.
        for (name, domain, info) in binders.into_iter().rev() {
            self.tick()?;
            value = Expr::lam(name, domain, value, info);
        }
        let capture_depth = u32::try_from(captures.len())
            .map_err(|_| unsupported("partial recursor capture depth"))?;
        let mut result = Expr::let_e(
            Name::anonymous(),
            self.lift(&callback_type, capture_depth)?,
            value,
            variable(0)?,
            false,
        );
        for (index, (name, domain, argument)) in captures.into_iter().enumerate().rev() {
            self.tick()?;
            let offset =
                u32::try_from(index).map_err(|_| unsupported("partial recursor capture depth"))?;
            result = Expr::let_e(
                name,
                self.lift(&domain, offset)?,
                self.lift(&argument, offset)?,
                result,
                false,
            );
        }
        Ok(Some(result))
    }
}

#[cfg(test)]
mod tests;
