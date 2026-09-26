//! Expose let-bound templates before runtime proof/type erasure. Only literal
//! lambdas are substitutable here: their captures are already evaluated values.
//! Initializers which compute a function retain their strict let and sharing.
use super::*;

impl Preparation<'_> {
    pub(super) fn local_callable_template(
        &mut self,
        value: &Expr,
        type_: &Expr,
    ) -> Result<Option<Expr>, IngressError> {
        let mut literal = value.clone();
        loop {
            self.tick()?;
            match literal.node() {
                ExprNode::MData { expr, .. } => literal = expr.clone(),
                ExprNode::Lam { .. } => break,
                _ => return Ok(None),
            }
        }
        let mut body = literal.clone();
        let mut type_ = self.type_head(type_)?;
        let mut depth = 0usize;
        loop {
            self.tick()?;
            if let ExprNode::MData { expr, .. } = body.node() {
                body = expr.clone();
                continue;
            }
            let (
                ExprNode::Lam { body: next, .. },
                ExprNode::ForallE {
                    binder_type,
                    body: result,
                    ..
                },
            ) = (body.node(), type_.node())
            else {
                // A real lambda followed by a strict function-producing body
                // must keep its stages when passed to a higher-order consumer.
                // A full ordinary lambda telescope stays a shared closure.
                return Ok(
                    (depth != 0 && matches!(type_.node(), ExprNode::ForallE { .. }))
                        .then_some(literal),
                );
            };
            depth = depth.saturating_add(1);
            if depth > self.limits.max_context_depth {
                return Err(IngressError::ResourceLimit {
                    resource: IngressResource::ContextDepth,
                    limit: self.limits.max_context_depth,
                    observed: depth,
                });
            }
            // Type and type-constructor parameters require specialization at
            // concrete uses, even after earlier runtime parameters. We inspect
            // only types; no instance computation or lambda body is evaluated.
            if self.type_parameter(binder_type)? {
                return Ok(Some(literal));
            }
            body = next.clone();
            type_ = self.type_head(result)?;
        }
    }
}

#[cfg(test)]
mod tests;
