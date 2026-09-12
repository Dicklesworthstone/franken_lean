//! Preserve the actual structural hypotheses across dependent matrix splits.
//!
//! A later discriminant can force the first child's type and hypothesis into
//! its generalized telescope. Private names survive that reconstruction; the
//! current local context, not a stale variable identity, determines scope.
//! Recursive calls are lowered while those locals are still open. Ordinary
//! proof and instance search never receive these compiler-only hypotheses.
use super::*;

impl Context {
    pub(in crate::source) fn is_matrix_hypothesis(&self, local: &LocalDecl) -> bool {
        self.recursion
            .as_ref()
            .is_some_and(|recursion| recursion.matrix_hidden.contains(&local.user_name))
    }

    pub(in crate::source) fn register_matrix_hypotheses(
        &mut self,
        locals: &mut Vec<LocalDecl>,
        hypotheses: &[(FVarId, FVarId)],
    ) -> Result<(), NatDefinitionElabError> {
        for (child, hypothesis) in hypotheses {
            self.tick()?;
            let name = self.fresh_name()?;
            let declaration = locals
                .iter_mut()
                .find(|local| &local.id == hypothesis)
                .ok_or_else(|| error(RecursionError::NotDecreasing))?;
            declaration.user_name = name.clone();
            declaration.index = self.txn.lctx.len();
            crate::source::tactics::eliminate::add_local(&mut self.txn.lctx, declaration);
            let child = self
                .txn
                .lctx
                .find(child)
                .cloned()
                .ok_or_else(|| error(RecursionError::NotDecreasing))?;
            let alias_name = self.fresh_name()?;
            let alias = LocalDecl {
                id: FVarId(alias_name.clone()),
                user_name: alias_name.clone(),
                type_: child.type_,
                value: Some(Expr::fvar(child.id)),
                binder_info: BinderInfo::Default,
                index: self.txn.lctx.len(),
            };
            crate::source::tactics::eliminate::add_local(&mut self.txn.lctx, &alias);
            locals.push(alias);
            let recursion = self.recursion.as_mut().expect("recursive matrix branch");
            recursion.matrix_hidden.insert(name.clone());
            recursion.matrix_hypotheses.push((alias_name, name));
        }
        Ok(())
    }

    /// Only complete source applications whose structural argument is already
    /// present are lowered here. Escaping bare markers remain subject to the
    /// final whole-branch traversal, including unused values and annotations.
    pub(in crate::source) fn lower_matrix_call(
        &mut self,
        value: &Expr,
    ) -> Result<Expr, NatDefinitionElabError> {
        let Some(recursion) = self.recursion.as_ref().filter(|r| r.matrix && !r.pending) else {
            return Ok(value.clone());
        };
        if recursion.matrix_hypotheses.is_empty() || !value.has_fvar() {
            return Ok(value.clone());
        }
        let marker = recursion.marker.clone();
        let decreasing = recursion.decreasing;
        let mut head = value;
        let mut arguments = Vec::new();
        while let ExprNode::App { f, a } = head.node() {
            self.tick()?;
            arguments.push(a.clone());
            head = f;
        }
        if !matches!(head.node(), ExprNode::FVar { id } if id == &marker)
            || arguments.len() <= decreasing
        {
            return Ok(value.clone());
        }
        let pairs = self
            .recursion
            .as_ref()
            .expect("recursive matrix")
            .matrix_hypotheses
            .clone();
        let mut hypotheses = Vec::new();
        for (child, hypothesis) in pairs {
            self.tick()?;
            let Some(child) = self.txn.lctx.find_by_user_name(&child).cloned() else {
                continue;
            };
            let Some(hypothesis) = self.txn.lctx.find_by_user_name(&hypothesis).cloned() else {
                continue;
            };
            let child = self.recursive_alias_value(&Expr::fvar(child.id))?;
            if let ExprNode::FVar { id } = child.node() {
                hypotheses.push((id.clone(), hypothesis.id));
            }
        }
        if hypotheses.is_empty() {
            return Ok(value.clone());
        }
        arguments.reverse();
        let mut application = Expr::fvar(marker);
        for argument in arguments {
            self.tick()?;
            let argument = self.instantiate(&argument)?;
            application = Expr::app(application, self.recursive_alias_value(&argument)?);
        }
        self.lower_recursive_calls(&application, &hypotheses)
    }
}
