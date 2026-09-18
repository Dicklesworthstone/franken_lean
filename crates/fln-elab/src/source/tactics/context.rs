//! Dependency-aware proof-context transformations. Reversion builds a new
//! telescope and applies its proof to the old locals; it never changes a local
//! variable's type or widens an existing metavariable's scope.
use super::*;
use std::collections::HashSet;

impl Context {
    /// Preserve a visible let binder before weak-head normalization erases it.
    /// Reintroduced lets retain their values in both the context and final proof.
    pub(super) fn introduce_proof_binder(
        &mut self,
        goal: &mut ProofGoal,
        name: Name,
    ) -> Result<(), NatDefinitionElabError> {
        let mut target = self.instantiate(&goal.target)?;
        while let ExprNode::MData { expr, .. } = target.node() {
            self.tick()?;
            target = expr.clone();
        }
        if !matches!(target.node(), ExprNode::LetE { .. }) {
            target = self.whnf(&target)?;
        }
        let id = FVarId(self.fresh_name()?);
        match target.node() {
            ExprNode::ForallE {
                binder_type,
                body,
                binder_info,
                ..
            } => {
                goal.target = self.substitute(body, &Expr::fvar(id.clone()))?;
                self.txn
                    .lctx
                    .add_param(id.clone(), name, binder_type.clone(), *binder_info);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                goal.target = self.substitute(body, &Expr::fvar(id.clone()))?;
                self.txn
                    .lctx
                    .add_let(id.clone(), name, type_.clone(), value.clone());
            }
            _ => return Err(failure(SourceInferenceError::ExpectedFunction)),
        }
        goal.introduced
            .push(self.txn.lctx.find(&id).expect("introduced local").clone());
        Ok(())
    }

    pub(super) fn revert_proof_locals(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, names] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "revert", "revert keyword")?;
        let names = expect_null_args(names, "revert names")?;
        if names.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        self.txn.lctx = goal.lctx.clone();
        self.flush(false)?;
        let mut removed = HashSet::new();
        for name in names {
            self.tick()?;
            let Syntax::Ident { val, .. } = name else {
                return Err(error(TacticError::MalformedScript));
            };
            let local = goal
                .lctx
                .find_by_user_name(val)
                .ok_or_else(|| error(TacticError::InvalidGeneralization))?;
            if self.is_matrix_hypothesis(local) || !removed.insert(local.id.clone()) {
                return Err(error(TacticError::InvalidGeneralization));
            }
        }
        // Types AND let values contribute forward dependencies. Context order
        // is already topological, so one charged pass computes the whole cone.
        let mut reverted = Vec::new();
        let mut retained = LocalContext::new();
        for local in goal.lctx.decls() {
            self.tick()?;
            let mut reads = self.elimination_reads(&local.type_)?;
            if let Some(value) = &local.value {
                reads.extend(self.elimination_reads(value)?);
            }
            if removed.contains(&local.id) || !reads.is_disjoint(&removed) {
                removed.insert(local.id.clone());
                reverted.push(local.clone());
            } else {
                eliminate::add_local(&mut retained, local);
            }
        }
        let mut target = self.instantiate(&goal.target)?;
        for local in reverted.iter().rev() {
            self.tick()?;
            target = target
                .abstract_fvar(&local.id, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?;
            let domain = self.instantiate(&local.type_)?;
            target = if let Some(value) = &local.value {
                Expr::let_e(
                    local.user_name.clone(),
                    domain,
                    self.instantiate(value)?,
                    target,
                    false,
                )
            } else {
                Expr::forall_e(local.user_name.clone(), domain, target, local.binder_info)
            };
        }
        self.txn.lctx = retained;
        let (mut value, child) = self.proof_goal(target)?;
        for local in reverted {
            self.tick()?;
            if local.value.is_none() {
                value = Expr::app(value, Expr::fvar(local.id));
            }
        }
        // Delaying the parent closure preserves earlier `intro`/`have` frames
        // and makes failure inside `first`/`try` use the ordinary rollback path.
        proof.work.push(Work::Close(goal, value));
        proof.work.push(Work::Goal(child));
        Ok(())
    }
}
