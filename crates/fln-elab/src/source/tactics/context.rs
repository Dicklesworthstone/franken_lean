//! Dependency-aware proof-context transformations. Reversion builds a new
//! telescope and applies its proof to the old locals; it never changes a local
//! variable's type or widens an existing metavariable's scope.
use super::*;
use std::collections::HashSet;

fn app<const N: usize>(head: Expr, arguments: [Expr; N]) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}

impl Context {
    /// Generalize exact elaborated occurrences in the goal, optionally keeping
    /// the equation `e = x`. The parent proof applies a fresh universal theorem
    /// to `e` and (when requested) `Eq.refl e`; no equality is assumed globally.
    pub(in crate::source) fn generalize_proof_term(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        name: Name,
        equality: Option<Name>,
        term: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.tick()?;
        if name.is_anonymous()
            || equality
                .as_ref()
                .is_some_and(|h| h.is_anonymous() || h == &name)
        {
            return Err(error(TacticError::InvalidGeneralization));
        }
        self.txn.lctx = goal.lctx.clone();
        self.resolve_instances(false)?;
        self.flush(false)?;
        let expression = self.instantiate(&term.value)?;
        let domain = self.instantiate(&term.type_)?;
        let target = self.instantiate(&goal.target)?;
        self.require_resolved(&[expression.clone(), domain.clone(), target.clone()])?;
        let marker = FVarId(self.fresh_name()?);
        let (mut target, _) =
            self.rewrite_template(&target, &expression, &Expr::fvar(marker.clone()))?;
        let mut reflexivity = None;
        if let Some(equality) = &equality {
            let sort = self
                .known_type(&domain)?
                .ok_or_else(|| failure(SourceInferenceError::ExpectedType))?;
            let level = self.sort_level(&Typed {
                value: domain.clone(),
                type_: sort,
            })?;
            let equation = app(
                Expr::const_(Name::from_components(["Eq"]), vec![level.clone()]),
                [
                    domain.clone(),
                    expression.clone(),
                    Expr::fvar(marker.clone()),
                ],
            );
            target = Expr::forall_e(equality.clone(), equation, target, BinderInfo::Default);
            reflexivity = Some(app(
                Expr::const_(Name::from_components(["Eq", "refl"]), vec![level]),
                [domain.clone(), expression.clone()],
            ));
        }
        target = Expr::forall_e(
            name.clone(),
            domain,
            target
                .abstract_fvar(&marker, 0)
                .map_err(|_| failure(SourceInferenceError::Scope))?,
            BinderInfo::Default,
        );
        // Generalizing an index can invalidate the types of untouched terms.
        // Validate the entire new telescope before a speculative branch may
        // commit. Type reconstruction merely proposes a sort; K1 checks it.
        let sort = self
            .known_type(&target)?
            .ok_or_else(|| error(TacticError::InvalidGeneralization))?;
        let check = self.hole(sort)?;
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::SafeDefinitions;
        let report = self
            .txn
            .unify(&check, &target, budget)
            .map_err(|reason| failure(SourceInferenceError::Unification(Box::new(reason))))?;
        assert!(report.awakened.is_empty(), "private source queue");
        let (root, mut child) = self.proof_goal(target.clone())?;
        self.introduce_proof_binder(&mut child, name)?;
        if let Some(equality) = equality {
            self.introduce_proof_binder(&mut child, equality)?;
        }
        child.lctx = self.txn.lctx.clone();
        let mut value = Expr::app(
            Expr::bvar(0).expect("generalized theorem binder"),
            expression,
        );
        if let Some(reflexivity) = reflexivity {
            value = Expr::app(value, reflexivity);
        }
        // Retain the universal theorem's asserted type in the final term.
        // Otherwise beta reduction of its immediate application could discard
        // an ill-typed generic proof that only works at the original argument.
        let value = Expr::let_e(self.fresh_name()?, target, root, value, false);
        proof.work.push(Work::Close(goal, value));
        proof.work.push(Work::Goal(child));
        Ok(())
    }

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
