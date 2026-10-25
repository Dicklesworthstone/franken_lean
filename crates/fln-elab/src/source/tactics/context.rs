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
        let (child, _) = self.generalized_proof_goal(proof, goal, name, equality, term)?;
        proof.work.push(Work::Goal(child));
        Ok(())
    }

    /// Return the fresh discriminant identity explicitly so elimination never
    /// has to recover it from a user name or consume a synthetic instruction.
    pub(super) fn generalized_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        name: Name,
        equality: Option<Name>,
        term: Typed,
    ) -> Result<(ProofGoal, FVarId), NatDefinitionElabError> {
        self.tick()?;
        if name.is_anonymous()
            || equality
                .as_ref()
                .is_some_and(|h| h.is_anonymous() || h == &name)
        {
            return Err(error(TacticError::InvalidGeneralization));
        }
        self.txn.lctx = goal.lctx.clone();
        // The pin elaborates the generalized term with `Tactic.elabTerm`, whose
        // `synthesizeSyntheticMVars (postpone := .no)` applies default instances:
        // `generalize 3 = x` generalizes `(3 : Nat)`.
        self.resolve_instances_with_defaults()?;
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
        self.inherit_goal_tag(&goal, &child);
        self.introduce_proof_binder(&mut child, name)?;
        let discriminant = child
            .introduced
            .last()
            .expect("generalized discriminant binder")
            .id
            .clone();
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
        Ok((child, discriminant))
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
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                self.trace_introduced_name(&id, &name, binder_name);
                goal.target = self.substitute(body, &Expr::fvar(id.clone()))?;
                self.txn
                    .lctx
                    .add_param(id.clone(), name, binder_type.clone(), *binder_info);
            }
            ExprNode::LetE {
                decl_name: binder_name,
                type_,
                value,
                body,
                ..
            } => {
                self.trace_introduced_name(&id, &name, binder_name);
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
        self.inherit_goal_tag(&goal, &child);
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

    /// `clear h₁ … hₙ` (`evalClear`, vendored src/Lean/Elab/Tactic/BuiltinTactic.lean): the
    /// named locals leave the goal, the latest first, as `MVarId.clear` removes each.
    pub(super) fn clear_proof_locals(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        let [keyword, names] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "clear", "clear keyword")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "clear"])?;
        let names = expect_null_args(names, "cleared names")?;
        if names.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        let mut removed = HashSet::new();
        for name in names {
            self.tick()?;
            let Syntax::Ident { val, .. } = name else {
                return Err(error(TacticError::MalformedScript));
            };
            // The pin elaborates each name to a free variable; a hidden recursion local is
            // not one the source can name, and naming a local twice clears a missing one.
            let local = goal
                .lctx
                .find_by_user_name(val)
                .filter(|local| !self.is_matrix_hypothesis(local))
                .ok_or_else(|| failure(SourceInferenceError::UnknownConstant(val.clone())))?;
            if !removed.insert(local.id.clone()) {
                return Err(failure(SourceInferenceError::UnknownConstant(val.clone())));
            }
        }
        if let Some(blocked) = self.clear_blocker(&goal, &removed)? {
            return Err(error(blocked));
        }
        self.push_cleared_goal(proof, goal, &removed)
    }

    /// The pin's `tryClear`: `local` leaves the goal unless something still reads it, in which
    /// case the goal is kept as it is.
    pub(super) fn try_clear_proof_local(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        local: FVarId,
    ) -> Result<(), NatDefinitionElabError> {
        let removed = HashSet::from([local]);
        if self.clear_blocker(&goal, &removed)?.is_some() {
            proof.work.push(Work::Goal(goal));
            return Ok(());
        }
        self.push_cleared_goal(proof, goal, &removed)
    }

    /// Why `removed` cannot leave the goal. `MVarId.clear` (vendored
    /// src/Lean/Meta/Tactic/Clear.lean), applied to the latest local first, refuses one that
    /// a remaining local reads (the first in context order) or that the target reads.
    pub(super) fn clear_blocker(
        &mut self,
        goal: &ProofGoal,
        removed: &HashSet<FVarId>,
    ) -> Result<Option<TacticError>, NatDefinitionElabError> {
        let mut reads = Vec::with_capacity(goal.lctx.len());
        for local in goal.lctx.decls() {
            self.tick()?;
            let mut read = self.elimination_reads(&local.type_)?;
            if let Some(value) = &local.value {
                read.extend(self.elimination_reads(value)?);
            }
            reads.push(read);
        }
        let target = self.elimination_reads(&goal.target)?;
        for cleared in goal.lctx.decls().iter().rev() {
            if !removed.contains(&cleared.id) {
                continue;
            }
            for (local, read) in goal.lctx.decls().iter().zip(&reads) {
                self.tick()?;
                if !removed.contains(&local.id) && read.contains(&cleared.id) {
                    return Ok(Some(TacticError::ClearDependency {
                        local: cleared.user_name.clone(),
                        dependent: Some(local.user_name.clone()),
                    }));
                }
            }
            if target.contains(&cleared.id) {
                return Ok(Some(TacticError::ClearDependency {
                    local: cleared.user_name.clone(),
                    dependent: None,
                }));
            }
        }
        Ok(None)
    }

    /// A fresh goal over the context without `removed`, which closes `goal`. Like the pin's
    /// new metavariable, it keeps the goal's tag.
    fn push_cleared_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        removed: &HashSet<FVarId>,
    ) -> Result<(), NatDefinitionElabError> {
        let child = self.cleared_proof_goal(proof, goal, removed)?;
        proof.work.push(Work::Goal(child));
        Ok(())
    }

    /// The pin's `tryClearMany`: of `candidates`, those nothing else in the goal reads leave
    /// it, the latest first. The goal that remains closes `goal`; it is returned unchanged
    /// when none can leave.
    pub(super) fn try_clear_proof_locals(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        candidates: &[FVarId],
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let mut removed = HashSet::new();
        for candidate in candidates.iter().rev() {
            self.tick()?;
            let mut trial = removed.clone();
            trial.insert(candidate.clone());
            if self.clear_blocker(&goal, &trial)?.is_none() {
                removed = trial;
            }
        }
        if removed.is_empty() {
            return Ok(goal);
        }
        self.cleared_proof_goal(proof, goal, &removed)
    }

    /// `goal` without `removed`, as a fresh goal that closes it; `removed` must be clearable
    /// ([`Self::clear_blocker`]).
    pub(super) fn cleared_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        removed: &HashSet<FVarId>,
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let mut retained = LocalContext::new();
        for local in goal.lctx.decls() {
            self.tick()?;
            if !removed.contains(&local.id) {
                eliminate::add_local(&mut retained, local);
            }
        }
        let target = self.instantiate(&goal.target)?;
        self.txn.lctx = retained;
        let (value, child) = self.proof_goal(target)?;
        self.inherit_goal_tag(&goal, &child);
        proof.work.push(Work::Close(goal, value));
        Ok(child)
    }

    /// `rename e => h` (`evalRename`, vendored src/Lean/Elab/Tactic/ElabTerm.lean:344-359): the
    /// last hypothesis, implementation details aside, whose type unifies with `e` at the ambient
    /// transparency (`findDeclRevM?`), the search's unifications undone
    /// (`withoutModifyingState`), is renamed `h` in a fresh goal that closes `goal`
    /// (`MVarId.rename`, vendored src/Lean/Meta/Tactic/Rename.lean).
    pub(super) fn rename_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        args: &[Syntax],
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let [keyword, pattern, arrow, Syntax::Ident { val: name, .. }] = args else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(keyword, "rename", "rename keyword")?;
        expect_atom(arrow, "=>", "rename arrow")?;
        self.require_declared_tactic(&["Lean", "Parser", "Tactic", "rename"])?;
        let snapshot = self.clone();
        let found = (|| {
            self.txn.lctx = goal.lctx.clone();
            let pattern = self.term(pattern, None)?;
            let pending = self.equations.len();
            for local in goal.lctx.decls().iter().rev() {
                self.tick()?;
                if self.is_matrix_hypothesis(local)
                    || (local.user_name.is_anonymous() && !self.unnamed_fields.contains(&local.id))
                {
                    continue;
                }
                // `isDefEq`, which synthesizes a pattern's pending instance once its type is
                // known (`synthPending`): `rename 1 = 1 => h` meets `@Eq Nat 1 1`.
                let candidate = self.clone();
                let matched = (|| {
                    self.constrain(&pattern.value, &local.type_)?;
                    self.resolve_instances(false)?;
                    self.flush(false)?;
                    Ok(self.equations.len() <= pending)
                })();
                match matched {
                    Ok(true) => return Ok(Some(local.id.clone())),
                    Ok(false) => {}
                    Err(problem) if backtrack::recoverable(&problem) => {}
                    Err(problem) => return Err(problem),
                }
                let spent = self.txn.budget.heartbeats_consumed;
                *self = candidate;
                self.txn.budget.heartbeats_consumed = spent;
            }
            Ok(None)
        })();
        let spent = self.txn.budget.heartbeats_consumed;
        *self = snapshot;
        self.txn.budget.heartbeats_consumed = spent;
        let id = found?.ok_or_else(|| error(TacticError::RenameNoHypothesis))?;
        let mut context = LocalContext::new();
        for local in goal.lctx.decls() {
            self.tick()?;
            let mut updated = local.clone();
            if local.id == id {
                updated.user_name = name.clone();
                self.trace_local_names.remove(&local.id);
                self.unnamed_fields.remove(&local.id);
            }
            eliminate::add_local(&mut context, &updated);
        }
        let target = self.instantiate(&goal.target)?;
        self.txn.lctx = context;
        let (value, child) = self.proof_goal(target)?;
        self.inherit_goal_tag(&goal, &child);
        proof.work.push(Work::Close(goal, value));
        Ok(child)
    }

    fn inherit_goal_tag(&mut self, parent: &ProofGoal, child: &ProofGoal) {
        if let Some(tag) = self.goal_tags.get(&parent.id).cloned() {
            self.goal_tags.insert(child.id.clone(), tag);
        }
    }

    /// `rename_i x₁ … xₙ` and `next x₁ … xₙ =>` (`renameInaccessibles`, vendored
    /// src/Lean/Elab/Tactic/RenameInaccessibles.lean): from the end of the context, each
    /// inaccessible or shadowed hypothesis takes the next name from the right, a `_` leaving
    /// it as it is. With no name at all the goal is returned unchanged; otherwise the renamed
    /// goal is a fresh one that closes `goal`. Names left over are refused, as the pin
    /// reports them.
    pub(super) fn renamed_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        names: &[Syntax],
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let mut pending = Vec::with_capacity(names.len());
        for name in names {
            self.tick()?;
            let [inner] = expect_node(
                name,
                &Name::from_components(["Lean", "binderIdent"]),
                1,
                "renamed hypothesis",
            )?
            else {
                return Err(error(TacticError::MalformedScript));
            };
            pending.push(match inner {
                Syntax::Ident { val, .. } => Some(val.clone()),
                hole if hole.kind() == Some(&parser_kind(&["Term", "hole"])) => None,
                _ => return Err(error(TacticError::MalformedScript)),
            });
        }
        if pending.iter().all(Option::is_none) {
            return Ok(goal);
        }
        let internal = Name::from_components(["_fln_source"]);
        let mut renamed = std::collections::HashMap::new();
        let mut later = HashSet::new();
        for local in goal.lctx.decls().iter().rev() {
            self.tick()?;
            // The pin skips implementation details. Here those are the hidden recursion
            // locals and the anonymous locals this engine binds for itself (a structure
            // instance's `with` source, a match discriminant); an unnamed elimination field is
            // the pin's inaccessible `n✝` instead.
            let unnamed_field = self.unnamed_fields.contains(&local.id);
            if self.is_matrix_hypothesis(local)
                || (local.user_name.is_anonymous() && !unnamed_field)
            {
                continue;
            }
            let inaccessible = unnamed_field
                || local.user_name.has_macro_scopes()
                || local.user_name.parent() == internal;
            if inaccessible || later.contains(&local.user_name) {
                if let Some(Some(name)) = pending.pop() {
                    renamed.insert(local.id.clone(), name);
                }
                if pending.is_empty() {
                    break;
                }
            }
            later.insert(local.user_name.clone());
        }
        if !pending.is_empty() {
            return Err(error(TacticError::RenameTooManyNames));
        }
        let mut context = LocalContext::new();
        for local in goal.lctx.decls() {
            self.tick()?;
            let mut updated = local.clone();
            if let Some(name) = renamed.get(&local.id) {
                updated.user_name = name.clone();
                // A trace shows the new name, not the hygienic one it replaced.
                self.trace_local_names.remove(&local.id);
            }
            eliminate::add_local(&mut context, &updated);
        }
        let target = self.instantiate(&goal.target)?;
        self.txn.lctx = context;
        let (value, child) = self.proof_goal(target)?;
        self.inherit_goal_tag(&goal, &child);
        proof.work.push(Work::Close(goal, value));
        Ok(child)
    }
}
