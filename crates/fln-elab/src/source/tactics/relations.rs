//! Relation tactics construct ordinary checked terms. The original goal is
//! closed only after every generated goal has a proof, so introduced binders
//! are never abstracted around an unresolved child metavariable.

use super::*;
use crate::symm::{SymmLemma, SymmRegistryError};
mod index;

pub(super) enum RelationTactic {
    Symmetry,
    Congruence,
    FunctionExtensionality,
}

pub(super) fn classify(kind: &Name) -> Option<RelationTactic> {
    if kind == &parser_kind(&["Tactic", "symm"]) {
        Some(RelationTactic::Symmetry)
    } else if kind == &parser_kind(&["Tactic", "congr"]) {
        Some(RelationTactic::Congruence)
    } else if kind == &Name::from_components(["tacticFunext___"]) {
        Some(RelationTactic::FunctionExtensionality)
    } else {
        None
    }
}

impl Context {
    pub(super) fn relation_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        tactic: RelationTactic,
        args: &[Syntax],
    ) -> Result<(), NatDefinitionElabError> {
        match tactic {
            RelationTactic::FunctionExtensionality => self.funext_proof_goal(proof, goal, args),
            RelationTactic::Congruence => self.congruence_proof_goal(proof, goal, args),
            RelationTactic::Symmetry => {
                let [keyword, location] = args else {
                    return Err(error(TacticError::MalformedScript));
                };
                expect_atom(keyword, "symm", "symmetry tactic")?;
                self.symmetrize_at_locations(proof, goal, location)
            }
        }
    }

    fn symmetrize_at_locations(
        &mut self,
        proof: &mut ProofState<'_>,
        mut goal: ProofGoal,
        location: &Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let Some(locations) = self.rewrite_locations(location)? else {
            let child = self.symmetrize_location(proof, goal, None)?;
            proof.work.push(Work::Goal(child));
            return Ok(());
        };
        if locations.all {
            // Lean.Elab.Tactic.withLocation tries the target first, then the
            // original hypotheses in reverse context order. Each failed
            // location is transactional; resource stops are never a nonmatch.
            // Retain identities, including shadowed and inaccessible locals:
            // spelling-based lookup could skip one or transform another twice.
            let hypotheses: Vec<_> = goal
                .lctx
                .decls()
                .iter()
                .filter(|local| !self.is_matrix_hypothesis(local))
                .map(|local| local.id.clone())
                .collect();
            let mut changed = false;
            for id in std::iter::once(None).chain(hypotheses.iter().rev().map(Some)) {
                self.tick()?;
                self.txn.lctx = goal.lctx.clone();
                let mut trial = self.rewrite_trial();
                let mut trial_proof = proof.clone();
                match trial.symmetrize_location(&mut trial_proof, goal.clone(), id) {
                    Ok(child) => {
                        *self = trial;
                        *proof = trial_proof;
                        goal = child;
                        changed = true;
                    }
                    Err(problem) if backtrack::recoverable(&problem) => {
                        self.charge_rewrite_trial(&trial);
                    }
                    Err(problem) => return Err(problem),
                }
            }
            if !changed {
                return Err(error(TacticError::ExpectedEquality));
            }
        } else {
            for name in &locations.hypotheses {
                let id = goal
                    .lctx
                    .find_by_user_name(name)
                    .ok_or_else(|| error(TacticError::RewriteLocation))?
                    .id
                    .clone();
                goal = self.symmetrize_location(proof, goal, Some(&id))?;
            }
            if locations.target {
                goal = self.symmetrize_location(proof, goal, None)?;
            }
        }
        proof.work.push(Work::Goal(goal));
        Ok(())
    }

    /// Apply the first matching registered symmetry lemma. Replacing a
    /// hypothesis preserves any old identity still read by its dependents.
    fn symmetrize_location(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        id: Option<&FVarId>,
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.flush(false)?;
        let local = id
            .map(|id| {
                goal.lctx
                    .find(id)
                    .cloned()
                    .ok_or_else(|| error(TacticError::RewriteLocation))
            })
            .transpose()?;
        let mut target =
            self.instantiate(local.as_ref().map_or(&goal.target, |local| &local.type_))?;
        if local.is_none() {
            while let ExprNode::MData { expr, .. } = target.node() {
                target = expr.clone();
            }
        }
        let candidates = self.symmetry_candidates(&target)?;
        if candidates.is_empty() {
            // The minimal native seed predates the source Eq.symm declaration
            // and has always supported symmetry through Eq.rec. Full source
            // and imported worlds use their actual registration journal. A
            // failed real rule must never fall back to this compatibility seam.
            if !self
                .txn
                .env
                .contains(&Name::from_components(["Eq", "symm"]))
            {
                return self.symmetrize_seed_equality(proof, goal, local.as_ref());
            }
            return Err(error(TacticError::ExpectedEquality));
        }
        for candidate in candidates {
            self.tick()?;
            let mut trial = self.rewrite_trial();
            let mut trial_proof = proof.clone();
            match trial.apply_symmetry_lemma(
                &mut trial_proof,
                goal.clone(),
                local.as_ref(),
                &candidate,
            ) {
                Ok(child) => {
                    *self = trial;
                    *proof = trial_proof;
                    return Ok(child);
                }
                Err(problem) if backtrack::recoverable(&problem) => {
                    self.charge_rewrite_trial(&trial)
                }
                Err(problem) => return Err(problem),
            }
        }
        Err(error(TacticError::ExpectedEquality))
    }

    /// `forallMetaTelescopeReducing`: all binders become ordinary assignable
    /// metavariables. In particular this does not silently synthesize or drop
    /// additional premises the last symmetry argument depends on.
    fn symmetry_telescope(
        &mut self,
        name: &Name,
    ) -> Result<(Typed, Vec<Expr>), NatDefinitionElabError> {
        let mut term = self.constant(name)?;
        let mut arguments = Vec::new();
        loop {
            self.tick()?;
            if !matches!(term.type_.node(), ExprNode::ForallE { .. }) {
                let reduced = self.whnf_with_transparency(
                    &term.type_,
                    UnificationTransparency::Abbreviations,
                    true,
                )?;
                if !matches!(reduced.node(), ExprNode::ForallE { .. }) {
                    break;
                }
                term.type_ = reduced;
            }
            let ExprNode::ForallE {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = term.type_.node()
            else {
                break;
            };
            let body = body.clone();
            let domain = binder_type.clone();
            let binder_name = binder_name.clone();
            let kind = if *binder_info == BinderInfo::InstImplicit {
                MetavarKind::Synthetic
            } else {
                MetavarKind::Natural
            };
            let id = MVarId(self.fresh_name()?);
            self.txn.mvars.declare(
                id.clone(),
                binder_name,
                domain,
                self.txn.lctx.clone(),
                kind,
                0,
                None,
            );
            let argument = Expr::mvar(id);
            term.type_ = self.substitute(&body, &argument)?;
            term.value = Expr::app(term.value, argument.clone());
            arguments.push(argument);
        }
        if arguments.is_empty() {
            return Err(failure(SourceInferenceError::Symm(
                SymmRegistryError::InvalidLemma(name.clone()),
            )));
        }
        Ok((term, arguments))
    }

    /// The attribute's actual semantic validation and captured insertion path.
    /// The pin checks a nonempty telescope and binary conclusion; whether the
    /// last premise is the converse is decided by ordinary application at use.
    pub(in crate::source) fn symm_lemma(
        &mut self,
        name: &Name,
    ) -> Result<SymmLemma, NatDefinitionElabError> {
        let (term, _) = self.symmetry_telescope(name)?;
        let target = self.meta_reduce_ambient(&term.type_, reduce::ReduceConfig::default())?;
        let relation = symmetry_relation(&target).ok_or_else(|| {
            failure(SourceInferenceError::Symm(SymmRegistryError::InvalidLemma(
                name.clone(),
            )))
        })?;
        Ok(SymmLemma {
            declaration: name.clone(),
            keys: self.symm_path(&relation, true)?,
        })
    }

    fn symmetry_candidates(
        &mut self,
        target: &Expr,
    ) -> Result<Vec<SymmLemma>, NatDefinitionElabError> {
        let relation =
            symmetry_relation(target).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let entries = crate::symm::read_with_scopes(&self.txn.env, &self.source_scope.symm_scopes)
            .map_err(scope::symm::registry_error)?;
        if entries.is_empty() {
            return Ok(Vec::new());
        }
        let query = self.symm_path(&relation, false)?;
        let mut matches = Vec::new();
        for entry in entries {
            self.tick()?;
            if self.symm_path_matches(&entry.keys, &query)? {
                matches.push(entry);
            }
        }
        matches.sort_by(|left, right| index::match_order(&left.keys, &right.keys));
        Ok(matches)
    }

    fn apply_symmetry_lemma(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        local: Option<&LocalDecl>,
        lemma: &SymmLemma,
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let (term, arguments) = self.symmetry_telescope(&lemma.declaration)?;
        let last = arguments
            .last()
            .ok_or_else(|| error(TacticError::ApplyMismatch))?;
        if let Some(local) = local {
            // Unify the argument itself, as Expr.applySymm does. Merely
            // comparing its type would lose dependent proof identities.
            if !self.symmetry_match(last, &Expr::fvar(local.id.clone()))? {
                return Err(error(TacticError::ApplyMismatch));
            }
            let replacement = Typed {
                value: self.instantiate(&term.value)?,
                type_: self.instantiate(&term.type_)?,
            };
            let (child, parent, value) =
                self.replace_rewritten_hypothesis(goal, local, replacement, false)?;
            self.inherit_goal_tag(&parent, &child);
            proof.work.push(Work::Close(parent, value));
            return Ok(child);
        }
        if !self.symmetry_match(&term.type_, &goal.target)? {
            return Err(error(TacticError::ApplyMismatch));
        }
        let ExprNode::MVar { id } = last.node() else {
            return Err(error(TacticError::ApplyMismatch));
        };
        let target = self
            .txn
            .mvars
            .get_decl(id)
            .ok_or_else(|| error(TacticError::ApplyMismatch))?
            .type_
            .clone();
        let target = self.instantiate(&target)?;
        let child = ProofGoal {
            id: id.clone(),
            no_implicit_lambda: self.implicit_lambda_blocked(&target)?,
            target,
            lctx: self.txn.lctx.clone(),
            introduced: Vec::new(),
        };
        self.inherit_goal_tag(&goal, &child);
        proof.work.push(Work::Close(goal, term.value));
        Ok(child)
    }

    /// Rule selection requires a completed `isDefEq` query. Ordinary source
    /// `constrain` may postpone an equation, which cannot authorize selecting a
    /// candidate ahead of another lemma. Only the compared equations must
    /// settle; independent implicit arguments may remain metavariables as at
    /// the pin. The enclosing trial rolls back a failed candidate completely.
    fn symmetry_match(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<bool, NatDefinitionElabError> {
        self.flush(false)?;
        let left = self.instantiate(left)?;
        let right = self.instantiate(right)?;
        let mut equations = Vec::new();
        if let (Some(a), Some(b)) = (self.known_type(&left)?, self.known_type(&right)?) {
            let a = self.instantiate(&a)?;
            let b = self.instantiate(&b)?;
            if a.has_level_mvar() || b.has_level_mvar() {
                equations.push((a, b));
            }
        }
        equations.push((left, right));
        let budget = self.ambient_budget(UnificationTransparency::Default);
        match self.txn.unify_many_with(&equations, budget, &|| false) {
            Ok(report) => {
                assert!(report.awakened.is_empty(), "private source queue");
                Ok(true)
            }
            Err(UnificationError::Deferred(_)) => Ok(false),
            Err(UnificationError::AssignmentCheck { outcome, .. })
                if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })) =>
            {
                Ok(false)
            }
            Err(problem) => Err(failure(SourceInferenceError::Unification(Box::new(
                problem,
            )))),
        }
    }

    fn symmetrize_seed_equality(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        local: Option<&LocalDecl>,
    ) -> Result<ProofGoal, NatDefinitionElabError> {
        let target = self.whnf(local.map_or(&goal.target, |local| &local.type_))?;
        let (level, alpha, left, right) =
            equality_target(&target).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let reversed =
            equality::equation(level.clone(), alpha.clone(), right.clone(), left.clone());
        if let Some(local) = local {
            let value = self.symmetric_equality(
                &level,
                &alpha,
                &left,
                &right,
                Expr::fvar(local.id.clone()),
            )?;
            let replacement = Typed {
                value,
                type_: reversed,
            };
            let (child, parent, value) =
                self.replace_rewritten_hypothesis(goal, local, replacement, false)?;
            self.inherit_goal_tag(&parent, &child);
            proof.work.push(Work::Close(parent, value));
            return Ok(child);
        }
        let (witness, child) = self.proof_goal(reversed)?;
        self.inherit_goal_tag(&goal, &child);
        let value = self.symmetric_equality(&level, &alpha, &right, &left, witness)?;
        proof.work.push(Work::Close(goal, value));
        Ok(child)
    }
}

fn symmetry_relation(target: &Expr) -> Option<Expr> {
    let ExprNode::App { f, .. } = target.node() else {
        return None;
    };
    let ExprNode::App { f: relation, .. } = f.node() else {
        return None;
    };
    Some(relation.clone())
}
