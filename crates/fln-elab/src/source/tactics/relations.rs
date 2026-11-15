//! Equality tactics construct ordinary eliminator terms. The original goal is
//! closed only after every generated goal has a proof, so introduced binders
//! are never abstracted around an unresolved child metavariable.

use super::*;

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

    /// Reverse one equality through an ordinary Eq.rec proof. Replacing a
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
        let target = self.whnf(local.as_ref().map_or(&goal.target, |local| &local.type_))?;
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
                self.replace_rewritten_hypothesis(goal, &local, replacement, false)?;
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
