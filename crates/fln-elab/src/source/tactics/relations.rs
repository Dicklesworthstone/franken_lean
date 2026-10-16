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
                expect_empty_null(location, "goal-only symmetry location")?;
                self.symmetrize_proof_goal(proof, goal)
            }
        }
    }

    pub(super) fn symmetrize_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.flush(false)?;
        let target = self.whnf(&goal.target)?;
        let (level, alpha, left, right) =
            equality_target(&target).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        let reversed =
            equality::equation(level.clone(), alpha.clone(), right.clone(), left.clone());
        let (witness, child) = self.proof_goal(reversed)?;
        let value = self.symmetric_equality(&level, &alpha, &right, &left, witness)?;
        proof.work.push(Work::Close(goal, value));
        proof.work.push(Work::Goal(child));
        Ok(())
    }
}
