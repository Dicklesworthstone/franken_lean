//! Equality tactics construct ordinary eliminator terms. The original goal is
//! closed only after every generated goal has a proof, so introduced binders
//! are never abstracted around an unresolved child metavariable.

use super::*;

impl Context {
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
