//! Definitional goal replacement, with the written target retained in the
//! proof term. A successful equality probe is not declaration admission.

use super::*;

impl Context {
    pub(in crate::source) fn change_proof_goal(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        annotation: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        self.resolve_instances(false)?;
        self.flush(false)?;
        self.sort_level(&annotation)?;

        // This equality must hold before subsequent tactics run, not merely
        // during final admission. Otherwise `first` could select a branch
        // which changed the target to an unrelated proposition.
        if !self.coercion_eq(&annotation.value, &goal.target)? {
            return Err(error(TacticError::ChangeMismatch));
        }
        let target = self.instantiate(&annotation.value)?;
        let (witness, child) = self.proof_goal(target.clone())?;

        // Retain the full written target as a checked annotation. Erasing it
        // after the conversion probe could erase an invalid subterm that the
        // elaborator left for K1 (for example inside a discarded argument).
        let value = Expr::let_e(
            Name::anonymous(),
            target,
            witness,
            Expr::bvar(0).expect("fixed target-replacement identity binder"),
            false,
        );
        proof.work.push(Work::Close(goal, value));
        proof.work.push(Work::Goal(child));
        Ok(())
    }
}
