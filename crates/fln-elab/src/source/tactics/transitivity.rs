//! Equality transitivity produces two ordered subgoals and a checked Eq.rec
//! bridge. This is not an axiom or a typeclass-selected relation theorem.
use super::*;

impl Context {
    pub(in crate::source) fn transitivity_domain(
        &mut self,
        goal: &ProofGoal,
    ) -> Result<Expr, NatDefinitionElabError> {
        let target = self.whnf(&goal.target)?;
        equality_target(&target)
            .map(|(_, alpha, _, _)| alpha)
            .ok_or_else(|| error(TacticError::ExpectedEquality))
    }

    pub(in crate::source) fn apply_transitivity(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: ProofGoal,
        middle: Typed,
    ) -> Result<(), NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let target = self.whnf(&goal.target)?;
        let (level, alpha, left, right) =
            equality_target(&target).ok_or_else(|| error(TacticError::ExpectedEquality))?;
        self.constrain_type(&middle.type_, &alpha)?;
        let left_type =
            equality::equation(level.clone(), alpha.clone(), left, middle.value.clone());
        let right_type = equality::equation(level, alpha, middle.value, right);
        let (left_proof, left_goal) = self.proof_goal(left_type.clone())?;
        let (right_proof, right_goal) = self.proof_goal(right_type.clone())?;
        let bridge = self.compose_calculation(
            Typed {
                value: left_proof,
                type_: left_type,
            },
            Typed {
                value: right_proof,
                type_: right_type,
            },
        )?;
        proof.work.push(Work::Close(goal, bridge.value));
        // LIFO work stack: establish the left endpoint first, then the right.
        // Neither this scheduling nor the source Typed wrappers grant trust.
        proof.work.push(Work::Goal(right_goal));
        proof.work.push(Work::Goal(left_goal));
        Ok(())
    }
}
