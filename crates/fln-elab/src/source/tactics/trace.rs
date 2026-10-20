//! Capture visible unsolved goals without stepping a tactic or assigning holes.
use super::*;

impl Context {
    pub(super) fn trace_proof_state(
        &mut self,
        proof: &ProofState<'_>,
        instruction: &Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        if instruction.kind() == Some(&parser_kind(&["Tactic", "traceMessage"])) {
            return self.record_message_trace(instruction);
        }
        let mut goals = Vec::new();
        for work in proof.work.iter().rev() {
            self.tick()?;
            match work {
                Work::EndScript(..)
                | Work::EndControl(_)
                | Work::EndAttempt(_)
                | Work::EndOptions(_) => break,
                Work::Goal(goal) if !self.txn.mvars.is_assigned(&goal.id) => {
                    goals.push(goal.clone())
                }
                _ => {}
            }
        }
        self.record_goal_trace(instruction, &goals)
    }
}
