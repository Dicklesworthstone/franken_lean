//! Scoped goal control over the existing proof worklist.
//!
//! A frame suspends sibling goals and continuations, not their metavariable
//! assignments. All-goals maps over the original frontier, never over goals
//! created by the mapped tactic. Deferred close actions retain dependent terms.
use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum Mode {
    Solve,
    Focus,
    All,
}
impl Mode {
    pub(super) fn keyword(self) -> &'static str {
        match self {
            Self::Solve => "·",
            Self::Focus => "focus",
            Self::All => "all_goals",
        }
    }
}
pub(super) fn mode(kind: &Name) -> Option<Mode> {
    if kind == &parser_kind(&["Tactic", "cdot"]) {
        Some(Mode::Solve)
    } else if kind == &parser_kind(&["Tactic", "focus"]) {
        Some(Mode::Focus)
    } else if kind == &parser_kind(&["Tactic", "allGoals"]) {
        Some(Mode::All)
    } else {
        None
    }
}
pub(super) struct Frame<'a> {
    mode: Mode,
    body: Vec<&'a Syntax>,
    instructions: Vec<&'a Syntax>,
    cursor: usize,
    waiting: Vec<Work<'a>>,
    // Execution order, reversed exactly once when restoring the outer worklist.
    deferred: Vec<Work<'a>>,
    // A sequencing frame first isolates its left operand, then maps this
    // continuation only over the resulting frontier, not over old siblings.
    after: Option<Vec<&'a Syntax>>,
}
impl Context {
    pub(super) fn start_goal_control<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        syntax: &'a Syntax,
        mode: Mode,
    ) -> Result<(), NatDefinitionElabError> {
        let body = self.proof_instructions(syntax)?;
        self.start_goal_control_body(proof, goal, body, mode, None)
    }

    pub(super) fn start_goal_sequence<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        left: &'a Syntax,
        right: &'a Syntax,
    ) -> Result<(), NatDefinitionElabError> {
        let left = self.proof_instructions(left)?;
        let right = self.proof_instructions(right)?;
        if right.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        self.start_goal_control_body(proof, goal, left, Mode::Focus, Some(right))
    }

    fn start_goal_control_body<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        goal: ProofGoal,
        body: Vec<&'a Syntax>,
        mode: Mode,
        after: Option<Vec<&'a Syntax>>,
    ) -> Result<(), NatDefinitionElabError> {
        if body.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        let frame = Frame {
            mode,
            body: body.clone(),
            instructions: std::mem::replace(&mut proof.instructions, body),
            cursor: std::mem::replace(&mut proof.cursor, 0),
            waiting: std::mem::take(&mut proof.work),
            deferred: Vec::new(),
            after,
        };
        let index = proof.controls.len();
        proof.controls.push(frame);
        proof.work.push(Work::EndControl(index));
        proof.work.push(Work::Goal(goal));
        Ok(())
    }

    /// A strict constructor alternative is an intervening barrier. A focus
    /// outside it cannot turn that alternative's unfinished proof into success.
    pub(super) fn suspend_goal_control(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: &ProofGoal,
    ) -> Result<bool, NatDefinitionElabError> {
        let mut boundary = None;
        for work in proof.work.iter().rev() {
            self.tick()?;
            match work {
                Work::EndScript(..) => return Ok(false),
                Work::EndControl(index) => {
                    boundary = Some(*index);
                    break;
                }
                _ => {}
            }
        }
        let Some(index) = boundary else {
            return Ok(false);
        };
        let mut pending = std::mem::take(&mut proof.work);
        if !matches!(pending.first(), Some(Work::EndControl(found)) if *found == index) {
            return Err(error(TacticError::MalformedScript));
        }
        pending.remove(0);
        pending.push(Work::Goal(goal.clone()));
        self.finish_goal_control(proof, index, pending)?;
        Ok(true)
    }

    pub(super) fn finish_goal_control<'a>(
        &mut self,
        proof: &mut ProofState<'a>,
        index: usize,
        pending: Vec<Work<'a>>,
    ) -> Result<(), NatDefinitionElabError> {
        if index + 1 != proof.controls.len() || !proof.work.is_empty() {
            return Err(error(TacticError::MalformedScript));
        }
        self.skip_empty_goal_controls(proof)?;
        if proof.cursor != proof.instructions.len() {
            return Err(error(TacticError::NoGoals));
        }
        let mut frame = proof.controls.pop().expect("validated control depth");
        if let Some(body) = frame.after.take()
            && !pending.is_empty()
        {
            let mut pending = pending;
            let Some(Work::Goal(goal)) = pending.pop() else {
                return Err(error(TacticError::MalformedScript));
            };
            // Keep the original scope as an outer barrier. The all-goals frame
            // sees exactly the newly produced frontier and its close actions.
            proof.instructions = Vec::new();
            proof.cursor = 0;
            proof.controls.push(frame);
            proof.work.push(Work::EndControl(index));
            proof.work.extend(pending);
            return self.start_goal_control_body(proof, goal, body, Mode::All, None);
        }
        if frame.mode == Mode::Solve && !pending.is_empty() {
            let mut count = 0;
            for work in &pending {
                self.tick()?;
                if let Work::Goal(goal) = work
                    && !self.txn.mvars.is_assigned(&goal.id)
                {
                    count += 1;
                }
            }
            return Err(error(TacticError::UnsolvedGoals { count }));
        }
        for work in pending.into_iter().rev() {
            self.tick()?;
            frame.deferred.push(work);
        }
        if frame.mode == Mode::All {
            loop {
                self.tick()?;
                match frame.waiting.last() {
                    Some(Work::Close(..)) => {
                        frame
                            .deferred
                            .push(frame.waiting.pop().expect("last exists"));
                    }
                    Some(Work::Goal(_)) => {
                        let Some(Work::Goal(goal)) = frame.waiting.pop() else {
                            unreachable!()
                        };
                        if self.txn.mvars.is_assigned(&goal.id) {
                            continue;
                        }
                        proof.instructions = frame.body.clone();
                        proof.cursor = 0;
                        proof.controls.push(frame);
                        proof.work.push(Work::EndControl(index));
                        proof.work.push(Work::Goal(goal));
                        return Ok(());
                    }
                    // Do not cross a scoped branch or an enclosing controller.
                    _ => break,
                }
            }
        }
        proof.instructions = frame.instructions;
        proof.cursor = frame.cursor;
        proof.work = frame.waiting;
        proof.work.extend(frame.deferred.into_iter().rev());
        Ok(())
    }

    /// Like mapping over an empty list, all_goals on no goals succeeds without
    /// executing its body. The parser still validates every token of that body.
    pub(super) fn skip_empty_goal_controls(
        &mut self,
        proof: &mut ProofState<'_>,
    ) -> Result<(), NatDefinitionElabError> {
        while let Some(Syntax::Node { kind, args, .. }) = proof.instructions.get(proof.cursor) {
            self.tick()?;
            if mode(kind) != Some(Mode::All) {
                break;
            }
            let [keyword, sequence] = args.as_slice() else {
                return Err(error(TacticError::MalformedScript));
            };
            expect_atom(keyword, "all_goals", "all-goals keyword")?;
            self.proof_instructions(sequence)?;
            proof.cursor += 1;
        }
        Ok(())
    }
}
