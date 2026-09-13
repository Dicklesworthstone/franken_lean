//! Transactional alternatives around the existing term/proof worklists.
//!
//! Checkpoints own semantic state, not work budgets. They are held in a flat
//! driver stack, so cloning a proof never recursively clones its ancestors.
use super::*;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::source) enum Mode {
    First,
    Try,
    Repeat,
}
pub(in crate::source) struct Spec<'a> {
    pub mode: Mode,
    pub branches: Vec<Vec<&'a Syntax>>,
}
pub(in crate::source) struct Checkpoint<'a> {
    context: Box<Context>,
    proof: ProofState<'a>,
    spec: Spec<'a>,
    next: usize,
    pub tasks: usize,
    pub values: usize,
}
impl<'a> Checkpoint<'a> {
    pub fn new(
        context: &Context,
        proof: &ProofState<'a>,
        spec: Spec<'a>,
        tasks: usize,
        values: usize,
    ) -> Self {
        Self {
            context: Box::new(context.clone()),
            proof: proof.clone(),
            spec,
            next: 0,
            tasks,
            values,
        }
    }
    pub fn begin(
        &mut self,
        context: &mut Context,
        index: usize,
    ) -> Result<ProofState<'a>, NatDefinitionElabError> {
        context.tick()?;
        context.attempt_depth = self
            .context
            .attempt_depth
            .checked_add(1)
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        let body = self
            .spec
            .branches
            .get(self.next)
            .ok_or_else(|| error(TacticError::MalformedScript))?
            .clone();
        self.next += 1;
        let mut proof = self.proof.clone();
        let at = proof
            .work
            .iter()
            .rposition(|work| {
                matches!(
                    work,
                    Work::EndScript(..) | Work::EndControl(_) | Work::EndAttempt(_)
                )
            })
            .map_or(0, |position| position + 1);
        proof.work.insert(at, Work::EndAttempt(index));
        proof.instructions = body;
        proof.cursor = 0;
        Ok(proof)
    }
    pub fn restore(&self, context: &mut Context) {
        let spent = context.txn.budget.heartbeats_consumed;
        *context = (*self.context).clone();
        context.txn.budget.heartbeats_consumed = spent;
    }
    pub fn retry(&self) -> bool {
        self.next < self.spec.branches.len()
    }
    pub fn optional(&self) -> bool {
        matches!(self.spec.mode, Mode::Try | Mode::Repeat)
    }
    pub fn finish(&self, context: &mut Context, proof: &mut ProofState<'a>) {
        context.attempt_depth = self.context.attempt_depth;
        proof.instructions = self.proof.instructions.clone();
        proof.cursor = self.proof.cursor;
    }
    pub fn original(self) -> ProofState<'a> {
        self.proof
    }
    /// Commit this iteration, not the entire repetition. The next failure must
    /// restore this successful state, including new goals and local binders.
    /// No progress heuristic can turn `repeat skip` into a successful proof.
    pub fn next_iteration(self, context: &Context, proof: &ProofState<'a>) -> Option<Self> {
        (self.spec.mode == Mode::Repeat)
            .then(|| Self::new(context, proof, self.spec, self.tasks, self.values))
    }
}

/// Only ordinary user-level failures are caught. Unknown/internal scope faults,
/// cancellation and every resource outcome propagate, including nested K1 stops.
pub(in crate::source) fn recoverable(problem: &NatDefinitionElabError) -> bool {
    match problem {
        NatDefinitionElabError::Inference(SourceInferenceError::Tactic(reason)) => {
            !matches!(reason, TacticError::MalformedScript)
        }
        NatDefinitionElabError::Inference(
            SourceInferenceError::UnknownConstant(_)
            | SourceInferenceError::ExpectedFunction
            | SourceInferenceError::ExpectedType
            | SourceInferenceError::Match(_)
            | SourceInferenceError::InstanceSynthesisRequired
            | SourceInferenceError::UnresolvedHoles { .. }
            | SourceInferenceError::UnresolvedUniverses,
        ) => true,
        NatDefinitionElabError::Inference(SourceInferenceError::Unification(reason)) => {
            match reason.as_ref() {
                UnificationError::Deferred(reason) => !matches!(
                    reason,
                    crate::constraint::unify::UnificationDeferred::InvalidLocalContext
                        | crate::constraint::unify::UnificationDeferred::UnknownMetavariable(_)
                ),
                UnificationError::AssignmentCheck { outcome, .. } => matches!(
                    outcome.as_ref(),
                    Outcome::Complete(Verdict::Rejected { .. })
                ),
                _ => false,
            }
        }
        NatDefinitionElabError::Inference(SourceInferenceError::TypeObligation(outcome)) => {
            matches!(
                outcome.as_ref(),
                Outcome::Complete(Verdict::Rejected { .. })
            )
        }
        _ => false,
    }
}

impl Context {
    pub(in crate::source) fn check_attempt_equation(
        &mut self,
        actual: &Expr,
        expected: &Expr,
    ) -> Result<(), NatDefinitionElabError> {
        if self.attempt_depth == 0 {
            return Ok(());
        }
        let mut budget = UnificationBudget::new(self.kernel);
        budget.transparency = UnificationTransparency::SafeDefinitions;
        self.txn
            .unify(actual, expected, budget)
            .map(|_| ())
            .map_err(|problem| failure(SourceInferenceError::Unification(Box::new(problem))))
    }
    pub(super) fn backtrack_instruction<'a>(
        &mut self,
        syntax: &'a Syntax,
    ) -> Result<Option<Spec<'a>>, NatDefinitionElabError> {
        let Syntax::Node { kind, args, .. } = syntax else {
            return Ok(None);
        };
        let mode = if kind == &parser_kind(&["Tactic", "first"]) {
            Mode::First
        } else if kind == &parser_kind(&["Tactic", "try"]) {
            Mode::Try
        } else if kind == &parser_kind(&["Tactic", "repeat"]) {
            Mode::Repeat
        } else {
            return Ok(None);
        };
        let [keyword, body] = args.as_slice() else {
            return Err(error(TacticError::MalformedScript));
        };
        expect_atom(
            keyword,
            match mode {
                Mode::First => "first",
                Mode::Try => "try",
                Mode::Repeat => "repeat",
            },
            "alternative keyword",
        )?;
        let mut branches = Vec::new();
        if mode == Mode::First {
            let rows = expect_null_args(body, "tactic alternatives")?;
            if rows.is_empty() || rows.len() % 2 != 0 {
                return Err(error(TacticError::MalformedScript));
            }
            for pair in rows.as_chunks::<2>().0 {
                self.tick()?;
                expect_atom(&pair[0], "|", "alternative separator")?;
                branches.push(self.proof_instructions(&pair[1])?);
            }
        } else {
            branches.push(self.proof_instructions(body)?);
        }
        if branches.iter().any(Vec::is_empty) {
            return Err(error(TacticError::MalformedScript));
        }
        Ok(Some(Spec { mode, branches }))
    }

    pub(super) fn suspend_attempt(
        &mut self,
        proof: &mut ProofState<'_>,
        goal: &ProofGoal,
    ) -> Result<Option<usize>, NatDefinitionElabError> {
        for position in (0..proof.work.len()).rev() {
            self.tick()?;
            match proof.work[position] {
                Work::EndScript(..) | Work::EndControl(_) => return Ok(None),
                Work::EndAttempt(index) => {
                    proof.work.remove(position);
                    proof.work.push(Work::Goal(goal.clone()));
                    return Ok(Some(index));
                }
                _ => {}
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn choice_catches_user_failures_but_never_resource_or_scope_faults() {
        assert!(recoverable(&error(TacticError::ExplicitFailure)));
        assert!(recoverable(&error(TacticError::ApplyMismatch)));
        for failure_kind in [
            UnificationError::Cancelled,
            UnificationError::HeartbeatLimit,
            UnificationError::StepLimit { limit: 0 },
            UnificationError::NodeLimit { limit: 0 },
            UnificationError::AssignmentLimit { limit: 0 },
            UnificationError::LooseBoundVariable,
            UnificationError::ExpressionScope,
            UnificationError::Deferred(
                crate::constraint::unify::UnificationDeferred::InvalidLocalContext,
            ),
        ] {
            assert!(!recoverable(&failure(SourceInferenceError::Unification(
                Box::new(failure_kind)
            ))));
        }
        for failure_kind in [
            SourceInferenceError::ResourceLimit,
            SourceInferenceError::Scope,
        ] {
            assert!(!recoverable(&failure(failure_kind)));
        }
        assert!(!recoverable(&error(TacticError::MalformedScript)));
    }

    #[test]
    fn nonprogressing_repetitions_and_backtracking_cannot_refund_work() {
        for body in [
            "repeat skip",
            "repeat try fail",
            "try repeat skip",
            "first | repeat skip | skip",
            "repeat (first | fail | skip)",
        ] {
            let source = format!("theorem t : Prop := by {body}");
            let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
            let mut pending = vec![parsed.syntax()];
            let syntax = loop {
                let node = pending.pop().expect("proof node");
                if node.kind() == Some(&parser_kind(&["Term", "byTactic"])) {
                    break node;
                }
                if let Syntax::Node { args, .. } = node {
                    pending.extend(args.iter());
                }
            };
            let mut context =
                Context::new(&Environment::new(), Budget::for_stack_bytes(128 * 1024));
            context.txn.budget.max_heartbeats = 400;
            let result = context.term(syntax, Some(Expr::sort(Level::zero())));
            assert!(
                matches!(
                    result,
                    Err(NatDefinitionElabError::Inference(
                        SourceInferenceError::ResourceLimit
                    ))
                ),
                "{body}"
            );
            assert!(context.txn.budget.heartbeats_consumed > 400);
        }
    }
}
