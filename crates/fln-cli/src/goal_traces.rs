//! Merge raw tactic observations with existing diagnostics, without changing verdicts.
use super::*;

pub(super) enum Message<'a> {
    Trace(&'a fln::SourceTraceMessage),
    Warning(&'a fln::SourceWarning),
}

impl Message<'_> {
    pub fn command(&self) -> usize {
        match self {
            Self::Trace(trace) => trace.command_index,
            Self::Warning(warning) => warning.command_index,
        }
    }

    pub fn emit(
        &self,
        sink: WarningSink<'_>,
        guards: &mut guard_messages::Guards<'_>,
        stdout: &mut String,
        budget: &mut source_evaluation::FormattedOutputBudget,
    ) -> Result<(), MultiplexerOutput> {
        match self {
            Self::Warning(warning) => emit_lean_warning(warning, sink, guards, stdout),
            Self::Trace(trace) => {
                let mut discarded = Vec::new();
                let target = guards.get_mut(&trace.command_index).and_then(|guard| {
                    use fln_parse::command_scope::guard_spec::{Action, Severity};
                    match guard.spec.action(Severity::Trace) {
                        Action::Check => {
                            // As with #check, a goal-display mismatch may be
                            // our partial printer, not a Reference rejection.
                            guard.from_check |= trace.is_goal_state;
                            Some(&mut guard.checked)
                        }
                        // Dropping a trace still traverses the bounded formatter.
                        Action::Drop => Some(&mut discarded),
                        Action::Pass => None,
                    }
                });
                budget
                    .append_trace(&trace.message, stdout, target)
                    .map_err(|error| error.failure(trace.command_index, SourcePresentation::Lean))
            }
        }
    }
}

pub(super) fn ordered(
    completed: &fln::SourceCommandBatchExecution,
) -> Result<Vec<Message<'_>>, MultiplexerOutput> {
    let mut messages = Vec::new();
    let mut previous = None;
    for trace in &completed.traces {
        if trace.command_index >= completed.command_count
            || previous.is_some_and(|prior| prior > trace.command_index)
        {
            return Err(source_failure(
                "internal-fault",
                "raw trace command order is invalid",
                false,
                SourcePresentation::Lean,
                4,
            ));
        }
        previous = Some(trace.command_index);
        messages.push(Message::Trace(trace));
    }
    messages.extend(completed.warnings.iter().map(Message::Warning));
    // Stable sorting keeps raw trace execution order, including failed choices.
    // A declaration's post-admission warning follows its elaboration traces.
    messages.sort_by_key(Message::command);
    Ok(messages)
}

#[cfg(test)]
mod tests {
    use super::*;
    fn render(source: &str) -> MultiplexerOutput {
        let limits = fln::EngineExecutionLimits::new(fln::Budget::for_stack_bytes(2 * 1024 * 1024));
        let engine = fln::Engine::with_source_seed(limits.admission())
            .unwrap()
            .into_complete()
            .unwrap();
        let commands = engine
            .execute_source_commands_with_checks(source.as_bytes(), &fln::KVMap::new(), limits)
            .unwrap()
            .into_complete()
            .unwrap();
        render_lean_source_commands(&commands, WarningSink::Unreachable)
    }
    #[test]
    fn seeded_traces_interleave_with_evaluation_and_guarded_output() {
        let result = render(
            "#eval 1\n/-- trace: a b : Nat\nh : a = b\n⊢ a = b -/\n#guard_msgs in\nexample (a b : Nat) (h : a = b) : a = b := by trace_state; exact h\nexample : True := by trace_state; constructor\n#eval 2",
        );
        assert_eq!(result.exit_code, 0, "{}", result.stderr);
        assert_eq!(result.stdout, "1\n⊢ True\n2\n");
    }
    #[test]
    fn goal_display_mismatch_is_not_a_false_reference_rejection() {
        let result = render(
            "/-- trace: not the goal -/\n#guard_msgs in\nexample : True := by trace_state; constructor",
        );
        assert_eq!(result.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);
        assert!(result.stdout.is_empty());
    }

    #[test]
    fn info_docstrings_cannot_accept_goal_traces() {
        let result = render(
            "/-- info: ⊢ True -/\n#guard_msgs in\nexample : True := by trace_state; constructor",
        );
        assert_eq!(result.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);
        assert!(result.stdout.is_empty());
    }

    #[test]
    fn literal_traces_are_checked_as_trace_not_info() {
        let body = "example : True := by trace \"hello λ\"; constructor";
        let accepted = render(&format!("/-- trace: hello λ -/\n#guard_msgs in\n{body}"));
        assert_eq!(accepted.exit_code, 0, "{}", accepted.stderr);
        assert!(accepted.stdout.is_empty());
        let refused = render(&format!("/-- info: hello λ -/\n#guard_msgs in\n{body}"));
        assert_eq!(refused.exit_code, 1, "{}", refused.stderr);
        assert!(refused.stdout.is_empty());
    }

    #[test]
    fn trace_filters_do_not_borrow_the_info_policy() {
        let body = "example : True := by trace \"hello\"; constructor";
        for (spec, expected) in [
            ("drop trace", ""),
            ("pass trace", "hello\n"),
            ("drop info", "hello\n"),
            ("info", "hello\n"),
            ("drop trace, trace", ""),
            ("pass trace, drop trace", "hello\n"),
        ] {
            let result = render(&format!("#guard_msgs ({spec}) in\n{body}"));
            assert_eq!(result.exit_code, 0, "{spec}: {}", result.stderr);
            assert_eq!(result.stdout, expected, "{spec}");
        }
        for spec in ["trace", "trace, drop trace", "all"] {
            let result = render(&format!(
                "/-- trace: hello -/\n#guard_msgs ({spec}) in\n{body}"
            ));
            assert_eq!(result.exit_code, 0, "{spec}: {}", result.stderr);
            assert!(result.stdout.is_empty(), "{spec}");
        }
    }

    #[test]
    fn trace_only_guards_leave_evaluation_messages_on_info() {
        let result = render(
            "#guard_msgs (trace) in\n#eval 7\n/-- info: 8 -/\n#guard_msgs in\n#eval 8",
        );
        assert_eq!(result.exit_code, 0, "{}", result.stderr);
        assert_eq!(result.stdout, "7\n");
    }

    #[test]
    fn dropped_traces_still_exhaust_the_shared_output_budget() {
        let limits = fln::EngineExecutionLimits::new(fln::Budget::for_stack_bytes(2 * 1024 * 1024));
        let engine = fln::Engine::with_source_seed(limits.admission())
            .unwrap()
            .into_complete()
            .unwrap();
        let commands = engine
            .execute_source_commands_with_checks(
                b"#guard_msgs (drop trace) in\nexample : True := by trace_state; constructor",
                &fln::KVMap::new(),
                limits,
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(commands.traces.len(), 1);
        let trace = &commands.traces[0];
        let guard = &commands.guards[0];
        let mut guards = guard_messages::Guards::new();
        guards.insert(guard.command_index, guard_messages::Buffer::new(&guard.spec));
        let mut stdout = String::new();
        let mut budget = source_evaluation::FormattedOutputBudget::new(1);
        let failure = Message::Trace(trace)
            .emit(WarningSink::Unreachable, &mut guards, &mut stdout, &mut budget)
            .unwrap_err();
        assert_eq!(failure.exit_code, 3);
        assert!(failure.stdout.is_empty() && stdout.is_empty());
        let buffer = &guards[&trace.command_index];
        assert!(buffer.checked.is_empty());
        assert!(!buffer.from_check, "discarded goals cannot taint checked messages");
    }
}
