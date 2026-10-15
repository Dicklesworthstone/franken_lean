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
                    // As with #check, a mismatch may be our partial printer,
                    // never evidence that the reference rejects the source.
                    guard.from_check |= guard
                        .spec
                        .action(fln_parse::command_scope::guard_spec::Severity::Info)
                        == fln_parse::command_scope::guard_spec::Action::Check;
                    guard.evaluation_target(&mut discarded)
                });
                budget
                    .append(&trace.message, stdout, target)
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
            "#eval 1\n/-- info: a b : Nat\nh : a = b\n⊢ a = b -/\n#guard_msgs in\nexample (a b : Nat) (h : a = b) : a = b := by trace_state; exact h\nexample : True := by trace_state; constructor\n#eval 2",
        );
        assert_eq!(result.exit_code, 0, "{}", result.stderr);
        assert_eq!(result.stdout, "1\n⊢ True\n2\n");
    }
    #[test]
    fn goal_display_mismatch_is_not_a_false_reference_rejection() {
        let result = render(
            "/-- info: not the goal -/\n#guard_msgs in\nexample : True := by trace_state; constructor",
        );
        assert_eq!(result.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);
        assert!(result.stdout.is_empty());
    }
}
