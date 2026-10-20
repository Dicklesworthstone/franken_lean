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
    /// An `example` that fails to elaborate under a guard expecting its error logs the error,
    /// which the guard judges, as the pin does; it declares nothing. A different wording is
    /// a non-answer, not a rejection, and so is an `example` that elaborates: this engine may
    /// accept what the pin rejects.
    #[test]
    fn a_guarded_example_error_is_judged_as_the_pins_message() {
        let accepted = render(
            "/-- error: Unknown identifier `nope` -/\n#guard_msgs in\nexample : Nat := nope\n#eval 3",
        );
        assert_eq!(accepted.exit_code, 0, "{}", accepted.stderr);
        assert_eq!(accepted.stdout, "3\n");
        let reworded =
            render("/-- error: Unknown constant `nope` -/\n#guard_msgs in\nexample : Nat := nope");
        assert_eq!(reworded.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);
        let elaborated =
            render("/-- error: Unknown identifier `nope` -/\n#guard_msgs in\nexample : Nat := 3");
        assert_eq!(
            elaborated.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT,
            "{}",
            elaborated.stderr
        );
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

    /// fln-guard-msgs-trace-severity-iss2: every literal is judged by the pinned `lean` first.
    /// A row the pin rejects must never be accepted here. Rows whose messages this engine
    /// reproduces exactly (`#eval` output, literal `trace`) must agree; goal-display rows may
    /// instead take the typed refusal, since this door's goal printer is not proven the pin's.
    #[test]
    fn guard_literals_agree_with_the_pin_or_refuse() {
        let pin = std::env::var_os("FLN_REFERENCE_LEAN")
            .map(std::path::PathBuf::from)
            .or_else(|| {
                std::env::var_os("HOME").map(|home| {
                    std::path::PathBuf::from(home)
                        .join(".elan/toolchains/leanprover--lean4---v4.32.0/bin/lean")
                })
            })
            .filter(|path| path.is_file());
        let Some(pin) = pin else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "FLN_REQUIRE_REFERENCE is set but the pinned Reference lean is absent"
            );
            eprintln!("SKIP: pinned Reference lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
            return;
        };
        let goal = "example (a b : Nat) (h : a = b) : a = b := by trace_state; exact h";
        let shown = "a b : Nat\nh : a = b\n⊢ a = b";
        let literal = "example : True := by trace \"hello\"; constructor";
        // (source, whether this engine must agree exactly rather than refuse)
        let rows = [
            (
                format!("/-- info: {shown} -/\n#guard_msgs in\n{goal}\n"),
                false,
            ),
            (
                format!("/-- trace: {shown} -/\n#guard_msgs in\n{goal}\n"),
                false,
            ),
            (
                format!("/-- info: not the goal -/\n#guard_msgs in\n{goal}\n"),
                false,
            ),
            (
                format!("/-- trace: not the goal -/\n#guard_msgs in\n{goal}\n"),
                false,
            ),
            (format!("#guard_msgs in\n{goal}\n"), false),
            (format!("{goal}\n"), false),
            (
                "/-- info: 3 -/\n#guard_msgs in\n#eval 1 + 1\n".to_owned(),
                true,
            ),
            (
                "/-- info: 2 -/\n#guard_msgs in\n#eval 1 + 1\n".to_owned(),
                true,
            ),
            (
                format!("/-- trace: hello -/\n#guard_msgs in\n{literal}\n"),
                true,
            ),
            (
                format!("/-- info: hello -/\n#guard_msgs in\n{literal}\n"),
                true,
            ),
        ];
        let directory = std::env::temp_dir().join(format!("fln-guard-pin-{}", std::process::id()));
        std::fs::create_dir_all(&directory).unwrap();
        let mut seen = [false; 2];
        for (index, (source, exact)) in rows.iter().enumerate() {
            let path = directory.join(format!("row{index}.lean"));
            std::fs::write(&path, source).unwrap();
            let reference = std::process::Command::new(&pin)
                .arg(&path)
                .current_dir(&directory)
                .output()
                .expect("the pinned Reference lean runs");
            let expected = reference.status.code().expect("the pin exits normally");
            assert!(matches!(expected, 0 | 1), "{source}: pin exit {expected}");
            seen[usize::from(expected == 1)] = true;
            let ours = render(source);
            assert!(
                !(expected != 0 && ours.exit_code == 0),
                "false accept: the pin rejects\n{source}"
            );
            if *exact || ours.exit_code != CAPABILITY_NOT_IMPLEMENTED_EXIT {
                assert_eq!(
                    i32::from(ours.exit_code),
                    expected,
                    "{source}\n{}",
                    ours.stderr
                );
            }
            if expected == 0 && ours.exit_code == 0 {
                assert_eq!(
                    ours.stdout.trim_end(),
                    String::from_utf8_lossy(&reference.stdout).trim_end(),
                    "{source}"
                );
            }
        }
        assert_eq!(
            seen,
            [true, true],
            "the table must hold accepted and rejected rows"
        );
    }

    #[test]
    fn trace_only_guards_leave_evaluation_messages_on_info() {
        let result =
            render("#guard_msgs (trace) in\n#eval 7\n/-- info: 8 -/\n#guard_msgs in\n#eval 8");
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
        guards.insert(
            guard.command_index,
            guard_messages::Buffer::new(&guard.spec),
        );
        let mut stdout = String::new();
        let mut budget = source_evaluation::FormattedOutputBudget::new(1);
        let failure = Message::Trace(trace)
            .emit(
                WarningSink::Unreachable,
                &mut guards,
                &mut stdout,
                &mut budget,
            )
            .unwrap_err();
        assert_eq!(failure.exit_code, 3);
        assert!(failure.stdout.is_empty() && stdout.is_empty());
        let buffer = &guards[&trace.command_index];
        assert!(buffer.checked.is_empty());
        assert!(
            !buffer.from_check,
            "discarded goals cannot taint checked messages"
        );
    }
}
