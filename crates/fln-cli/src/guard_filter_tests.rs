//! Severity policies over real checked commands, plus retained diagnostic routing.
use super::*;

fn execute(source: &str) -> Result<fln::SourceCommandBatchExecution, fln::EngineExecutionError> {
    let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = fln::Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &fln::KVMap::new(),
            fln::EngineExecutionLimits::new(admission.kernel),
        )
        .map(|result| result.into_complete().unwrap())
}

fn render(source: &str) -> MultiplexerOutput {
    let completed = execute(source).unwrap();
    render_lean_source_commands(&completed, WarningSink::Unreachable)
}

#[test]
fn guard_filters_check_drop_and_pass_preserve_command_order() {
    for (spec, expected, stdout) in [
        ("info", "info: 4", "1\n3\n"),
        ("check info", "info: 4", "1\n3\n"),
        ("drop info", "", "1\n3\n"),
        ("pass info", "", "1\n4\n3\n"),
        ("drop warning", "", "1\n4\n3\n"),
        ("pass all, drop info", "", "1\n4\n3\n"),
        ("drop info, pass all", "", "1\n3\n"),
        ("pass error, drop all", "", "1\n3\n"),
        ("drop warning, info", "info: 4", "1\n3\n"),
    ] {
        let source =
            format!("#eval 1\n/-- {expected} -/\n#guard_msgs ({spec}) in\n#eval 2 + 2\n#eval 3\n");
        let output = render(&source);
        assert_eq!(output.exit_code, 0, "{spec}: {}", output.stderr);
        assert_eq!(output.stdout, stdout, "{spec}");
    }
    // A checked expectation does not match an info message that was passed through.
    let output = render("/-- info: 4 -/\n#guard_msgs (pass info) in\n#eval 4\n");
    assert_eq!(output.exit_code, 1);
}

#[test]
fn guard_filters_apply_to_check_without_fabricating_rendering_certainty() {
    for spec in ["info", "drop warning, info"] {
        let output = render(&format!(
            "/-- info: 1 : Nat -/\n#guard_msgs ({spec}) in\n#check 1\n"
        ));
        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stdout.is_empty());
    }
    let output = render("#guard_msgs (drop info) in\n#check 1\n");
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.is_empty());
    let output = render("#guard_msgs (pass info) in\n#check 1\n");
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert_eq!(output.stdout, "1 : Nat\n");
    let output = render("/-- info: 1 : Int -/\n#guard_msgs (info) in\n#check 1\n");
    assert_eq!(output.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);
}

fn warning_batch(source: &str) -> fln::SourceCommandBatchExecution {
    let mut completed = execute(source).unwrap();
    // The warning producer has its own source tests. Here exercise the same typed
    // diagnostic payload at the presentation boundary without importing sorryAx.
    completed.warnings.push(fln::SourceWarning {
        command_index: 0,
        at: fln_parse::BytePos(0),
        message: "declaration uses `sorry`".to_owned(),
    });
    completed
}

#[test]
fn guard_filters_route_positioned_warnings_and_sort_before_matching() {
    let source = "/-- info: 4 -/\n#guard_msgs (drop warning, info) in\n#eval 4\n";
    let output = render_lean_source_commands(&warning_batch(source), WarningSink::Unreachable);
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.is_empty());

    let source = "/-- info: 4 -/\n#guard_msgs (info) in\n#eval 4\n";
    let output = render_lean_source_commands(
        &warning_batch(source),
        WarningSink::Print {
            file: "Main.lean",
            source: source.as_bytes(),
        },
    );
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.starts_with("Main.lean:"));
    assert!(
        output
            .stdout
            .ends_with("warning: declaration uses `sorry`\n")
    );

    let source = "/-- info: 4\n---\nwarning: declaration uses `sorry` -/\n#guard_msgs (ordering := sorted) in\n#eval 4\n";
    let output = render_lean_source_commands(&warning_batch(source), WarningSink::Unreachable);
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert!(output.stdout.is_empty());
    let source = source.replace("sorted", "exact");
    let output = render_lean_source_commands(&warning_batch(&source), WarningSink::Unreachable);
    assert_eq!(output.exit_code, 1);
}

#[test]
fn guard_filters_never_ignore_errors_or_unsupported_positions() {
    for spec in [
        "drop error",
        "drop all",
        "drop all, pass error",
        "positions := true",
    ] {
        let error = execute(&format!("#guard_msgs ({spec}) in\n#eval 4\n")).unwrap_err();
        assert_eq!(
            execution_error_disposition(&error),
            ("capability", false, 5),
            "{spec}: {error}"
        );
    }
    let error = execute("#guard_msgs (pass error, drop all) in\n#check missingGuardSpecName\n")
        .unwrap_err();
    assert_ne!(execution_error_disposition(&error).2, 0);
}

#[test]
fn guard_filters_reject_ambiguous_retained_guard_tables() {
    let mut completed = execute("#guard_msgs in\ndef x : Nat := 1\n").unwrap();
    completed.guards.push(completed.guards[0].clone());
    let output = render_lean_source_commands(&completed, WarningSink::Unreachable);
    assert_eq!(output.exit_code, 4);
    assert!(output.stdout.is_empty());
    completed.guards.pop();
    completed.guards[0].command_index = completed.command_count;
    let output = render_lean_source_commands(&completed, WarningSink::Unreachable);
    assert_eq!(output.exit_code, 4);
}
