//! Native engine-to-renderer regressions; no reference toolchain or subprocess.
use super::*;

fn render(source: &str) -> MultiplexerOutput {
    let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = fln::Engine::with_source_seed(admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let completed = engine
        .execute_source_commands_with_checks(
            source.as_bytes(),
            &fln::KVMap::new(),
            fln::EngineExecutionLimits::new(admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    render_lean_source_commands(&completed, WarningSink::Unreachable)
}

#[test]
fn guard_spec_whitespace_modes_change_real_command_judgments() {
    for mode in ["normalized", "lax"] {
        let source =
            format!("/-- info:\n4 -/\n#guard_msgs (whitespace := {mode}) in\n#eval 2 + 2\n");
        let output = render(&source);
        assert_eq!(output.exit_code, 0, "{}", output.stderr);
        assert!(output.stdout.is_empty());
    }
    let output = render("/-- info:\n4 -/\n#guard_msgs (whitespace := exact) in\n#eval 2 + 2\n");
    assert_eq!(output.exit_code, 1);
    assert!(output.stderr.contains("Docstring on `#guard_msgs`"));
    let output = render("/-- info:   4 -/\n#guard_msgs (whitespace := lax) in\n#eval 2 + 2\n");
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    let output =
        render("/-- info:   4 -/\n#guard_msgs (whitespace := normalized) in\n#eval 2 + 2\n");
    assert_eq!(output.exit_code, 1);
}

#[test]
fn guard_spec_substring_preserves_neighbor_outputs_and_real_mismatches() {
    let output =
        render("#eval 1\n/-- 4 -/\n#guard_msgs (substring := true) in\n#eval 2 + 2\n#eval 3\n");
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert_eq!(output.stdout, "1\n3\n");
    let output = render("/-- 5 -/\n#guard_msgs (substring := true) in\n#eval 2 + 2\n");
    assert_eq!(output.exit_code, 1);
    assert!(output.stdout.is_empty());
    let output = render("/-- 4 -/\n#guard_msgs (substring := false) in\n#eval 2 + 2\n");
    assert_eq!(output.exit_code, 1);
}

#[test]
fn guard_spec_first_option_wins_through_engine_and_renderer() {
    let output = render(
        "/-- info:\n4 -/\n#guard_msgs (whitespace := exact, whitespace := lax) in\n#eval 2 + 2\n",
    );
    assert_eq!(output.exit_code, 1);
    let output = render(
        "/-- info:\n4 -/\n#guard_msgs (whitespace := lax, whitespace := exact) in\n#eval 2 + 2\n",
    );
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    let output = render("#guard_msgs () in\ndef x : Nat := 1\n#eval x\n");
    assert_eq!(output.exit_code, 0, "{}", output.stderr);
    assert_eq!(output.stdout, "1\n");
}

#[test]
fn guard_spec_does_not_turn_check_rendering_gaps_into_rejections() {
    let output = render("/-- 1 : Int -/\n#guard_msgs (substring := true) in\n#check 1\n");
    assert_eq!(output.exit_code, CAPABILITY_NOT_IMPLEMENTED_EXIT);
    assert!(output.stderr.contains("#check"));
}
