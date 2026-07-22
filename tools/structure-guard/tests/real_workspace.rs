//! The workspace-graph snapshot test (bead fln-8mj): the REAL repository must be
//! structurally clean against its reviewed acknowledgment files. Any new crate or
//! dependency edge fails this test until `ci/WORKSPACE_GRAPH.txt` is edited in the
//! same change — that edit is the review surface.

#![forbid(unsafe_code)]

use std::path::Path;
use std::process::{Command, Output};

fn run_cli(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_structure-guard"))
        .args(args)
        .output()
        .expect("run structure-guard CLI")
}

fn assert_versioned_robot_lines(stdout: &str, expected_lines: usize) {
    let lines: Vec<_> = stdout.lines().collect();
    assert_eq!(lines.len(), expected_lines, "robot output:\n{stdout}");
    assert!(
        lines.iter().all(|line| line.starts_with('{')),
        "robot mode emitted human output: {stdout}"
    );
    assert!(
        lines
            .iter()
            .all(|line| line.contains("\"schema\":\"structure-guard/2\"")),
        "robot output used the wrong schema: {stdout}"
    );
}

#[test]
fn real_workspace_is_structurally_clean() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
    let outcome = structure_guard::checks::run(root).expect("structure-guard setup");
    assert!(
        outcome.findings.is_empty(),
        "structural findings against the real workspace:\n{}",
        structure_guard::report::render_human(&root.display().to_string(), &outcome)
    );
    assert!(
        outcome.crate_count > 0,
        "workspace discovery found no crates"
    );
}

#[test]
fn robot_unknown_argument_is_visible_even_when_robot_flag_comes_later() {
    let output = run_cli(&["--unknown", "--robot"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stderr.is_empty(), "robot stderr must be empty");
    let stdout = String::from_utf8(output.stdout).expect("robot stdout is UTF-8");
    assert_versioned_robot_lines(&stdout, 2);
    assert!(stdout.contains("\"verdict\":\"setup_error\""));
    assert!(stdout.contains("\"reason_code\":\"cli_parse_failure\""));
    assert!(stdout.contains("unknown argument `--unknown`"));
}

#[test]
fn robot_missing_root_value_is_a_machine_visible_parse_failure() {
    for args in [["--root", "--robot"], ["--robot", "--root"]] {
        let output = run_cli(&args);
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stderr.is_empty(), "robot stderr must be empty");
        let stdout = String::from_utf8(output.stdout).expect("robot stdout is UTF-8");
        assert_versioned_robot_lines(&stdout, 2);
        assert!(stdout.contains("\"reason_code\":\"cli_parse_failure\""));
        assert!(stdout.contains("--root requires a path"));
    }
}

#[test]
fn robot_help_remains_machine_only_in_either_argument_order() {
    for args in [["--robot", "--help"], ["--help", "--robot"]] {
        let output = run_cli(&args);
        assert!(output.status.success());
        assert!(output.stderr.is_empty(), "robot stderr must be empty");
        let stdout = String::from_utf8(output.stdout).expect("robot stdout is UTF-8");
        assert_versioned_robot_lines(&stdout, 3);
        assert!(stdout.contains("\"event\":\"help\""));
        assert!(stdout.contains("\"reason_code\":\"help_requested\""));
        assert!(stdout.contains("\"exit_code\":0"));
    }
}
