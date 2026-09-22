//! Integration tests for new fln multiplexer verbs (diff, goals, doctor, serve-mcp,
//! replay, cache, build explain) and toolchain personalities (leanc, lake).
#![forbid(unsafe_code)]

use std::process::Command;

#[test]
fn multiplexer_doctor_verb_reports_healthy_audit() {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("doctor")
        .output()
        .expect("run fln doctor");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("fln doctor: environment and subsystem audit"));
    assert!(stdout.contains("reference pin: v4.32.0"));
    assert!(stdout.contains("all core subsystem checks passed"));

    let json_output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["doctor", "--json"])
        .output()
        .expect("run fln doctor --json");
    assert!(json_output.status.success());
    let json_stdout = String::from_utf8(json_output.stdout).expect("utf8 stdout");
    assert!(json_stdout.contains("\"schema\":\"fln.doctor/1\""));
    assert!(json_stdout.contains("\"status\":\"healthy\""));
    assert!(json_stdout.contains("\"kernel_checker\""));
}

#[test]
fn multiplexer_capability_notices_are_typed_and_exit_cleanly() {
    for (verb, expected_gate, expected_desc) in [
        ("serve-mcp", "G6", "Envoy"),
        ("replay", "G5", "Palimpsest"),
        ("cache", "G2", "Ledger"),
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .arg(verb)
            .output()
            .expect("run verb");
        assert!(output.status.success());
        let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
        assert!(stdout.contains(expected_gate), "verb {verb}: {stdout}");
        assert!(stdout.contains(expected_desc), "verb {verb}: {stdout}");

        let json_output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args([verb, "--json"])
            .output()
            .expect("run verb --json");
        assert!(json_output.status.success());
        let json_stdout = String::from_utf8(json_output.stdout).expect("utf8 stdout");
        assert!(json_stdout.contains("\"schema\":\"fln.capability-notice/1\""));
        assert!(json_stdout.contains(&format!("\"command\":\"{verb}\"")));
        assert!(json_stdout.contains(&format!("\"gate\":\"{expected_gate}\"")));
    }

    // Test build explain
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["build", "explain"])
        .output()
        .expect("run build explain");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("G2"));
    assert!(stdout.contains("Ledger"));
}

#[test]
fn multiplexer_diff_verb_routes_to_olean_diff() {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["diff", "--help"])
        .output()
        .expect("run fln diff --help");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Usage:"));
}

#[test]
fn multiplexer_goals_verb_inspects_proof_goals() {
    let example_path = "examples/native_goal_control.lean";

    // Test with PATH:LINE:COL
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("goals")
        .arg(format!("{example_path}:7:3"))
        .output()
        .expect("run fln goals");
    assert!(
        output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("goal") || stdout.contains("⊢"), "{stdout}");

    // Test with --json and --line --col
    let json_output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["goals", "--json", "--line", "7", "--col", "3", example_path])
        .output()
        .expect("run fln goals --json");
    assert!(
        json_output.status.success(),
        "stderr: {}",
        String::from_utf8_lossy(&json_output.stderr)
    );
    let json_stdout = String::from_utf8(json_output.stdout).expect("utf8 stdout");
    assert!(json_stdout.contains("\"schema\":\"fln.goals/1\""), "{json_stdout}");
    assert!(json_stdout.contains("\"goals\""), "{json_stdout}");
}

#[test]
fn leanc_personality_respects_cli_transcripts() {
    // leanc --version
    let output = Command::new(env!("CARGO_BIN_EXE_leanc"))
        .arg("--version")
        .output()
        .expect("run leanc --version");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("leanc"));
    assert!(stdout.contains("4.32.0"));

    // leanc --help
    let output = Command::new(env!("CARGO_BIN_EXE_leanc"))
        .arg("--help")
        .output()
        .expect("run leanc --help");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Usage: leanc"));

    // leanc --fln-census-unknown
    let output = Command::new(env!("CARGO_BIN_EXE_leanc"))
        .arg("--fln-census-unknown")
        .output()
        .expect("run leanc --fln-census-unknown");
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
    assert!(stderr.contains("unrecognized command-line option"));
}

#[test]
fn lake_personality_respects_cli_transcripts() {
    // lake (bare usage)
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .output()
        .expect("run lake");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Lake version 5.0.0-src"));
    assert!(stdout.contains("COMMANDS:"));

    // lake --help
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--help")
        .output()
        .expect("run lake --help");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Lake version 5.0.0-src"));

    // lake --version
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .arg("--version")
        .output()
        .expect("run lake --version");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Lake version 5.0.0-src"));
    assert!(stdout.contains("4.32.0"));

    // lake help build
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["help", "build"])
        .output()
        .expect("run lake help build");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Build targets"));

    // lake help query
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["help", "query"])
        .output()
        .expect("run lake help query");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Build targets and output results"));

    // lake help env
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["help", "env"])
        .output()
        .expect("run lake help env");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Execute a command in Lake's environment"));

    // lake --json help query
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--json", "help", "query"])
        .output()
        .expect("run lake --json help query");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("utf8 stdout");
    assert!(stdout.contains("Build targets and output results"));

    // lake --fln-census-unknown help
    let output = Command::new(env!("CARGO_BIN_EXE_lake"))
        .args(["--fln-census-unknown", "help"])
        .output()
        .expect("run lake --fln-census-unknown help");
    assert_eq!(output.status.code(), Some(1));
    let stderr = String::from_utf8(output.stderr).expect("utf8 stderr");
    assert!(stderr.contains("unknown option"));
}
