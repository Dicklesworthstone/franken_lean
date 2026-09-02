#![forbid(unsafe_code)]

use std::process::Command;

fn replay() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-replay"))
}

#[test]
fn help_is_side_effect_free_and_uses_stdout() {
    let output = replay().arg("--help").output().unwrap();
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with("Usage: fln-lsp-replay"));
    assert!(stdout.contains("--expect"));
    assert!(stdout.contains("--output"));
}

#[test]
fn missing_input_is_a_usage_refusal() {
    let output = replay().output().unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("missing input transcript"));
    assert!(stderr.contains("Usage: fln-lsp-replay"));
}

#[test]
fn duplicate_singleton_options_are_refused_before_io() {
    for arguments in [
        ["--expect", "a", "--expect", "b", "input"],
        ["--output", "a", "--output", "b", "input"],
    ] {
        let output = replay().args(arguments).output().unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8(output.stderr)
            .unwrap()
            .contains("may be supplied at most once"));
    }
}
