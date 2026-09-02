#![forbid(unsafe_code)]

use std::process::{Command, Stdio};

fn validator() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-validate"))
}

#[test]
fn help_is_side_effect_free_and_uses_stdout() {
    let output = validator().arg("--help").output().unwrap();
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with("Usage: fln-lsp-validate"));
    assert!(stdout.contains("INPUT=-"));
}

#[test]
fn missing_input_is_a_usage_refusal() {
    let output = validator().output().unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("missing input transcript"));
    assert!(stderr.contains("Usage: fln-lsp-validate"));
}

#[test]
fn empty_stdin_is_a_valid_empty_transcript() {
    let mut child = validator()
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    drop(child.stdin.take());
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "{\"schema\":\"fln.lsp-transcript-validation/1\",\"frames\":0,\"requests\":0,\"notifications\":0,\"bodyBytes\":0}\n"
    );
}
