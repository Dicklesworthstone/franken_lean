#![forbid(unsafe_code)]

use std::io::Write;
use std::process::{Command, Stdio};

fn inspector() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-inspect"))
}

fn frame(body: &str) -> Vec<u8> {
    let mut bytes = Vec::new();
    fln_server::transport::write_message(&mut bytes, body.as_bytes()).unwrap();
    bytes
}

#[test]
fn help_is_side_effect_free_and_uses_stdout() {
    let output = inspector().arg("--help").output().unwrap();
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with("Usage: fln-lsp-inspect"));
    assert!(stdout.contains("--max-frames"));
    assert!(stdout.contains("Parameter contents and source text are not"));
    assert!(stdout.contains("params container kind"));
}

#[test]
fn missing_input_is_a_usage_refusal() {
    let output = inspector().output().unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("missing input transcript"));
    assert!(stderr.contains("Usage: fln-lsp-inspect"));
}

#[test]
fn empty_stdin_succeeds_without_decorative_output() {
    let mut child = inspector()
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    drop(child.stdin.take());
    let output = child.wait_with_output().unwrap();
    assert!(output.status.success());
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
}

#[test]
fn frame_rows_expose_kind_without_parameter_contents() {
    let secret = "secret-source-must-not-leak";
    let body = format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":\"file:///Main.lean\",\"version\":1,\"text\":\"{secret}\"}}}}}}"
    );
    let mut child = inspector()
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .as_mut()
        .expect("piped inspector stdin")
        .write_all(&frame(&body))
        .unwrap();
    drop(child.stdin.take());
    let output = child.wait_with_output().unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"fln.lsp-frame/2\""));
    assert!(stdout.contains("\"method\":\"textDocument/didOpen\""));
    assert!(stdout.contains("\"paramsKind\":\"object\""));
    assert!(!stdout.contains(secret));
    assert!(!stdout.contains("\"params\":"));
}
