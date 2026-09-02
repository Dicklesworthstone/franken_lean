#![forbid(unsafe_code)]

use std::io::Write;
use std::process::{Command, Output, Stdio};

fn validator() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-validate"))
}

fn framed(body: &str) -> Vec<u8> {
    let mut bytes = Vec::new();
    fln_server::transport::write_message(&mut bytes, body.as_bytes()).unwrap();
    bytes
}

fn lifecycle() -> Vec<u8> {
    let mut bytes = Vec::new();
    for body in [
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":"hover","method":"textDocument/hover","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    ] {
        bytes.extend(framed(body));
    }
    bytes
}

fn run_stdin(arguments: &[&str], input: &[u8]) -> Output {
    let mut child = validator()
        .args(arguments)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .as_mut()
        .expect("piped validator stdin")
        .write_all(input)
        .unwrap();
    drop(child.stdin.take());
    child.wait_with_output().unwrap()
}

#[test]
fn help_is_side_effect_free_and_uses_stdout() {
    let output = validator().arg("--help").output().unwrap();
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with("Usage: fln-lsp-validate"));
    assert!(stdout.contains("INPUT=-"));
    assert!(stdout.contains("--client-lifecycle"));
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
fn duplicate_lifecycle_mode_is_a_usage_refusal() {
    let output = validator()
        .args(["--client-lifecycle", "--client-lifecycle", "-"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("may be supplied at most once"));
}

#[test]
fn empty_stdin_is_a_valid_syntax_only_transcript() {
    let output = run_stdin(&["-"], &[]);
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        "{\"schema\":\"fln.lsp-transcript-validation/2\",\"frames\":0,\"requests\":0,\"notifications\":0,\"wireBytes\":0,\"bodyBytes\":0}\n"
    );
}

#[test]
fn receipt_reports_complete_wire_bytes_including_extension_headers() {
    let body = r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#;
    let framed = format!(
        "X-Evidence: retained\r\nContent-Length: {}\r\n\r\n{}",
        body.len(),
        body
    );
    let output = run_stdin(&["-"], framed.as_bytes());
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    assert_eq!(
        String::from_utf8(output.stdout).unwrap(),
        format!(
            "{{\"schema\":\"fln.lsp-transcript-validation/2\",\"frames\":1,\"requests\":0,\"notifications\":1,\"wireBytes\":{},\"bodyBytes\":{}}}\n",
            framed.len(),
            body.len()
        )
    );
}

#[test]
fn lifecycle_mode_emits_exact_handshake_evidence() {
    let input = lifecycle();
    let output = run_stdin(&["--client-lifecycle", "-"], &input);
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"fln.lsp-client-lifecycle/1\""));
    assert!(stdout.contains("\"finalState\":\"exited\""));
    assert!(stdout.contains(&format!("\"wireBytes\":{}", input.len())));
    assert!(stdout.contains("\"initializeFrame\":1"));
    assert!(stdout.contains("\"initializedFrame\":2"));
    assert!(stdout.contains("\"shutdownFrame\":4"));
    assert!(stdout.contains("\"exitFrame\":5"));
}

#[test]
fn lifecycle_mode_refuses_empty_input_without_a_success_receipt() {
    let output = run_stdin(&["--client-lifecycle", "-"], &[]);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("expected exited"));
}

#[test]
fn lifecycle_mode_refuses_known_method_role_inversion() {
    let input = framed(r#"{"jsonrpc":"2.0","method":"initialize","params":{}}"#);
    let output = run_stdin(&["--client-lifecycle", "-"], &input);
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("request-only method"));
    assert!(stderr.contains("frame 1"));
}
