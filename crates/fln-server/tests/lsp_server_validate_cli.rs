#![forbid(unsafe_code)]

use std::io::Write;
use std::process::{Command, Stdio};

fn validator() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-server-validate"))
}

fn frame(body: &str) -> Vec<u8> {
    let mut framed = Vec::new();
    fln_server::transport::write_message(&mut framed, body.as_bytes()).unwrap();
    framed
}

fn run_stdin(input: &[u8]) -> std::process::Output {
    let mut child = validator()
        .arg("-")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .as_mut()
        .expect("piped stdin")
        .write_all(input)
        .unwrap();
    drop(child.stdin.take());
    child.wait_with_output().unwrap()
}

#[test]
fn help_and_missing_input_are_side_effect_free() {
    let help = validator().arg("--help").output().unwrap();
    assert!(help.status.success());
    assert!(help.stderr.is_empty());
    let stdout = String::from_utf8(help.stdout).unwrap();
    assert!(stdout.starts_with("Usage: fln-lsp-server-validate"));
    assert!(stdout.contains("server-initiated requests are refused"));
    assert!(stdout.contains("notification payloads are validated"));

    let missing = validator().output().unwrap();
    assert_eq!(missing.status.code(), Some(2));
    assert!(missing.stdout.is_empty());
    assert!(String::from_utf8(missing.stderr)
        .unwrap()
        .contains("missing server transcript"));
}

#[test]
fn mixed_server_stream_emits_schema_v3_resource_receipt() {
    let mut input = frame(r#"{"jsonrpc":"2.0","id":"init","result":{"capabilities":{}}}"#);
    input.extend(frame(
        r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///A.lean","version":null,"diagnostics":[]}}"#,
    ));
    input.extend(frame(
        r#"{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"textDocument":{"uri":"file:///A.lean"},"processing":[]}}"#,
    ));
    input.extend(frame(
        r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":3,"message":"ready"}}"#,
    ));
    input.extend(frame(
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":0}}"#,
    ));
    input.extend(frame(
        r#"{"jsonrpc":"2.0","id":1.25e2,"error":{"code":-32601,"message":"method not found"}}"#,
    ));

    let output = run_stdin(&input);
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"fln.lsp-server-transcript/3\""));
    assert!(stdout.contains("\"frames\":6"));
    assert!(stdout.contains("\"responses\":2"));
    assert!(stdout.contains("\"resultResponses\":1"));
    assert!(stdout.contains("\"errorResponses\":1"));
    assert!(stdout.contains("\"notifications\":4"));
    assert!(stdout.contains("\"diagnosticPublications\":1"));
    assert!(stdout.contains("\"diagnosticOutcomes\":1"));
    assert!(stdout.contains("\"fileProgressNotifications\":1"));
    assert!(stdout.contains("\"logMessages\":1"));
    assert!(stdout.contains("\"wireBytes\":"));
    assert!(stdout.contains("\"bodyBytes\":"));
    assert!(stdout.contains("\"metadataBytes\":"));
    assert!(stdout.contains("\"frameCeiling\":1000000"));
    assert!(stdout.contains("\"metadataByteCeiling\":33554432"));
}

#[test]
fn invalid_response_request_and_notification_fail_without_receipt() {
    for body in [
        r#"{"jsonrpc":"2.0","id":1,"result":null,"error":{"code":-1,"message":"ambiguous"}}"#,
        r#"{"jsonrpc":"2.0","id":1,"method":"workspace/configuration","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///A.lean","diagnostics":{}}}"#,
        r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":9,"message":"bad"}}"#,
    ] {
        let output = run_stdin(&frame(body));
        assert_eq!(output.status.code(), Some(1));
        assert!(output.stdout.is_empty());
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(
            stderr.contains("both result and error")
                || stderr.contains("server-initiated request")
                || stderr.contains("must be an array")
                || stderr.contains("from 1 through 4"),
            "{stderr}"
        );
    }
}
