#![forbid(unsafe_code)]

use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

fn validator() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-validate"))
}

fn replay() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-replay"))
}

fn frame(body: &str) -> Vec<u8> {
    let mut framed = Vec::new();
    fln_server::transport::write_message(&mut framed, body.as_bytes()).unwrap();
    framed
}

fn transcript(events: &[&str]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for body in std::iter::once(
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
    )
    .chain(std::iter::once(
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
    ))
    .chain(events.iter().copied())
    .chain([
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    ]) {
        bytes.extend(frame(body));
    }
    bytes
}

fn run_stdin(command: &mut Command, input: &[u8]) -> std::process::Output {
    let mut child = command
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

fn scratch(name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "franken-lean-{name}-{}",
        std::process::id()
    ))
}

#[test]
fn validator_emits_document_semantic_session_receipt() {
    let input = transcript(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A.lean","version":1,"text":"def a := 1"}}}"#,
        r#"{"jsonrpc":"2.0","id":"wait","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///A.lean","version":2}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///A.lean","version":2},"contentChanges":[{"text":"def a := 2"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///A.lean"}}}"#,
        r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"wait"}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///A.lean"}}}"#,
    ]);
    let output = run_stdin(
        validator().args(["--client-session", "-"]),
        &input,
    );
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"fln.lsp-client-session/1\""));
    assert!(stdout.contains("\"documentsOpened\":1"));
    assert!(stdout.contains("\"documentsChanged\":1"));
    assert!(stdout.contains("\"documentsSaved\":1"));
    assert!(stdout.contains("\"documentsClosed\":1"));
    assert!(stdout.contains("\"diagnosticWaits\":1"));
    assert!(stdout.contains("\"cancellations\":1"));
    assert!(stdout.contains("\"finalOpenDocuments\":0"));
}

#[test]
fn lifecycle_and_session_modes_have_deliberately_different_authority() {
    let input = transcript(&[
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Missing.lean","version":2},"contentChanges":[{"text":"source"}]}}"#,
    ]);

    let lifecycle = run_stdin(
        validator().args(["--client-lifecycle", "-"]),
        &input,
    );
    assert!(lifecycle.status.success());
    assert!(lifecycle.stderr.is_empty());
    assert!(String::from_utf8(lifecycle.stdout)
        .unwrap()
        .contains("fln.lsp-client-lifecycle/1"));

    let session = run_stdin(
        validator().args(["--client-session", "-"]),
        &input,
    );
    assert_eq!(session.status.code(), Some(1));
    assert!(session.stdout.is_empty());
    assert!(String::from_utf8(session.stderr)
        .unwrap()
        .contains("didChange targets unopened document"));
}

#[test]
fn replay_session_preflight_fails_before_output_publication() {
    let input_path = scratch("invalid-session.frames");
    let output_path = scratch("invalid-session.server.frames");
    let _ = fs::remove_file(&input_path);
    let _ = fs::remove_file(&output_path);
    fs::write(
        &input_path,
        transcript(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///Missing.lean"}}}"#,
        ]),
    )
    .unwrap();

    let output = replay()
        .arg("--client-session")
        .arg("--output")
        .arg(&output_path)
        .arg(&input_path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(!output_path.exists());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("client session validation failed"));
    assert!(stderr.contains("didSave targets unopened document"));

    fs::remove_file(input_path).unwrap();
}
