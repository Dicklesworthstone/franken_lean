#![forbid(unsafe_code)]

use std::io::Write;
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
        .expect("piped validator stdin")
        .write_all(framed.as_bytes())
        .unwrap();
    drop(child.stdin.take());
    let output = child.wait_with_output().unwrap();
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
