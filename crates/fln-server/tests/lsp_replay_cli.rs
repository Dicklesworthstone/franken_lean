#![forbid(unsafe_code)]

use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_PATH: AtomicU64 = AtomicU64::new(0);

fn replay() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-replay"))
}

fn temporary_path(label: &str) -> PathBuf {
    let sequence = NEXT_PATH.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "franken-lean-lsp-replay-{label}-{}-{sequence}",
        std::process::id()
    ))
}

fn frame(body: &str) -> Vec<u8> {
    let mut bytes = Vec::new();
    fln_server::transport::write_message(&mut bytes, body.as_bytes()).unwrap();
    bytes
}

fn transcript(role_inversion: bool) -> Vec<u8> {
    let mut bytes = Vec::new();
    for body in [
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        if role_inversion {
            r#"{"jsonrpc":"2.0","id":"bad-open","method":"textDocument/didOpen","params":{}}"#
        } else {
            r#"{"jsonrpc":"2.0","id":"hover","method":"textDocument/hover","params":{}}"#
        },
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    ] {
        bytes.extend(frame(body));
    }
    bytes
}

fn write_transcript(label: &str, role_inversion: bool) -> PathBuf {
    let path = temporary_path(label);
    fs::write(&path, transcript(role_inversion)).unwrap();
    path
}

#[test]
fn help_is_side_effect_free_and_uses_stdout() {
    let output = replay().arg("--help").output().unwrap();
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.starts_with("Usage: fln-lsp-replay"));
    assert!(stdout.contains("--client-lifecycle"));
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
        vec!["--expect", "a", "--expect", "b", "input"],
        vec!["--output", "a", "--output", "b", "input"],
        vec!["--client-lifecycle", "--client-lifecycle", "input"],
    ] {
        let output = replay().args(arguments).output().unwrap();
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stdout.is_empty());
        assert!(
            String::from_utf8(output.stderr)
                .unwrap()
                .contains("may be supplied at most once")
        );
    }
}

#[test]
fn lifecycle_preflight_accepts_a_clean_client_stream() {
    let input = write_transcript("clean", false);
    let output = replay()
        .args(["--client-lifecycle", input.to_str().unwrap()])
        .output()
        .unwrap();
    fs::remove_file(&input).unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    assert!(output.stdout.starts_with(b"Content-Length: "));
    assert!(
        output
            .stdout
            .windows(b"FrankenLean".len())
            .any(|window| window == b"FrankenLean")
    );
}

#[test]
fn lifecycle_preflight_refuses_before_stdout_or_output_publication() {
    let input = write_transcript("role-inversion", true);
    let output_path = temporary_path("must-not-exist");
    let output = replay()
        .args([
            "--client-lifecycle",
            "--output",
            output_path.to_str().unwrap(),
            input.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    fs::remove_file(&input).unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(!output_path.exists());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("client lifecycle validation failed"));
    assert!(stderr.contains("notification-only method"));
}
