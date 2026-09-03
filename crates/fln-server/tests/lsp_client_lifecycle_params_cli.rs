#![forbid(unsafe_code)]

use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_PATH: AtomicU64 = AtomicU64::new(0);

fn validator() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-validate"))
}

fn replay() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-replay"))
}

fn temporary_path(label: &str) -> PathBuf {
    let sequence = NEXT_PATH.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "franken-lean-lsp-params-{label}-{}-{sequence}",
        std::process::id()
    ))
}

fn frame(body: &str) -> Vec<u8> {
    let mut bytes = Vec::new();
    fln_server::transport::write_message(&mut bytes, body.as_bytes()).unwrap();
    bytes
}

fn transcript(bodies: &[&str]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for body in bodies {
        bytes.extend(frame(body));
    }
    bytes
}

fn run_validator(arguments: &[&str], input: &[u8]) -> Output {
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
fn syntax_only_mode_preserves_parameter_shape_negative_fixtures() {
    let input = transcript(&[
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":[]}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    ]);
    let syntax = run_validator(&["-"], &input);
    assert!(syntax.status.success());
    assert!(syntax.stderr.is_empty());
    assert!(
        String::from_utf8(syntax.stdout)
            .unwrap()
            .contains("\"schema\":\"fln.lsp-transcript-validation/2\"")
    );

    let lifecycle = run_validator(&["--client-lifecycle", "-"], &input);
    assert_eq!(lifecycle.status.code(), Some(1));
    assert!(lifecycle.stdout.is_empty());
    let stderr = String::from_utf8(lifecycle.stderr).unwrap();
    assert!(stderr.contains("frame 1"));
    assert!(stderr.contains("requires object params"));
}

#[test]
fn lifecycle_mode_accepts_missing_shutdown_and_exit_params() {
    let input = transcript(&[
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]);
    let output = run_validator(&["--client-lifecycle", "-"], &input);
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"fln.lsp-client-lifecycle/1\""));
    assert!(stdout.contains("\"shutdownFrame\":3"));
    assert!(stdout.contains("\"exitFrame\":4"));
}

#[test]
fn replay_param_preflight_fails_before_output_publication() {
    let input_path = temporary_path("input");
    let output_path = temporary_path("output-must-not-exist");
    fs::write(
        &input_path,
        transcript(&[
            r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]),
    )
    .unwrap();

    let output = replay()
        .args([
            "--client-lifecycle",
            "--output",
            output_path.to_str().unwrap(),
            input_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    fs::remove_file(&input_path).unwrap();

    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(!output_path.exists());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("client lifecycle validation failed"));
    assert!(stderr.contains("shutdown"));
    assert!(stderr.contains("permits only missing or null params"));
}
