#![forbid(unsafe_code)]

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn timeline_binary() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-timeline"))
}

fn event(direction: &str, message: &str) -> Vec<u8> {
    let body = format!(
        "{{\"schema\":\"fln.lsp-interleaved-event/1\",\"direction\":{},\"message\":{message}}}",
        fln_server::json_string(direction)
    );
    let mut framed = Vec::new();
    fln_server::transport::write_message(&mut framed, body.as_bytes()).unwrap();
    framed
}

fn timeline(events: &[(&str, &str)]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for (direction, message) in events {
        bytes.extend(event(direction, message));
    }
    bytes
}

fn valid_events() -> Vec<(&'static str, &'static str)> {
    vec![
        (
            "client",
            r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
        ),
        (
            "server",
            r#"{"jsonrpc":"2.0","id":"init","result":{"capabilities":{}}}"#,
        ),
        (
            "client",
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        ),
        (
            "client",
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A.lean","version":1,"text":"def a := 1"}}}"#,
        ),
        (
            "client",
            r#"{"jsonrpc":"2.0","id":"wait","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///A.lean","version":1}}"#,
        ),
        (
            "client",
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"wait"}}"#,
        ),
        (
            "server",
            r#"{"jsonrpc":"2.0","id":"wait","error":{"code":-32800,"message":"request cancelled"}}"#,
        ),
        (
            "client",
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
        ),
        (
            "server",
            r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
        ),
        (
            "client",
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ),
    ]
}

fn scratch(label: &str) -> PathBuf {
    let nanos = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .expect("system clock is after the Unix epoch")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "franken-lean-lsp-timeline-{label}-{}-{nanos}.frames",
        std::process::id()
    ))
}

fn write_timeline(label: &str, bytes: &[u8]) -> PathBuf {
    let path = scratch(label);
    let _ = fs::remove_file(&path);
    fs::write(&path, bytes).unwrap();
    path
}

#[test]
fn help_and_usage_are_side_effect_free() {
    let help = timeline_binary().arg("--help").output().unwrap();
    assert!(help.status.success());
    assert!(help.stderr.is_empty());
    let stdout = String::from_utf8(help.stdout).unwrap();
    assert!(stdout.starts_with("Usage: fln-lsp-timeline"));
    assert!(stdout.contains("fln.lsp-interleaved-event/1"));
    assert!(stdout.contains("initialized follows the initialize response"));
    assert!(stdout.contains("not a wall-clock"));

    let missing = timeline_binary().output().unwrap();
    assert_eq!(missing.status.code(), Some(2));
    assert!(missing.stdout.is_empty());
    assert!(
        String::from_utf8(missing.stderr)
            .unwrap()
            .contains("exactly one TIMELINE path is required")
    );
}

#[test]
fn valid_interleaving_emits_cross_stream_causality_receipt() {
    let path = write_timeline("valid", &timeline(&valid_events()));
    let output = timeline_binary().arg(&path).output().unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"fln.lsp-interleaved-timeline/1\""));
    assert!(stdout.contains("\"eventSchema\":\"fln.lsp-interleaved-event/1\""));
    assert!(stdout.contains("\"causalitySchema\":\"fln.lsp-cross-stream-causality/1\""));
    assert!(stdout.contains("\"events\":10"));
    assert!(stdout.contains("\"initializeRequestEvent\":1"));
    assert!(stdout.contains("\"initializeResponseEvent\":2"));
    assert!(stdout.contains("\"initializedEvent\":3"));
    assert!(stdout.contains("\"shutdownRequestEvent\":8"));
    assert!(stdout.contains("\"shutdownResponseEvent\":9"));
    assert!(stdout.contains("\"exitEvent\":10"));
    assert!(stdout.contains("\"responsesBeforeRequests\":0"));
    assert!(stdout.contains("\"cancellations\":1"));
    assert!(stdout.contains("\"cancellationsBeforeResponse\":1"));
    assert!(stdout.contains("\"cancellationsAfterResponse\":0"));
    assert!(stdout.contains("\"cancelledTargetRequestCancelledResponses\":1"));
    assert!(stdout.contains(
        "\"correlation\":{\"schema\":\"fln.lsp-client-server-correlation/5\""
    ));
    fs::remove_file(path).unwrap();
}

#[test]
fn cancellation_after_response_fails_without_a_receipt() {
    let mut events = valid_events();
    events[5] = (
        "server",
        r#"{"jsonrpc":"2.0","id":"wait","result":{}}"#,
    );
    events[6] = (
        "client",
        r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"wait"}}"#,
    );
    let path = write_timeline("late-cancel", &timeline(&events));
    let output = timeline_binary().arg(&path).output().unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert!(output.stdout.is_empty());
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .contains("after its server response event")
    );
    fs::remove_file(path).unwrap();
}

#[test]
fn option_terminator_allows_a_real_dash_prefixed_path() {
    let directory = scratch("dash-path-directory").with_extension("");
    fs::create_dir(&directory).unwrap();
    let relative = PathBuf::from("--session.timeline");
    fs::write(directory.join(&relative), timeline(&valid_events())).unwrap();

    let output = timeline_binary()
        .current_dir(&directory)
        .args(["--", "--session.timeline"])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::remove_dir_all(directory).unwrap();
}
