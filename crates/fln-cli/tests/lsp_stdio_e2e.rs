#![forbid(unsafe_code)]

use std::io::{BufReader, Cursor, Write};
use std::process::{Command, Stdio};

fn push_frame(stream: &mut Vec<u8>, body: &str) {
    fln_server::transport::write_message(stream, body.as_bytes()).unwrap();
}

fn run_session(
    binary: &str,
    arguments: &[&str],
    bodies: &[&str],
) -> (std::process::ExitStatus, Vec<String>, String) {
    let mut input = Vec::new();
    for body in bodies {
        push_frame(&mut input, body);
    }

    let mut child = Command::new(binary)
        .args(arguments)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.as_mut().unwrap().write_all(&input).unwrap();
    drop(child.stdin.take());
    let output = child.wait_with_output().unwrap();

    let mut reader = BufReader::new(Cursor::new(output.stdout));
    let mut messages = Vec::new();
    while let Some(body) = fln_server::transport::read_message(&mut reader).unwrap() {
        messages.push(String::from_utf8(body).unwrap());
    }
    (
        output.status,
        messages,
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn run_fln_session(bodies: &[&str]) -> (std::process::ExitStatus, Vec<String>, String) {
    run_session(env!("CARGO_BIN_EXE_fln"), &["serve-lsp"], bodies)
}

#[test]
fn real_fln_server_executes_full_document_lifecycle() {
    let (status, messages, stderr) = run_fln_session(&[
        r#"{"jsonrpc":"2.0","id":"init-1","method":"initialize","params":{"capabilities":{"general":{"positionEncodings":["utf-16"]}}}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/FrankenLeanE2E.lean","languageId":"lean4","version":1,"text":"def answer := 42"}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///tmp/FrankenLeanE2E.lean","version":2},"contentChanges":[{"text":"def answer := 43"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///tmp/FrankenLeanE2E.lean"}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///tmp/FrankenLeanE2E.lean"}}}"#,
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]);

    assert!(status.success(), "stderr: {stderr}");
    assert!(
        stderr.is_empty(),
        "successful protocol output leaked to stderr: {stderr}"
    );
    assert!(messages.iter().any(|message| {
        message.contains("\"id\":\"init-1\"")
            && message.contains("\"positionEncoding\":\"utf-16\"")
            && message.contains("\"change\":1")
    }));
    assert!(messages.iter().any(|message| {
        message.contains("\"id\":99") && message.contains("\"result\":null")
    }));

    let progress_started = messages
        .iter()
        .filter(|message| message.contains("$/lean/fileProgress") && message.contains("\"kind\":1"))
        .count();
    let progress_finished = messages
        .iter()
        .filter(|message| {
            message.contains("$/lean/fileProgress") && message.contains("\"processing\":[]")
        })
        .count();
    assert_eq!(progress_started, 3, "messages: {messages:#?}");
    assert_eq!(progress_finished, 3, "messages: {messages:#?}");

    let document_uri = "file:///tmp/FrankenLeanE2E.lean";
    assert!(messages.iter().any(|message| {
        message.contains("textDocument/publishDiagnostics")
            && message.contains(document_uri)
            && message.contains("\"diagnostics\":[]")
    }));
    assert!(messages.last().is_some_and(|message| {
        message.contains("\"id\":99") && message.contains("\"result\":null")
    }));
}

#[test]
fn installed_lsp_doors_preserve_encoded_unsaved_document_identity() {
    const DOCUMENT_URI: &str = "file:///tmp/FrankenLean%20Unsaved.lean";
    let session = [
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{"capabilities":{"general":{"positionEncodings":["utf-16"]}}}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/FrankenLean%20Unsaved.lean","languageId":"lean4","version":1,"text":"def answer : Nat := missing"}}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ];

    for (label, binary, arguments) in [
        ("fln", env!("CARGO_BIN_EXE_fln"), &["serve-lsp"][..]),
        ("lean", env!("CARGO_BIN_EXE_lean"), &["--server"][..]),
    ] {
        let (status, messages, stderr) = run_session(binary, arguments, &session);
        assert!(status.success(), "{label} stderr: {stderr}");
        assert!(stderr.is_empty(), "{label} leaked stderr: {stderr}");

        let publications = messages
            .iter()
            .filter(|message| message.contains("textDocument/publishDiagnostics"))
            .collect::<Vec<_>>();
        let diagnostic = publications
            .iter()
            .copied()
            .find(|message| !message.contains("\"diagnostics\":[]"))
            .unwrap_or_else(|| panic!("{label} emitted no nonempty diagnostic: {messages:#?}"));
        assert!(
            diagnostic.contains(&format!("\"uri\":\"{DOCUMENT_URI}\"")),
            "{label} changed the document identity: {diagnostic}"
        );
        assert!(diagnostic.contains("\"causeClass\":\"engine-error\""));
        assert!(
            publications
                .iter()
                .all(|message| message.contains(DOCUMENT_URI)),
            "{label} split one document into multiple URI identities: {publications:#?}"
        );
        assert!(
            messages.iter().all(|message| !message.contains("%2520")),
            "{label} double-encoded the already escaped URI: {messages:#?}"
        );
    }
}

#[test]
fn fln_serve_lsp_rejects_trailing_arguments_before_transport_startup() {
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["serve-lsp", "unexpected"])
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stdout.is_empty());
    assert_eq!(
        String::from_utf8(output.stderr).unwrap(),
        "fln: serve-lsp does not accept arguments\n"
    );
}

// A syntax error must publish a diagnostic at the real source position, in LSP
// UTF-16 columns — not the file-head fallback the compatibility `project` entry
// produced. This exercises the full CLI bridge: the parser's byte offset is
// rebased into the file, converted to a Lean line/codepoint column, and the
// exact unsaved document is passed to `project_with_sources` so the codepoint
// column becomes a UTF-16 code unit.
//
// The document is:
//   line 1 (0-based 0): `def ok : Nat := 1`   — valid, so a good command does
//                                                not suppress a later error
//   line 2 (0-based 1): `def s : String := "🤖"@more`
// The offending `@` sits after `def s : String := "🤖"`. Its codepoint column is
// 21 (`def s : String := "` = 19, `🤖` = 1 codepoint, `"` = 1); its UTF-16 column
// is 22 because `🤖` is two UTF-16 code units. Asserting 22 (not 21) proves the
// source-aware conversion actually ran — a regression to `project` would leave
// the raw codepoint column 21, and the pre-fix code hardcoded line 0 column 0.
#[test]
fn syntax_error_reports_a_real_utf16_source_position() {
    let uri = "file:///tmp/PositionedError.lean";
    let (status, messages, stderr) = run_fln_session(&[
        r#"{"jsonrpc":"2.0","id":"init-1","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///tmp/PositionedError.lean","languageId":"lean4","version":1,"text":"def ok : Nat := 1\ndef s : String := \"🤖\"@more"}}}"#,
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]);

    assert!(status.success(), "stderr: {stderr}");
    let diagnostic = messages
        .iter()
        .find(|message| message.contains("publishDiagnostics") && message.contains(uri))
        .unwrap_or_else(|| panic!("no publishDiagnostics for {uri}: {messages:#?}"));

    assert!(
        diagnostic.contains(r#""start":{"line":1,"character":22}"#),
        "expected the diagnostic at line 1 (0-based) UTF-16 character 22, got: {diagnostic}"
    );
    // The pre-fix behaviour: a file-head fallback at line 0, column 0.
    assert!(
        !diagnostic.contains(r#""start":{"line":0,"character":0}"#),
        "diagnostic regressed to the hardcoded file-head position: {diagnostic}"
    );
    // The unconverted codepoint column would be 21; UTF-16 conversion makes it 22.
    assert!(
        !diagnostic.contains(r#""line":1,"character":21}"#),
        "diagnostic kept the raw codepoint column; source-aware UTF-16 conversion did not run: {diagnostic}"
    );
}
