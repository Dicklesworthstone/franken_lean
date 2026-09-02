#![forbid(unsafe_code)]

use std::io::{BufReader, Cursor, Write};
use std::process::{Command, Stdio};

fn push_frame(stream: &mut Vec<u8>, body: &str) {
    fln_server::transport::write_message(stream, body.as_bytes()).unwrap();
}

fn run_session(bodies: &[&str]) -> (std::process::ExitStatus, Vec<String>, String) {
    let mut input = Vec::new();
    for body in bodies {
        push_frame(&mut input, body);
    }

    let mut child = Command::new(env!("CARGO_BIN_EXE_fln"))
        .arg("serve-lsp")
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

#[test]
fn real_fln_server_executes_full_document_lifecycle() {
    let (status, messages, stderr) = run_session(&[
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
    assert!(stderr.is_empty(), "successful protocol output leaked to stderr: {stderr}");
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
        .filter(|message| {
            message.contains("$/lean/fileProgress") && message.contains("\"kind\":1")
        })
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
