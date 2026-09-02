#![forbid(unsafe_code)]

use std::io::{BufReader, Cursor};

use fln_server::dispatch::serve;
use fln_server::transport::{read_message, write_message};

fn framed_session(document_uri: &str) -> Vec<u8> {
    let mut input = Vec::new();
    for message in [
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#.to_string(),
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#.to_string(),
        format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"version\":1,\"text\":\"source\"}}}}}}",
            fln_server::json_string(document_uri)
        ),
        format!(
            "{{\"jsonrpc\":\"2.0\",\"id\":\"wait\",\"method\":\"textDocument/waitForDiagnostics\",\"params\":{{\"uri\":{},\"version\":1}}}}",
            fln_server::json_string(document_uri)
        ),
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown"}"#.to_string(),
        r#"{"jsonrpc":"2.0","method":"exit"}"#.to_string(),
    ] {
        write_message(&mut input, message.as_bytes()).expect("frame protocol input");
    }
    input
}

fn run_with_callback(callback_message: String) -> Vec<String> {
    let input = framed_session("file:///Contract.lean");
    let mut reader = BufReader::new(Cursor::new(input));
    let mut output = Vec::new();
    let outcome = serve(&mut reader, &mut output, &mut |_, _| {
        vec![callback_message.clone()]
    })
    .expect("serve diagnostic-outcome contract session");
    assert!(outcome.clean);

    let mut reader = BufReader::new(Cursor::new(output));
    let mut messages = Vec::new();
    while let Some(body) = read_message(&mut reader).expect("decode server output") {
        messages.push(String::from_utf8(body).expect("server output is UTF-8 JSON"));
    }
    messages
}

fn joined(messages: &[String]) -> String {
    messages.join("\n")
}

#[test]
fn incoherent_outcome_tuples_are_withheld_and_faulted() {
    let cases = [
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"wrong-schema","outcome":"complete","authority":true,"marker":"wrong-schema-marker"}}"#,
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"inconclusive","authority":true,"marker":"inconclusive-true-marker"}}"#,
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":false,"marker":"complete-false-marker"}}"#,
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"future","authority":true,"marker":"future-outcome-marker"}}"#,
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"\u0061uthority":false,"marker":"duplicate-authority-marker"}}"#,
    ];

    for callback in cases {
        let messages = run_with_callback(callback.to_string());
        let output = joined(&messages);
        assert!(output.contains("discarded malformed diagnostic callback output"));
        assert!(output.contains("diagnostic-callback-terminal-message"));
        assert!(output.contains("\"id\":\"wait\",\"error\":{\"code\":-32803"));
        assert!(
            !output.contains("-marker"),
            "forwarded invalid callback: {callback}"
        );
    }
}

#[test]
fn nested_decoys_cannot_promote_a_non_authoritative_outcome() {
    let messages = run_with_callback(
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"inconclusive","authority":false,"detail":{"schema":"wrong","outcome":"complete","authority":true},"message":"\"authority\":true"}}"#.to_string(),
    );
    let output = joined(&messages);

    assert!(output.contains("\"outcome\":\"inconclusive\""));
    assert!(output.contains("\"authority\":false"));
    assert!(output.contains("\"id\":\"wait\",\"error\":{\"code\":-32803"));
    assert!(!output.contains("diagnostic-callback-terminal-message"));
}

#[test]
fn nested_decoys_cannot_demote_an_authoritative_complete_outcome() {
    let messages = run_with_callback(
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":0,"detail":{"schema":"wrong","outcome":"internal_fault","authority":false},"message":"\"authority\":false"}}"#.to_string(),
    );
    let output = joined(&messages);

    assert!(output.contains("\"outcome\":\"complete\""));
    assert!(output.contains("\"id\":\"wait\",\"result\":{}"));
    assert!(!output.contains("diagnostic-callback-terminal-message"));
}
