use std::io::BufReader;

use fln_server::dispatch::{ServerOutcome, serve};
use fln_server::transport::{read_message, write_message};

fn frame(output: &mut Vec<u8>, body: &str) {
    write_message(output, body.as_bytes()).expect("frame protocol message");
}

fn session() -> Vec<u8> {
    let mut input = Vec::new();
    for body in [
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Accounting.lean","languageId":"lean4","version":1,"text":"source"}}}"#,
        r#"{"jsonrpc":"2.0","id":"wait","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///Accounting.lean","version":1}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    ] {
        frame(&mut input, body);
    }
    input
}

fn run(outcome: &str) -> (ServerOutcome, Vec<String>) {
    let input = session();
    let mut reader = BufReader::new(input.as_slice());
    let mut output = Vec::new();
    let outcome_message = outcome.to_string();
    let result = serve(&mut reader, &mut output, &mut |_, _| {
        vec![outcome_message.clone()]
    })
    .expect("serve framed protocol session");

    let mut frames = Vec::new();
    let mut reader = BufReader::new(output.as_slice());
    while let Some(body) = read_message(&mut reader).expect("decode server output") {
        frames.push(String::from_utf8(body).expect("server emits UTF-8 JSON"));
    }
    (result, frames)
}

fn canonical_complete(count: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"$/lean/diagnosticOutcome\",\"params\":{{\"schema\":\"fln.diagnostic-projection/1\",\"outcome\":\"complete\",\"authority\":true,\"diagnosticCount\":{count}}}}}"
    )
}

fn assert_failed_accounting(message: &str) {
    let (outcome, frames) = run(message);
    assert!(outcome.clean);
    assert!(frames.iter().any(|frame| {
        frame.contains("\"id\":\"wait\"") && frame.contains("\"code\":-32803")
    }));
    assert!(frames.iter().any(|frame| {
        frame.contains("diagnostic-callback-terminal-message")
            && frame.contains("\"authority\":false")
    }));
    assert!(frames.iter().any(|frame| {
        frame.contains("textDocument/publishDiagnostics")
            && frame.contains("\"uri\":\"file:///Accounting.lean\"")
            && frame.contains("\"diagnostics\":[]")
    }));
    assert!(
        !frames.iter().any(|frame| frame == message),
        "invalid callback outcome must not be forwarded"
    );
}

#[test]
fn zero_count_complete_outcome_releases_wait() {
    let message = canonical_complete("0");
    let (outcome, frames) = run(&message);
    assert!(outcome.clean);
    assert!(frames.iter().any(|frame| frame == &message));
    assert!(frames.iter().any(|frame| {
        frame.contains("\"id\":\"wait\"") && frame.contains("\"result\":{}")
    }));
    assert!(!frames
        .iter()
        .any(|frame| frame.contains("diagnostic-callback-terminal-message")));
}

#[test]
fn complete_outcome_requires_exact_zero_accounting() {
    for message in [
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true}}"#.to_string(),
        canonical_complete("1"),
        canonical_complete("-0"),
        canonical_complete("0.0"),
        canonical_complete("\"0\""),
        canonical_complete("18446744073709551616"),
        r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":0,"\u0064iagnosticCount":0}}"#.to_string(),
    ] {
        assert_failed_accounting(&message);
    }
}

#[test]
fn non_authoritative_outcomes_cannot_claim_complete_accounting() {
    for outcome_name in ["inconclusive", "internal_fault"] {
        let message = format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"$/lean/diagnosticOutcome\",\"params\":{{\"schema\":\"fln.diagnostic-projection/1\",\"outcome\":\"{outcome_name}\",\"authority\":false,\"diagnosticCount\":0}}}}"
        );
        assert_failed_accounting(&message);
    }
}
