#![forbid(unsafe_code)]

use std::io::BufReader;

use fln_server::dispatch::{ServerOutcome, serve};
use fln_server::transport::{read_message, write_message};

const DOCUMENT_URI_BUDGET_BYTES: usize = 4 * 1024 * 1024;

fn frame(output: &mut Vec<u8>, body: &str) {
    write_message(output, body.as_bytes()).expect("frame protocol message");
}

fn run(messages: &[String]) -> (ServerOutcome, Vec<String>, Vec<String>) {
    let mut input = Vec::new();
    frame(
        &mut input,
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
    );
    frame(
        &mut input,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
    );
    for message in messages {
        frame(&mut input, message);
    }
    frame(
        &mut input,
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
    );
    frame(
        &mut input,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    );

    let mut checked = Vec::new();
    let mut reader = BufReader::new(input.as_slice());
    let mut output = Vec::new();
    let outcome = serve(&mut reader, &mut output, &mut |uri, _| {
        checked.push(uri.to_string());
        vec![format!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
            fln_server::json_string(uri)
        )]
    })
    .expect("serve bounded URI transcript");

    let mut frames = Vec::new();
    let mut reader = BufReader::new(output.as_slice());
    while let Some(body) = read_message(&mut reader).expect("decode server output") {
        frames.push(String::from_utf8(body).expect("server emits UTF-8 JSON"));
    }
    (outcome, frames, checked)
}

#[test]
fn oversized_uri_is_refused_without_poisoning_the_session() {
    let oversized_uri = "u".repeat(DOCUMENT_URI_BUDGET_BYTES + 1);
    let oversized_open = format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/didOpen\",\"params\":{{\"textDocument\":{{\"uri\":{},\"languageId\":\"lean4\",\"version\":1,\"text\":\"oversized-uri-source\"}}}}}}",
        fln_server::json_string(&oversized_uri)
    );
    let normal_open = r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Normal.lean","languageId":"lean4","version":1,"text":"normal-source"}}}"#.to_string();

    let (outcome, output, checked) = run(&[oversized_open, normal_open]);
    assert!(outcome.clean);
    assert_eq!(outcome.documents_opened, 1);
    assert_eq!(checked, vec!["file:///Normal.lean".to_string()]);
    assert!(output.iter().any(|message| {
        message.contains("window/logMessage")
            && message.contains("bounded open-document URI budget was reached")
    }));
    assert!(output.iter().any(|message| {
        message.contains("textDocument/publishDiagnostics")
            && message.contains("\"uri\":\"file:///Normal.lean\"")
    }));
}
