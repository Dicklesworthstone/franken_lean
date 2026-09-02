#![forbid(unsafe_code)]

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn correlator() -> Command {
    Command::new(env!("CARGO_BIN_EXE_fln-lsp-correlate"))
}

fn frame(body: &str) -> Vec<u8> {
    let mut framed = Vec::new();
    fln_server::transport::write_message(&mut framed, body.as_bytes()).unwrap();
    framed
}

fn framed(bodies: &[&str]) -> Vec<u8> {
    let mut bytes = Vec::new();
    for body in bodies {
        bytes.extend(frame(body));
    }
    bytes
}

fn client() -> Vec<u8> {
    framed(&[
        r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A.lean","version":1,"text":"def a := 1"}}}"#,
        r#"{"jsonrpc":"2.0","id":1.25e2,"method":"textDocument/hover","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///A.lean"}}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    ])
}

fn server() -> Vec<u8> {
    framed(&[
        r#"{"jsonrpc":"2.0","id":"init","result":{"capabilities":{}}}"#,
        r#"{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"textDocument":{"uri":"file:///A.lean"},"processing":[{"kind":"processing"}]}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///A.lean","diagnostics":[]}}"#,
        r#"{"jsonrpc":"2.0","id":1.25e2,"error":{"code":-32601,"message":"method not found"}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
    ])
}

fn scratch(scenario: &str, name: &str) -> PathBuf {
    std::env::temp_dir().join(format!(
        "franken-lean-correlate-{scenario}-{name}-{}",
        std::process::id()
    ))
}

fn write_pair(scenario: &str, client: &[u8], server: &[u8]) -> (PathBuf, PathBuf) {
    let client_path = scratch(scenario, "client.frames");
    let server_path = scratch(scenario, "server.frames");
    let _ = fs::remove_file(&client_path);
    let _ = fs::remove_file(&server_path);
    fs::write(&client_path, client).unwrap();
    fs::write(&server_path, server).unwrap();
    (client_path, server_path)
}

#[test]
fn help_and_usage_refusals_are_side_effect_free() {
    let help = correlator().arg("--help").output().unwrap();
    assert!(help.status.success());
    assert!(help.stderr.is_empty());
    let stdout = String::from_utf8(help.stdout).unwrap();
    assert!(stdout.starts_with("Usage: fln-lsp-correlate"));
    assert!(stdout.contains("Number lexemes"));
    assert!(stdout.contains("string IDs compare by decoded value"));
    assert!(stdout.contains("not cross-stream timing"));

    let missing = correlator().output().unwrap();
    assert_eq!(missing.status.code(), Some(2));
    assert!(missing.stdout.is_empty());
    assert!(String::from_utf8(missing.stderr)
        .unwrap()
        .contains("exactly two transcripts are required"));
}

#[test]
fn successful_join_emits_zero_unmatched_resource_receipt() {
    let (client_path, server_path) = write_pair("success", &client(), &server());
    let output = correlator()
        .arg(&client_path)
        .arg(&server_path)
        .output()
        .unwrap();
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"schema\":\"fln.lsp-client-server-correlation/2\""));
    assert!(stdout.contains("\"idPolicy\":\"number-lexeme-string-value-v1\""));
    assert!(stdout.contains("\"clientRequests\":3"));
    assert!(stdout.contains("\"serverResponses\":3"));
    assert!(stdout.contains("\"matchedResponses\":3"));
    assert!(stdout.contains("\"unmatchedClientRequests\":0"));
    assert!(stdout.contains("\"unsolicitedServerResponses\":0"));
    assert!(stdout.contains("\"resultResponses\":2"));
    assert!(stdout.contains("\"errorResponses\":1"));
    assert!(stdout.contains("\"clientWireBytes\":"));
    assert!(stdout.contains("\"serverWireBytes\":"));
    assert!(stdout.contains("\"serverMetadataBytes\":"));
    assert!(stdout.contains("\"clientRequestIdBytes\":"));
    assert!(stdout.contains("\"serverResponseIdBytes\":"));
    assert!(stdout.contains("\"requestIdCountCeiling\":262144"));
    assert!(stdout.contains("\"requestIdByteCeiling\":33554432"));
    assert!(stdout.contains("\"documentsOpened\":1"));
    assert!(stdout.contains("\"documentsClosed\":1"));

    fs::remove_file(client_path).unwrap();
    fs::remove_file(server_path).unwrap();
}

#[test]
fn equivalent_string_escape_spelling_correlates_by_decoded_value() {
    let client = framed(&[
        r#"{"jsonrpc":"2.0","id":"\u0069nit","method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
        r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
    ]);
    let server = framed(&[
        r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
    ]);
    let (client_path, server_path) = write_pair("escaped-string", &client, &server);
    let output = correlator()
        .arg(&client_path)
        .arg(&server_path)
        .output()
        .unwrap();
    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    assert!(String::from_utf8(output.stdout)
        .unwrap()
        .contains("\"matchedResponses\":2"));
    fs::remove_file(client_path).unwrap();
    fs::remove_file(server_path).unwrap();
}

#[test]
fn missing_response_and_numeric_normalization_fail_without_receipt() {
    let missing_server = framed(&[
        r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
        r#"{"jsonrpc":"2.0","id":1.25e2,"result":null}"#,
    ]);
    let (client_path, server_path) = write_pair("failure", &client(), &missing_server);
    let missing = correlator()
        .arg(&client_path)
        .arg(&server_path)
        .output()
        .unwrap();
    assert_eq!(missing.status.code(), Some(1));
    assert!(missing.stdout.is_empty());
    assert!(String::from_utf8(missing.stderr)
        .unwrap()
        .contains("has no server response"));
    fs::remove_file(&server_path).unwrap();

    let normalized_server = framed(&[
        r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
        r#"{"jsonrpc":"2.0","id":125,"result":null}"#,
        r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
    ]);
    fs::write(&server_path, normalized_server).unwrap();
    let normalized = correlator()
        .arg(&client_path)
        .arg(&server_path)
        .output()
        .unwrap();
    assert_eq!(normalized.status.code(), Some(1));
    assert!(normalized.stdout.is_empty());
    assert!(String::from_utf8(normalized.stderr)
        .unwrap()
        .contains("unknown canonical request ID 125"));

    fs::remove_file(client_path).unwrap();
    fs::remove_file(server_path).unwrap();
}
