//! Definition transport tests include the real dispatcher, not just serialization.
use super::*;
use std::io::Cursor;

fn query() -> Query<'static> {
    Query { kind: QueryKind::Definition, uri: "file:///Main.lean", version: 7, text: "value", offset: 0 }
}
fn definition(uri: &str, source: &str, range: Range<usize>) -> Answer {
    Answer::Definition { uri: uri.to_owned(), source: source.to_owned(), range }
}

#[test]
fn locations_use_target_utf16_and_crlf_coordinates_without_leaking_source() {
    let source = "-- private source\r\nα😀value";
    let start = source.find("value").unwrap();
    let result = result_json(definition("file:///Lib%20One.lean", source, start..start + 5), query()).unwrap();
    assert_eq!(result, r#"{"uri":"file:///Lib%20One.lean","range":{"start":{"line":1,"character":3},"end":{"line":1,"character":8}}}"#);
    assert!(!result.contains("private source"));
    assert!(!result.contains("%2520"));
}

#[test]
fn malformed_empty_split_and_unrepresentable_target_ranges_refuse() {
    for range in [0..0, Range { start: 5, end: 1 }, 0..100, 1..4, 4..5] {
        assert!(result_json(definition("file:///Lib.lean", "😀\r\nx", range), query()).is_err());
    }
    for uri in ["", "file:///bad\n.lean"] {
        assert!(result_json(definition(uri, "x", 0..1), query()).is_err());
    }
    assert!(result_json(definition(&"x".repeat(16 * 1024 + 1), "x", 0..1), query()).is_err());
    assert!(result_json(definition("file:///Lib.lean", &"x".repeat(MAX_RESULT_BYTES + 1), 0..1), query()).is_err());
}

#[test]
fn same_document_targets_and_query_kinds_cannot_be_substituted() {
    assert!(result_json(definition(query().uri, "stale", 0..1), query()).is_err());
    assert!(result_json(Answer::Goals { goals: Vec::new() }, query()).is_err());
    assert!(result_json(definition("file:///Lib.lean", "x", 0..1), Query { kind: QueryKind::Hover, ..query() }).is_err());
    assert!(result_json(definition(query().uri, "value", 0..5), query()).is_ok());
}

#[test]
fn open_target_authority_rejects_stale_and_unavailable_import_snapshots() {
    let target = definition("file:///Lib.lean", "current", 0..7);
    for text in [Some("stale"), None] {
        assert!(validate_target_source(&target, &[OpenDocumentSource {
            uri: "file:///Lib.lean", version: 2, text,
        }]).is_err());
    }
    assert!(validate_target_source(&target, &[OpenDocumentSource {
        uri: "file:///Lib.lean", version: 2, text: Some("current"),
    }]).is_ok());
}

struct Provider {
    enabled: bool,
    answer: Result<Option<Answer>, String>,
    seen: Vec<(QueryKind, i64, usize, String)>,
}
impl CheckSource for Provider {
    fn semantic_queries(&self) -> bool { self.enabled }
    fn check(&mut self, uri: &str, _: &str, _: &[OpenDocumentSource<'_>]) -> Vec<String> {
        vec![format!("{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}", crate::json_string(uri))]
    }
    fn query(&mut self, q: Query<'_>, _: &[OpenDocumentSource<'_>]) -> Result<Option<Answer>, String> {
        self.seen.push((q.kind, q.version, q.offset, q.text.to_owned()));
        self.answer.clone()
    }
}
fn run(provider: &mut Provider, messages: &[&str]) -> String {
    let mut input = Vec::new();
    for message in [
        r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
    ].into_iter().chain(messages.iter().copied()).chain([
        r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        r#"{"jsonrpc":"2.0","method":"exit"}"#,
    ]) {
        transport::write_message(&mut input, message.as_bytes()).unwrap();
    }
    let mut output = Vec::new();
    assert!(super::super::serve_inner(&mut Cursor::new(input), &mut output, provider).unwrap().clean);
    String::from_utf8(output).unwrap()
}
fn provider(answer: Result<Option<Answer>, String>) -> Provider {
    Provider { enabled: true, answer, seen: Vec::new() }
}
const OPEN: &str = r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Main.lean","version":7,"text":"😀value"}}}"#;
const REQUEST: &str = r#"{"jsonrpc":"2.0","id":"definition","method":"textDocument/definition","params":{"textDocument":{"uri":"file:///Main.lean"},"position":{"line":0,"character":2}}}"#;

#[test]
fn dispatcher_routes_definition_with_the_accepted_version_and_byte_offset() {
    let mut p = provider(Ok(Some(definition("file:///Lib.lean", "value", 0..5))));
    let out = run(&mut p, &[OPEN, REQUEST]);
    assert!(out.contains(r#""definitionProvider":true"#));
    assert!(out.contains(r#""id":"definition","result":{"uri":"file:///Lib.lean""#));
    assert_eq!(p.seen, vec![(QueryKind::Definition, 7, 4, "😀value".to_owned())]);
}

#[test]
fn dispatcher_does_not_query_invalid_surrogate_positions_or_closed_documents() {
    let mut p = provider(Ok(None));
    let out = run(&mut p, &[
        OPEN,
        r#"{"jsonrpc":"2.0","id":"split","method":"textDocument/definition","params":{"textDocument":{"uri":"file:///Main.lean"},"position":{"line":0,"character":1}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///Main.lean"}}}"#,
        REQUEST,
    ]);
    assert!(p.seen.is_empty());
    assert!(out.contains(r#""id":"split","error":{"code":-32602"#));
    assert!(out.contains(r#""id":"definition","result":null"#));
}

#[test]
fn unavailable_open_import_prevents_a_provider_from_returning_disk_locations() {
    let mut p = provider(Ok(Some(definition("file:///Lib.lean", "disk", 0..4))));
    let out = run(&mut p, &[
        OPEN,
        r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Lib.lean","version":1,"text":"unsaved"}}}"#,
        r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Lib.lean","version":2},"contentChanges":null}}"#,
        REQUEST,
    ]);
    assert_eq!(p.seen.len(), 1);
    assert!(out.contains(r#""id":"definition","error":{"code":-32803"#));
    assert!(!out.contains(r#""id":"definition","result"#));
}

#[test]
fn legacy_embedders_keep_null_results_without_advertising_navigation() {
    let mut p = provider(Ok(Some(definition("file:///Lib.lean", "value", 0..5))));
    p.enabled = false;
    let out = run(&mut p, &[OPEN, REQUEST]);
    assert!(p.seen.is_empty());
    assert!(!out.contains(r#""definitionProvider":true"#));
    assert!(out.contains(r#""id":"definition","result":null"#));
}

#[test]
fn provider_failure_is_a_typed_error_not_a_no_target_result() {
    let mut p = provider(Err("checked import did not complete".to_owned()));
    let out = run(&mut p, &[OPEN, REQUEST]);
    assert_eq!(p.seen.len(), 1);
    assert!(out.contains(r#""id":"definition","error":{"code":-32803"#));
    assert!(out.contains("checked import did not complete"));
}
