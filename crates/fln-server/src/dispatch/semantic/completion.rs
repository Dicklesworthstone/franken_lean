//! Bounded plain-text completion edits, tied to the accepted source snapshot.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompletionItem {
    pub label: String,
    pub replacement: String,
}

pub(super) fn result(
    items: Vec<CompletionItem>,
    range: Range<usize>,
    is_incomplete: bool,
    query: Query<'_>,
) -> Result<String, &'static str> {
    if items.len() > 256 || range.start > query.offset || query.offset > range.end {
        return Err("semantic completion response exceeds its bounds");
    }
    let start = position(query.text, range.start)?;
    let end = position(query.text, range.end)?;
    // LSP completion TextEdits are single-line ranges containing the cursor.
    // Byte/position round-trips exclude the interior of CRLF as well as split
    // UTF-8 scalars; neither can be repaired by silently moving the edit.
    if start.line != end.line
        || json::byte_offset(query.text, start)? != range.start
        || json::byte_offset(query.text, end)? != range.end
    {
        return Err("completion range has no exact single-line LSP mapping");
    }
    let mut bytes = 0usize;
    for item in &items {
        bytes = bytes
            .checked_add(item.label.len())
            .and_then(|n| n.checked_add(item.replacement.len()))
            .filter(|n| *n <= MAX_RESULT_BYTES / 16)
            .ok_or("semantic completion response exceeds its output budget")?;
        if item.label.is_empty()
            || item.replacement.is_empty()
            || item.label.chars().any(char::is_control)
            || item.replacement.chars().any(char::is_control)
        {
            return Err("completion requires nonempty plain-text labels and replacements");
        }
    }
    let edit_range = format!(
        "{{\"start\":{{\"line\":{},\"character\":{}}},\"end\":{{\"line\":{},\"character\":{}}}}}",
        start.line, start.character, end.line, end.character,
    );
    let mut result = format!("{{\"isIncomplete\":{is_incomplete},\"items\":[");
    for (index, item) in items.into_iter().enumerate() {
        if index != 0 {
            result.push(',');
        }
        // The replacement is also the filter spelling so explicitly typed
        // `_root_.` prefixes remain visible to client-side filtering.
        let replacement = crate::json_string(&item.replacement);
        result.push_str(&format!(
            "{{\"label\":{},\"kind\":21,\"insertTextFormat\":1,\"filterText\":{},\"textEdit\":{{\"range\":{},\"newText\":{}}}}}",
            crate::json_string(&item.label), replacement, edit_range, replacement,
        ));
    }
    result.push_str("]}");
    if result.len() > MAX_RESULT_BYTES {
        return Err("semantic completion response exceeds its wire budget");
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn query(text: &str, offset: usize) -> Query<'_> {
        Query {
            kind: QueryKind::Completion,
            uri: "file:///Main.lean",
            version: 7,
            text,
            offset,
        }
    }
    fn item() -> CompletionItem {
        CompletionItem {
            label: "value".into(),
            replacement: "_root_.value".into(),
        }
    }

    #[test]
    fn completion_text_edits_preserve_utf16_crlf_and_incomplete_status() {
        let text = "-- private source\r\n😀val\r\n";
        let start = text.find("val").unwrap();
        let answer = result(vec![item()], start..start + 3, true, query(text, start + 3)).unwrap();
        assert_eq!(
            answer,
            r#"{"isIncomplete":true,"items":[{"label":"value","kind":21,"insertTextFormat":1,"filterText":"_root_.value","textEdit":{"range":{"start":{"line":1,"character":2},"end":{"line":1,"character":5}},"newText":"_root_.value"}}]}"#
        );
        assert!(!answer.contains("private source"));
    }

    #[test]
    fn completion_ranges_must_contain_the_cursor_and_have_exact_boundaries() {
        let text = "😀val\r\nx";
        for range in [
            0..2,
            1..7,
            4..6,
            8..9,
            4..8,
            4..10,
            0..99,
            Range { start: 9, end: 4 },
        ] {
            assert!(
                result(vec![item()], range.clone(), false, query(text, 7)).is_err(),
                "{range:?}"
            );
        }
        assert!(result(vec![item()], 4..7, false, query(text, 7)).is_ok());
    }

    #[test]
    fn completion_strings_are_escaped_and_counts_and_bytes_are_bounded() {
        let special = CompletionItem {
            label: "a\"\\b".into(),
            replacement: "a\"\\b".into(),
        };
        let out = result(vec![special], 0..1, false, query("x", 1)).unwrap();
        assert!(out.contains(r#""label":"a\"\\b""#));
        assert!(result(vec![item(); 257], 0..1, false, query("x", 1)).is_err());
        let large = CompletionItem {
            label: "x".repeat(MAX_RESULT_BYTES / 16),
            replacement: "x".into(),
        };
        assert!(result(vec![large], 0..1, false, query("x", 1)).is_err());
        for replacement in ["", "x\ny", "x\0y"] {
            assert!(
                result(
                    vec![CompletionItem {
                        label: "x".into(),
                        replacement: replacement.into()
                    }],
                    0..1,
                    false,
                    query("x", 1)
                )
                .is_err()
            );
        }
    }

    #[test]
    fn empty_results_and_query_kind_mismatches_remain_distinct() {
        assert_eq!(
            result(Vec::new(), 0..1, false, query("x", 1)).unwrap(),
            r#"{"isIncomplete":false,"items":[]}"#
        );
        assert!(result_json(Answer::Goals { goals: Vec::new() }, query("x", 1)).is_err());
        assert!(
            result_json(
                Answer::Completion {
                    items: vec![item()],
                    range: 0..1,
                    is_incomplete: false
                },
                Query {
                    kind: QueryKind::Hover,
                    ..query("x", 1)
                }
            )
            .is_err()
        );
    }

    struct Provider {
        enabled: bool,
        answer: Result<Option<Answer>, String>,
        seen: Vec<(QueryKind, i64, usize, String)>,
    }
    impl CheckSource for Provider {
        fn semantic_queries(&self) -> bool {
            self.enabled
        }
        fn check(&mut self, uri: &str, _: &str, _: &[OpenDocumentSource<'_>]) -> Vec<String> {
            vec![format!(
                "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
                crate::json_string(uri)
            )]
        }
        fn query(
            &mut self,
            q: Query<'_>,
            _: &[OpenDocumentSource<'_>],
        ) -> Result<Option<Answer>, String> {
            self.seen
                .push((q.kind, q.version, q.offset, q.text.to_owned()));
            self.answer.clone()
        }
    }
    fn provider(answer: Result<Option<Answer>, String>) -> Provider {
        Provider {
            enabled: true,
            answer,
            seen: Vec::new(),
        }
    }
    fn run(provider: &mut Provider, messages: &[&str]) -> String {
        let mut input = Vec::new();
        for message in [
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        ]
        .into_iter()
        .chain(messages.iter().copied())
        .chain([
            r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
            r#"{"jsonrpc":"2.0","method":"exit"}"#,
        ]) {
            transport::write_message(&mut input, message.as_bytes()).unwrap();
        }
        let mut output = Vec::new();
        assert!(
            super::super::super::serve_inner(
                &mut std::io::Cursor::new(input),
                &mut output,
                provider,
            )
            .unwrap()
            .clean
        );
        String::from_utf8(output).unwrap()
    }
    const OPEN: &str = r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Main.lean","version":7,"text":"😀val"}}}"#;
    const REQUEST: &str = r#"{"jsonrpc":"2.0","id":"completion","method":"textDocument/completion","params":{"textDocument":{"uri":"file:///Main.lean"},"position":{"line":0,"character":5}}}"#;

    #[test]
    fn dispatcher_routes_completion_with_the_accepted_source_and_coordinates() {
        let mut p = provider(Ok(Some(Answer::Completion {
            items: vec![item()],
            range: 4..7,
            is_incomplete: false,
        })));
        let out = run(&mut p, &[OPEN, REQUEST]);
        assert!(out.contains(
            r#""completionProvider":{"resolveProvider":false,"triggerCharacters":["."]}"#
        ));
        assert!(out.contains(r#""id":"completion","result":{"isIncomplete":false,"items":["#));
        assert_eq!(p.seen, [(QueryKind::Completion, 7, 7, "😀val".to_owned())]);
    }

    #[test]
    fn invalid_positions_closed_documents_and_unavailable_sources_never_reach_provider() {
        let mut p = provider(Ok(None));
        let out = run(
            &mut p,
            &[
                OPEN,
                r#"{"jsonrpc":"2.0","id":"split","method":"textDocument/completion","params":{"textDocument":{"uri":"file:///Main.lean"},"position":{"line":0,"character":1}}}"#,
                r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///Main.lean"}}}"#,
                REQUEST,
            ],
        );
        assert!(p.seen.is_empty());
        assert!(out.contains(r#""id":"split","error":{"code":-32602"#));
        assert!(out.contains(r#""id":"completion","result":null"#));
        let out = run(
            &mut p,
            &[
                OPEN,
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Main.lean","version":8},"contentChanges":null}}"#,
                REQUEST,
            ],
        );
        assert!(p.seen.is_empty());
        assert!(out.contains(r#""id":"completion","error":{"code":-32803"#));
    }

    #[test]
    fn legacy_embedders_do_not_advertise_or_execute_completion() {
        let mut p = provider(Ok(None));
        p.enabled = false;
        let out = run(&mut p, &[OPEN, REQUEST]);
        assert!(p.seen.is_empty());
        assert!(!out.contains("completionProvider"));
        assert!(out.contains(r#""id":"completion","result":null"#));
    }

    #[test]
    fn failed_or_mismatched_completion_providers_return_errors_not_empty_lists() {
        for answer in [
            Err("checked prefix did not complete".to_owned()),
            Ok(Some(Answer::Goals { goals: Vec::new() })),
        ] {
            let mut p = provider(answer);
            let out = run(&mut p, &[OPEN, REQUEST]);
            assert_eq!(p.seen.len(), 1);
            assert!(out.contains(r#""id":"completion","error":{"code":-32803"#));
            assert!(!out.contains(r#""id":"completion","result"#));
        }
    }
}
