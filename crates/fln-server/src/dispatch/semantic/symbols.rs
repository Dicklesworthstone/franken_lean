//! Exact document outline coordinates, with the pin's declaration symbol kind.
use super::*;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocumentSymbol {
    pub name: String,
    pub range: Range<usize>,
    pub selection_range: Range<usize>,
}

pub(super) fn payload_bytes(symbols: &[DocumentSymbol]) -> Result<usize, &'static str> {
    if symbols.len() > 4096 {
        return Err("document symbols exceed their count budget");
    }
    symbols.iter().try_fold(0usize, |bytes, symbol| {
        if symbol.name.is_empty() || symbol.name.chars().any(char::is_control) {
            return Err("document symbol names must be nonempty plain text");
        }
        bytes
            .checked_add(symbol.name.len())
            .and_then(|bytes| bytes.checked_add(128))
            .filter(|bytes| *bytes <= MAX_RESULT_BYTES / 2)
            .ok_or("document symbols exceed their payload budget")
    })
}

fn range_json(text: &str, range: &Range<usize>) -> Result<String, &'static str> {
    if range.start >= range.end {
        return Err("document symbol range is empty or inverted");
    }
    let start = position(text, range.start)?;
    let end = position(text, range.end)?;
    if json::byte_offset(text, start)? != range.start || json::byte_offset(text, end)? != range.end
    {
        return Err("document symbol range has no exact LSP coordinate mapping");
    }
    Ok(format!(
        "{{\"start\":{{\"line\":{},\"character\":{}}},\"end\":{{\"line\":{},\"character\":{}}}}}",
        start.line, start.character, end.line, end.character,
    ))
}

pub(super) fn result(
    symbols: Vec<DocumentSymbol>,
    query: Query<'_>,
) -> Result<String, &'static str> {
    payload_bytes(&symbols)?;
    // Coordinate conversions scan prefixes of the source. Bound total work,
    // not merely the number of rows, before any repeated scans or serialization.
    if query
        .text
        .len()
        .checked_mul(symbols.len())
        .is_none_or(|work| work > 64 * 1024 * 1024)
    {
        return Err("document symbol coordinate work exceeds its budget");
    }
    let mut result = String::from("[");
    let mut previous = 0;
    for (index, symbol) in symbols.into_iter().enumerate() {
        if symbol.range.start > symbol.selection_range.start
            || symbol.range.end < symbol.selection_range.end
            || (index > 0 && symbol.range.start < previous)
        {
            return Err("document symbol selection is outside its declaration or source order");
        }
        previous = symbol.range.start;
        let range = range_json(query.text, &symbol.range)?;
        let selection = range_json(query.text, &symbol.selection_range)?;
        if index != 0 {
            result.push(',');
        }
        // Lean's native outline reports declarations as SymbolKind.method (6).
        // Qualified names preserve scope without synthesizing namespace nodes.
        result.push_str(&format!(
            "{{\"name\":{},\"kind\":6,\"range\":{range},\"selectionRange\":{selection}}}",
            crate::json_string(&symbol.name),
        ));
    }
    result.push(']');
    if result.len() > MAX_RESULT_BYTES {
        return Err("document symbols exceed their wire budget");
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn query(text: &str) -> Query<'_> {
        Query {
            kind: QueryKind::DocumentSymbols,
            uri: "file:///Main.lean",
            version: 1,
            text,
            offset: 0,
        }
    }
    fn symbol(range: Range<usize>, selection_range: Range<usize>) -> DocumentSymbol {
        DocumentSymbol {
            name: "Outer.Inner.value".into(),
            range,
            selection_range,
        }
    }

    #[test]
    fn outline_coordinates_use_original_utf16_and_crlf_bytes() {
        let text = "-- 😀\r\ndef value : Nat := 1\r\n";
        let at = text.find("def").unwrap();
        let out = result(
            vec![symbol(at..text.len() - 2, at + 4..at + 9)],
            query(text),
        )
        .unwrap();
        assert_eq!(
            out,
            r#"[{"name":"Outer.Inner.value","kind":6,"range":{"start":{"line":1,"character":0},"end":{"line":1,"character":20}},"selectionRange":{"start":{"line":1,"character":4},"end":{"line":1,"character":9}}}]"#
        );
        assert!(!out.contains("😀"));
    }

    #[test]
    fn invalid_symbol_ranges_and_payloads_refuse_the_whole_answer() {
        let text = "😀x\r\ny";
        for candidate in [
            symbol(0..text.len(), 1..4),
            symbol(0..text.len(), 0..99),
            symbol(0..5, 5..6),
            symbol(0..6, 4..5),
            symbol(0..0, 0..0),
        ] {
            assert!(result(vec![candidate], query(text)).is_err());
        }
        assert!(result(vec![symbol(0..1, 0..1); 4097], query("x")).is_err());
        let mut bad = symbol(0..1, 0..1);
        bad.name = "x\ny".into();
        assert!(result(vec![bad], query("x")).is_err());
        assert_eq!(result(Vec::new(), query("x")).unwrap(), "[]");
    }

    struct Provider {
        answer: Result<Option<Answer>, String>,
        seen: Vec<(i64, String)>,
    }
    impl CheckSource for Provider {
        fn semantic_queries(&self) -> bool {
            true
        }
        fn check(&mut self, _: &str, _: &str, _: &[OpenDocumentSource<'_>]) -> Vec<String> {
            Vec::new()
        }
        fn query(
            &mut self,
            query: Query<'_>,
            _: &[OpenDocumentSource<'_>],
        ) -> Result<Option<Answer>, String> {
            assert_eq!(query.kind, QueryKind::DocumentSymbols);
            assert_eq!(query.offset, 0);
            self.seen.push((query.version, query.text.into()));
            self.answer.clone()
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
                provider
            )
            .unwrap()
            .clean
        );
        String::from_utf8(output).unwrap()
    }
    const OPEN: &str = r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///Main.lean","version":1,"text":"x"}}}"#;
    const REQUEST: &str = r#"{"jsonrpc":"2.0","id":"outline","method":"textDocument/documentSymbol","params":{"textDocument":{"uri":"file:///Main.lean"}}}"#;

    #[test]
    fn outline_requests_need_no_position_and_follow_the_accepted_version() {
        let mut provider = Provider {
            answer: Ok(Some(Answer::DocumentSymbols {
                symbols: vec![symbol(0..1, 0..1)],
            })),
            seen: Vec::new(),
        };
        let out = run(
            &mut provider,
            &[
                OPEN,
                REQUEST,
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Main.lean","version":2},"contentChanges":[{"text":"y"}]}}"#,
                REQUEST,
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Main.lean","version":1},"contentChanges":[{"text":"stale"}]}}"#,
                REQUEST,
                r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///Main.lean"}}}"#,
                REQUEST,
            ],
        );
        assert!(out.contains(r#""documentSymbolProvider":true"#));
        assert_eq!(
            provider.seen,
            [(1, "x".into()), (2, "y".into()), (2, "y".into())]
        );
        assert_eq!(
            out.matches(r#""id":"outline","result":[{"name":"Outer.Inner.value""#)
                .count(),
            3
        );
        assert!(out.contains(r#""id":"outline","result":null"#));
    }

    #[test]
    fn unavailable_documents_and_wrong_provider_answers_never_become_empty_outlines() {
        let mut provider = Provider {
            answer: Ok(Some(Answer::DocumentSymbols {
                symbols: Vec::new(),
            })),
            seen: Vec::new(),
        };
        let out = run(
            &mut provider,
            &[
                OPEN,
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///Main.lean","version":2},"contentChanges":null}}"#,
                REQUEST,
            ],
        );
        assert!(provider.seen.is_empty());
        assert!(out.contains(r#""id":"outline","error":{"code":-32803"#));
        for answer in [
            Err("checked document failed".into()),
            Ok(Some(Answer::Goals { goals: Vec::new() })),
        ] {
            let mut provider = Provider {
                answer,
                seen: Vec::new(),
            };
            let out = run(&mut provider, &[OPEN, REQUEST]);
            assert!(out.contains(r#""id":"outline","error":{"code":-32803"#));
            assert!(!out.contains(r#""id":"outline","result":[]"#));
        }
    }
}
