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

/// Sort the bounded set of endpoints, then visit the source once. Declaration
/// ranges may overlap, so their ends need not follow their source-ordered starts.
/// Keep endpoint identities to restore the provider's original result order.
fn coordinates(
    text: &str,
    symbols: &[DocumentSymbol],
    max_source_bytes: usize,
) -> Result<Vec<[json::Position; 4]>, &'static str> {
    let mut endpoints = Vec::with_capacity(symbols.len() * 4);
    let mut previous = 0;
    for (index, symbol) in symbols.iter().enumerate() {
        if symbol.range.start >= symbol.range.end
            || symbol.selection_range.start >= symbol.selection_range.end
        {
            return Err("document symbol range is empty or inverted");
        }
        if symbol.range.start > symbol.selection_range.start
            || symbol.range.end < symbol.selection_range.end
            || (index > 0 && symbol.range.start < previous)
        {
            return Err("document symbol selection is outside its declaration or source order");
        }
        previous = symbol.range.start;
        for (boundary, offset) in [
            symbol.range.start,
            symbol.range.end,
            symbol.selection_range.start,
            symbol.selection_range.end,
        ]
        .into_iter()
        .enumerate()
        {
            if offset > text.len() || !text.is_char_boundary(offset) {
                return Err("semantic range is outside the accepted source");
            }
            // There is no LSP position between the two bytes of CRLF. Reject
            // it before scanning, rather than rounding to the following line.
            if offset > 0
                && text.as_bytes()[offset - 1] == b'\r'
                && text.as_bytes().get(offset) == Some(&b'\n')
            {
                return Err("document symbol range has no exact LSP coordinate mapping");
            }
            endpoints.push((offset, index, boundary));
        }
    }
    endpoints.sort_unstable();
    if endpoints
        .last()
        .is_some_and(|(offset, _, _)| *offset > max_source_bytes)
    {
        return Err("document symbol coordinate work exceeds its budget");
    }
    let mut current = json::Position {
        line: 0,
        character: 0,
    };
    let mut result = vec![[current; 4]; symbols.len()];
    let mut chars = text.chars().peekable();
    let mut consumed = 0;
    for (offset, index, boundary) in endpoints {
        while consumed < offset {
            let c = chars.next().ok_or("document symbol source ended early")?;
            consumed += c.len_utf8();
            if c == '\r' || c == '\n' {
                if c == '\r' && chars.peek() == Some(&'\n') {
                    chars.next();
                    consumed += 1;
                }
                current.line = current
                    .line
                    .checked_add(1)
                    .ok_or("semantic line overflow")?;
                current.character = 0;
            } else {
                current.character = current
                    .character
                    .checked_add(c.len_utf16() as u32)
                    .ok_or("semantic column overflow")?;
            }
        }
        result[index][boundary] = current;
    }
    Ok(result)
}

fn range_json(start: json::Position, end: json::Position) -> String {
    format!(
        "{{\"start\":{{\"line\":{},\"character\":{}}},\"end\":{{\"line\":{},\"character\":{}}}}}",
        start.line, start.character, end.line, end.character,
    )
}

pub(super) fn result(
    symbols: Vec<DocumentSymbol>,
    query: Query<'_>,
) -> Result<String, &'static str> {
    payload_bytes(&symbols)?;
    // The count/payload bounds above also bound endpoint sorting and storage.
    // Source traversal has its own budget, independent of the number of symbols.
    let coordinates = coordinates(query.text, &symbols, 64 * 1024 * 1024)?;
    let mut result = String::from("[");
    for (index, (symbol, [start, end, selection_start, selection_end])) in
        symbols.into_iter().zip(coordinates).enumerate()
    {
        let range = range_json(start, end);
        let selection = range_json(selection_start, selection_end);
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
    fn a_large_document_outline_does_not_multiply_source_work_by_symbol_count() {
        let mut text = String::new();
        let mut symbols = Vec::new();
        for index in 0..2000 {
            let name = format!("declaration_{index}");
            let start = text.len();
            text.push_str(&format!("def {name} : Nat := {index}\r\n"));
            symbols.push(DocumentSymbol {
                selection_range: start + 4..start + 4 + name.len(),
                name,
                range: start..text.len() - 2,
            });
        }
        assert!(text.len() < 1024 * 1024);
        assert!(text.len() * symbols.len() > 64 * 1024 * 1024);
        let out = result(symbols, query(&text)).expect("one bounded pass over the source");
        assert_eq!(out.matches("\"kind\":6").count(), 2000);
        assert!(out.contains(
            "\"name\":\"declaration_1999\",\"kind\":6,\"range\":{\"start\":{\"line\":1999,\"character\":0}"
        ));
    }

    #[test]
    fn batched_coordinates_match_exact_single_range_conversion() {
        for text in ["abc", "α😀\r\nβ\rγ\n终", "\r\r\n\n😀", "x\0y"] {
            for start in 0..text.len() {
                for end in start + 1..=text.len() {
                    let expected = (|| {
                        let a = position(text, start)?;
                        let b = position(text, end)?;
                        if json::byte_offset(text, a)? != start
                            || json::byte_offset(text, b)? != end
                        {
                            return Err("not an exact source boundary");
                        }
                        Ok([a, b, a, b])
                    })();
                    let actual = coordinates(text, &[symbol(start..end, start..end)], text.len());
                    match (expected, actual) {
                        (Ok(expected), Ok(actual)) => {
                            for (expected, actual) in expected.iter().zip(&actual[0]) {
                                assert_eq!(
                                    (actual.line, actual.character),
                                    (expected.line, expected.character),
                                    "{text:?} at {start}..{end}"
                                );
                            }
                        }
                        (Err(_), Err(_)) => {}
                        _ => panic!("coordinate agreement at {start}..{end} in {text:?}"),
                    }
                }
            }
        }
    }

    #[test]
    fn overlapping_ranges_keep_their_identity_and_share_one_scan_budget() {
        let text = "α😀\r\nnested\nz";
        let nested = text.find("nested").unwrap();
        let symbols = [
            symbol(0..text.len(), 0..2),
            symbol(nested..nested + 6, nested..nested + 6),
        ];
        let positions = coordinates(text, &symbols, text.len()).unwrap();
        assert_eq!((positions[0][1].line, positions[0][1].character), (2, 1));
        assert_eq!((positions[1][0].line, positions[1][0].character), (1, 0));
        assert_eq!((positions[1][1].line, positions[1][1].character), (1, 6));
        assert!(matches!(
            coordinates(text, &symbols, text.len() - 1),
            Err("document symbol coordinate work exceeds its budget")
        ));
        assert!(coordinates(text, &[], 0).unwrap().is_empty());
        assert!(coordinates(text, &[symbols[1].clone(), symbols[0].clone()], text.len()).is_err());
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
