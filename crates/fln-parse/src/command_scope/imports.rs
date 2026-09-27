//! Header-only source import parsing over Vellum's real token stream.
//! No source is synthesized and the returned body offset names original bytes.
use super::*;
use fln_syntax::token::lex_token;
use fln_syntax::trivia::scan_trivia;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceHeader {
    /// Exact structural module names, in source order, including repeated imports.
    pub imports: Vec<Name>,
    pub body_start: BytePos,
    /// The caller supplies the initial environment; this is not an implicit Init loader.
    pub prelude: bool,
}

/// Split plain `import A B` headers from the ordinary source-command body.
/// Comments, quoted names, BOM and CRLF use the same lexer/view as declarations.
/// New module-system visibility modifiers are deliberately not stripped or guessed.
pub fn parse_source_header(source: &[u8]) -> Result<SourceHeader, DefinitionParseError> {
    // SourceView normalizes line endings, but the underlying token table does
    // not consume a UTF-8 BOM. Strip it only at the file boundary and rebase
    // every returned offset and parser refusal to the original bytes.
    let bom_bytes = if source.starts_with(b"\xef\xbb\xbf") {
        3
    } else {
        0
    };
    let mut header = parse_header(&source[bom_bytes..])
        .map_err(|error| error.with_original_offset(BytePos(bom_bytes)))?;
    header.body_start.0 += bom_bytes;
    Ok(header)
}

fn parse_header(source: &[u8]) -> Result<SourceHeader, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    let table = table();
    // Import discovery is not whole-file validation. Once the first body token
    // is observed, do not lex its unfinished terms, comments, or later commands.
    // The ordinary body parser/checker still refuses those exact bytes when
    // checking the file; no recovered body is installed or called valid here.
    let first = next_header_token(&view, &table, BytePos(0))?;
    let (prelude, mut next) = match first {
        Some(token) if matches!(&token.kind, TokenKind::Symbol(s) if s == "prelude") => {
            (true, next_header_token(&view, &table, token.extent.end())?)
        }
        token => (false, token),
    };
    let mut imports = Vec::new();
    while let Some(LexedToken { kind: TokenKind::Symbol(symbol), extent }) = &next {
        if symbol != "import" {
            break;
        }
        next = next_header_token(&view, &table, extent.end())?;
        let begin = imports.len();
        while let Some(LexedToken {
            kind: TokenKind::Ident(name),
            extent,
        }) = &next
        {
            imports.push(name.clone());
            next = next_header_token(&view, &table, extent.end())?;
        }
        if imports.len() == begin {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: next.as_ref().map_or(BytePos(source.len()), |token| {
                    view.to_original(token.extent.start())
                }),
                expected: NatDefinitionExpectation::ImportedModule,
            });
        }
    }
    let body_start = if !prelude && imports.is_empty() {
        BytePos(0)
    } else {
        next.as_ref().map_or(BytePos(source.len()), |token| {
            view.to_original(token.extent.start())
        })
    };
    Ok(SourceHeader {
        imports,
        body_start,
        prelude,
    })
}

fn next_header_token(
    view: &SourceView,
    table: &TokenTable,
    from: BytePos,
) -> Result<Option<LexedToken>, DefinitionParseError> {
    let text = view.normalized();
    let at = scan_trivia(text, from).map_err(|error| NatDefinitionParseError::Lexical {
        diagnostics: vec![ParseDiagnostic {
            message: error.message(),
            at: view.to_original(error.at()),
        }],
    })?;
    if at.0 >= text.len_bytes() {
        return Ok(None);
    }
    lex_token(text, table, at)
        .map(Some)
        .map_err(|error| NatDefinitionParseError::Lexical {
            diagnostics: vec![ParseDiagnostic {
                message: error.message(),
                at: view.to_original(error.at()),
            }],
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unfinished_bodies_do_not_prevent_header_discovery_or_become_valid_files() {
        for body in [
            "def pending := \"unfinished",
            "def pending := /- unfinished",
            "def pending := \t",
            "def pending := 1\r",
        ] {
            let source = format!("prelude\nimport Real\n{body}");
            let header = parse_source_header(source.as_bytes()).unwrap();
            assert!(header.prelude);
            assert_eq!(header.imports, [Name::from_components(["Real"])]);
            assert_eq!(header.body_start.0, source.find("def pending").unwrap());
            assert!(partition(&source.as_bytes()[header.body_start.0..]).is_err(),
                "header discovery must not repair or validate the body: {source}");
        }
        let source = b"def pending := \"unfinished";
        let header = parse_source_header(source).unwrap();
        assert!(header.imports.is_empty());
        assert_eq!(header.body_start, BytePos(0));
    }

    #[test]
    fn streaming_headers_preserve_repeated_imports_bom_crlf_and_header_errors() {
        let source = "\u{feff}/- heading -/\r\nprelude\r\nimport A.B «C.D»\r\nimport A.B\r\ndef pending := \"unfinished";
        let header = parse_source_header(source.as_bytes()).unwrap();
        assert_eq!(header.imports, [Name::from_components(["A", "B"]),
            Name::from_components(["C.D"]), Name::from_components(["A", "B"])]);
        assert_eq!(header.body_start.0, source.find("def pending").unwrap());
        let source = "\u{feff}prelude\r\nimport 42\r\ndef pending := \"unfinished";
        let error = parse_source_header(source.as_bytes()).unwrap_err();
        assert_eq!(error.primary_offset(), Some(BytePos(source.find("42").unwrap())));
        for source in ["import «unfinished", "import /- unfinished", "import A\tB"] {
            assert!(parse_source_header(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn original_body_offsets_and_structural_names_survive_header_removal() {
        let source = "\u{feff}/- 🤖 import Fake -/\r\nprelude\r\nimport A.B «C.D»\r\nimport A.B\r\nnamespace Proof\r\ndef value := 1\r\nend Proof";
        let header = parse_source_header(source.as_bytes()).unwrap();
        assert!(header.prelude);
        assert_eq!(
            header.imports,
            [
                Name::from_components(["A", "B"]),
                Name::from_components(["C.D"]),
                Name::from_components(["A", "B"])
            ]
        );
        assert_eq!(header.body_start.0, source.find("namespace Proof").unwrap());
        assert_eq!(
            partition(&source.as_bytes()[header.body_start.0..])
                .unwrap()
                .len(),
            3
        );
    }

    #[test]
    fn import_looking_strings_and_comments_do_not_create_dependencies() {
        let source = "-- import Fake\ndef text := \"import Other\"";
        let header = parse_source_header(source.as_bytes()).unwrap();
        assert!(header.imports.is_empty());
        assert_eq!(header.body_start, BytePos(0));
        let header = parse_source_header(b"import Real /- trailing -/").unwrap();
        assert_eq!(header.imports, [Name::from_components(["Real"])]);
        assert_eq!(header.body_start.0, b"import Real /- trailing -/".len());
    }

    #[test]
    fn malformed_headers_are_not_silently_discarded() {
        for source in [
            "import",
            "import -- no name",
            "import 42",
            "import\nimport A",
        ] {
            assert!(parse_source_header(source.as_bytes()).is_err(), "{source}");
        }
        for source in ["public import A", "meta import A", "module\nimport A"] {
            assert_eq!(
                parse_source_header(source.as_bytes()).unwrap().body_start,
                BytePos(0)
            );
        }
    }
}
