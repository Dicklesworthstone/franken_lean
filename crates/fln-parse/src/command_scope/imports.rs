//! Header-only source import parsing over Vellum's real token stream.
//! No source is synthesized and the returned body offset names original bytes.
use super::*;

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
    let tokens = tokens(&view)?;
    let symbol = |index: usize, wanted: &str| {
        tokens.get(index).is_some_and(
            |token| matches!(&token.kind, TokenKind::Symbol(actual) if actual == wanted),
        )
    };
    let mut cursor = 0;
    let prelude = symbol(cursor, "prelude");
    if prelude {
        cursor += 1;
    }
    let mut imports = Vec::new();
    while symbol(cursor, "import") {
        cursor += 1;
        let begin = cursor;
        while let Some(LexedToken {
            kind: TokenKind::Ident(name),
            ..
        }) = tokens.get(cursor)
        {
            imports.push(name.clone());
            cursor += 1;
        }
        if cursor == begin {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: tokens.get(cursor).map_or(BytePos(source.len()), |token| {
                    view.to_original(token.extent.start())
                }),
                expected: NatDefinitionExpectation::ImportedModule,
            });
        }
    }
    let body_start = if cursor == 0 {
        BytePos(0)
    } else {
        tokens.get(cursor).map_or(BytePos(source.len()), |token| {
            view.to_original(token.extent.start())
        })
    };
    Ok(SourceHeader {
        imports,
        body_start,
        prelude,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

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
