//! Header-only source import parsing over Vellum's real token stream.
//! No source is synthesized and the returned body offset names original bytes.
use super::*;
use fln_syntax::token::{TokenTable, lex_token};
use fln_syntax::trivia::scan_trivia;

/// One explicit import directive. Modifier positions name the original source
/// bytes, so a consumer that does not implement their semantics can refuse the
/// modifier itself instead of silently treating it as an ordinary import.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceImport {
    pub module: Name,
    pub import_at: BytePos,
    pub module_at: BytePos,
    pub public_at: Option<BytePos>,
    pub meta_at: Option<BytePos>,
    pub all_at: Option<BytePos>,
}

/// Invalid combinations diagnosed by the pin's `Parser.parseHeader`, after the
/// header grammar has recognized the directive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleHeaderError {
    PublicWithoutModule,
    MetaWithoutModule,
    AllWithoutModule,
    PublicImportAll,
}

impl std::fmt::Display for ModuleHeaderError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::PublicWithoutModule => "cannot use `public import` without `module`",
            Self::MetaWithoutModule => "cannot use `meta import` without `module`",
            Self::AllWithoutModule => "cannot use `import all` without `module`",
            Self::PublicImportAll => "cannot use `all` with `public import`",
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceHeader {
    /// Exact structural module names, in source order, including repeated imports.
    pub imports: Vec<Name>,
    /// Explicit directives only; an implicit Init dependency is not source text.
    pub import_specs: Vec<SourceImport>,
    pub body_start: BytePos,
    /// The caller supplies the initial environment; this is not an implicit Init loader.
    pub prelude: bool,
    /// `module` enables the pin's private-by-default module semantics. Recognizing
    /// it does not authorize a consumer to discard that visibility boundary.
    pub module_system: bool,
    pub module_at: Option<BytePos>,
}

/// Split the pin's `module? prelude? import*` header from the command body.
/// Each directive imports one module, with optional `public`, then `meta`, then
/// `import`, then optional `all` (`Lean/Parser/Module/Syntax.lean`). Comments,
/// quoted names, BOM and CRLF use the same lexer/view as declarations. Visibility
/// and phase modifiers remain in `import_specs` for the elaborator to implement
/// or explicitly refuse; parsing alone never grants their semantics.
pub fn parse_source_header(source: &[u8]) -> Result<SourceHeader, DefinitionParseError> {
    parse_header(source).map(|parsed| parsed.header)
}

/// The pin's `Lean.Parser.Module.header` tree over the same recognized header.
/// Leaves carry positions in `SourceView::of(source)` (CRLF normalized, BOM
/// retained), as other parser trees do. Header metadata and refusals instead
/// carry original-file positions. The body is neither parsed nor synthesized.
pub fn parse_source_header_syntax(source: &[u8]) -> Result<Syntax, DefinitionParseError> {
    let parsed = parse_header(source)?;
    // Header parsing stops before the first body token. In the pin's retained
    // header tree, the final header token owns all intervening whitespace;
    // command parsing has not supplied a successor to update its trailing span.
    let text =
        SourceText::from_utf8(&parsed.view.normalized().as_bytes()[..parsed.body_position.0])
            .map_err(NatDefinitionParseError::Source)?;
    let leaves = Leaves::build(&text, &parsed.tokens)?;
    let node = |kind: &str, args| Syntax::node(parser_kind(&["Module", kind]), args);
    let optional = |kind: &str, at: Option<usize>| -> Result<Syntax, DefinitionParseError> {
        Ok(null_node(match at {
            Some(at) => vec![node(kind, vec![leaves.leaf(at)?])],
            None => Vec::new(),
        }))
    };
    let imports = parsed
        .directives
        .iter()
        .map(|directive| {
            Ok(node(
                "import",
                vec![
                    optional("public", directive.public)?,
                    optional("meta", directive.meta)?,
                    leaves.leaf(directive.import)?,
                    optional("all", directive.all)?,
                    leaves.leaf(directive.module)?,
                    // `identWithPartialTrailingDot` has a second, optional
                    // slot; a completed import always leaves that slot empty.
                    null_node(Vec::new()),
                ],
            ))
        })
        .collect::<Result<Vec<_>, DefinitionParseError>>()?;
    Ok(node(
        "header",
        vec![
            optional("moduleTk", parsed.module)?,
            optional("prelude", parsed.prelude)?,
            null_node(imports),
        ],
    ))
}

struct DirectiveTokens {
    public: Option<usize>,
    meta: Option<usize>,
    import: usize,
    all: Option<usize>,
    module: usize,
}

struct ParsedHeader {
    header: SourceHeader,
    view: SourceView,
    tokens: Vec<LexedToken>,
    module: Option<usize>,
    prelude: Option<usize>,
    directives: Vec<DirectiveTokens>,
    body_position: BytePos,
}

fn is(token: Option<&LexedToken>, word: &str) -> bool {
    matches!(token.map(|token| &token.kind), Some(TokenKind::Symbol(symbol)) if symbol == word)
}

fn take(
    view: &SourceView,
    table: &TokenTable,
    next: &mut Option<LexedToken>,
    tokens: &mut Vec<LexedToken>,
) -> Result<usize, DefinitionParseError> {
    let token = next.take().expect("the caller matched the next token");
    *next = next_header_token(view, table, token.extent.end())?;
    let index = tokens.len();
    tokens.push(token);
    Ok(index)
}

fn optional_keyword(
    view: &SourceView,
    table: &TokenTable,
    next: &mut Option<LexedToken>,
    tokens: &mut Vec<LexedToken>,
    word: &str,
) -> Result<Option<usize>, DefinitionParseError> {
    if is(next.as_ref(), word) {
        take(view, table, next, tokens).map(Some)
    } else {
        Ok(None)
    }
}

/// The pin makes the `public? meta? import` prefix atomic. A `public def`,
/// `meta section`, or unfinished body beginning with a modifier belongs to the
/// body and must not consume any header tokens or hide its original position.
fn import_prefix(
    view: &SourceView,
    table: &TokenTable,
    first: Option<&LexedToken>,
) -> Option<Vec<LexedToken>> {
    let mut next = first.cloned();
    let mut prefix = Vec::new();
    optional_keyword(view, table, &mut next, &mut prefix, "public").ok()?;
    optional_keyword(view, table, &mut next, &mut prefix, "meta").ok()?;
    if !is(next.as_ref(), "import") {
        return None;
    }
    prefix.push(next?);
    Some(prefix)
}

fn parse_header(source: &[u8]) -> Result<ParsedHeader, DefinitionParseError> {
    let original = SourceText::from_utf8(source).map_err(NatDefinitionParseError::Source)?;
    let view = SourceView::of(&original);
    // The Reference lexes the header before any import exists: builtin tokens plus the
    // header parser's own (`prelude`, `module`, `all`), never the body's imported notation.
    let table = crate::reference_tokens::header_table();
    // Import discovery is not whole-file validation. Once the first body token
    // is observed, do not lex its unfinished terms, comments, or later commands.
    // The ordinary body parser/checker still refuses those exact bytes when
    // checking the file; no recovered body is installed or called valid here.
    // The BOM belongs to the view and to the first token's leading trivia, but
    // only a BOM at byte zero is skipped by the header lexer.
    let start = BytePos(if source.starts_with(b"\xef\xbb\xbf") {
        3
    } else {
        0
    });
    let mut next = next_header_token(&view, table, start)?;
    let mut tokens = Vec::new();
    let module = optional_keyword(&view, table, &mut next, &mut tokens, "module")?;
    let prelude = optional_keyword(&view, table, &mut next, &mut tokens, "prelude")?;
    let mut imports = Vec::new();
    let mut import_specs = Vec::new();
    let mut directives = Vec::new();
    while let Some(prefix) = import_prefix(&view, table, next.as_ref()) {
        let start = tokens.len();
        let public = is(prefix.first(), "public").then_some(start);
        let meta = prefix
            .iter()
            .position(|token| is(Some(token), "meta"))
            .map(|index| start + index);
        let import = start + prefix.len() - 1;
        let end = prefix
            .last()
            .expect("the prefix ends in import")
            .extent
            .end();
        tokens.extend(prefix);
        next = next_header_token(&view, table, end)?;
        let all = optional_keyword(&view, table, &mut next, &mut tokens, "all")?;
        let name = match next.as_ref().map(|token| &token.kind) {
            Some(TokenKind::Ident(name)) => name.clone(),
            _ => {
                return Err(NatDefinitionParseError::OutsideSeedGrammar {
                    at: next.as_ref().map_or(BytePos(source.len()), |token| {
                        view.to_original(token.extent.start())
                    }),
                    expected: NatDefinitionExpectation::ImportedModule,
                });
            }
        };
        let module_token = take(&view, table, &mut next, &mut tokens)?;
        // A trailing dot is partial syntax, never a completed import. The
        // pin retains its partial tree for completion and diagnoses it here.
        if is(next.as_ref(), ".")
            && next
                .as_ref()
                .is_some_and(|token| token.extent.start() == tokens[module_token].extent.end())
        {
            return Err(NatDefinitionParseError::OutsideSeedGrammar {
                at: view.to_original(next.as_ref().expect("matched dot").extent.start()),
                expected: NatDefinitionExpectation::ImportedModule,
            });
        }
        let at = |index: usize| view.to_original(tokens[index].extent.start());
        let spec = SourceImport {
            module: name.clone(),
            import_at: at(import),
            module_at: at(module_token),
            public_at: public.map(at),
            meta_at: meta.map(at),
            all_at: all.map(at),
        };
        validate_import(&spec, module.is_some())?;
        imports.push(name);
        import_specs.push(spec);
        directives.push(DirectiveTokens {
            public,
            meta,
            import,
            all,
            module: module_token,
        });
    }
    let body_position = if module.is_none() && prelude.is_none() && imports.is_empty() {
        start
    } else {
        next.as_ref()
            .map_or(BytePos(view.normalized().len_bytes()), |token| {
                token.extent.start()
            })
    };
    Ok(ParsedHeader {
        header: SourceHeader {
            imports,
            import_specs,
            body_start: view.to_original(body_position),
            prelude: prelude.is_some(),
            module_system: module.is_some(),
            module_at: module.map(|index| view.to_original(tokens[index].extent.start())),
        },
        view,
        tokens,
        module,
        prelude,
        directives,
        body_position,
    })
}

fn validate_import(import: &SourceImport, module: bool) -> Result<(), DefinitionParseError> {
    let invalid = if !module {
        import
            .public_at
            .map(|at| (at, ModuleHeaderError::PublicWithoutModule))
            .or_else(|| {
                import
                    .meta_at
                    .map(|at| (at, ModuleHeaderError::MetaWithoutModule))
            })
            .or_else(|| {
                import
                    .all_at
                    .map(|at| (at, ModuleHeaderError::AllWithoutModule))
            })
    } else if import.public_at.is_some() {
        import
            .all_at
            .map(|at| (at, ModuleHeaderError::PublicImportAll))
    } else {
        None
    };
    match invalid {
        Some((at, reason)) => Err(NatDefinitionParseError::ModuleHeader { at, reason }),
        None => Ok(()),
    }
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
            assert!(
                partition(&source.as_bytes()[header.body_start.0..]).is_err(),
                "header discovery must not repair or validate the body: {source}"
            );
        }
        let source = b"def pending := \"unfinished";
        let header = parse_source_header(source).unwrap();
        assert!(header.imports.is_empty());
        assert_eq!(header.body_start, BytePos(0));
    }

    #[test]
    fn streaming_headers_preserve_repeated_imports_bom_crlf_and_header_errors() {
        let source = "\u{feff}/- heading -/\r\nprelude\r\nimport A.B\r\nimport «C.D»\r\nimport A.B\r\ndef pending := \"unfinished";
        let header = parse_source_header(source.as_bytes()).unwrap();
        assert_eq!(
            header.imports,
            [
                Name::from_components(["A", "B"]),
                Name::from_components(["C.D"]),
                Name::from_components(["A", "B"])
            ]
        );
        assert_eq!(header.body_start.0, source.find("def pending").unwrap());
        let source = "\u{feff}prelude\r\nimport 42\r\ndef pending := \"unfinished";
        let error = parse_source_header(source.as_bytes()).unwrap_err();
        assert_eq!(
            error.primary_offset(),
            Some(BytePos(source.find("42").unwrap()))
        );
        for source in ["import «unfinished", "import /- unfinished", "import A\tB"] {
            assert!(parse_source_header(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn original_body_offsets_and_structural_names_survive_header_removal() {
        let source = "\u{feff}/- 🤖 import Fake -/\r\nprelude\r\nimport A.B\r\nimport «C.D»\r\nimport A.B\r\nnamespace Proof\r\ndef value := 1\r\nend Proof";
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
        for source in ["public import A", "meta import A", "import all A"] {
            assert!(
                matches!(
                    parse_source_header(source.as_bytes()),
                    Err(NatDefinitionParseError::ModuleHeader { .. })
                ),
                "{source}"
            );
        }
    }

    #[test]
    fn module_and_import_modifiers_retain_their_original_positions() {
        let source = "\u{feff}/- 🤖 header -/\r\nmodule\r\nprelude\r\npublic meta import A.B\r\nmeta import all «C.D»\r\nimport A.B\r\npublic def pending := \"unfinished";
        let header = parse_source_header(source.as_bytes()).unwrap();
        assert!(header.module_system);
        assert!(header.prelude);
        assert_eq!(
            header.module_at,
            Some(BytePos(source.find("module").unwrap()))
        );
        assert_eq!(header.body_start.0, source.find("public def").unwrap());
        assert_eq!(
            header.imports,
            [
                Name::from_components(["A", "B"]),
                Name::from_components(["C.D"]),
                Name::from_components(["A", "B"])
            ]
        );
        assert_eq!(header.import_specs.len(), 3);
        let first = &header.import_specs[0];
        assert_eq!(first.module, header.imports[0]);
        assert_eq!(
            first.public_at,
            Some(BytePos(source.find("public meta").unwrap()))
        );
        assert_eq!(
            first.meta_at,
            Some(BytePos(source.find("meta import").unwrap()))
        );
        assert_eq!(first.import_at, BytePos(source.find("import A.B").unwrap()));
        assert_eq!(first.module_at, BytePos(source.find("A.B").unwrap()));
        assert_eq!(first.all_at, None);
        let second = &header.import_specs[1];
        assert_eq!(second.public_at, None);
        assert_eq!(
            second.meta_at,
            Some(BytePos(source.find("meta import all").unwrap()))
        );
        assert_eq!(
            second.all_at,
            Some(BytePos(source.find("all «C.D»").unwrap()))
        );
        assert_eq!(second.module_at, BytePos(source.find("«C.D»").unwrap()));
        let third = &header.import_specs[2];
        assert_eq!(
            (third.public_at, third.meta_at, third.all_at),
            (None, None, None)
        );
    }

    #[test]
    fn header_modifier_refusals_follow_the_pins_combination_rules() {
        for (source, word, reason) in [
            (
                "public import A",
                "public",
                ModuleHeaderError::PublicWithoutModule,
            ),
            (
                "meta import A",
                "meta",
                ModuleHeaderError::MetaWithoutModule,
            ),
            ("import all A", "all", ModuleHeaderError::AllWithoutModule),
            (
                "module\npublic import all A",
                "all",
                ModuleHeaderError::PublicImportAll,
            ),
            (
                "module\npublic meta import all A",
                "all",
                ModuleHeaderError::PublicImportAll,
            ),
        ] {
            let original = format!("\u{feff}/- header -/\r\n{}", source.replace('\n', "\r\n"));
            let at = BytePos(original.find(word).unwrap());
            let error = parse_source_header(original.as_bytes()).unwrap_err();
            assert_eq!(error, NatDefinitionParseError::ModuleHeader { at, reason });
            assert_eq!(error.primary_offset(), Some(at));
            assert_eq!(
                error.with_original_offset(BytePos(7)).primary_offset(),
                Some(BytePos(at.0 + 7))
            );
        }
        for directive in [
            "import A",
            "public import A",
            "meta import A",
            "public meta import A",
            "import all A",
            "meta import all A",
        ] {
            let source = format!("module\n{directive}\n");
            let header = parse_source_header(source.as_bytes()).unwrap();
            assert_eq!(header.imports, [Name::from_components(["A"])]);
            assert_eq!(header.body_start.0, source.len());
        }
    }

    #[test]
    fn an_import_has_one_name_and_an_atomic_ordered_prefix() {
        let source = b"module\nimport A B\nimport C\ndef d := 0";
        let header = parse_source_header(source).unwrap();
        assert_eq!(header.imports, [Name::from_components(["A"])]);
        assert_eq!(&source[header.body_start.0..], b"B\nimport C\ndef d := 0");
        for body in [
            "public def x := 0",
            "meta section",
            "public section",
            "meta public import A",
            "public public import A",
            "all import A",
            "public \"unfinished",
            "meta /- unfinished",
        ] {
            let source = format!("module\nprelude\n{body}");
            let header = parse_source_header(source.as_bytes()).unwrap();
            assert!(header.imports.is_empty(), "{source}");
            assert_eq!(&source[header.body_start.0..], body);
        }
        for source in [
            "prelude\nmodule",
            "module\nmodule",
            "module\nprelude\nprelude",
        ] {
            let header = parse_source_header(source.as_bytes()).unwrap();
            assert!(header.body_start.0 < source.len(), "{source}");
        }
        for source in ["import A.", "module\nimport A."] {
            assert!(parse_source_header(source.as_bytes()).is_err(), "{source}");
        }
    }

    #[test]
    fn module_header_tree_keeps_the_pins_slots_and_leaf_positions() {
        fn shape(syntax: &Syntax) -> String {
            match syntax {
                Syntax::Missing => "missing".to_owned(),
                Syntax::Atom { val, .. } => format!("{val:?}"),
                Syntax::Ident { val, .. } => format!("`{}", val.to_display_string()),
                Syntax::Node { kind, args, .. } => {
                    let children = args.iter().map(shape).collect::<Vec<_>>().join(" ");
                    if kind == &Name::from_components(["null"]) {
                        format!("[{children}]")
                    } else {
                        let name = kind.to_display_string();
                        format!(
                            "({} {children})",
                            name.strip_prefix("Lean.Parser.").unwrap_or(&name)
                        )
                    }
                }
            }
        }
        // Shape derived from the vendored `Module/Syntax.lean` combinators.
        // This unit cell does not claim a live Reference comparison.
        let source = "\u{feff}/- h -/\r\nmodule\r\nprelude\r\npublic meta import A\r\nimport all B\r\ndef pending := \"unfinished";
        let tree = parse_source_header_syntax(source.as_bytes()).unwrap();
        assert_eq!(
            shape(&tree),
            "(Module.header [(Module.moduleTk \"module\")] [(Module.prelude \"prelude\")] [(Module.import [(Module.public \"public\")] [(Module.meta \"meta\")] \"import\" [] `A []) (Module.import [] [] \"import\" [(Module.all \"all\")] `B [])])"
        );
        let original = SourceText::from_utf8(source.as_bytes()).unwrap();
        let view = SourceView::of(&original);
        let mut stack = vec![&tree];
        let mut starts = Vec::new();
        while let Some(syntax) = stack.pop() {
            match syntax {
                Syntax::Node { args, .. } => stack.extend(args.iter().rev()),
                Syntax::Atom { info, .. } | Syntax::Ident { info, .. } => {
                    let fln_syntax::source::SourceInfo::Original { pos, end_pos, .. } = info else {
                        panic!("every header leaf retains original source information")
                    };
                    starts.push(view.to_original(*pos).0);
                    assert!(end_pos.0 <= view.normalized().as_str().find("def pending").unwrap());
                }
                Syntax::Missing => panic!("a complete header has no missing syntax"),
            }
        }
        let expected = [
            "module",
            "prelude",
            "public",
            "meta",
            "import A",
            "A\r\n",
            "import all",
            "all",
            "B\r\n",
        ]
        .map(|word| source.find(word).unwrap());
        assert_eq!(starts, expected);
        assert_eq!(
            shape(&parse_source_header_syntax(b"def pending := \"unfinished").unwrap()),
            "(Module.header [] [] [])"
        );
    }
}
