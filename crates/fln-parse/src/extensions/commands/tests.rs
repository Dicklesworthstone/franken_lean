use super::*;

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn sequence(left: Descr, right: Descr) -> Descr {
    Descr::Binary(name("andthen"), Box::new(left), Box::new(right))
}

fn declaration(kind: &str, body: Descr) -> Arc<SyntaxDecl> {
    Arc::new(SyntaxDecl {
        module: name("Library"),
        decl: name(kind),
        category: Some(name("command")),
        leading: true,
        priority: DEFAULT_PRIORITY,
        scope: None,
        descr: Descr::Node {
            kind: name(kind),
            prec: 1022,
            body: Box::new(body),
        },
    })
}

fn artifact(precedence: u32) -> ImportedSyntaxModule {
    ImportedSyntaxModule {
        entries: vec![
            ImportedSyntaxEntry::Token {
                scope: None,
                token: "declare%".into(),
            },
            ImportedSyntaxEntry::Kind {
                scope: None,
                kind: name("Library.declare"),
            },
            ImportedSyntaxEntry::Parser(declaration(
                "Library.declare",
                sequence(
                    Descr::Symbol("declare%".into()),
                    sequence(
                        Descr::Symbol("[".into()),
                        sequence(
                            Descr::Cat(name("command"), precedence),
                            Descr::Symbol("]".into()),
                        ),
                    ),
                ),
            )),
        ],
    }
}

fn grammar() -> FileGrammar {
    let mut file = FileGrammar::new(false, &[], Some(name("Consumer")))
        .unwrap()
        .own_syntax_only();
    file.import_artifact(&artifact(0)).unwrap();
    file
}

fn parse(
    file: &FileGrammar,
    source: &str,
) -> Result<crate::ParsedSourceCommand, crate::DefinitionParseError> {
    with_grammar(&file.grammar(), || {
        crate::parse_source_command(source.as_bytes())
    })
}

#[test]
fn nested_command_operands_preserve_full_trivia_and_unicode_crlf_positions() {
    let file = grammar();
    let source = concat!(
        "-- leading λ\r\n",
        "declare% [ -- outer trivia\r\n",
        "  declare% [\r\n",
        "    def α : Nat := 42 -- inner trailing trivia\r\n",
        "  ]\r\n",
        "]\r\n",
    );
    let parsed = parse(&file, source).unwrap();
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().as_deref(),
        Some(parsed.source_view().normalized().as_bytes())
    );
    let mut wrappers = 0;
    let mut definitions = 0;
    let mut identifiers = 0;
    let mut pending = vec![parsed.syntax()];
    while let Some(syntax) = pending.pop() {
        match syntax {
            Syntax::Node { kind, args, .. } => {
                wrappers += usize::from(*kind == name("Library.declare"));
                definitions += usize::from(*kind == name("Lean.Parser.Command.declaration"));
                pending.extend(args);
            }
            Syntax::Ident {
                info, raw_val, val, ..
            } if *val == name("α") => {
                identifiers += 1;
                assert_eq!(raw_val.text(parsed.source_view().normalized()), Some("α"));
                assert_eq!(info.pos(false), Some(raw_val.span().start()));
                assert_eq!(
                    parsed.source_view().to_original(raw_val.span().start()).0,
                    source.find('α').unwrap()
                );
            }
            _ => {}
        }
    }
    assert_eq!((wrappers, definitions, identifiers), (2, 1, 1));
}

#[test]
fn command_operands_require_one_complete_command_at_zero_precedence() {
    let file = grammar();
    for source in [
        "declare% []",
        "declare% [def broken : Nat :=]",
        "declare% [def first := 1 def second := 2]",
        "declare% [def chosen := 1] leftover",
    ] {
        assert!(parse(&file, source).is_err(), "{source}");
    }
    for precedence in [1, 1023, 1024] {
        let mut file = FileGrammar::new(false, &[], None)
            .unwrap()
            .own_syntax_only();
        assert_eq!(
            file.import_artifact(&artifact(precedence)),
            Err("artifact command operands require zero precedence")
        );
        assert!(parse(&file, "declare% [def unavailable := 1]").is_err());
        assert!(parse(&file, "def ordinary := 1").is_ok());
    }
}

#[test]
fn command_reentry_exhaustion_refuses_the_whole_choice_and_resets_between_commands() {
    let file = grammar();
    let nested = format!(
        "{}def deepest : Nat := 1{}",
        "declare% [".repeat(MAX_DESCR_DEPTH + 1),
        "]".repeat(MAX_DESCR_DEPTH + 1),
    );
    assert!(parse(&file, &nested).is_err());
    assert!(parse(&file, "declare% [def next : Nat := 2]").is_ok());

    // Native source grammars can have several candidates for one head. The
    // second candidate would succeed if the first exhausted its allowance in
    // isolation. Keep the refusal shared across the complete candidate loop.
    let mut padding = Descr::Const(name("ppSpace"));
    for _ in 0..12 {
        padding = sequence(padding.clone(), padding);
    }
    let mut file = FileGrammar::new(false, &[], None)
        .unwrap()
        .own_syntax_only();
    file.import_native(&NativeSyntaxModule {
        declarations: vec![
            declaration(
                "Library.expensive",
                sequence(Descr::Symbol("budget%".into()), padding),
            ),
            declaration("Library.fallback", Descr::Symbol("budget%".into())),
            declaration("Library.fresh", Descr::Symbol("fresh%".into())),
        ],
        ..NativeSyntaxModule::default()
    })
    .unwrap();
    assert!(parse(&file, "budget%").is_err());
    assert!(parse(&file, "fresh%").is_ok());

    let mut fallback = FileGrammar::new(false, &[], None)
        .unwrap()
        .own_syntax_only();
    fallback
        .import_native(&NativeSyntaxModule {
            declarations: vec![declaration(
                "Library.fallback",
                Descr::Symbol("budget%".into()),
            )],
            ..NativeSyntaxModule::default()
        })
        .unwrap();
    assert!(parse(&fallback, "budget%").is_ok());
}
