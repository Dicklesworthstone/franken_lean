//! Data-product integration tests. The `.olean` decoder and checked declaration
//! binding are exercised by their owning crates, not assumed by these fixtures.
use super::*;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn grammar() -> FileGrammar {
    FileGrammar::new(false, &[], Some(name("Consumer")))
        .unwrap()
        .own_syntax_only()
}

fn token(text: &str, scope: Option<&str>) -> ImportedSyntaxEntry {
    ImportedSyntaxEntry::Token {
        scope: scope.map(name),
        token: text.to_string(),
    }
}

fn sequence(left: Descr, right: Descr) -> Descr {
    Descr::Binary(name("andthen"), Box::new(left), Box::new(right))
}

fn symbol(text: &str) -> Descr {
    Descr::Symbol(text.to_string())
}

fn parser(
    declaration: &str,
    category: &str,
    scope: Option<&str>,
    descr: Descr,
) -> ImportedSyntaxEntry {
    ImportedSyntaxEntry::Parser(Arc::new(SyntaxDecl {
        module: name("Library"),
        decl: name(declaration),
        category: Some(name(category)),
        leading: matches!(descr, Descr::Node { .. }),
        priority: DEFAULT_PRIORITY,
        scope: scope.map(name),
        descr,
    }))
}

fn leading(declaration: &str, head: &str, scope: Option<&str>) -> ImportedSyntaxEntry {
    parser(
        declaration,
        "term",
        scope,
        Descr::Node {
            kind: name(declaration),
            prec: LEAD_PREC,
            body: Box::new(sequence(symbol(head), Descr::Cat(name("term"), MAX_PREC))),
        },
    )
}

fn category(behavior: IdentBehavior) -> ImportedSyntaxEntry {
    ImportedSyntaxEntry::Category {
        scope: None,
        category: name("artifactItem"),
        declaration: name("Library.itemCategory"),
        behavior,
    }
}

fn parse(grammar: &FileGrammar, source: &str) -> Result<Syntax, String> {
    with_grammar(&grammar.grammar(), || {
        crate::parse_source_command(source.as_bytes())
    })
    .map(|parsed| {
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        parsed.syntax().clone()
    })
    .map_err(|error| format!("{error:?}"))
}

fn contains(syntax: &Syntax, expected: &str) -> bool {
    let expected = name(expected);
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == expected {
                return true;
            }
            pending.extend(args);
        }
    }
    false
}

#[test]
fn imported_custom_term_parses_without_local_declaration_or_native_template() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("choose!", None),
            ImportedSyntaxEntry::Kind {
                scope: None,
                kind: name("Library.choose"),
            },
            leading("Library.choose", "choose!", None),
        ],
    })
    .unwrap();
    let syntax = parse(&file, "def chosen : Nat := choose! (40 + 2)").unwrap();
    assert!(contains(&syntax, "Library.choose"));
    assert!(file.rules().next().is_none());
    assert!(file.export_native().unwrap().is_empty());
    assert!(
        file.native_namespace_anchors()
            .contains(&name("Library.choose"))
    );
    assert!(!contains(
        &parse(&grammar(), "def ordinary := 42").unwrap(),
        "Library.choose"
    ));
}

#[test]
fn standalone_scoped_tokens_and_kinds_activate_and_restore_without_parsers() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("globalArtifact!", None),
            token("scopedArtifact!", Some("OnlyScopedRows")),
            ImportedSyntaxEntry::Kind {
                scope: Some(name("OnlyScopedRows")),
                kind: name("Library.standaloneKind"),
            },
        ],
    })
    .unwrap();
    let inactive = file.grammar();
    assert!(inactive.table().contains("globalArtifact!"));
    assert!(!inactive.table().contains("scopedArtifact!"));
    assert!(!inactive.is_registered_artifact_kind(&name("Library.standaloneKind")));
    assert!(
        file.native_namespace_anchors()
            .iter()
            .any(|anchor| { anchor.parent() == name("OnlyScopedRows") })
    );
    file.apply(&ScopeCommand::Section(None));
    file.apply(&ScopeCommand::OpenScoped(vec![name("OnlyScopedRows")]));
    assert!(file.grammar().table().contains("scopedArtifact!"));
    assert!(
        file.grammar()
            .is_registered_artifact_kind(&name("Library.standaloneKind"))
    );
    file.apply(&ScopeCommand::End(None));
    assert!(!file.grammar().table().contains("scopedArtifact!"));
    assert!(
        !file
            .grammar()
            .is_registered_artifact_kind(&name("Library.standaloneKind"))
    );
    assert!(file.export_native().unwrap().is_empty());
}

#[test]
fn a_kind_row_cannot_enable_a_census_parser_alternative() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![ImportedSyntaxEntry::Kind {
            scope: None,
            kind: name("term{}"),
        }],
    })
    .unwrap();
    assert!(file.grammar().is_registered_artifact_kind(&name("term{}")));
    assert!(!file.grammar().kinds.contains(&name("term{}")));
    let parsed = parse(&file, "def x := {}").unwrap();
    assert!(!contains(&parsed, "term{}"));
}

#[test]
fn scoped_parser_and_independent_token_scope_both_follow_activation() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("chooseScoped!", Some("TokenScope")),
            leading("Library.scoped", "chooseScoped!", Some("ParserScope")),
        ],
    })
    .unwrap();
    assert!(!file.grammar().table().contains("chooseScoped!"));
    assert!(!contains(
        &parse(&file, "def x := chooseScoped! 42").unwrap(),
        "Library.scoped"
    ));
    file.apply(&ScopeCommand::Section(None));
    file.apply(&ScopeCommand::OpenScoped(vec![name("TokenScope")]));
    assert!(file.grammar().table().contains("chooseScoped!"));
    assert!(parse(&file, "def x := chooseScoped! 42").is_err());
    file.apply(&ScopeCommand::OpenScoped(vec![name("ParserScope")]));
    assert!(contains(
        &parse(&file, "def x := chooseScoped! 42").unwrap(),
        "Library.scoped"
    ));
    file.apply(&ScopeCommand::End(None));
    assert!(!contains(
        &parse(&file, "def x := chooseScoped! 42").unwrap(),
        "Library.scoped"
    ));
    assert!(!file.grammar().table().contains("chooseScoped!"));
}

#[test]
fn a_parser_row_does_not_fabricate_missing_token_rows() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![leading("Library.onlyParser", "noTokenRow!", None)],
    })
    .unwrap();
    assert!(!file.grammar().table().contains("noTokenRow!"));
    assert!(file.artifact.tokens.is_empty());
    assert!(file.artifact.kinds.is_empty());
}

#[test]
fn a_reserved_symbol_never_matches_an_identifier_before_its_token_scope_opens() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("artifactWord", Some("WordTokens")),
            leading("Library.word", "artifactWord", None),
        ],
    })
    .unwrap();
    let ordinary = parse(&file, "def x := artifactWord 42").unwrap();
    assert!(!contains(&ordinary, "Library.word"));
    file.apply(&ScopeCommand::Section(None));
    file.apply(&ScopeCommand::OpenScoped(vec![name("WordTokens")]));
    let extended = parse(&file, "def x := artifactWord 42").unwrap();
    assert!(contains(&extended, "Library.word"));
    file.apply(&ScopeCommand::End(None));
    let restored = parse(&file, "def x := artifactWord 42").unwrap();
    assert!(!contains(&restored, "Library.word"));
}

#[test]
fn late_refusal_preserves_categories_tokens_names_and_cached_grammar() {
    let mut file = grammar();
    let before = file.grammar();
    let generation = file.generation;
    let invalid = ImportedSyntaxModule {
        entries: vec![
            token("mustNotLeak!", None),
            category(IdentBehavior::Default),
            parser(
                "Library.unsupported",
                "term",
                None,
                Descr::Node {
                    kind: name("Library.unsupported"),
                    prec: LEAD_PREC,
                    body: Box::new(sequence(
                        symbol("bad!"),
                        sequence(Descr::Parser(name("Unbound.parser")), symbol("done")),
                    )),
                },
            ),
        ],
    };
    assert_eq!(
        file.import_artifact(&invalid),
        Err("artifact parser dependencies must be resolved from checked descriptions")
    );
    assert_eq!(file.generation, generation);
    assert!(Rc::ptr_eq(&before, &file.grammar()));
    assert!(!file.grammar().table().contains("mustNotLeak!"));
    assert!(!file.categories.contains_key(&name("artifactItem")));
    assert!(!file.constants.contains(&name("Library.itemCategory")));
    assert!(!file.constants.contains(&name("Library.unsupported")));
    assert_eq!(file.artifact.work, 0);
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![category(IdentBehavior::Default)],
    })
    .unwrap();
}

#[test]
fn categories_replay_idempotently_in_order_without_replacing_builtins() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            category(IdentBehavior::Default),
            category(IdentBehavior::Both),
            ImportedSyntaxEntry::Category {
                scope: None,
                category: name("term"),
                declaration: name("Library.termCategory"),
                behavior: IdentBehavior::Symbol,
            },
        ],
    })
    .unwrap();
    assert_eq!(
        file.categories[&name("artifactItem")],
        IdentBehavior::Default
    );
    assert!(!file.grammar().source_categories.contains(&name("term")));
    let unavailable = parser(
        "Library.tooEarly",
        "artifactItem",
        None,
        Descr::Node {
            kind: name("Library.tooEarly"),
            prec: MAX_PREC,
            body: Box::new(Descr::Const(name("num"))),
        },
    );
    assert_eq!(
        grammar().import_artifact(&ImportedSyntaxModule {
            entries: vec![unavailable, category(IdentBehavior::Default)],
        }),
        Err("artifact parser names an unavailable category")
    );
}

#[test]
fn artifact_categories_do_not_acquire_an_unregistered_quotation_parser() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            category(IdentBehavior::Default),
            parser(
                "Library.itemNumber",
                "artifactItem",
                None,
                Descr::Node {
                    kind: name("Library.itemNumber"),
                    prec: MAX_PREC,
                    body: Box::new(Descr::Const(name("num"))),
                },
            ),
        ],
    })
    .unwrap();
    let opener = "`(artifactItem|";
    assert!(!file.grammar().table().contains(opener));
    // Even its explicit token row does not substitute for the separate term
    // parser which declareSyntaxCatQuotParser registers at the pin.
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![token(opener, None)],
    })
    .unwrap();
    assert!(file.grammar().table().contains(opener));
    assert!(with_grammar(&file.grammar(), || { category_for_quotation(opener) }).is_none());
    assert!(parse(&file, "#check `(artifactItem| 1)").is_err());

    let before = file.grammar();
    let quotation = parser(
        "artifactItem.quot",
        "term",
        None,
        Descr::Node {
            kind: name("Lean.Parser.Term.quot"),
            prec: MAX_PREC,
            body: Box::new(Descr::Node {
                kind: name("artifactItem.quot"),
                prec: MAX_PREC,
                body: Box::new(sequence(
                    symbol(opener),
                    sequence(Descr::Cat(name("artifactItem"), 0), symbol(")")),
                )),
            }),
        },
    );
    assert!(
        file.import_artifact(&ImportedSyntaxModule {
            entries: vec![token("quotationMustNotLeak!", None), quotation],
        })
        .is_err()
    );
    assert!(Rc::ptr_eq(&before, &file.grammar()));
    assert!(!file.grammar().table().contains("quotationMustNotLeak!"));
}

#[test]
fn custom_category_pratt_parsers_and_native_term_infix_are_executable() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            category(IdentBehavior::Default),
            parser(
                "Library.itemNumber",
                "artifactItem",
                None,
                Descr::Node {
                    kind: name("Library.itemNumber"),
                    prec: MAX_PREC,
                    body: Box::new(Descr::Const(name("num"))),
                },
            ),
            token("%%", None),
            parser(
                "Library.itemPlus",
                "artifactItem",
                None,
                Descr::TrailingNode {
                    kind: name("Library.itemPlus"),
                    prec: 65,
                    lhs_prec: 65,
                    body: Box::new(sequence(symbol("%%"), Descr::Cat(name("artifactItem"), 66))),
                },
            ),
            token("itemBox!", None),
            parser(
                "Library.itemBox",
                "term",
                None,
                Descr::Node {
                    kind: name("Library.itemBox"),
                    prec: LEAD_PREC,
                    body: Box::new(sequence(
                        symbol("itemBox!"),
                        sequence(
                            symbol("["),
                            sequence(Descr::Cat(name("artifactItem"), 0), symbol("]")),
                        ),
                    )),
                },
            ),
            token("<+>", None),
            parser(
                "Library.termPlus",
                "term",
                None,
                Descr::TrailingNode {
                    kind: name("Library.termPlus"),
                    prec: 65,
                    lhs_prec: 65,
                    body: Box::new(sequence(symbol("<+>"), Descr::Cat(name("term"), 66))),
                },
            ),
        ],
    })
    .unwrap();
    let custom = parse(&file, "def x := itemBox! [1 %% 2 %% 3]").unwrap();
    assert!(contains(&custom, "Library.itemBox"));
    assert!(contains(&custom, "Library.itemNumber"));
    assert!(contains(&custom, "Library.itemPlus"));
    let infix = parse(&file, "def y := 1 <+> 2").unwrap();
    assert!(contains(&infix, "Library.termPlus"));
    assert!(file.export_native().unwrap().is_empty());
}

#[test]
fn unsupported_aliases_contextual_checks_and_nested_shapes_never_install() {
    for unsupported in [
        Descr::Const(name("colGt")),
        Descr::Const(name("arbitraryAlias")),
        Descr::Unary(name("unknownUnary"), Box::new(symbol("inner"))),
        Descr::Binary(
            name("unknownBinary"),
            Box::new(symbol("left")),
            Box::new(symbol("right")),
        ),
        Descr::Cat(name("term"), 65),
        Descr::Cat(name("unknownCategory"), 0),
        Descr::NodeWithAntiquot(
            "piece".into(),
            name("Library.piece"),
            Box::new(symbol("piece")),
        ),
        Descr::TrailingNode {
            kind: name("Library.nested"),
            prec: 65,
            lhs_prec: 65,
            body: Box::new(symbol("nested")),
        },
        Descr::Unary(
            name("many"),
            Box::new(Descr::Unary(name("optional"), Box::new(symbol("maybe")))),
        ),
    ] {
        let mut file = grammar();
        let row = parser(
            "Library.unsupported",
            "term",
            None,
            Descr::Node {
                kind: name("Library.unsupported"),
                prec: LEAD_PREC,
                body: Box::new(sequence(
                    symbol("bad!"),
                    sequence(unsupported.clone(), symbol("done")),
                )),
            },
        );
        assert!(
            file.import_artifact(&ImportedSyntaxModule {
                entries: vec![token("bad!", None), row],
            })
            .is_err(),
            "{unsupported:?}"
        );
        assert!(!file.grammar().table().contains("bad!"));
        assert!(file.artifact.imported.is_empty());
    }
}

#[test]
fn overlapping_inactive_scopes_are_refused_before_they_can_change_a_parse() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("sameHead!", None),
            leading("Library.first", "sameHead!", Some("First")),
        ],
    })
    .unwrap();
    assert_eq!(
        file.import_artifact(&ImportedSyntaxModule {
            entries: vec![
                token("mustNotLeak!", None),
                leading("Library.second", "sameHead!", Some("Second"))
            ],
        }),
        Err("overlapping artifact parser productions")
    );
    assert!(!file.grammar().table().contains("mustNotLeak!"));
    assert!(!file.artifact.namespaces.contains(&name("Second")));
    file.apply(&ScopeCommand::OpenScoped(vec![name("First")]));
    assert!(contains(
        &parse(&file, "def x := sameHead! 42").unwrap(),
        "Library.first"
    ));
}

#[test]
fn census_names_and_late_imports_do_not_grant_artifact_authority() {
    let mut file = grammar();
    assert_eq!(
        file.import_artifact(&ImportedSyntaxModule {
            entries: vec![leading("term_+_", "pretend!", None)],
        }),
        Err("an artifact parser declaration is already declared")
    );
    assert_eq!(
        file.import_artifact(&ImportedSyntaxModule {
            entries: vec![parser(
                "Library.differentOwner",
                "term",
                None,
                Descr::Node {
                    kind: name("term{}"),
                    prec: LEAD_PREC,
                    body: Box::new(sequence(
                        symbol("pretend!"),
                        Descr::Cat(name("term"), MAX_PREC)
                    )),
                },
            )],
        }),
        Err("artifact parser kind overlaps census-backed native syntax")
    );
    file.apply(&ScopeCommand::Section(None));
    assert_eq!(
        file.import_artifact(&ImportedSyntaxModule {
            entries: vec![leading("Library.late", "late!", None)],
        }),
        Err("artifact parsers must be installed before source scope transitions")
    );
    let mut census = FileGrammar::new(false, &[], Some(name("Consumer"))).unwrap();
    assert_eq!(
        census.import_artifact(&ImportedSyntaxModule {
            entries: vec![leading("Library.ambient", "ambient!", None)],
        }),
        Err("artifact parsers require a grammar without census registrations")
    );
}

#[test]
fn malformed_standalone_rows_and_exhausted_work_leave_no_prefix() {
    for invalid in [
        token("", None),
        ImportedSyntaxEntry::Token {
            scope: Some(Name::anonymous()),
            token: "badScope!".into(),
        },
        ImportedSyntaxEntry::Kind {
            scope: None,
            kind: Name::anonymous(),
        },
        ImportedSyntaxEntry::Category {
            scope: Some(name("Scoped")),
            category: name("artifactItem"),
            declaration: name("Library.category"),
            behavior: IdentBehavior::Default,
        },
    ] {
        let mut file = grammar();
        assert!(
            file.import_artifact(&ImportedSyntaxModule {
                entries: vec![token("noPrefix!", None), invalid],
            })
            .is_err()
        );
        assert!(!file.grammar().table().contains("noPrefix!"));
        assert_eq!(file.artifact.work, 0);
    }
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![token("existing!", None)],
    })
    .unwrap();
    assert!(
        file.import_artifact(&ImportedSyntaxModule {
            entries: (0..MAX_TEMPLATE_NODES)
                .map(|_| token("tooMuch!", None))
                .collect(),
        })
        .is_err()
    );
    assert!(file.grammar().table().contains("existing!"));
    assert!(!file.grammar().table().contains("tooMuch!"));
}
