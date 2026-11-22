//! Shared imported heads retain native priority, choice and lexical scope.
use super::*;

fn term(declaration: &str, precedence: u32, body: Descr) -> ImportedSyntaxEntry {
    parser(
        declaration,
        "term",
        None,
        Descr::Node {
            kind: name(declaration),
            prec: precedence,
            body: Box::new(body),
        },
    )
}

fn configured(
    mut entry: ImportedSyntaxEntry,
    priority: u32,
    scope: Option<&str>,
) -> ImportedSyntaxEntry {
    let ImportedSyntaxEntry::Parser(declaration) = &mut entry else {
        unreachable!()
    };
    let declaration = Arc::make_mut(declaration);
    declaration.priority = priority;
    declaration.scope = scope.map(name);
    entry
}

fn delimited(open: &str, minimum: u32, close: &str) -> Descr {
    sequence(
        symbol("shared!"),
        sequence(
            symbol(open),
            sequence(Descr::Cat(name("term"), minimum), symbol(close)),
        ),
    )
}

fn node<'a>(syntax: &'a Syntax, expected: &str) -> &'a [Syntax] {
    let expected = name(expected);
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == expected {
                return args;
            }
            pending.extend(args.iter().rev());
        }
    }
    panic!("missing {expected:?}: {syntax:?}")
}

fn custom_leaf(declaration: &str) -> ImportedSyntaxEntry {
    parser(
        declaration,
        "artifactItem",
        None,
        Descr::Node {
            kind: name(declaration),
            prec: MAX_PREC,
            body: Box::new(symbol("v")),
        },
    )
}

fn custom_trailing(declaration: &str) -> ImportedSyntaxEntry {
    parser(
        declaration,
        "artifactItem",
        None,
        Descr::TrailingNode {
            kind: name(declaration),
            prec: 65,
            lhs_prec: 65,
            body: Box::new(sequence(symbol("%%"), Descr::Cat(name("artifactItem"), 66))),
        },
    )
}

fn custom_reader() -> ImportedSyntaxEntry {
    term(
        "Library.inspect",
        LEAD_PREC,
        sequence(
            symbol("inspectArtifact"),
            sequence(
                symbol("["),
                sequence(Descr::Cat(name("artifactItem"), 0), symbol("]")),
            ),
        ),
    )
}

fn choice_kinds(syntax: &Syntax) -> Vec<Name> {
    node(syntax, "choice")
        .iter()
        .map(|syntax| {
            let Syntax::Node { kind, .. } = syntax else {
                panic!("expected a parser node: {syntax:?}")
            };
            kind.clone()
        })
        .collect()
}

#[test]
fn imported_category_choices_keep_order_priority_and_lexical_scope() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            category(IdentBehavior::Default),
            token("v", None),
            token("inspectArtifact", None),
            custom_leaf("Library.older"),
            custom_reader(),
        ],
    })
    .unwrap();
    let source = "#check inspectArtifact [v]";
    assert!(!contains(&parse(&file, source).unwrap(), "choice"));
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            configured(custom_leaf("Library.low"), DEFAULT_PRIORITY - 1, None),
            custom_leaf("Library.newer"),
            configured(
                custom_leaf("Library.scoped"),
                DEFAULT_PRIORITY,
                Some("OnlyScopedRows"),
            ),
        ],
    })
    .unwrap();
    let syntax = parse(&file, source).unwrap();
    assert_eq!(
        choice_kinds(&syntax),
        vec![name("Library.newer"), name("Library.older")]
    );
    assert!(!contains(&syntax, "Library.low"));
    assert!(!contains(&syntax, "Library.scoped"));

    file.apply(&ScopeCommand::Section(None));
    file.apply(&ScopeCommand::OpenScoped(vec![name("OnlyScopedRows")]));
    assert_eq!(
        choice_kinds(&parse(&file, source).unwrap()),
        vec![
            name("Library.scoped"),
            name("Library.newer"),
            name("Library.older")
        ]
    );
    file.apply(&ScopeCommand::End(None));
    assert_eq!(
        choice_kinds(&parse(&file, source).unwrap()),
        choice_kinds(&syntax)
    );
}

#[test]
fn identical_imported_category_trailing_bodies_retain_all_readings() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            category(IdentBehavior::Default),
            token("v", None),
            token("%%", None),
            token("inspectArtifact", None),
            custom_leaf("Library.value"),
            custom_trailing("Library.older"),
            custom_trailing("Library.newer"),
            custom_reader(),
        ],
    })
    .unwrap();
    let syntax = parse(&file, "#check inspectArtifact [v %% v %% v]").unwrap();
    assert_eq!(
        choice_kinds(&syntax),
        vec![name("Library.newer"), name("Library.older")]
    );
    for reading in node(&syntax, "choice") {
        let Syntax::Node { args, .. } = reading else {
            unreachable!()
        };
        assert_eq!(
            choice_kinds(&args[0]),
            vec![name("Library.newer"), name("Library.older")]
        );
        assert!(!contains(&args[2], "choice"));
    }
    assert!(parse(&file, "#check inspectArtifact [v %%]").is_err());
}

#[test]
fn incompatible_custom_category_overlaps_still_refuse_transactionally() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            category(IdentBehavior::Default),
            token("v", None),
            custom_leaf("Library.older"),
        ],
    })
    .unwrap();
    let before = file.grammar();
    let generation = file.generation;
    let work = file.artifact.work;
    let incompatible = parser(
        "Library.incompatible",
        "artifactItem",
        None,
        Descr::Node {
            kind: name("Library.incompatible"),
            prec: MAX_PREC,
            body: Box::new(sequence(symbol("v"), symbol("mustNotLeak!"))),
        },
    );
    assert_eq!(
        file.import_artifact(&ImportedSyntaxModule {
            entries: vec![token("mustNotLeak!", None), incompatible],
        }),
        Err("overlapping artifact parser productions")
    );
    assert!(Rc::ptr_eq(&before, &file.grammar()));
    assert_eq!(file.generation, generation);
    assert_eq!(file.artifact.work, work);
    assert!(!file.constants.contains(&name("Library.incompatible")));
    assert!(!file.grammar().table().contains("mustNotLeak!"));
}

fn assert_overlap_refused(first: ImportedSyntaxEntry, second: ImportedSyntaxEntry) {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![token("shared!", None), first],
    })
    .unwrap();
    let before = file.grammar();
    let generation = file.generation;
    let work = file.artifact.work;
    let ImportedSyntaxEntry::Parser(declaration) = &second else {
        unreachable!()
    };
    let rejected = declaration.decl.clone();
    assert_eq!(
        file.import_artifact(&ImportedSyntaxModule {
            entries: vec![token("mustNotLeak!", None), second],
        }),
        Err("overlapping artifact parser productions")
    );
    assert!(Rc::ptr_eq(&before, &file.grammar()));
    assert_eq!(file.generation, generation);
    assert_eq!(file.artifact.work, work);
    assert!(!file.constants.contains(&rejected));
    assert!(!file.grammar().table().contains("mustNotLeak!"));
}

#[test]
fn imported_shared_heads_select_distinct_delimiters_and_nested_operands() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("shared!", None),
            term("Library.round", LEAD_PREC, delimited("(", 0, ")")),
            term("Library.square", LEAD_PREC, delimited("[", 0, "]")),
        ],
    })
    .unwrap();

    for (source, selected, absent) in [
        (
            "def result := shared! (f x + 1)",
            "Library.round",
            "Library.square",
        ),
        (
            "def result := shared! [f x * 2]",
            "Library.square",
            "Library.round",
        ),
    ] {
        let syntax = parse(&file, source).unwrap();
        assert!(contains(&syntax, selected));
        assert!(!contains(&syntax, absent));
        assert!(!contains(&syntax, "choice"));
    }
    let nested = parse(&file, "def result := shared! [shared! (f x + 1)]").unwrap();
    assert!(contains(&nested, "Library.square"));
    assert!(contains(&nested, "Library.round"));
    assert!(contains(&nested, "term_+_"));
    for source in [
        "def result := shared! (1",
        "def result := shared! [1",
        "def result := shared! (1]",
        "def result := shared! [1)",
        "def result := shared! ()",
        "def result := shared! [shared! (1]",
    ] {
        assert!(parse(&file, source).is_err(), "{source}");
    }
}

#[test]
fn identical_imported_descriptions_preserve_priority_and_newest_first_choices() {
    let body = || sequence(symbol("shared!"), Descr::Cat(name("term"), MAX_PREC));
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("shared!", None),
            configured(
                term("Library.older", LEAD_PREC, body()),
                DEFAULT_PRIORITY + 1,
                None,
            ),
            term("Library.low", LEAD_PREC, body()),
        ],
    })
    .unwrap();
    let unique = parse(&file, "def result := shared! 42").unwrap();
    assert!(contains(&unique, "Library.older"));
    assert!(!contains(&unique, "Library.low"));
    assert!(!contains(&unique, "choice"));

    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![configured(
            term("Library.newer", LEAD_PREC, body()),
            DEFAULT_PRIORITY + 1,
            None,
        )],
    })
    .unwrap();
    let tied = parse(&file, "def result := shared! (40 + 2)").unwrap();
    let readings = node(&tied, "choice");
    assert_eq!(readings.len(), 2);
    assert_eq!(readings[0].kind(), Some(&name("Library.newer")));
    assert_eq!(readings[1].kind(), Some(&name("Library.older")));
    assert!(!contains(&tied, "Library.low"));
    assert!(contains(&readings[0], "term_+_"));
    assert!(contains(&readings[1], "term_+_"));
}

#[test]
fn identical_imported_prefixes_share_operand_binding_and_priority() {
    let prefix = |declaration| {
        term(
            declaration,
            90,
            sequence(symbol("shared!"), Descr::Cat(name("term"), 75)),
        )
    };
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("shared!", None),
            configured(prefix("Library.older"), DEFAULT_PRIORITY + 1, None),
            prefix("Library.low"),
            configured(prefix("Library.newer"), DEFAULT_PRIORITY + 1, None),
        ],
    })
    .unwrap();
    let syntax = parse(&file, "def result := shared! a ^ b * c + d").unwrap();
    let readings = node(&syntax, "choice");
    assert_eq!(readings.len(), 2);
    for (reading, expected) in readings.iter().zip(["Library.newer", "Library.older"]) {
        assert_eq!(reading.kind(), Some(&name(expected)));
        let args = node(reading, expected);
        assert_eq!(args[1].kind(), Some(&name("term_^_")));
        assert!(!contains(&args[1], "term_*_"));
        assert!(!contains(&args[1], "term_+_"));
    }
    assert!(contains(&syntax, "term_*_"));
    assert!(contains(&syntax, "term_+_"));
    assert!(!contains(&syntax, "Library.low"));
    assert!(parse(&file, "def result := shared!").is_err());
}

#[test]
fn shared_scoped_imports_activate_and_restore_independently() {
    let body = || sequence(symbol("shared!"), Descr::Cat(name("term"), MAX_PREC));
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("shared!", None),
            configured(
                term("Library.first", LEAD_PREC, body()),
                DEFAULT_PRIORITY,
                Some("First"),
            ),
            configured(
                term("Library.second", LEAD_PREC, body()),
                DEFAULT_PRIORITY + 1,
                Some("Second"),
            ),
        ],
    })
    .unwrap();
    let inactive = file.grammar();
    let source = "def result := shared! 42";
    assert!(parse(&file, source).is_err());

    file.apply(&ScopeCommand::Section(None));
    file.apply(&ScopeCommand::OpenScoped(vec![name("First")]));
    let first = file.grammar();
    assert!(contains(&parse(&file, source).unwrap(), "Library.first"));
    file.apply(&ScopeCommand::Section(None));
    file.apply(&ScopeCommand::OpenScoped(vec![name("Second")]));
    let second = parse(&file, source).unwrap();
    assert!(contains(&second, "Library.second"));
    assert!(!contains(&second, "Library.first"));
    file.apply(&ScopeCommand::End(None));
    assert!(Rc::ptr_eq(&first, &file.grammar()));
    assert!(contains(&parse(&file, source).unwrap(), "Library.first"));
    file.apply(&ScopeCommand::End(None));
    assert!(Rc::ptr_eq(&inactive, &file.grammar()));
    assert!(parse(&file, source).is_err());
}

#[test]
fn incompatible_shared_dispatch_and_binding_powers_refuse_atomically() {
    let description = || sequence(symbol("shared!"), Descr::Cat(name("term"), MAX_PREC));
    assert_overlap_refused(
        term("Library.first", LEAD_PREC, description()),
        term("Library.second", MAX_PREC, description()),
    );
    for (left_precedence, right_precedence, right_operand) in [(90, 91, 75), (90, 90, 76)] {
        assert_overlap_refused(
            term(
                "Library.first",
                left_precedence,
                sequence(symbol("shared!"), Descr::Cat(name("term"), 75)),
            ),
            term(
                "Library.second",
                right_precedence,
                sequence(symbol("shared!"), Descr::Cat(name("term"), right_operand)),
            ),
        );
    }
    for reverse in [false, true] {
        let prefix = term(
            "Library.prefix",
            LEAD_PREC,
            sequence(symbol("shared!"), Descr::Cat(name("term"), 75)),
        );
        let description = term("Library.description", LEAD_PREC, delimited("(", 0, ")"));
        let (first, second) = if reverse {
            (description, prefix)
        } else {
            (prefix, description)
        };
        assert_overlap_refused(first, second);
    }
}

#[test]
fn shorter_fallbacks_and_delimiters_after_terms_do_not_prove_safe_overlap() {
    // A farther-consuming missing suffix must not expose the shorter reading.
    for reverse in [false, true] {
        let short = term("Library.short", MAX_PREC, symbol("shared!"));
        let long = term(
            "Library.long",
            MAX_PREC,
            sequence(
                symbol("shared!"),
                sequence(Descr::Cat(name("term"), MAX_PREC), symbol("end!")),
            ),
        );
        let (first, second) = if reverse {
            (long, short)
        } else {
            (short, long)
        };
        assert_overlap_refused(first, second);
    }
    let after_term = |delimiter| {
        sequence(
            sequence(symbol("shared!"), Descr::Cat(name("term"), MAX_PREC)),
            symbol(delimiter),
        )
    };
    assert_overlap_refused(
        term("Library.first", MAX_PREC, after_term("(")),
        term("Library.second", MAX_PREC, after_term("[")),
    );
}

#[test]
fn unicode_discriminators_with_a_shared_ascii_spelling_remain_ambiguous() {
    let body = |unicode: &str| {
        sequence(
            symbol("shared!"),
            sequence(
                Descr::UnicodeSymbol(unicode.into(), "<<".into(), true),
                sequence(Descr::Cat(name("term"), MAX_PREC), symbol("end!")),
            ),
        )
    };
    assert_overlap_refused(
        term("Library.first", MAX_PREC, body("⟪")),
        term("Library.second", MAX_PREC, body("⟦")),
    );
}

#[test]
fn every_existing_shared_candidate_is_checked_before_import_mutation() {
    // The third production conflicts with either the first or the last stored
    // production. Keeping a single representative would miss one of these.
    for (open, close) in [("(", ")"), ("[", "]")] {
        let mut file = grammar();
        file.import_artifact(&ImportedSyntaxModule {
            entries: vec![
                token("shared!", None),
                term("Library.round", LEAD_PREC, delimited("(", 0, ")")),
                term("Library.square", LEAD_PREC, delimited("[", 0, "]")),
            ],
        })
        .unwrap();
        let before = file.grammar();
        let work = file.artifact.work;
        assert_eq!(
            file.import_artifact(&ImportedSyntaxModule {
                entries: vec![
                    token("mustNotLeak!", None),
                    term("Library.third", LEAD_PREC, delimited(open, MAX_PREC, close)),
                ],
            }),
            Err("overlapping artifact parser productions")
        );
        assert!(Rc::ptr_eq(&before, &file.grammar()));
        assert_eq!(file.artifact.work, work);
        assert!(!file.constants.contains(&name("Library.third")));
        assert!(!file.grammar().table().contains("mustNotLeak!"));
        assert!(parse(&file, "def result := shared! (f x)").is_ok());
        assert!(parse(&file, "def result := shared! [f x]").is_ok());
    }
}
