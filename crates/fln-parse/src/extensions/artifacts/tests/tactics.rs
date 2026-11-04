//! Imported tactic heads keep their identifier behavior and syntax envelopes.
use super::*;

fn tactic_parser(declaration: &str, body: Descr, scope: Option<&str>) -> ImportedSyntaxEntry {
    parser(
        declaration,
        "tactic",
        scope,
        Descr::Node {
            kind: name(declaration),
            prec: MAX_PREC,
            body: Box::new(body),
        },
    )
}

fn nonreserved(text: &str) -> Descr {
    Descr::NonReservedSymbol(text.to_string(), false)
}

fn node<'a>(syntax: &'a Syntax, expected: &str) -> Option<&'a Syntax> {
    let expected = name(expected);
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if *kind == expected {
                return Some(syntax);
            }
            pending.extend(args);
        }
    }
    None
}

#[test]
fn ordinary_tactic_heads_match_exactly_without_reserving_identifiers() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![tactic_parser(
            "Library.importedDone",
            nonreserved("imported_done "),
            None,
        )],
    })
    .unwrap();
    assert!(!file.grammar().table().contains("imported_done"));
    for source in [
        "theorem done : True := by imported_done",
        "def quoted := `(tactic| imported_done)",
    ] {
        assert!(contains(
            &parse(&file, source).unwrap(),
            "Library.importedDone"
        ));
    }
    for source in [
        "def imported_done : Nat := 0",
        "def ordinary : Nat := imported_done",
        "def ordinary : Nat := «imported_done»",
    ] {
        assert!(!contains(
            &parse(&file, source).unwrap(),
            "Library.importedDone"
        ));
    }
    for head in [
        "«imported_done»",
        "Other.imported_done",
        "imported_done_extra",
    ] {
        let source = format!("theorem rejected : True := by {head}");
        assert!(parse(&file, &source).is_err(), "accepted {head}");
    }
}

#[test]
fn grouped_macro_heads_keep_their_group_and_nested_node_shapes() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![tactic_parser(
            "Library.groupedTactic",
            Descr::Unary(
                name("ppGroup"),
                Box::new(Descr::Unary(
                    name("group"),
                    Box::new(Descr::Binary(
                        name("orelse"),
                        Box::new(nonreserved("imported_group")),
                        Box::new(Descr::Node {
                            kind: name("Library.otherHead"),
                            prec: MAX_PREC,
                            body: Box::new(nonreserved("imported_other")),
                        }),
                    )),
                )),
            ),
            None,
        )],
    })
    .unwrap();
    for head in ["imported_group", "imported_other"] {
        for source in [
            format!("theorem done : True := by {head}"),
            format!("def quoted := `(tactic| {head})"),
        ] {
            let syntax = parse(&file, &source).unwrap();
            let Syntax::Node { args, .. } = node(&syntax, "Library.groupedTactic").unwrap() else {
                unreachable!()
            };
            assert_eq!(args.len(), 1);
            assert_eq!(args[0].kind(), Some(&name("group")));
            assert_eq!(
                contains(&args[0], "Library.otherHead"),
                head == "imported_other"
            );
        }
    }
    assert!(!file.grammar().table().contains("imported_group"));
    assert!(!file.grammar().table().contains("imported_other"));
}

#[test]
fn grouped_atom_bounded_terms_preserve_their_argument_boundary() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("groupedTerm!", None),
            parser(
                "Library.groupedTerm",
                "term",
                None,
                Descr::Node {
                    kind: name("Library.groupedTerm"),
                    prec: MAX_PREC,
                    body: Box::new(Descr::Unary(
                        name("group"),
                        Box::new(sequence(
                            symbol("groupedTerm!"),
                            Descr::Cat(name("term"), MAX_PREC),
                        )),
                    )),
                },
            ),
        ],
    })
    .unwrap();
    let syntax = parse(&file, "def value : Nat := groupedTerm! (40 + 1) + 1").unwrap();
    let Syntax::Node { args, .. } = node(&syntax, "Library.groupedTerm").unwrap() else {
        unreachable!()
    };
    assert_eq!(args.len(), 1);
    let Syntax::Node { kind, args, .. } = &args[0] else {
        unreachable!()
    };
    assert_eq!(*kind, name("group"));
    assert_eq!(args.len(), 2);
    assert_eq!(args[1].kind(), Some(&name("Lean.Parser.Term.paren")));
}

#[test]
fn scoped_nonreserved_tactics_activate_and_restore_without_keyword_leaks() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![tactic_parser(
            "Library.scopedTactic",
            nonreserved("imported_scoped"),
            Some("TacticScope"),
        )],
    })
    .unwrap();
    let source = "theorem done : True := by imported_scoped";
    assert!(parse(&file, source).is_err());
    file.apply(&ScopeCommand::Section(None));
    file.apply(&ScopeCommand::OpenScoped(vec![name("TacticScope")]));
    assert!(contains(
        &parse(&file, source).unwrap(),
        "Library.scopedTactic"
    ));
    assert!(!file.grammar().table().contains("imported_scoped"));
    file.apply(&ScopeCommand::End(None));
    assert!(parse(&file, source).is_err());
    assert!(!file.grammar().table().contains("imported_scoped"));
}

#[test]
fn unsupported_identifier_dispatch_refuses_the_entire_import() {
    for (category_name, include_ident) in [
        ("tactic", true),
        ("term", false),
        ("command", false),
        ("attr", false),
        ("artifactItem", false),
    ] {
        let mut file = grammar();
        let before = file.grammar();
        assert!(
            file.import_artifact(&ImportedSyntaxModule {
                entries: vec![
                    category(IdentBehavior::Default),
                    token("mustNotLeak!", None),
                    parser(
                        "Library.unsupportedHead",
                        category_name,
                        None,
                        Descr::Node {
                            kind: name("Library.unsupportedHead"),
                            prec: MAX_PREC,
                            body: Box::new(Descr::Unary(
                                name("group"),
                                Box::new(Descr::NonReservedSymbol(
                                    "imported_unknown".to_string(),
                                    include_ident,
                                )),
                            )),
                        },
                    ),
                ],
            })
            .is_err(),
            "accepted {category_name} includeIdent={include_ident}"
        );
        assert!(Rc::ptr_eq(&before, &file.grammar()));
        assert!(!file.grammar().table().contains("mustNotLeak!"));
    }
}

#[test]
fn tactic_arguments_use_the_compound_planner_but_require_one_tactic() {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![tactic_parser(
            "Library.wrappedTactic",
            sequence(
                nonreserved("imported_wrap"),
                sequence(
                    symbol("["),
                    sequence(Descr::Cat(name("tactic"), 0), symbol("]")),
                ),
            ),
            None,
        )],
    })
    .unwrap();
    for (body, expected) in [
        ("(intro h; exact h)", "Lean.Parser.Tactic.paren"),
        (
            "{ intro h; exact h }",
            "Lean.Parser.Tactic.tacticSeqBracketed",
        ),
        ("first | exact 0 | rfl", "Lean.Parser.Tactic.first"),
        ("all_goals rfl", "Lean.Parser.Tactic.allGoals"),
        ("constructor <;> rfl", "Lean.Parser.Tactic.tactic_<;>_"),
        ("imported_wrap [rfl]", "Library.wrappedTactic"),
    ] {
        let source = format!("theorem done : True := by imported_wrap [{body}]");
        let syntax = parse(&file, &source).unwrap();
        let Syntax::Node { args, .. } = node(&syntax, "Library.wrappedTactic").unwrap() else {
            unreachable!()
        };
        assert_eq!(args.len(), 4);
        assert_eq!(args[2].kind(), Some(&name(expected)), "{body}");
    }
    for body in ["intro h; exact h", "rfl;", ""] {
        let source = format!("theorem rejected : True := by imported_wrap [{body}]");
        assert!(parse(&file, &source).is_err(), "accepted sequence {body}");
    }
    let deeply_nested = format!(
        "theorem rejected : True := by {}rfl{}",
        "imported_wrap [".repeat(32),
        "]".repeat(32)
    );
    assert!(parse(&file, &deeply_nested).is_err());
}

#[test]
fn native_reflexivity_tactics_are_contextual_and_operandless() {
    let file = grammar();
    for (keyword, kind) in [("eq_refl", "eqRefl"), ("apply_rfl", "applyRfl")] {
        for source in [
            format!("theorem done (n : Nat) : n = n := by {keyword}"),
            format!("def quoted := `(tactic| {keyword})"),
        ] {
            let syntax = parse(&file, &source).unwrap();
            let Syntax::Node { args, .. } =
                node(&syntax, &format!("Lean.Parser.Tactic.{kind}")).unwrap()
            else {
                unreachable!()
            };
            assert!(matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == keyword));
        }
        assert!(parse(&file, &format!("def {keyword} : Nat := 0")).is_ok());
        assert!(
            parse(
                &file,
                &format!("theorem rejected : True := by {keyword} extra")
            )
            .is_err()
        );
    }
}
