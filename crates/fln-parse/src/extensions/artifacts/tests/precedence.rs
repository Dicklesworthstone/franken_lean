//! Imported operand precedences use the scalar parser's actual Pratt boundary.
use super::*;

fn bounded(precedence: u32) -> ImportedSyntaxEntry {
    parser(
        "Library.bounded",
        "term",
        None,
        Descr::Node {
            kind: name("Library.bounded"),
            prec: LEAD_PREC,
            body: Box::new(sequence(
                symbol("bounded!"),
                sequence(
                    symbol("["),
                    sequence(Descr::Cat(name("term"), precedence), symbol("]")),
                ),
            )),
        },
    )
}

fn infix(declaration: &str, token: &str, prec: u32, lhs: u32, rhs: u32) -> ImportedSyntaxEntry {
    parser(
        declaration,
        "term",
        None,
        Descr::TrailingNode {
            kind: name(declaration),
            prec,
            lhs_prec: lhs,
            body: Box::new(sequence(symbol(token), Descr::Cat(name("term"), rhs))),
        },
    )
}

fn at_precedence(precedence: u32) -> FileGrammar {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("bounded!", None),
            bounded(precedence),
            token("<+>", None),
            infix("Library.plus", "<+>", 65, 65, 66),
            token("<^>", None),
            infix("Library.power", "<^>", 80, 81, 80),
            token("<+~>", None),
            infix("Library.looseRight", "<+~>", 80, 80, 0),
            token("<+~+>", None),
            infix("Library.equalRight", "<+~+>", 80, 80, 65),
            token("<!!>", None),
            infix("Library.nonassoc", "<!!>", 50, 51, 51),
            token("<strict!>", None),
            infix("Library.strictLeft", "<strict!>", 50, 80, 81),
        ],
    })
    .unwrap_or_else(|error| panic!("precedence {precedence}: {error}"));
    file
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

fn operand(file: &FileGrammar, expression: &str) -> Syntax {
    let source = format!("def result := bounded! [{expression}]");
    let syntax = parse(file, &source).unwrap_or_else(|error| panic!("{source}: {error}"));
    node(&syntax, "Library.bounded")[2].clone()
}

fn kind(syntax: &Syntax, expected: &str) {
    assert_eq!(syntax.kind(), Some(&name(expected)), "{syntax:?}");
}

#[test]
fn imported_operand_precedences_admit_the_complete_bounded_interval() {
    for precedence in 0..=MAX_PREC {
        let file = at_precedence(precedence);
        kind(&operand(&file, "42"), "num");
    }
}

#[test]
fn imported_operands_preserve_arithmetic_application_and_associativity() {
    let file = at_precedence(65);
    let arithmetic = operand(&file, "f a + b * c ^ d ^ e");
    kind(&arithmetic, "term_+_");
    let plus = node(&arithmetic, "term_+_");
    kind(&plus[0], "Lean.Parser.Term.app");
    kind(&plus[2], "term_*_");
    let power = node(&plus[2], "term_^_");
    kind(&power[2], "term_^_");

    let left = operand(&file, "a <+> b <+> c");
    let plus = node(&left, "Library.plus");
    kind(&plus[0], "Library.plus");
    let right = operand(&file, "a <^> b <^> c");
    let power = node(&right, "Library.power");
    kind(&power[2], "Library.power");

    let nested = operand(&file, "bounded! [a + b] * c");
    kind(&nested, "term_*_");
    assert!(contains(&nested, "Library.bounded"));
    kind(&operand(&at_precedence(66), "(a + b) * c"), "term_*_");
    kind(
        &operand(&at_precedence(256), "f a b"),
        "Lean.Parser.Term.app",
    );
    kind(
        &operand(&at_precedence(1022), "f a b"),
        "Lean.Parser.Term.app",
    );
}

#[test]
fn imported_operands_refuse_a_lower_precedence_without_consuming_its_suffix() {
    for (precedence, expression) in [
        (11, "f <| x"),
        (26, "A → B"),
        (26, "(x : Nat) → Nat"),
        (51, "a = b"),
        (66, "a + b"),
        (66, "a <+> b"),
        (71, "a * b"),
        (81, "a ^ b"),
        (81, "a <^> b"),
        (1023, "f a"),
        (1024, "f a"),
    ] {
        let source = format!("def result := bounded! [{expression}]");
        assert!(
            parse(&at_precedence(precedence), &source).is_err(),
            "{precedence}: {source}"
        );
    }
    kind(
        &operand(&at_precedence(25), "(x : Nat) → Nat"),
        "Lean.Parser.Term.depArrow",
    );
    kind(
        &operand(&at_precedence(51), "(a = b)"),
        "Lean.Parser.Term.paren",
    );
    for expression in ["a +", "a * * b", "a = b = c", "(a + b", "a)"] {
        let source = format!("def result := bounded! [{expression}]");
        assert!(parse(&at_precedence(65), &source).is_err(), "{source}");
    }
}

#[test]
fn imported_infix_rhs_minimum_is_independent_of_its_node_precedence() {
    for precedence in [0, 80] {
        let file = at_precedence(precedence);
        for (expression, expected) in [
            ("a <+~> b + c", "Library.looseRight"),
            ("a <+~+> b + c", "Library.equalRight"),
        ] {
            let syntax = operand(&file, expression);
            kind(&syntax, expected);
            kind(&node(&syntax, expected)[2], "term_+_");
        }
    }
    for precedence in [1023, 1024] {
        let syntax = operand(&at_precedence(precedence), "(a <+~> b + c)");
        kind(&syntax, "Lean.Parser.Term.paren");
        kind(&node(&syntax, "Library.looseRight")[2], "term_+_");
    }
    let file = at_precedence(50);
    assert!(parse(&file, "def bad := bounded! [a <!!> b <!!> c]").is_err());
    let syntax = operand(&file, "a <!!> (b <!!> c)");
    kind(&syntax, "Library.nonassoc");
    kind(
        &node(&syntax, "Library.nonassoc")[2],
        "Lean.Parser.Term.paren",
    );
}

#[test]
fn imported_operand_minimum_does_not_leak_into_prefix_or_binder_bodies() {
    // Lean 4's unary minus `«term-_»` has leading precedence 75 (`Init/Notation.lean:293`),
    // so `term:81` refuses `- a ^ b` while `term:75` accepts it without leaking into `a ^ b`.
    assert!(parse(&at_precedence(81), "def result := bounded! [- a ^ b]").is_err());
    let negative = operand(&at_precedence(75), "- a ^ b");
    kind(&negative, "term-_");
    assert!(contains(&negative, "term_^_"));
    let lambda = operand(&at_precedence(1022), "fun x => x + 1");
    kind(&lambda, "Lean.Parser.Term.fun");
    assert!(contains(&lambda, "term_+_"));
    let opened = operand(&at_precedence(1022), "open Nat in 1 + 2");
    kind(&opened, "Lean.Parser.Term.open");
    assert!(contains(&opened, "term_+_"));
}

fn add_shared_prefixes(file: &mut FileGrammar) {
    let mut declarations = Vec::new();
    for (declaration, head, precedence) in [
        ("Library.lowParser", "low!", 60),
        ("Library.highParser", "high!", 70),
        ("Library.highestParser", "highest!", 90),
    ] {
        let ImportedSyntaxEntry::Parser(declaration) = parser(
            declaration,
            "term",
            None,
            Descr::Node {
                // Parser declaration identities and result kinds are distinct.
                kind: name("Library.sharedKind"),
                prec: precedence,
                body: Box::new(sequence(symbol(head), Descr::Cat(name("term"), 75))),
            },
        ) else {
            unreachable!()
        };
        declarations.push(declaration);
    }
    file.import_native(&NativeSyntaxModule {
        declarations,
        ..NativeSyntaxModule::default()
    })
    .unwrap();
}

#[test]
fn leading_minimum_belongs_to_the_selected_parser_before_any_trailing_wrapper() {
    let mut file = at_precedence(65);
    add_shared_prefixes(&mut file);
    assert!(parse(&file, "def unrestricted := low! x").is_ok());
    kind(&operand(&file, "high! x"), "Library.sharedKind");
    for expression in [
        "low! x",
        "low! x y",
        "low! x.field",
        "low! x + y",
        "x + low! y",
        "- high! x",
    ] {
        let source = format!("def result := bounded! [{expression}]");
        assert!(parse(&file, &source).is_err(), "{source}");
    }
    kind(&operand(&file, "(low! x)"), "Lean.Parser.Term.paren");
    kind(&operand(&file, "x + (low! y)"), "term_+_");
}

#[test]
fn imported_trailing_lhs_minimum_checks_the_actual_leading_parser() {
    let mut file = at_precedence(0);
    add_shared_prefixes(&mut file);
    for expression in [
        "x <strict!> y",
        "(low! x) <strict!> y",
        "highest! x <strict!> y",
    ] {
        kind(&operand(&file, expression), "Library.strictLeft");
    }
    for expression in ["low! x <strict!> y", "high! x <strict!> y"] {
        let source = format!("def result := bounded! [{expression}]");
        assert!(parse(&file, &source).is_err(), "{source}");
    }
}

fn split_at(precedence: u32, separator: &str) -> FileGrammar {
    let mut file = grammar();
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("split!", None),
            token("done!", None),
            parser(
                "Library.split",
                "term",
                None,
                Descr::Node {
                    kind: name("Library.split"),
                    prec: LEAD_PREC,
                    body: Box::new(sequence(
                        symbol("split!"),
                        sequence(
                            Descr::Cat(name("term"), precedence),
                            sequence(
                                symbol(separator),
                                sequence(Descr::Cat(name("term"), MAX_PREC), symbol("done!")),
                            ),
                        ),
                    )),
                },
            ),
        ],
    })
    .unwrap();
    file
}

#[test]
fn an_operator_separator_is_available_only_when_the_operand_does_not_consume_it() {
    let source = "def result := split! a + b done!";
    assert!(parse(&split_at(66, "+"), source).is_ok());
    assert!(parse(&split_at(65, "+"), source).is_err());

    let file = split_at(81, "^");
    assert!(parse(&file, "def result := split! a ^ b done!").is_ok());
    // Negation's own operand is term:75. Its exponentiation belongs inside
    // that operand even though the surrounding category asks for term:81.
    assert!(parse(&file, "def result := split! - a ^ b done!").is_err());
}

fn add_open_body(file: &mut FileGrammar, leading: u32, minimum: u32, binder: bool) {
    let operand = Descr::Cat(name("term"), minimum);
    let body = if binder {
        sequence(Descr::Const(name("ident")), sequence(symbol("=>"), operand))
    } else {
        operand
    };
    file.import_artifact(&ImportedSyntaxModule {
        entries: vec![
            token("body!", None),
            parser(
                "Library.body",
                "term",
                None,
                Descr::Node {
                    kind: name("Library.body"),
                    prec: leading,
                    body: Box::new(sequence(symbol("body!"), body)),
                },
            ),
        ],
    })
    .unwrap();
}

#[test]
fn imported_open_ended_terms_keep_their_full_body_and_enclosing_delimiters() {
    let mut file = at_precedence(0);
    add_open_body(&mut file, LEAD_PREC, 0, true);
    for (expression, expected) in [
        ("body! x => f x + 1 * 2", "term_+_"),
        ("body! x => fun y => f x y", "Lean.Parser.Term.fun"),
        ("body! x => let y := x; y + 1", "Lean.Parser.Term.let"),
        ("body! x => body! y => x + y", "Library.body"),
    ] {
        let parsed = operand(&file, expression);
        kind(&parsed, "Library.body");
        kind(&node(&parsed, "Library.body")[3], expected);
    }
    let parenthesized = operand(&file, "(body! x => x) + 1");
    kind(&parenthesized, "term_+_");
    kind(
        &node(&parenthesized, "term_+_")[0],
        "Lean.Parser.Term.paren",
    );
    assert!(contains(&parenthesized, "Library.body"));
    kind(&operand(&file, "f (body! x => x)"), "Lean.Parser.Term.app");
    for expression in [
        "body! x =>",
        "body! => x",
        "body! x => x +",
        "f body! x => x",
    ] {
        let source = format!("def result := bounded! [{expression}]");
        assert!(parse(&file, &source).is_err(), "{source}");
    }
}

#[test]
fn imported_open_ended_operand_minima_leave_lower_precedence_suffixes_outside() {
    let mut file = at_precedence(0);
    add_open_body(&mut file, LEAD_PREC, 66, true);
    let parsed = operand(&file, "body! x => f x * y + z");
    kind(&parsed, "term_+_");
    let body = &node(&parsed, "term_+_")[0];
    kind(body, "Library.body");
    kind(&node(body, "Library.body")[3], "term_*_");

    let nested = operand(&file, "body! x => (f x + y) * z");
    kind(&nested, "Library.body");
    kind(&node(&nested, "Library.body")[3], "term_*_");
    assert!(contains(&nested, "term_+_"));

    // An inner prefix owns its operand precedence, independently of term:66.
    let negative = operand(&file, "body! x => - a ^ b + c");
    kind(&negative, "term_+_");
    let body = &node(&negative, "term_+_")[0];
    kind(&node(body, "Library.body")[3], "term-_");
    assert!(contains(body, "term_^_"));
}

#[test]
fn imported_simple_prefixes_honor_both_leading_and_operand_precedence() {
    let mut file = at_precedence(65);
    add_open_body(&mut file, 60, 75, false);
    let direct = parse(&file, "def result := body! a ^ b").unwrap();
    kind(&node(&direct, "Library.body")[1], "term_^_");
    assert!(
        parse(&file, "def result := bounded! [body! x]").is_err(),
        "a leading node at 60 cannot enter a term:65 operand"
    );
    kind(&operand(&file, "(body! x)"), "Lean.Parser.Term.paren");

    let mut file = at_precedence(0);
    add_open_body(&mut file, 90, 75, false);
    let parsed = operand(&file, "body! a ^ b * c + d");
    kind(&parsed, "term_+_");
    let product = &node(&parsed, "term_+_")[0];
    kind(product, "term_*_");
    let body = &node(product, "term_*_")[0];
    kind(body, "Library.body");
    kind(&node(body, "Library.body")[1], "term_^_");

    // The simple-prefix dispatch stores the operand minimum as u8. The
    // highest representable minimum still admits application (precedence 1023).
    let mut file = at_precedence(0);
    add_open_body(&mut file, 90, 255, false);
    kind(
        &node(&operand(&file, "body! f x"), "Library.body")[1],
        "Lean.Parser.Term.app",
    );
}

#[test]
fn unsupported_low_precedence_leading_shapes_leave_no_partial_import() {
    for body in [
        sequence(
            symbol("badBody!"),
            sequence(Descr::Const(name("ident")), Descr::Cat(name("term"), 0)),
        ),
        sequence(symbol("badBody!"), symbol("done!")),
        sequence(symbol("badBody!"), Descr::Cat(name("term"), 256)),
    ] {
        let mut file = grammar();
        let error = file
            .import_artifact(&ImportedSyntaxModule {
                entries: vec![
                    token("badBody!", None),
                    parser(
                        "Library.badBody",
                        "term",
                        None,
                        Descr::Node {
                            kind: name("Library.badBody"),
                            prec: 60,
                            body: Box::new(body),
                        },
                    ),
                ],
            })
            .unwrap_err();
        assert_eq!(
            error,
            "artifact term parser is not a supported leading production"
        );
        assert!(!file.grammar().table().contains("badBody!"));
        assert!(file.artifact.imported.is_empty());
    }
}
