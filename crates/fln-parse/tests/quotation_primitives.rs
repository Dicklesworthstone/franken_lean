//! Token-parser quotations preserve primitive node kinds and source bytes.
//! Semantics: the pinned Parser.Extra token parsers and Basic.mkAntiquot.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::extensions::{FileGrammar, with_grammar};
use fln_parse::parse_source_command;
use fln_syntax::tree::Syntax;

fn parse(source: &str) -> Result<Syntax, String> {
    let file = FileGrammar::new(false, &[], None).unwrap();
    with_grammar(&file.grammar(), || parse_source_command(source.as_bytes()))
        .map(|command| command.syntax().clone())
        .map_err(|error| format!("{error:?}"))
}
fn dynamic_body(syntax: &Syntax) -> &Syntax {
    let mut pending = vec![syntax];
    while let Some(node) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = node {
            if *kind == Name::from_components(["Lean", "Parser", "Term", "dynamicQuot"]) {
                assert_eq!(args.len(), 5);
                return &args[3];
            }
            pending.extend(args);
        }
    }
    panic!("no dynamic quotation in {syntax:?}");
}

#[test]
fn primitive_quotations_keep_the_primitive_not_the_term_wrapper() {
    for (category, value) in [
        ("num", "0x2a"),
        ("str", "\"λ🙂\""),
        ("char", "'λ'"),
        ("scientific", "1.25e-3"),
        ("name", "`Example.member"),
        ("ident", "Example.member"),
    ] {
        let source = format!("def q := `({category}| {value})");
        let tree = parse(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
        let body = dynamic_body(&tree);
        if category == "ident" {
            assert!(matches!(body, Syntax::Ident { .. }));
        } else {
            let Syntax::Node { kind, args, .. } = body else {
                panic!("{body:?}")
            };
            assert_eq!(*kind, Name::from_components([category]));
            assert_eq!(args.len(), 1);
            assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == value));
        }
    }
}

#[test]
fn primitive_antiquotations_select_the_slots_kind_with_or_without_annotation() {
    for category in ["num", "str", "char", "scientific", "name", "ident"] {
        for variable in ["x", "_", "(x)"] {
            for annotated in [false, true] {
                let suffix = if annotated {
                    format!(":{category}")
                } else {
                    String::new()
                };
                let source = format!("def q := `({category}| ${variable}{suffix})");
                let tree = parse(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
                let Syntax::Node { kind, args, .. } = dynamic_body(&tree) else {
                    panic!("{tree:?}")
                };
                assert_eq!(*kind, Name::from_components([category, "antiquot"]));
                assert_eq!(args.len(), 4);
                assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "$"));
                let Syntax::Node {
                    args: annotation, ..
                } = &args[3]
                else {
                    panic!("{args:?}")
                };
                assert_eq!(annotation.len(), if annotated { 2 } else { 0 });
            }
        }
    }
}

#[test]
fn primitive_quotations_reject_wrong_types_annotations_and_partial_payloads() {
    for (category, bad) in [
        ("num", "\"42\""),
        ("str", "42"),
        ("ident", "42"),
        ("scientific", "42"),
        ("char", "\"x\""),
        ("name", "ordinary"),
        ("num", "$x:ident"),
        ("ident", "$x:num"),
        ("str", "$x:term"),
        ("num", "$x:"),
        ("num", "$ x"),
        ("num", "$ $x"),
        ("num", "$$ x"),
        ("num", "$$"),
        ("num", "$xs,*"),
        ("num", "42 43"),
        ("str", "\"x\" \"y\""),
        ("num", ""),
    ] {
        let source = format!("def q := `({category}| {bad})");
        assert!(parse(&source).is_err(), "accepted {source}");
    }
    assert!(parse("def outside := $x:num").is_err());
    assert!(parse("def recovered := `(num| 7)").is_ok());
}

#[test]
fn escaped_antiquotations_keep_each_dollar_and_the_primitive_capture_kind() {
    for category in ["ident", "num", "str", "char", "scientific", "name"] {
        for count in 1..=4 {
            let dollars = "$".repeat(count);
            let source = format!("def q := `({category}| {dollars}x:{category})");
            let tree = parse(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
            let Syntax::Node { kind, args, .. } = dynamic_body(&tree) else {
                panic!("{tree:?}");
            };
            assert_eq!(*kind, Name::from_components([category, "antiquot"]));
            assert_eq!(args.len(), 4);
            let Syntax::Node { args: escapes, .. } = &args[1] else {
                panic!("{args:?}");
            };
            assert_eq!(escapes.len(), count - 1);
            assert!(
                escapes
                    .iter()
                    .all(|escape| { matches!(escape, Syntax::Atom { val, .. } if val == "$") })
            );
            assert!(
                matches!(&args[2], Syntax::Ident { val, .. } if *val == Name::from_components(["x"]))
            );
        }
    }
}

#[test]
fn nested_antiquotation_expressions_obey_quotation_depth_and_recover_on_error() {
    for source in ["def q := `(num| $(f $x))", "def q := `(num| $(f)) trailing"] {
        assert!(parse(source).is_err(), "accepted {source}");
    }
    let source = "def q := `(num| $(f `(str| \"λ\")))";
    assert!(parse(source).is_ok(), "{source}");
    assert!(parse("def q := `(ident| «some identifier»)").is_ok());
}

/// Captured from Parser.Term's `binderIdent` alternatives on the pinned
/// frontend. Unlike parenthesized lambda terms, these positions preserve both
/// token-parser alternatives until the quotation selects its canonical capture.
#[test]
fn binder_captures_preserve_the_pins_ident_hole_choice() {
    for body in [
        "fun {$x : Type} => $x",
        "fun ⦃$x : Type⦄ => $x",
        "($x : Type) → $x",
        "∀ ($x : Type), $x",
        "let $x := 3; $x",
        "have $x : Nat := 3; $x",
    ] {
        let source = format!("def q := `({body})");
        let syntax = parse(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
        let mut pending = vec![&syntax];
        let mut choices = 0;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                if *kind == Name::from_components(["choice"]) {
                    choices += 1;
                    assert_eq!(args.len(), 2, "{source}");
                    assert_eq!(
                        args[0].kind(),
                        Some(&Name::from_components(["ident", "antiquot"]))
                    );
                    assert_eq!(
                        args[1].kind(),
                        Some(&Name::from_components([
                            "Lean", "Parser", "Term", "hole", "antiquot"
                        ]))
                    );
                    let (Syntax::Node { args: ident, .. }, Syntax::Node { args: hole, .. }) =
                        (&args[0], &args[1])
                    else {
                        panic!("{source}: {args:?}");
                    };
                    assert_eq!(ident, hole, "{source}");
                }
                pending.extend(args);
            }
        }
        assert_eq!(choices, 1, "{source}");
    }
    for body in [
        "fun ($x : Type) => $x",
        "fun {$x:ident : Type} => $x",
        "($x:ident : Type) → $x",
        "let $x:ident := 3; $x",
        "fun [$t:term] => 3",
    ] {
        let source = format!("def q := `({body})");
        let syntax = parse(&source).unwrap_or_else(|error| panic!("{source}: {error}"));
        let mut pending = vec![&syntax];
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                assert_ne!(*kind, Name::from_components(["choice"]), "{source}");
                pending.extend(args);
            }
        }
    }
    for source in [
        "def q := fun {$x : Type} => $x",
        "def q := let $x := 3; $x",
        "def q := `(∀ ($x:num : Type), $x)",
        "def q := `(let $x:num := 3; $x)",
    ] {
        assert!(parse(source).is_err(), "accepted {source}");
    }
}

#[test]
fn leading_macros_own_their_final_term_and_bound_host_reentry() {
    let mut file = FileGrammar::new(false, &[], None).unwrap();
    let source = r#"macro "bodyFn " x:ident " => " body:term : term => `(fun $x => $body)"#;
    let command =
        with_grammar(&file.grammar(), || parse_source_command(source.as_bytes())).unwrap();
    file.declare(command.syntax()).unwrap();
    for source in [
        "def increment : Nat → Nat := bodyFn n => n + 1",
        "def applied : Nat := (bodyFn n => n + 1) 41",
        "def nested := bodyFn x => bodyFn y => x + y",
    ] {
        let command = with_grammar(&file.grammar(), || parse_source_command(source.as_bytes()))
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(command.reconstruct_original(), source.as_bytes());
    }
    let source = format!("def excessive := {}0", "bodyFn x => ".repeat(64));
    assert!(with_grammar(&file.grammar(), || parse_source_command(source.as_bytes())).is_err());
    let source = "def recovered := bodyFn n => n + 1";
    assert!(with_grammar(&file.grammar(), || parse_source_command(source.as_bytes())).is_ok());
}
