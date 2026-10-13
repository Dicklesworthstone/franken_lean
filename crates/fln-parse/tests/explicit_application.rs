//! Explicit application keeps the canonical syntax shape and original bytes.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::{parse_definition, parse_nat_definition};
use fln_syntax::tree::Syntax;

#[test]
fn explicit_heads_preserve_comments_parentheses_and_universe_suffixes() {
    for text in [
        "def x : Nat := @id Nat 7",
        "def x : Nat := (@id) Nat 7",
        "def x : Nat := @id.{0} Nat 7",
        "def x : Nat := @id -- select explicit\r\n Nat 7\r\n",
        "def x : Nat := f (@g) 7",
    ] {
        let parsed = parse_definition(text.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), text.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            parsed.source_view().normalized().as_bytes()
        );
        let target = Name::from_components(["Lean", "Parser", "Term", "explicit"]);
        let mut pending = vec![parsed.syntax()];
        let mut count = 0;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                if kind == &target {
                    count += 1;
                    assert_eq!(args.len(), 2);
                    assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "@"));
                }
                pending.extend(args);
            }
        }
        assert_eq!(count, 1, "{text}");
    }
}

#[test]
fn missing_explicit_heads_are_not_repaired_and_nat_only_stays_narrow() {
    for text in [
        "def x : Nat := @",
        "def x : Nat := (@)",
        "def x : Nat := @ + 1",
    ] {
        assert!(parse_definition(text.as_bytes()).is_err(), "{text}");
    }
    assert!(parse_nat_definition(b"def x : Nat := @f Nat 7").is_err());
}

fn term_args<'a>(syntax: &'a Syntax, name: &str) -> &'a [Syntax] {
    let target = Name::from_components(["Lean", "Parser", "Term", name]);
    let mut pending = vec![syntax];
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &target {
                return args;
            }
            pending.extend(args.iter().rev());
        }
    }
    panic!("missing {name} term");
}

#[test]
fn raw_operator_arguments_keep_complete_nested_leading_terms() {
    // The v4.32.0 parser's `termParser maxPrec` accepts a whole leading
    // operator form here, including one without surrounding parentheses.
    for (kind, body, nested_index) in [
        ("binop", "binop% f unop% g a b", 2),
        ("binop_lazy", "binop_lazy% f a unop% g b", 3),
        ("binrel", "binrel% f unop% g a b", 2),
        ("binrel_no_prop", "binrel_no_prop% f a unop% g b", 3),
        ("leftact", "leftact% f a unop% g b", 3),
        ("rightact", "rightact% f unop% g a b", 2),
        ("unop", "unop% f unop% g a", 2),
    ] {
        let source = format!("def x : Nat := {body}");
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
        let args = term_args(parsed.syntax(), kind);
        assert_eq!(args.len(), if kind == "unop" { 3 } else { 4 });
        assert!(
            matches!(&args[1], Syntax::Ident { val, .. } if val == &Name::from_components(["f"]))
        );
        let Syntax::Node { kind, args, .. } = &args[nested_index] else {
            panic!("{source}: nested operand lost its operator node");
        };
        assert_eq!(
            kind,
            &Name::from_components(["Lean", "Parser", "Term", "unop"])
        );
        assert_eq!(args.len(), 3);
        assert!(
            matches!(&args[1], Syntax::Ident { val, .. } if val == &Name::from_components(["g"]))
        );
    }
}

#[test]
fn nested_binary_arity_leaves_trailing_application_outside_the_operator() {
    let source = b"def x : Nat := binop% f binop% g a b c d";
    let parsed = parse_definition(source).unwrap();
    let app = term_args(parsed.syntax(), "app");
    assert_eq!(app.len(), 2);
    let outer = term_args(&app[0], "binop");
    assert_eq!(outer.len(), 4);
    assert!(matches!(&outer[3], Syntax::Ident { val, .. } if val == &Name::from_components(["c"])));
    let inner = term_args(&outer[2], "binop");
    assert_eq!(inner.len(), 4);
    for (argument, name) in inner[1..].iter().zip(["g", "a", "b"]) {
        assert!(
            matches!(argument, Syntax::Ident { val, .. } if val == &Name::from_components([name]))
        );
    }
    let Syntax::Node { args, .. } = &app[1] else {
        panic!("trailing application arguments");
    };
    assert_eq!(args.len(), 1);
    assert!(matches!(&args[0], Syntax::Ident { val, .. } if val == &Name::from_components(["d"])));
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source);
}

#[test]
fn incomplete_and_deep_raw_operator_arguments_stay_bounded() {
    for body in [
        "binop% f unop% g a",
        "binop% f binop% g a b",
        "binop% f unop% (g) a b",
        "unop% f unop%",
    ] {
        assert!(
            parse_definition(format!("def x := {body}").as_bytes()).is_err(),
            "{body}"
        );
    }
    let source = format!("def x := {}a", "unop% f ".repeat(20_000));
    assert!(parse_definition(source.as_bytes()).is_err());
    // The refusal unwinds the existing nested-term guard on this same thread.
    assert!(parse_definition(b"def x := unop% f unop% g a").is_ok());
}
