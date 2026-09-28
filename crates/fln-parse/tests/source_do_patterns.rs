//! Parser coverage for immutable monadic destructuring on the shared term stack.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

fn nodes<'a>(syntax: &'a Syntax, leaf: &str) -> Vec<&'a [Syntax]> {
    let expected = Name::from_components(["Lean", "Parser", "Term", leaf]);
    let mut pending = vec![syntax];
    let mut result = Vec::new();
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &expected {
                result.push(args.as_slice());
            }
            pending.extend(args.iter().rev());
        }
    }
    result
}

#[test]
fn named_binds_keep_their_existing_canonical_node() {
    let parsed = parse_definition(b"def f : Nat := do let x : Nat <- action; return x").unwrap();
    assert_eq!(nodes(parsed.syntax(), "doIdDecl").len(), 1);
    assert!(nodes(parsed.syntax(), "doPatDecl").is_empty());
}

#[test]
fn nested_patterns_annotations_and_both_arrows_have_the_pinned_shape() {
    for source in [
        "def f : Nat := do let Pair.mk a b ← action; return a",
        "def f : Nat := do { let Wrapped.mk (Pair.mk a _) : Wrapped <- action; return a }",
        "def f : Nat := do\r\n  let Pair.mk «𝒙» _ /- pattern -/ ← action\r\n  return «𝒙»",
        "def f : Nat := do let _ ← action; return 42",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        let patterns = nodes(parsed.syntax(), "doPatDecl");
        assert_eq!(patterns.len(), 1, "{source}");
        assert_eq!(patterns[0].len(), 5, "{source}");
        assert!(matches!(&patterns[0][2], Syntax::Atom { val, .. }
            if val == "←" || val == "<-"));
        assert!(matches!(&patterns[0][4], Syntax::Node { kind, args, .. }
            if kind == &Name::from_components(["null"]) && args.is_empty()));
    }
}

#[test]
fn pattern_binders_do_not_consume_nested_actions_or_the_next_statement() {
    let source =
        "def f : Nat := do\n  let Pair.mk a b ← (do { return pair })\n  let _ ← action\n  return a";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(nodes(parsed.syntax(), "doPatDecl").len(), 2);
    assert_eq!(nodes(parsed.syntax(), "do").len(), 2);
    assert_eq!(nodes(parsed.syntax(), "doReturn").len(), 2);
}

#[test]
fn incomplete_patterns_and_unhandled_control_forms_fail_closed() {
    for source in [
        "def f : Nat := do let Pair.mk a b; return a",
        "def f : Nat := do let Pair.mk a b ←; return a",
        "def f : Nat := do let Pair.mk a b : ← action; return a",
        "def f : Nat := do { let Pair.mk a b ← action }",
        "def f : Nat := do let mut Pair.mk a b ← action; return a",
        "def f : Nat := do let rec Pair.mk a b ← action; return a",
        "def f : Nat := do let Pair.mk a b ← action | return 0; return a",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn long_pattern_bind_chains_stay_on_the_existing_heap_frames() {
    let mut source = String::from("def f : Nat := do\n");
    for index in 0..128 {
        source.push_str(&format!("  let Pair.mk x{index} y{index} ← action\n"));
    }
    source.push_str("  return x127");
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(nodes(parsed.syntax(), "doPatDecl").len(), 128);
}
