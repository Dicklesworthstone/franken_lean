//! Explicit do delimiters must not become record syntax or close outer scopes.
#![forbid(unsafe_code)]
use fln_parse::parse_definition;

#[test]
fn bracketed_do_preserves_tokens_and_nests_with_layout_and_records() {
    for source in [
        "def f : Id Nat := do { return 7 }",
        "def f : Id Nat := do { let x <- a; return x; }",
        "def f : Id Nat := do { let x : Nat ← a; let y := x; return y }",
        "def f : Id Nat := do {\r\n  let x ← a; /- keep -/\r\n  return x\r\n}",
        "def f : Id Nat := do { let x ← (do { return 7 }); return x }",
        "def f : Id Nat := do\n  let x ← do { return 7 }\n  return x",
        "def f : Id Nat := do { let x := { value := 7 }; return x.value }",
        "def f : Id Nat := take (do { return 7 })",
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
    }
}

#[test]
fn malformed_braces_and_incomplete_statements_are_refused() {
    for source in [
        "def f : Id Nat := do {}",
        "def f : Id Nat := do { return 7",
        "def f : Id Nat := do { return 7 )",
        "def f : Id Nat := do { return 7 }}",
        "def f : Id Nat := do { let x := 7 }",
        "def f : Id Nat := do { let x ← a; }",
        "def f : Id Nat := do { return 7; return 8 }",
        "def f : Id Nat := do { a;; return 7 }",
        "def f : Id Nat := do { let x : Nat }",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn adjacent_bracketed_arguments_do_not_merge_their_scopes() {
    let source = "def f : Id Nat := combine (do { return 1 }) (do { return 2 })";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
}
