//! Guarded do blocks retain original leaves and the enclosing control scope.
use super::*;
fn count(syntax: &Syntax, kind: &str) -> usize {
    // The pin's term `if` is the root-namespace notation `termIfThenElse`.
    let kind = if kind == "termIfThenElse" {
        Name::from_components([kind])
    } else {
        parser_kind(&["Term", kind])
    };
    let mut work = vec![syntax];
    let mut result = 0;
    while let Some(syntax) = work.pop() {
        if let Syntax::Node {
            kind: actual, args, ..
        } = syntax
        {
            result += usize::from(actual == &kind);
            work.extend(args);
        }
    }
    result
}
#[test]
fn guarded_multi_statement_blocks_round_trip_without_new_do_scopes() {
    for source in [
        "def run : Nat := do { unless flag do { let x := 7; visit x; after x }; return 42 }",
        "def run : Nat := do\r\n  unless flag /- condition -/ do\r\n    let «𝒙» := 7\r\n    visit «𝒙»\r\n    after «𝒙»\r\n  return 42",
    ] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
        assert_eq!(count(parsed.syntax(), "doUnless"), 1);
        assert_eq!(count(parsed.syntax(), "do"), 1);
        assert_eq!(count(parsed.syntax(), "doLet"), 1);
        assert_eq!(count(parsed.syntax(), "doExpr"), 2);
    }
}
#[test]
fn nested_guards_and_loops_keep_original_jump_nodes() {
    let source = "def run : Nat := do { for h : x in xs do { unless first do { unless second do { visit h; continue }; break } }; return 42 }";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(count(parsed.syntax(), "doFor"), 1);
    assert_eq!(count(parsed.syntax(), "doUnless"), 2);
    assert_eq!(count(parsed.syntax(), "doBreak"), 1);
    assert_eq!(count(parsed.syntax(), "doContinue"), 1);
    assert_eq!(count(parsed.syntax(), "do"), 1);
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
}
#[test]
fn missing_guard_predicates_delimiters_and_bodies_remain_refusals() {
    for source in [
        "def run := do { unless do action; return 7 }",
        "def run := do { unless flag action; return 7 }",
        "def run := do { unless flag do {}; return 7 }",
        "def run := do { unless flag do { let x := 7 }; return 7 }",
        "def run := do { unless flag do { continue; missing }; return 7 }",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    let source = "def run := do\r\n  unless flag do\r\n  return 7";
    assert_eq!(
        parse_definition(source.as_bytes())
            .unwrap_err()
            .primary_offset(),
        Some(BytePos(source.find("return").unwrap()))
    );
}
#[test]
fn parenthesized_predicates_and_escaped_guard_names_are_not_reinterpreted() {
    let source = "def run := do { «unless»; unless (if a then b else c) do { visit (do return 7) }; return 42 }";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(count(parsed.syntax(), "doUnless"), 1);
    assert_eq!(count(parsed.syntax(), "termIfThenElse"), 1);
    assert_eq!(count(parsed.syntax(), "do"), 2);
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
}
