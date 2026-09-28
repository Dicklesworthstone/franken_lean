//! Real multi-arm statement matches retain source leaves and control scopes.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::{ParsedDefinition, parse_definition};
use fln_syntax::tree::Syntax;

fn count(syntax: &Syntax, label: &str) -> usize {
    let expected = Name::from_components(["Lean", "Parser", "Term", label]);
    let mut pending = vec![syntax];
    let mut n = 0;
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            n += usize::from(kind == &expected);
            pending.extend(args);
        }
    }
    n
}
fn roundtrip(source: &str) -> ParsedDefinition {
    let parsed = parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source.replace("\r\n", "\n").as_bytes()
    );
    parsed
}

#[test]
fn indented_and_braced_arms_contain_statements_not_independent_do_expressions() {
    for source in [
        "def run := do\n  match value with\n  | .found x =>\n    let y := x\n    visit y\n    finish y\n  | .absent =>\n    fallback\n  return 42",
        "def run := do { match value with | .found x => { let y := x; visit y; finish y } | .absent => { fallback }; return 42 }",
        "def run := do\r\n  match value /- discriminant -/ with\r\n  | .found «𝒙» =>\r\n    let y := «𝒙»\r\n    visit y\r\n    finish y\r\n  | .absent =>\r\n    fallback\r\n  return 42",
    ] {
        let p = roundtrip(source);
        assert_eq!(count(p.syntax(), "doMatch"), 1);
        assert_eq!(count(p.syntax(), "do"), 1);
        assert_eq!(count(p.syntax(), "doLet"), 1);
        assert_eq!(count(p.syntax(), "doReturn"), 1);
        assert_eq!(count(p.syntax(), "doExpr"), 3);
    }
}

#[test]
fn nested_match_if_and_unless_leave_the_outer_match_arms_distinct() {
    for source in [
        "def run := do\n  match a with\n  | true =>\n    match b with\n    | true =>\n      first\n      second\n    | false =>\n      third\n    after\n  | false =>\n    fallback\n  return 42",
        "def run := do\n  match a with\n  | true =>\n    if b then\n      first\n      second\n    else\n      third\n    after\n  | false =>\n    unless c do\n      fallback\n  return 42",
        "def run := do\n  if a then\n    match b with\n    | true =>\n      first\n      second\n    | false =>\n      third\n  else\n    fallback\n  return 42",
    ] {
        let p = roundtrip(source);
        assert_eq!(count(p.syntax(), "do"), 1);
        assert_eq!(
            count(p.syntax(), "doMatch"),
            if source.contains("match a") && source.contains("match b") {
                2
            } else {
                1
            }
        );
    }
}

#[test]
fn named_and_multiple_discriminants_and_nested_patterns_retain_their_source() {
    let p = roundtrip(
        "def run := do\n  match h : xs, value with\n  | [x], .found (.found y) =>\n    let z <- visit x y h\n    finish z\n  | _, _ =>\n    fallback\n  return 42",
    );
    assert_eq!(count(p.syntax(), "doMatch"), 1);
    assert_eq!(count(p.syntax(), "doLetArrow"), 1);
    assert_eq!(count(p.syntax(), "matchDiscr"), 2);
}

#[test]
fn loop_exits_and_genuine_nested_do_returns_keep_distinct_scopes() {
    let p = roundtrip(
        "def run := do\n  for x in xs do\n    match x with\n    | 1 =>\n      visit x\n      continue\n    | _ =>\n      visit (do return x)\n      break\n  return 42",
    );
    assert_eq!(count(p.syntax(), "doMatch"), 1);
    assert_eq!(count(p.syntax(), "doFor"), 1);
    assert_eq!(count(p.syntax(), "doContinue"), 1);
    assert_eq!(count(p.syntax(), "doBreak"), 1);
    assert_eq!(count(p.syntax(), "doReturn"), 2);
    assert_eq!(count(p.syntax(), "do"), 2);
}

#[test]
fn term_matches_inside_actions_bindings_and_parentheses_stay_term_matches() {
    for source in [
        "def run := do { let y := (match x with | true => 1 | false => 2); visit y; return 42 }",
        "def run := do\n  match x with\n  | true =>\n    let y := match x with | true => 1 | false => 2\n    visit y\n  | false =>\n    fallback\n  return 42",
        "def run := do { match x with | true => { visit (match x with | true => 1 | false => 2) } | false => { fallback }; return 42 }",
    ] {
        let p = roundtrip(source);
        assert_eq!(count(p.syntax(), "match"), 1);
    }
}

#[test]
fn malformed_or_empty_statement_matches_never_synthesize_a_fallthrough_arm() {
    for source in [
        "def run := do match x with",
        "def run := do { match x with | true => {}; return 42 }",
        "def run := do { match x with | true => { visit } | false => {}; return 42 }",
        "def run := do { match x with | true => { let y := 7 }; return 42 }",
        "def run := do { match x with | true => { continue; missing }; return 42 }",
        "def run := do\n    match x with\n    | true =>\n  return 42",
        "def run := do\n  match x with\n  | true =>\n    visit\n   | false =>\n    fallback",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn deep_statement_matches_use_heap_frames_on_a_small_native_stack() {
    std::thread::Builder::new()
        .name("deep-do-match".into())
        .stack_size(128 * 1024)
        .spawn(|| {
            let depth = 800;
            let source = format!(
                "def run := do {{ {}visit{}; return 42 }}",
                "match x with | _ => { ".repeat(depth),
                " }".repeat(depth)
            );
            let p = roundtrip(&source);
            assert_eq!(count(p.syntax(), "doMatch"), depth);
            assert_eq!(count(p.syntax(), "do"), 1);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn an_arm_body_may_start_in_the_pipe_column_as_the_pin_requires() {
    // Term.matchAlt uses checkColGe, not checkColGt. A same-column RHS
    // belongs to this arm, whereas an offside RHS is missing (tested above).
    let p = roundtrip("def run := do\n  match x with\n  | true =>\n  return 42");
    assert_eq!(count(p.syntax(), "doMatch"), 1);
    assert_eq!(count(p.syntax(), "doReturn"), 1);
}

#[test]
fn a_single_monadic_discriminant_preserves_its_arrow_and_branches() {
    for arrow in ["←", "<-"] {
        let source = format!(
            "def run := do\n  match {arrow} fetch flag with\n  | .found x =>\n    visit x\n    return x\n  | .absent =>\n    fallback\n  return 42"
        );
        let p = roundtrip(&source);
        assert_eq!(count(p.syntax(), "nestedAction"), 1);
        assert_eq!(count(p.syntax(), "doMatch"), 1);
        assert_eq!(count(p.syntax(), "do"), 1);
    }
    for source in [
        "def bad := do match ← with | _ => return 7",
        "def bad := do match ← first, second with | _, _ => return 7",
        "def bad := match ← first with | _ => 7",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}
