//! Real branch source is parsed on the ordinary heap frames, not reparsed text.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::{parse_definition, parse_nat_definition};
use fln_syntax::tree::Syntax;

fn kind(label: &str) -> Name {
    // The pin's term `if` is the root-namespace notation `termIfThenElse`.
    if label == "termIfThenElse" {
        return Name::from_components([label]);
    }
    Name::from_components(["Lean", "Parser", "Term", label])
}
fn nodes<'a>(syntax: &'a Syntax, label: &str) -> Vec<&'a [Syntax]> {
    let expected = kind(label);
    let mut work = vec![syntax];
    let mut result = Vec::new();
    while let Some(syntax) = work.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &expected {
                result.push(args.as_slice());
            }
            work.extend(args.iter().rev());
        }
    }
    result
}
fn roundtrip(source: &str) -> fln_parse::ParsedDefinition {
    let parsed = parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source.replace("\r\n", "\n").as_bytes()
    );
    parsed
}

#[test]
fn braced_branch_sequences_retain_let_bind_action_and_outer_continuation() {
    let p = roundtrip(
        "def run := do { if flag then { let x := 7; let y <- action x; visit y } else { fallback; finish }; return 42 }",
    );
    assert_eq!(nodes(p.syntax(), "doIf").len(), 1);
    assert_eq!(nodes(p.syntax(), "doLet").len(), 1);
    assert_eq!(nodes(p.syntax(), "doLetArrow").len(), 1);
    assert_eq!(nodes(p.syntax(), "doReturn").len(), 1);
    assert_eq!(nodes(p.syntax(), "do").len(), 1);
    assert_eq!(nodes(p.syntax(), "doSeqBracketed").len(), 3);
}

#[test]
fn indented_branch_sequences_and_omitted_else_keep_original_scopes() {
    for source in [
        "def run := do\n  if flag then\n    let x := 7\n    action x\n    finish x\n  else\n    fallback\n    finish 9\n  return 42",
        "def run := do\r\n  if flag then\r\n    let «𝒙» := 7 /- local -/\r\n    visit «𝒙»\r\n    finish\r\n  return 42",
        "def run := do { if flag then { first; second }; return 42 }",
    ] {
        let p = roundtrip(source);
        assert_eq!(nodes(p.syntax(), "doIf").len(), 1);
        assert_eq!(nodes(p.syntax(), "do").len(), 1);
        let conditionals = nodes(p.syntax(), "doIf");
        let Syntax::Node { args, .. } = &conditionals[0][5] else {
            panic!("else clause")
        };
        assert_eq!(args.len(), if source.contains("else") { 2 } else { 0 });
    }
}

#[test]
fn outer_else_does_not_attach_to_a_more_indented_if_without_else() {
    let p = roundtrip(
        "def run := do\n  if outer then\n    if inner then\n      first\n      second\n  else\n    fallback\n  return 42",
    );
    let conditions = nodes(p.syntax(), "doIf");
    assert_eq!(conditions.len(), 2);
    let Syntax::Node { args: outer, .. } = &conditions[0][5] else {
        panic!("outer else")
    };
    let Syntax::Node { args: inner, .. } = &conditions[1][5] else {
        panic!("inner else")
    };
    assert_eq!(outer.len(), 2);
    assert_eq!(inner.len(), 0);
}

#[test]
fn else_if_layout_and_nearest_inline_else_remain_distinct() {
    // `else if` is one `doIf` with an else-if clause (the pin's `group (group "else" "if") …`);
    // an `if` in the `then` branch is a second `doIf`.
    for (source, conditionals, clauses) in [
        (
            "def run := do\n  if a then\n    first\n  else if b then\n    second\n  else\n    third\n  return 42",
            1,
            1,
        ),
        (
            "def run := do { if a then if b then first else second else third; return 42 }",
            2,
            0,
        ),
    ] {
        let p = roundtrip(source);
        assert_eq!(nodes(p.syntax(), "doIf").len(), conditionals, "{source}");
        let else_ifs: usize = nodes(p.syntax(), "doIf")
            .into_iter()
            .map(|parts| match &parts[4] {
                Syntax::Node { args, .. } => args.len(),
                _ => 0,
            })
            .sum();
        assert_eq!(else_ifs, clauses, "{source}");
        assert_eq!(nodes(p.syntax(), "do").len(), 1);
    }
}

#[test]
fn nested_loop_controls_stay_in_branch_sequences_not_new_do_expressions() {
    let p = roundtrip(
        "def run := do\n  for x in xs do\n    if x == 1 then\n      visit x\n      continue\n    else\n      for y in ys do\n        mark y\n        break\n      after x\n    remaining x\n  return 42",
    );
    assert_eq!(nodes(p.syntax(), "doIf").len(), 1);
    assert_eq!(nodes(p.syntax(), "doFor").len(), 2);
    assert_eq!(nodes(p.syntax(), "doContinue").len(), 1);
    assert_eq!(nodes(p.syntax(), "doBreak").len(), 1);
    assert_eq!(nodes(p.syntax(), "do").len(), 1);
}

#[test]
fn expression_conditionals_and_nested_do_keep_their_own_grammar() {
    for source in [
        "def run := do { let x := if a then 1 else 2; if b then { visit x }; return x }",
        "def run := do { let x := let y := 7; if a then y else 9; if b then { visit x }; return x }",
        "def run := do { if a then { visit (if b then 1 else 2) } else { visit (do { return 3 }) }; return 42 }",
        "def run := do\n  if a then\n    f (if b then 1 else 2)\n  else\n    f 3\n  return 42",
        "def run := do\n  if a then\n    let x := if b then 1 else 2\n    f x\n  else\n    f 3\n  return 42",
    ] {
        let p = roundtrip(source);
        assert_eq!(nodes(p.syntax(), "doIf").len(), 1);
        assert_eq!(nodes(p.syntax(), "termIfThenElse").len(), 1);
    }
    for source in [
        "def run := if flag then 7",
        "def run := do { let x := if flag then 7; return x }",
        "def run := do { visit (if flag then 7); return 42 }",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    assert!(parse_nat_definition(b"def run := do if flag then action").is_err());
}

#[test]
fn malformed_and_empty_branches_are_not_absent_else() {
    for source in [
        "def run := do if flag then",
        "def run := do { if flag then {}; return 42 }",
        "def run := do { if flag then { action } else {}; return 42 }",
        "def run := do { if flag then action else; return 42 }",
        "def run := do { if then action; return 42 }",
        "def run := do { if flag then { break 7 }; return 42 }",
        "def run := do { if flag then { continue; unreachable }; return 42 }",
        "def run := do\n  if flag then\n  return 42",
        "def run := do\n  if flag then\n    action\n  else\n  return 42",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn terminal_branch_returns_are_source_nodes_and_do_not_capture_outer_actions() {
    let p = roundtrip(
        "def select := do\n  if flag then\n    let x := 7\n    return x\n  else\n    return 9",
    );
    assert_eq!(nodes(p.syntax(), "doReturn").len(), 2);
    assert_eq!(nodes(p.syntax(), "doIf").len(), 1);
    assert_eq!(nodes(p.syntax(), "do").len(), 1);
}

#[test]
fn conditionals_compose_with_unless_and_membership_loop_headers() {
    for source in [
        "def run := do { for h : x in xs do { if flag then { unless other do { visit h; continue } }; after x }; return 42 }",
        "def run := do\n  unless flag do\n    if ready then\n      first\n      second\n    after\n  return 42",
    ] {
        let p = roundtrip(source);
        assert_eq!(nodes(p.syntax(), "doIf").len(), 1);
        assert_eq!(nodes(p.syntax(), "doUnless").len(), 1);
        assert_eq!(nodes(p.syntax(), "do").len(), 1);
    }
}

#[test]
fn nested_branches_parse_without_consuming_the_native_call_stack() {
    std::thread::Builder::new()
        .name("deep-do-branches".into())
        .stack_size(128 * 1024)
        .spawn(|| {
            let depth = 1500;
            let source = format!(
                "def run := do {{ {}action{}; return 42 }}",
                "if flag then { ".repeat(depth),
                " }".repeat(depth)
            );
            let p = parse_definition(source.as_bytes()).expect("deep parse");
            assert_eq!(p.reconstruct_normalized().unwrap(), source.as_bytes());
            assert_eq!(nodes(p.syntax(), "doIf").len(), depth);
            assert_eq!(nodes(p.syntax(), "do").len(), 1);
        })
        .unwrap()
        .join()
        .unwrap();
}
