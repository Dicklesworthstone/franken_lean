//! Postcondition loops retain the pin's four source children on heap frames.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::{ParsedDefinition, parse_definition};
use fln_syntax::tree::Syntax;

fn nodes<'a>(syntax: &'a Syntax, label: &str) -> Vec<&'a [Syntax]> {
    let expected = Name::from_components(["Lean", "Parser", "Term", label]);
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

fn parsed(source: &str) -> ParsedDefinition {
    let parsed = parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source.replace("\r\n", "\n").as_bytes()
    );
    parsed
}

#[test]
fn postcondition_owns_original_delimiters_body_and_condition() {
    for source in [
        "def run := do\n  repeat\n    step\n  until ready\n  return 42",
        "def run := do { repeat { first; step } until ready; return 42 }",
        "def run := do repeat step until ready; return 42",
        "def run := do\r\n  repeat /- body -/\r\n    step\r\n  until /- test -/ ready\r\n  return 42\r\n",
    ] {
        let p = parsed(source);
        let loops = nodes(p.syntax(), "doRepeatUntil");
        assert_eq!(loops.len(), 1);
        let [repeat, body, until, condition] = loops[0] else {
            panic!("four source children")
        };
        assert!(matches!(repeat, Syntax::Atom { val, .. } if val == "repeat"));
        assert!(matches!(until, Syntax::Atom { val, .. } if val == "until"));
        assert!(matches!(body, Syntax::Node { kind, .. }
            if kind == &Name::from_components(["Lean", "Parser", "Term", "doSeqIndent"])
            || kind == &Name::from_components(["Lean", "Parser", "Term", "doSeqBracketed"])));
        assert!(
            matches!(condition, Syntax::Ident { val, .. } if val == &Name::from_components(["ready"]))
        );
        assert!(nodes(p.syntax(), "doRepeat").is_empty());
        assert_eq!(nodes(p.syntax(), "doReturn").len(), 1);
    }
}

#[test]
fn nearest_repeat_owns_until_and_preserves_outer_continuations() {
    for source in [
        "def run := do\n  repeat\n    repeat\n      inner\n    until innerReady\n    outer\n  until outerReady\n  return 42",
        "def run := do { repeat { repeat inner until innerReady; outer } until outerReady; return 42 }",
        "def run := do repeat repeat inner until innerReady until outerReady; return 42",
    ] {
        let p = parsed(source);
        let loops = nodes(p.syntax(), "doRepeatUntil");
        assert_eq!(loops.len(), 2);
        assert!(matches!(&loops[0][3], Syntax::Ident { val, .. }
            if val == &Name::from_components(["outerReady"])));
        assert!(matches!(&loops[1][3], Syntax::Ident { val, .. }
            if val == &Name::from_components(["innerReady"])));
        assert_eq!(nodes(p.syntax(), "doReturn").len(), 1);
    }
}

#[test]
fn a_braced_inner_repeat_does_not_close_its_ancestors_branch() {
    let p = parsed(
        "def run := do\n  repeat\n    if flag then\n      repeat { step } until innerReady\n      branchAfter\n    outerAfter\n  until outerReady\n  return 42",
    );
    let loops = nodes(p.syntax(), "doRepeatUntil");
    assert_eq!(loops.len(), 2);
    assert!(matches!(&loops[0][3], Syntax::Ident { val, .. }
        if val == &Name::from_components(["outerReady"])));
    assert!(matches!(&loops[1][3], Syntax::Ident { val, .. }
        if val == &Name::from_components(["innerReady"])));
    let conditionals = nodes(p.syntax(), "doIf");
    assert_eq!(conditionals.len(), 1);
    assert_eq!(nodes(&conditionals[0][3], "doRepeatUntil").len(), 1);
}

#[test]
fn compound_body_and_condition_keep_different_control_scopes() {
    for source in [
        "def run := do\n  repeat\n    if skip then continue\n    step\n  until ready\n  return 42",
        "def run := do repeat if skip then continue else step until ready; return 42",
        "def run := do repeat match value with | some x => visit x | none => break until ready; return 42",
        "def run := do repeat try step catch e => recover e until ready; return 42",
        "def run := do repeat do step until (if flag then ready else other); return 42",
        "def run := do repeat step until (← poll); return 42",
        "def run := do repeat step until if flag then ready else other; return 42",
    ] {
        let p = parsed(source);
        assert_eq!(nodes(p.syntax(), "doRepeatUntil").len(), 1);
        assert_eq!(nodes(p.syntax(), "doReturn").len(), 1);
    }
}

#[test]
fn malformed_or_orphaned_until_never_becomes_an_action_call() {
    for source in [
        "def run := do until ready",
        "def run := do repeat until ready",
        "def run := do repeat step until",
        "def run := do { repeat { step } until; return 42 }",
        "def run := do repeat step until ; return 42",
        "def run := do repeat step until ready until other",
        "def run := do { repeat { step until ready }; return 42 }",
        "def run := do repeat let x := 7 until ready",
        "def run := repeat step until ready",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    let p = parsed("def run := do repeat «until» 7; break");
    assert_eq!(nodes(p.syntax(), "doRepeat").len(), 1);
    assert!(nodes(p.syntax(), "doRepeatUntil").is_empty());
}

#[test]
fn nested_postcondition_loops_use_the_existing_heap_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut source = String::from("def run := do ");
            for _ in 0..300 {
                source.push_str("repeat { ");
            }
            source.push_str("step");
            for _ in 0..300 {
                source.push_str(" } until ready");
            }
            source.push_str("; return 42");
            let p = parsed(&source);
            assert_eq!(nodes(p.syntax(), "doRepeatUntil").len(), 300);
        })
        .unwrap()
        .join()
        .unwrap();
}
