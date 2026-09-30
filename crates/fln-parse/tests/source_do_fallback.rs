//! Refutable do-bind grammar preserves the pinned fallback/continuation slots.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

fn nodes<'a>(syntax: &'a Syntax, label: &str) -> Vec<&'a [Syntax]> {
    let mut pending = vec![syntax];
    let mut result = Vec::new();
    let expected = Name::from_components(["Lean", "Parser", "Term", label]);
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
fn monadic_fallback_retains_original_leaves_and_captured_continuation() {
    for source in [
        "def f : Nat := do\n  let Maybe.some x ← action | return 0\n  return x",
        "def f : Nat := do\r\n  let Maybe.some «𝒙» : Maybe Nat <- action /- once -/ | return 0\r\n  return «𝒙»",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        let patterns = nodes(parsed.syntax(), "doPatDecl");
        assert_eq!(patterns.len(), 1);
        assert_eq!(patterns[0].len(), 5);
        let Syntax::Node { args, .. } = &patterns[0][4] else {
            panic!("fallback slots")
        };
        assert_eq!(args.len(), 3);
        assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "|"));
        assert_eq!(nodes(&args[1], "doReturn").len(), 1);
        assert_eq!(nodes(&args[2], "doReturn").len(), 1);
        assert_eq!(nodes(parsed.syntax(), "do").len(), 1);
        assert!(nodes(parsed.syntax(), "nativeDoFailureValue").is_empty());
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            parsed.source_view().normalized().as_bytes()
        );
    }
}

#[test]
fn tactic_alternatives_outside_do_are_not_failure_branches() {
    // Only a `do` block has refutable bindings: after a term `have`, `first | a | b`
    // belongs to the proof parser, as it did before failure branches existed.
    for source in [
        "theorem t : 0 = 0 := have n : Nat := 0; by first | exact (show n = 0 from rfl) | rfl",
        "theorem t : 0 = 0 := have n : Nat := 0\n  by first | rfl | rfl",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert!(nodes(parsed.syntax(), "doPatDecl").is_empty());
        assert!(nodes(parsed.syntax(), "do").is_empty());
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
}

#[test]
fn pure_fallback_uses_the_separate_pinned_do_let_else_production() {
    let source = "def f : Nat := do\n  let (Maybe.some x) := value | return 0\n  return x";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    let patterns = nodes(parsed.syntax(), "doLetElse");
    assert_eq!(patterns.len(), 1);
    assert_eq!(patterns[0].len(), 9);
    assert_eq!(nodes(&patterns[0][7], "doReturn").len(), 1);
    assert_eq!(nodes(&patterns[0][8], "doReturn").len(), 1);
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
}

#[test]
fn nested_failures_and_outer_match_pipes_keep_their_owners() {
    for source in [
        "def f : Nat := do\n  let Maybe.some x ← action |\n    let Maybe.some y ← other | return 1\n    return y\n  return x",
        "def f : Nat := do\n  match value with\n  | Maybe.some outer =>\n    let Maybe.some inner ← action | return 0\n    return inner\n  | Maybe.none => return 1",
        "def f : Nat := do\n  if flag then\n    let Maybe.some x ← action | return 0\n    return x\n  else\n    return 1",
        "def f : Nat := do\n  let Maybe.some x ← (match flag with | true => left | false => right) |\n    if flag then return 1 else return 2\n  return x",
        "def f : Nat := do\n  let Maybe.some x ← action\n  | return 0\n  return x",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert!(nodes(parsed.syntax(), "nativeDoFailureValue").is_empty());
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            parsed.source_view().normalized().as_bytes()
        );
    }
}

#[test]
fn explicit_do_in_the_failure_arm_has_an_independent_return_scope() {
    let source = "def f : Nat := do\n  let Maybe.some x ← action |\n    let y ← (do { return 3 })\n    return y\n  return x";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(nodes(parsed.syntax(), "do").len(), 2);
    assert_eq!(nodes(parsed.syntax(), "doReturn").len(), 3);
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
}

#[test]
fn malformed_failures_never_discard_source() {
    for source in [
        "def f : Nat := do\n  let Maybe.some x ← action |\n",
        "def f : Nat := do\n  let Maybe.some x ← | return 0\n  return x",
        "def f : Nat := do\n  let Maybe.some x ← action | return 0; hidden\n  return x",
        "def f : Nat := do\n  let Maybe.some x ← action | return 0\n | return x",
        "def f : Nat := do\n  let mut Maybe.some x ← action | return 0\n  return x",
        "def f : Nat := do\n  let rec Maybe.some x ← action | return 0\n  return x",
        "def f : Nat := do\n  let Maybe.some x ← action | { return 0 }\n  return x",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn long_fallback_chains_use_heap_plans_and_preserve_each_source_leaf() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut source = String::from("def f : Nat := do\n");
            for index in 0..128 {
                source.push_str(&format!(
                    "  let Maybe.some x{index} ← action | return {index}\n"
                ));
            }
            source.push_str("  return x127");
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(nodes(parsed.syntax(), "doPatDecl").len(), 128);
            assert_eq!(nodes(parsed.syntax(), "doReturn").len(), 129);
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        })
        .unwrap()
        .join()
        .unwrap();
}
