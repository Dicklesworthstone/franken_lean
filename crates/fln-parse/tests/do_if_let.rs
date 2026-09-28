//! Pattern conditions use the ordinary pattern parser without inventing do scopes.
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

fn count(syntax: &Syntax, label: &str) -> usize {
    let expected = fln_core::name::Name::from_components(["Lean", "Parser", "Term", label]);
    let mut pending = vec![syntax];
    let mut found = 0;
    while let Some(syntax) = pending.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            found += usize::from(kind == &expected);
            pending.extend(args);
        }
    }
    found
}

#[test]
fn pure_and_monadic_pattern_headers_retain_the_pinned_syntax_shape() {
    for (assignment, kind) in [
        (":=", "doIfLetPure"),
        ("←", "doIfLetBind"),
        ("<-", "doIfLetBind"),
    ] {
        for source in [
            format!(
                "def run : Nat := do {{ if let .some x {assignment} value then {{ use x; use x }} else fallback; return 7 }}"
            ),
            format!(
                "def run : Nat := do\r\n  if let .some «𝒙» {assignment} value /- header -/ then\r\n    use «𝒙»\r\n    use «𝒙»\r\n  else\r\n    fallback\r\n  return 7"
            ),
        ] {
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(count(parsed.syntax(), "doIf"), 1);
            assert_eq!(count(parsed.syntax(), "doIfLet"), 1);
            assert_eq!(count(parsed.syntax(), kind), 1);
            assert_eq!(count(parsed.syntax(), "doIfProp"), 0);
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(
                parsed.reconstruct_normalized().unwrap(),
                source.replace("\r\n", "\n").as_bytes()
            );
        }
    }
}

#[test]
fn nested_patterns_guards_and_else_if_keep_statement_boundaries() {
    let source = "def run : Nat := do { if let .some (.some x) := value then { let y := x; use y } else if let .some _ <- action then fallback; return 7 }";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(count(parsed.syntax(), "doIfLet"), 2);
    assert_eq!(count(parsed.syntax(), "doLet"), 1);
    assert_eq!(count(parsed.syntax(), "do"), 1);
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
}

#[test]
fn nested_condition_expressions_and_term_let_separators_are_protected() {
    for value in [
        "(if flag then yes else no)",
        "(let x := value; x)",
        "(do { return value })",
    ] {
        let source =
            format!("def run : Nat := do {{ if let .some x := {value} then use x; return 7 }}");
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(count(parsed.syntax(), "doIfLet"), 1);
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
    }
}

#[test]
fn invalid_headers_are_not_laundered_into_ordinary_local_definitions() {
    for header in [
        "let := value",
        "let .some x value",
        "let .some x :=",
        "let .some x <-",
        "let .some x : Nat",
    ] {
        let source = format!("def run := do {{ if {header} then use; return 7 }}");
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn deep_pattern_conditionals_remain_on_the_heap_plan() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut source = String::from("def run : Nat := do { ");
            for _ in 0..1000 {
                source.push_str("if let .some x := value then { ");
            }
            source.push_str("use x");
            for _ in 0..1000 {
                source.push_str(" }");
            }
            source.push_str("; return 7 }");
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(count(parsed.syntax(), "doIfLet"), 1000);
            assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
        })
        .unwrap()
        .join()
        .unwrap();
}
