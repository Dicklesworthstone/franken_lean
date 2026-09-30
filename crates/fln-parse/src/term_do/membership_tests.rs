//! Membership binders retain the pin's optional identifier-colon syntax.
use super::*;

fn declarations(syntax: &Syntax) -> Vec<&[Syntax]> {
    let mut result = Vec::new();
    let mut work = vec![syntax];
    while let Some(syntax) = work.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &parser_kind(&["Term", "doForDecl"]) {
                result.push(args.as_slice());
            }
            work.extend(args.iter().rev());
        }
    }
    result
}

#[test]
fn membership_binders_and_wildcards_preserve_every_original_leaf() {
    for source in [
        "def run : Nat := do { for h : x in xs do { visit x h }; return 7 }",
        "def run : Nat := do\r\n  for «𝒉» /- witness -/ : «𝒙» in xs do\r\n    visit «𝒙» «𝒉»\r\n  return 7",
        "def run : Nat := do { for h : _ in xs do { visit h }; return 7 }",
        "def run : Nat := do { for _ in xs do { visit }; return 7 }",
    ] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
        let declarations = declarations(parsed.syntax());
        assert_eq!(declarations.len(), 1);
        let parts = declarations[0];
        assert_eq!(parts.len(), 4);
        let Syntax::Node { kind, args, .. } = &parts[0] else {
            panic!("the optional binder has a null container")
        };
        assert_eq!(kind, &state::null_kind());
        assert_eq!(args.len(), if source.contains("for _") { 0 } else { 2 });
        if let [name, colon] = args.as_slice() {
            assert!(matches!(name, Syntax::Ident { .. }));
            assert!(matches!(colon, Syntax::Atom { val, .. } if val == ":"));
        }
        if source.contains("_ in") {
            assert!(matches!(&parts[1], Syntax::Node { kind, args, .. }
                if kind == &parser_kind(&["Term", "hole"])
                    && matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "_")));
        }
    }
}

#[test]
fn nested_witnesses_and_conditional_terms_keep_distinct_headers() {
    let source = "def run : Nat := do { for h : x in (if flag then xs else ys) do { for k : y in zs do { visit x h y k } }; return 7 }";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(declarations(parsed.syntax()).len(), 2);
    assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
}

#[test]
fn malformed_membership_headers_never_fall_back_to_ordinary_for() {
    for header in [
        "h : : x in xs",
        "_ : x in xs",
        "A.h : x in xs",
        "h : A.x in xs",
        "h : in xs",
        "h : (x, y) in xs",
        "h : x xs",
        "h : x in",
    ] {
        let source = format!("def run : Nat := do {{ for {header} do {{ visit }}; return 7 }}");
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn missing_dependent_loop_body_reports_original_crlf_position() {
    let source = "def run : Nat := do\r\n  for h : x in xs do\r\n  return 7";
    let error = parse_definition(source.as_bytes()).unwrap_err();
    assert_eq!(
        error.primary_offset(),
        Some(BytePos(source.find("return").unwrap()))
    );
}
