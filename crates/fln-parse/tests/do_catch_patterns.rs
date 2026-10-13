//! Pattern catches reuse the lossless do-match planner and its arm scopes.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

fn nodes<'a>(syntax: &'a Syntax, label: &str) -> Vec<&'a [Syntax]> {
    let wanted = Name::from_components(["Lean", "Parser", "Term", label]);
    let mut work = vec![syntax];
    let mut found = Vec::new();
    while let Some(syntax) = work.pop() {
        if let Syntax::Node { kind, args, .. } = syntax {
            if kind == &wanted {
                found.push(args.as_slice());
            }
            work.extend(args.iter().rev());
        }
    }
    found
}

#[test]
fn pattern_catch_forms_retain_original_source() {
    for source in [
        "def f := do { try { action } catch | .bad n => { recover n } | .other => { fallback } }",
        "def f := do\n  try\n    action\n  catch\n  | .bad n => recover n\n  | .other => fallback",
        "def f := do { try { action } catch | .bad n => { first n; second } | .other => { fallback } finally { cleanup }; suffix }",
        "def f := do { try { action } catch | .bad n => { first n } | _ => { fallback } catch e => { recover e } }",
        "-- lossless\r\ndef f := do\r\n  try\r\n    action -- protected\r\n  catch\r\n  | .bad «é» =>\r\n    recover «é» -- matched\r\n  | _ => fallback\r\n",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
        assert_eq!(nodes(parsed.syntax(), "doCatchMatch").len(), 1);
    }
}

#[test]
fn a_pattern_clause_is_one_catch_with_do_match_alternatives() {
    let source = "def f := do { try { action } catch | .bad n => { first n; second } | _ => { fallback }; suffix }";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    let clauses = nodes(parsed.syntax(), "doCatchMatch");
    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0].len(), 2);
    assert!(matches!(&clauses[0][0], Syntax::Atom {val,..} if val == "catch"));
    assert!(nodes(parsed.syntax(), "doCatch").is_empty());
    let rows = nodes(&clauses[0][1], "matchAlt");
    assert_eq!(rows.len(), 2);
    assert_eq!(nodes(&rows[0][3], "doSeqItem").len(), 2);
    assert_eq!(nodes(&rows[1][3], "doSeqItem").len(), 1);
    // The suffix is a sibling of the try, not an extra item of its final arm.
    let ordinary_do = nodes(parsed.syntax(), "do");
    let Syntax::Node { args, .. } = &ordinary_do[0][1] else {
        panic!("do sequence")
    };
    let Syntax::Node { args: items, .. } = &args[1] else {
        panic!("braced items")
    };
    assert_eq!(items.len(), 2);
}

#[test]
fn mixed_catch_chains_and_finally_keep_source_order() {
    let source = "def f := do { try { action } catch | .bad n => { first n } | _ => { fallback } catch e : Other => { rethrow e } catch | .last => { recovered } | _ => { failed } finally { cleanup }; suffix }";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    let tries = nodes(parsed.syntax(), "doTry");
    assert_eq!(tries.len(), 1);
    let Syntax::Node { args: catches, .. } = &tries[0][2] else {
        panic!("catch list")
    };
    assert_eq!(catches.len(), 3);
    for (catch, expected) in catches
        .iter()
        .zip(["doCatchMatch", "doCatch", "doCatchMatch"])
    {
        assert_eq!(
            catch.kind(),
            Some(&Name::from_components(["Lean", "Parser", "Term", expected]))
        );
    }
    assert_eq!(nodes(&tries[0][3], "doFinally").len(), 1);
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
}

#[test]
fn nested_matches_and_pattern_handlers_do_not_steal_each_others_pipes() {
    for source in [
        "def f := do { try { action } catch | .bad n => { match n with | .zero => first | .succ k => second k } | .other => { fallback } }",
        "def f := do\n  match value with\n  | .left x =>\n    try\n      action x\n    catch\n    | .bad n => recover n\n    | _ => fallback\n  | .right y => other y",
        "def f := do\n  try\n    action\n  catch\n  | .bad n =>\n    try\n      first n\n    catch\n    | .bad k => recover k\n    | _ => fallback\n  | .other => last\n  suffix",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert!(!nodes(parsed.syntax(), "doCatchMatch").is_empty());
    }
}

#[test]
fn malformed_or_multidiscriminant_catches_are_refused() {
    for source in [
        "def f := do { try action catch | }",
        "def f := do { try action catch | .bad n }",
        "def f := do { try action catch | => recover }",
        "def f := do { try action catch | .bad n => }",
        "def f := do { try action catch | .bad n => recover n | }",
        "def f := do { try action catch | .bad n, .other => recover n }",
        "def f := do { catch | .bad n => recover n }",
        "def f := do { try action finally cleanup catch | _ => recover }",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn deeply_nested_pattern_handlers_use_the_existing_heap_planner() {
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let mut body = "action".to_owned();
            for _ in 0..80 {
                body = format!(
                    "try {{ {body} }} catch | .bad n => {{ recover n }} | _ => {{ fallback }}"
                );
            }
            let source = format!("def f := do {{ {body} }}");
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(nodes(parsed.syntax(), "doTry").len(), 80);
            assert_eq!(nodes(parsed.syntax(), "doCatchMatch").len(), 80);
            assert_eq!(nodes(parsed.syntax(), "matchAlt").len(), 160);
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        })
        .unwrap()
        .join()
        .unwrap();
}
