//! Pinned doTry/doCatch trees retain source and nested statement scopes.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

fn count(syntax: &Syntax, label: &str) -> usize {
    let wanted = Name::from_components(["Lean", "Parser", "Term", label]);
    let mut work = vec![syntax];
    let mut n = 0;
    while let Some(s) = work.pop() {
        if let Syntax::Node { kind, args, .. } = s {
            n += usize::from(kind == &wanted);
            work.extend(args);
        }
    }
    n
}
#[test]
fn handlers_preserve_source_leaves_and_categories() {
    for s in [
        "def f := do { try { action } catch e => { recover e } }",
        "def f := do\n  try\n    let n <- action\n    return n\n  catch e : Nat =>\n    return e",
        "-- unicode\r\ndef f := do\r\n  try\r\n    action -- protected\r\n  catch «é» : Error Nat =>\r\n    recover «é»\r\n",
        "def f := do { try action catch _ => fallback }",
    ] {
        let p = parse_definition(s.as_bytes()).unwrap_or_else(|e| panic!("{s}\n{e:?}"));
        assert_eq!(p.reconstruct_original(), s.as_bytes());
        assert_eq!(
            p.reconstruct_normalized().unwrap(),
            s.replace("\r\n", "\n").as_bytes()
        );
        assert_eq!(count(p.syntax(), "doTry"), 1);
        assert_eq!(count(p.syntax(), "doCatch"), 1);
    }
}
#[test]
fn nested_tries_handlers_and_statement_conditionals_keep_their_owners() {
    for s in [
        "def f := do { try { try { action } catch inner => { recover inner }; after } catch outer => { fallback outer }; suffix }",
        "def f := do\n  try\n    if flag then\n      action\n    else\n      fallback\n  catch e =>\n    recover e\n  suffix",
        "def f := do { try { action } catch a : First => { first a } catch b : Second => { second b } }",
    ] {
        let p = parse_definition(s.as_bytes()).unwrap_or_else(|e| panic!("{s}\n{e:?}"));
        assert_eq!(p.reconstruct_original(), s.as_bytes());
        assert!(count(p.syntax(), "doTry") >= 1);
    }
}
#[test]
fn malformed_handlers_and_outside_do_tries_refuse() {
    for s in [
        "def f := do { try }",
        "def f := do { try action catch }",
        "def f := do { try action catch e }",
        "def f := do { try action catch e : => x }",
        "def f := do { try action catch e => }",
        "def f := do { catch e => x }",
        "def f := try action catch e => x",
        "def f := do { try { action catch e => x } }",
    ] {
        assert!(parse_definition(s.as_bytes()).is_err(), "{s}");
    }
}

#[test]
fn exception_planning_is_nonrecursive_and_retains_deep_source() {
    std::thread::Builder::new()
        .stack_size(512 * 1024)
        .spawn(|| {
            let mut source = "action".to_owned();
            for _ in 0..80 {
                source = format!("try {{ {source} }} catch e => {{ recover e }}");
            }
            let source = format!("def f := do {{ {source} }}");
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(count(parsed.syntax(), "doTry"), 80);
            assert_eq!(count(parsed.syntax(), "doCatch"), 80);
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn finalizers_preserve_original_tokens_and_scope_order() {
    for (source, regions, finalizers) in [
        (
            "def f := do { try { action } finally { cleanup }; suffix }",
            1,
            1,
        ),
        (
            "def f := do\r\n  try\r\n    action\r\n  catch e : Error =>\r\n    recover e\r\n  finally\r\n    cleanup -- last\r\n  suffix",
            1,
            1,
        ),
        (
            "def f := do { try { try { action } finally { inner } } finally { outer } }",
            2,
            2,
        ),
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(count(parsed.syntax(), "doTry"), regions);
        assert_eq!(count(parsed.syntax(), "doFinally"), finalizers);
    }
    for source in [
        "def f := do { try { action } finally }",
        "def f := do { try { action } finally { cleanup } catch e => { recover e } }",
        "def f := do { try { action } finally { cleanup } finally { again } }",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}
