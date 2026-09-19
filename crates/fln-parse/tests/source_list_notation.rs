//! List syntax preserves the source tree before native constructor expansion.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::{parse_definition, parse_nat_definition};
use fln_syntax::tree::Syntax;

fn nodes<'a>(root: &'a Syntax, kind: &str) -> Vec<&'a Syntax> {
    let kind = Name::from_components(kind.split('.'));
    let mut pending = vec![root];
    let mut found = Vec::new();
    while let Some(node) = pending.pop() {
        if node.kind() == Some(&kind) {
            found.push(node);
        }
        if let Syntax::Node { args, .. } = node {
            pending.extend(args.iter().rev());
        }
    }
    found
}

#[test]
fn lists_preserve_brackets_comments_crlf_and_trailing_commas() {
    for source in [
        "def xs : List Nat := []",
        "def xs := [1, 2, 3,]",
        "def xs := [[1], [], [2, 3,],]",
        "def xs := [1, /- between -/\r\n  2, -- before closer\r\n]",
        "def fs := [fun x => x, fun y => y + 1,]",
        "def rs := [{ value := 1 }, { value := 2 },]",
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        let normalized = source.replace("\r\n", "\n");
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            normalized.as_bytes()
        );
        assert!(!nodes(parsed.syntax(), "term[_]").is_empty());
    }
}

#[test]
fn list_trees_keep_the_pins_elements_and_separators_shape() {
    let parsed = parse_definition(b"def xs := [1, 2,]").unwrap();
    let found = nodes(parsed.syntax(), "term[_]");
    let [Syntax::Node { args, .. }] = found.as_slice() else {
        panic!("one canonical list node");
    };
    assert_eq!(args.len(), 3);
    assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "["));
    assert!(matches!(&args[2], Syntax::Atom { val, .. } if val == "]"));
    let Syntax::Node { kind, args, .. } = &args[1] else {
        panic!("separator array")
    };
    assert_eq!(kind, &Name::from_components(["null"]));
    assert_eq!(args.len(), 4);
    assert!(matches!(&args[1], Syntax::Atom { val, .. } if val == ","));
    assert!(matches!(&args[3], Syntax::Atom { val, .. } if val == ","));
}

#[test]
fn cons_is_right_associative_and_binds_below_multiplication() {
    let parsed = parse_definition(b"def xs := 2 * 3 :: 4 :: []").unwrap();
    let found = nodes(parsed.syntax(), "term_::_");
    let Syntax::Node { args, .. } = found[0] else {
        panic!("outer cons")
    };
    assert_eq!(args[0].kind(), Some(&Name::from_components(["term_*_"])));
    assert_eq!(args[2].kind(), Some(&Name::from_components(["term_::_"])));
    let parsed = parse_definition(b"def xs := [] ++ 1 :: []").unwrap();
    let found = nodes(parsed.syntax(), "term_++_");
    let Syntax::Node { args, .. } = found[0] else {
        panic!("append tree")
    };
    assert_eq!(args[2].kind(), Some(&Name::from_components(["term_::_"])));
}

#[test]
fn delimiters_never_escape_their_list_parenthesis_or_binder() {
    for source in [
        "def xs := [,]",
        "def xs := [1,,2]",
        "def xs := [1,,]",
        "def xs := [1)",
        "def xs := (1]",
        "def xs := [1, (2]",
        "def xs := [1,",
        "def xs := [1] ]",
        "def xs := 1 ::",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    for source in [
        "def f [h : Inhabited Nat] := [default]",
        "def f := fun [h : Inhabited Nat] => [default]",
        "def f := fun (x : Nat) => [(x : Nat), x]",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}: {e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
    assert!(parse_nat_definition(b"def xs := []").is_err());
    assert!(parse_nat_definition(b"def xs := 1 :: []").is_err());
}

#[test]
fn flat_and_nested_lists_use_heap_frames() {
    let flat = format!("def xs := [{}]", vec!["1"; 512].join(","));
    let nested = format!("def xs := {}1{}", "[".repeat(128), "]".repeat(128));
    let chain = format!("def xs := {}[]", "1 :: ".repeat(512));
    for source in [flat, nested, chain] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
    }
}
