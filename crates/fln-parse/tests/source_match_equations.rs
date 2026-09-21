//! Named discriminants retain the pinned syntax shape and original token leaves.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::{parse_definition, parse_nat_definition};
use fln_syntax::tree::Syntax;

fn discriminants(syntax: &Syntax) -> Vec<&[Syntax]> {
    let mut pending = vec![syntax];
    let mut found = Vec::new();
    let kind = Name::from_components(["Lean", "Parser", "Term", "matchDiscr"]);
    while let Some(node) = pending.pop() {
        if let Syntax::Node {
            kind: actual, args, ..
        } = node
        {
            if actual == &kind {
                found.push(args.as_slice());
            }
            pending.extend(args.iter().rev());
        }
    }
    found
}
#[test]
fn named_anonymous_and_unannotated_columns_keep_their_two_child_shape() {
    let source = "-- 🦀\r\ndef f (n : Nat) : Nat := match hé /- binding -/ : n, _ : n, (n : Nat) with | Nat.zero, _, _ => 0 | _, _, _ => 1\r\n";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source.replace("\r\n", "\n").as_bytes()
    );
    let nodes = discriminants(parsed.syntax());
    assert_eq!(nodes.len(), 3);
    for (index, args) in nodes.iter().enumerate() {
        assert_eq!(args.len(), 2);
        let Syntax::Node { args: binding, .. } = &args[0] else {
            panic!("optional binder");
        };
        assert_eq!(binding.len(), if index == 2 { 0 } else { 2 });
        if index < 2 {
            assert!(matches!(&binding[1], Syntax::Atom { val, .. } if val == ":"));
        }
    }
}
#[test]
fn nested_equations_and_quoted_names_preserve_source() {
    for source in [
        "def f (n : Nat) : Nat := match h : n with | Nat.zero => 0 | Nat.succ k => (match e : k with | Nat.zero => 1 | Nat.succ j => j)",
        "def f (n : Nat) : Nat := match «match» : n with | Nat.zero => 0 | Nat.succ k => k",
        "def f (n : Nat) : Nat := (match h : n with | Nat.zero => 0 | Nat.succ k => k) + 1",
    ] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
    }
}
#[test]
fn malformed_binders_fail_closed_and_nat_only_does_not_widen() {
    for source in [
        "def f := match h : with | Nat.zero => 0",
        "def f := match 7 : n with | Nat.zero => 0",
        "def f := match h h : n with | Nat.zero => 0",
        "def f := match : n with | Nat.zero => 0",
        "def f := match h : n, e : with | _, _ => 0",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    assert!(
        parse_nat_definition(
            b"def f : Nat := match h : Nat.zero with | Nat.zero => 0 | Nat.succ k => k"
        )
        .is_err()
    );
}
