//! The pinned namedArgument syntax is built from original leaves, not rewritten text.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::{parse_definition, parse_nat_definition};
use fln_syntax::tree::Syntax;

fn named_nodes(syntax: &Syntax) -> Vec<&Syntax> {
    let mut pending = vec![syntax];
    let mut result = Vec::new();
    let kind = Name::from_components(["Lean", "Parser", "Term", "namedArgument"]);
    while let Some(node) = pending.pop() {
        if node.kind() == Some(&kind) {
            result.push(node);
        }
        if let Syntax::Node { args, .. } = node {
            pending.extend(args.iter());
        }
    }
    result
}

#[test]
fn named_arguments_have_the_pinned_five_child_shape_and_exact_source() {
    let source = "-- 🤖\r\ndef answer := f (β := 2) (α := g (x := 40))\r\n";
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source.replace("\r\n", "\n").as_bytes()
    );
    let nodes = named_nodes(parsed.syntax());
    assert_eq!(nodes.len(), 3);
    for node in nodes {
        let Syntax::Node { args, .. } = node else {
            unreachable!()
        };
        assert_eq!(args.len(), 5);
        assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "("));
        assert!(matches!(&args[1], Syntax::Ident { .. }));
        assert!(matches!(&args[2], Syntax::Atom { val, .. } if val == ":="));
        assert!(matches!(&args[4], Syntax::Atom { val, .. } if val == ")"));
    }
}

#[test]
fn labels_nest_with_ascriptions_lambdas_and_quoted_identifiers() {
    for source in [
        "def result := f (A := Nat) (x := (1 : Nat))",
        "def result := f (g := fun x => x) (x := 1)",
        "def result := f («a.b» := 1) («end» := 2)",
        "def result := @f (x := 1) Nat",
        "def result := f (x := g (y := h (z := 1)))",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|error| panic!("{source}: {error}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
    }
}

#[test]
fn malformed_or_standalone_assignments_and_nat_only_do_not_gain_acceptance() {
    for source in [
        "def result := (x := 1)",
        "def result := f ((x := 1))",
        "def result := f (x :=)",
        "def result := f (x := 1",
        "def result := f (1 := 2)",
        "def result := f (x y := 1)",
        "def result := f (x := 1 : Nat)",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    assert!(parse_nat_definition(b"def result := f (x := 1)").is_err());
}

#[test]
fn deeply_nested_named_values_use_bounded_frames() {
    let mut source = "def result := ".to_owned();
    for _ in 0..128 {
        source.push_str("f (x := ");
    }
    source.push('1');
    for _ in 0..128 {
        source.push(')');
    }
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(named_nodes(parsed.syntax()).len(), 128);
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
}
