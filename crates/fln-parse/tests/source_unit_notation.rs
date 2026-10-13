//! Empty tuple notation retains its canonical syntax and original source.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::{parse_definition, parse_nat_definition, parse_source_command};
use fln_syntax::tree::Syntax;

fn unit_nodes(root: &Syntax) -> Vec<&Syntax> {
    let tuple = Name::from_components(["Lean", "Parser", "Term", "tuple"]);
    let mut pending = vec![root];
    let mut found = Vec::new();
    while let Some(node) = pending.pop() {
        if node.kind() == Some(&tuple) {
            found.push(node);
        }
        if let Syntax::Node { args, .. } = node {
            pending.extend(args.iter().rev());
        }
    }
    found
}

#[test]
fn unit_terms_parse_in_definitions_applications_and_explicit_evaluation() {
    for source in [
        "def value := ()",
        "def value : Unit := ((()))",
        "def value := id ()",
        "def value := fun (x : Unit) => ()",
        "def ioSelectedProbe6 := (pure () : IO Unit)",
        "def value := ( /- before closer -/\r\n -- retained\r\n )\r\n",
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
        assert_eq!(unit_nodes(parsed.syntax()).len(), 1);
    }
    for source in [
        "#eval ()",
        "#eval (pure () : IO Unit)",
        "#check (() : Unit)",
    ] {
        let parsed = parse_source_command(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(parsed.reconstruct_normalized().unwrap(), source.as_bytes());
        assert_eq!(unit_nodes(parsed.syntax()).len(), 1);
    }
}

#[test]
fn empty_tuple_has_the_pins_hygienic_opener_and_absent_optional_body() {
    let parsed = parse_definition(b"def value := ()").unwrap();
    let nodes = unit_nodes(parsed.syntax());
    let [Syntax::Node { args, .. }] = nodes.as_slice() else {
        panic!("one canonical tuple node");
    };
    assert_eq!(args.len(), 3);
    let Syntax::Node { kind, args, .. } = &args[0] else {
        panic!("hygienic opener");
    };
    assert_eq!(
        kind,
        &Name::from_components(["Lean", "Parser", "Term", "hygienicLParen"])
    );
    assert_eq!(args.len(), 2);
    assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "("));
    let Syntax::Node { kind, args, .. } = &args[1] else {
        panic!("hygiene information");
    };
    assert_eq!(kind, &Name::from_components(["hygieneInfo"]));
    assert!(matches!(args.as_slice(), [Syntax::Ident { val, .. }] if val.is_anonymous()));
    let Syntax::Node { args, .. } = nodes[0] else {
        unreachable!();
    };
    assert!(matches!(&args[1], Syntax::Node { kind, args, .. }
        if kind == &Name::from_components(["null"]) && args.is_empty()));
    assert!(matches!(&args[2], Syntax::Atom { val, .. } if val == ")"));
}

#[test]
fn empty_tuple_does_not_swallow_missing_values_or_expand_the_nat_only_grammar() {
    for source in [
        "def value := (",
        "def value := ())",
        "def value := ( : Unit)",
        "def value := (name :=)",
        "def value := f (name :=)",
        "def value := (;)",
        "def value := (,)",
        "def value := (-)",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    assert!(parse_nat_definition(b"def value : Nat := ()").is_err());
}

#[test]
fn deeply_grouped_unit_terms_use_the_existing_heap_frames() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let source = format!("def value := {}(){}", "(".repeat(600), ")".repeat(600));
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            assert_eq!(unit_nodes(parsed.syntax()).len(), 1);
        })
        .unwrap()
        .join()
        .unwrap();
}
