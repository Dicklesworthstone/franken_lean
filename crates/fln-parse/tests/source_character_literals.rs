//! Character terms retain the pin's literal node and their original spelling.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::{parse_definition, parse_nat_definition, parse_source_command};
use fln_syntax::tree::Syntax;

fn characters(root: &Syntax) -> Vec<&Syntax> {
    let mut pending = vec![root];
    let mut found = Vec::new();
    while let Some(node) = pending.pop() {
        if node.kind() == Some(&Name::from_components(["char"])) {
            found.push(node);
        }
        if let Syntax::Node { args, .. } = node {
            pending.extend(args.iter().rev());
        }
    }
    found
}

#[test]
fn character_terms_parse_in_definitions_applications_and_queries() {
    for (source, spelling) in [
        ("def value := 'a'", "'a'"),
        ("def value : Char := ((('λ')))", "'λ'"),
        ("def value := String.push \"λ\" '🙂'", "'🙂'"),
        ("def value := fun (c : Char) => '\\n'", "'\\n'"),
        ("def value := let c := '\\uD800'; c", "'\\uD800'"),
        ("def value := /- before -/ '☃' -- after\r\n", "'☃'"),
    ] {
        let parsed = parse_definition(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace("\r\n", "\n").as_bytes()
        );
        let nodes = characters(parsed.syntax());
        let [Syntax::Node { args, .. }] = nodes.as_slice() else {
            panic!("one canonical character node: {source}");
        };
        assert!(matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == spelling));
    }
    for source in [
        "#eval '🙂'",
        "#eval String.push \"λ\" '🙂'",
        "#check ('a' : Char)",
        "#eval do IO.println 'λ'",
    ] {
        let parsed = parse_source_command(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(characters(parsed.syntax()).len(), 1, "{source}");
    }
}

#[test]
fn character_terms_keep_the_existing_escape_and_single_scalar_rules() {
    for spelling in [
        "'a'",
        "'λ'",
        "'🙂'",
        "'\\n'",
        "'\\r'",
        "'\\t'",
        "'\\\\'",
        "'\\\''",
        "'\\\"'",
        "'\\x00'",
        "'\\xFF'",
        "'\\u2665'",
        "'\\uD7FF'",
        "'\\uD800'",
        "'\\uDFFF'",
        "'\\uE000'",
    ] {
        let source = format!("#eval {spelling}");
        let parsed = parse_source_command(source.as_bytes())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(characters(parsed.syntax()).len(), 1);
    }
    for spelling in [
        "''",
        "'''",
        "'ab'",
        "'❤️'",
        "'unterminated",
        "'\\0'",
        "'\\b'",
        "'\\f'",
        "'\\a'",
        "'\\U0001F642'",
        "'\\u{1F642}'",
        "'\\x0'",
        "'\\xGG'",
        "'\\u123'",
        "'\\u12GG'",
        "'\\uD800\\uDC00'",
        "'\\\n  a'",
    ] {
        let source = format!("#eval {spelling}");
        assert!(parse_source_command(source.as_bytes()).is_err(), "{source}");
    }
    assert!(parse_nat_definition(b"def value : Nat := 'a'").is_err());
}
