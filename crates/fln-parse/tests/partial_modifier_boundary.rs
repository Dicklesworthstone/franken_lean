//! Partial recursion is requested by its canonical modifier, not body text.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

fn has_partial(source: &str) -> bool {
    let parsed = parse_definition(source.as_bytes()).unwrap();
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    let Syntax::Node { args, .. } = parsed.syntax() else {
        panic!("declaration");
    };
    let Syntax::Node { args: slots, .. } = &args[0] else {
        panic!("modifiers");
    };
    assert_eq!(slots.len(), 7);
    let Syntax::Node { args: optional, .. } = &slots[6] else {
        panic!("optional partial marker");
    };
    match optional.as_slice() {
        [] => false,
        [Syntax::Node { kind, args, .. }] => {
            assert_eq!(
                kind,
                &Name::from_components(["Lean", "Parser", "Command", "partial"])
            );
            assert!(matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "partial"));
            true
        }
        _ => panic!("one partial marker"),
    }
}

#[test]
fn partial_headers_survive_lossless_parsing() {
    for source in [
        include_str!("fixtures/partial_definitions/Gcd.lean"),
        include_str!("fixtures/partial_definitions/Opacity.lean"),
        "partial /- retained -/ def loop (n : Nat) : Nat := loop n\r\n",
        "private partial def hidden (n : Nat) : Nat := hidden n",
    ] {
        assert!(has_partial(source));
    }
}

#[test]
fn comments_strings_and_identifiers_do_not_request_partial_companions() {
    for source in [
        "/-- partial def -/ def answer : Nat := 7",
        "def «partial» : Nat := 7",
        "def text : String := \"partial def\"",
        "def ordinary («partial» : Nat) : Nat := «partial»",
    ] {
        assert!(!has_partial(source));
    }
}
