//! Safety is declaration syntax, not a spelling inferred from the body. Keep
//! its exact slot and all original bytes for the elaborator's safety boundary.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

#[test]
fn unsafe_modifier_occupies_only_its_canonical_slot() {
    for source in [
        "unsafe def step (n : Nat) : Nat := n + 1",
        "unsafe abbrev number : Nat := 7",
        "unsafe opaque hidden : Nat := 7",
        "unsafe axiom assumed : False",
        "unsafe instance chosen : Token := { value := 7 }",
        "private unsafe def hidden (n : Nat) : Nat := n",
        "/-- body -/\r\nunsafe /- marker -/ def step : Nat := 7\r\n",
    ] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("declaration");
        };
        let Syntax::Node { args: slots, .. } = &args[0] else {
            panic!("modifiers");
        };
        assert_eq!(slots.len(), 7);
        let Syntax::Node { args: optional, .. } = &slots[5] else {
            panic!("optional unsafe marker");
        };
        let [Syntax::Node { kind, args, .. }] = optional.as_slice() else {
            panic!("one unsafe marker");
        };
        assert_eq!(
            kind,
            &Name::from_components(["Lean", "Parser", "Command", "unsafe"])
        );
        assert!(matches!(args.as_slice(), [Syntax::Atom { val, .. }] if val == "unsafe"));
        assert!(matches!(&slots[6], Syntax::Node { args, .. } if args.is_empty()));
    }
}

#[test]
fn unsafe_in_a_name_comment_or_body_does_not_mark_a_declaration() {
    for source in [
        "def «unsafe» : Nat := 7",
        "def step («unsafe» : Nat) : Nat := «unsafe»",
        "/-- unsafe -/ def step : Nat := 7",
        "def text : String := \"unsafe\"",
    ] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        let Syntax::Node { args, .. } = parsed.syntax() else {
            panic!("declaration");
        };
        let Syntax::Node { args: slots, .. } = &args[0] else {
            panic!("modifiers");
        };
        assert!(matches!(&slots[5], Syntax::Node { args, .. } if args.is_empty()));
    }
}
