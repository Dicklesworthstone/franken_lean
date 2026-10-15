//! The native unsafe declaration door consumes the pin's exact modifier slot.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

fn args(syntax: &Syntax) -> &[Syntax] {
    let Syntax::Node { args, .. } = syntax else {
        panic!("expected a node")
    };
    args
}

#[test]
fn unsafe_def_abbrev_and_instance_keep_their_complete_original_source() {
    for source in [
        "/-- 🦀 unsafe is a modifier, not a stripped prefix -/\r\nprivate unsafe def «value» (n : Nat) := n\r\n",
        "unsafe abbrev value : Nat := 7\n",
        "unsafe instance value : Inhabited Nat := ⟨7⟩\n",
        "unsafe def countdown : Nat -> Nat | 0 => 0 | n + 1 => countdown n\n",
        "noncomputable unsafe def value : Nat := 7\n",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        let modifiers = args(&args(parsed.syntax())[0]);
        assert_eq!(modifiers.len(), 7);
        let slot = args(&modifiers[5]);
        assert_eq!(slot.len(), 1);
        assert_eq!(
            slot[0].kind(),
            Some(&Name::from_components([
                "Lean", "Parser", "Command", "unsafe"
            ]))
        );
        assert!(matches!(args(&slot[0]), [Syntax::Atom { val, .. }] if val == "unsafe"));
        assert!(args(&modifiers[6]).is_empty());
    }
}

#[test]
fn escaped_keywords_and_comments_cannot_grant_unsafe_status() {
    for source in [
        "def «unsafe» : Nat := 7",
        "/-- unsafe -/ def safe : Nat := 7",
        "def safe : String := \"unsafe\"",
    ] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert!(args(&args(&args(parsed.syntax())[0])[5]).is_empty());
    }
    for source in [
        "unsafe unsafe def bad : Nat := 7",
        "unsafe private def bad : Nat := 7",
        "«unsafe» def bad : Nat := 7",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn conflicting_modifiers_are_retained_for_elaborator_refusal() {
    // The parser must not "repair" the semantically invalid combination by
    // dropping either modifier. Admission, not parsing, enforces this rule.
    let source = b"unsafe partial def loop (n : Nat) : Nat := loop n";
    let parsed = parse_definition(source).unwrap();
    assert_eq!(parsed.reconstruct_original(), source);
    let modifiers = args(&args(parsed.syntax())[0]);
    assert_eq!(args(&modifiers[5]).len(), 1);
    assert_eq!(args(&modifiers[6]).len(), 1);
}
