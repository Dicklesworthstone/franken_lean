//! Explicit application keeps the canonical syntax shape and original bytes.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::{parse_definition, parse_nat_definition};
use fln_syntax::tree::Syntax;

#[test]
fn explicit_heads_preserve_comments_parentheses_and_universe_suffixes() {
    for text in [
        "def x : Nat := @id Nat 7",
        "def x : Nat := (@id) Nat 7",
        "def x : Nat := @id.{0} Nat 7",
        "def x : Nat := @id -- select explicit\r\n Nat 7\r\n",
        "def x : Nat := f (@g) 7",
    ] {
        let parsed = parse_definition(text.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), text.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            parsed.source_view().normalized().as_bytes()
        );
        let target = Name::from_components(["Lean", "Parser", "Term", "explicit"]);
        let mut pending = vec![parsed.syntax()];
        let mut count = 0;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                if kind == &target {
                    count += 1;
                    assert_eq!(args.len(), 2);
                    assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "@"));
                }
                pending.extend(args);
            }
        }
        assert_eq!(count, 1, "{text}");
    }
}

#[test]
fn missing_explicit_heads_are_not_repaired_and_nat_only_stays_narrow() {
    for text in [
        "def x : Nat := @",
        "def x : Nat := (@)",
        "def x : Nat := @ + 1",
    ] {
        assert!(parse_definition(text.as_bytes()).is_err(), "{text}");
    }
    assert!(parse_nat_definition(b"def x : Nat := @f Nat 7").is_err());
}
