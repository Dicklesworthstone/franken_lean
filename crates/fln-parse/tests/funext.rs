//! The pin's funext macro has a root syntax kind and term introductions.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

#[test]
fn funext_keeps_root_kind_names_holes_and_original_unicode_source() {
    for tail in ["funext", "funext x", "funext _ x", "funext «λ» y"] {
        let source =
            format!("-- 🦀\r\ntheorem t (f : Nat -> Nat) : f = f := by\r\n  {tail}\r\n  rfl");
        let parsed = parse_definition(source.as_bytes()).unwrap();
        let mut pending = vec![parsed.syntax()];
        let mut found = false;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                if kind == &Name::from_components(["tacticFunext___"]) {
                    assert_eq!(args.len(), 2);
                    assert!(matches!(&args[0], Syntax::Atom { val, .. } if val == "funext"));
                    assert!(
                        matches!(&args[1], Syntax::Node { kind, .. } if kind == &Name::from_components(["null"]))
                    );
                    found = true;
                }
                pending.extend(args);
            }
        }
        assert!(found, "{source}");
    }
    assert!(parse_definition(b"def funext (n : Nat) := n").is_ok());
}

#[test]
fn malformed_funext_arguments_do_not_disappear() {
    for tail in ["funext 2", "funext x, y", "funext [x]", "funext := x"] {
        let source = format!("theorem t (f : Nat -> Nat) : f = f := by {tail}");
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}
