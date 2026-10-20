//! Introduction arguments remain structured terms, never flattened name lists.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

#[test]
fn intro_annotations_and_patterns_keep_their_term_categories_and_source_bytes() {
    for (pattern, category) in [
        ("(x : Nat)", "typeAscription"),
        ("(_ : _)", "typeAscription"),
        ("(x :)", "typeAscription"),
        ("(a, (b, c))", "tuple"),
        ("⟨a, ⟨b, c⟩⟩", "anonymousCtor"),
    ] {
        let source = format!("-- 🦀\r\ntheorem t : True := by\r\n  intro {pattern}\r\n");
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        let mut pending = vec![parsed.syntax()];
        let mut found = false;
        while let Some(syntax) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = syntax {
                if kind == &Name::from_components(["Lean", "Parser", "Tactic", "intro"]) {
                    let [
                        _,
                        Syntax::Node {
                            args: arguments, ..
                        },
                    ] = args.as_slice()
                    else {
                        panic!("intro must have exactly two slots");
                    };
                    assert_eq!(arguments.len(), 1);
                    assert_eq!(
                        arguments[0].kind(),
                        Some(&Name::from_components(["Lean", "Parser", "Term", category]))
                    );
                    found = true;
                }
                pending.extend(args);
            }
        }
        assert!(found, "{pattern}");
    }
}

#[test]
fn intros_remains_a_name_list_and_does_not_silently_accept_patterns() {
    for pattern in ["(x : Nat)", "(a, b)", "⟨a, b⟩"] {
        let source = format!("theorem t : True := by intros {pattern}");
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
    assert!(parse_definition(b"theorem t : True := by intros x _ y").is_ok());
}
