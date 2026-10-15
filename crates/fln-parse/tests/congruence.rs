//! The congruence executor consumes the pin's original syntax, not reparsed text.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

#[test]
fn congruence_depth_and_original_source_bytes_survive_parsing() {
    for suffix in ["", " 0", " 1", " 0x10", " 184467440737095516160"] {
        let source =
            format!("/-- λ -/\r\ntheorem t (a : Nat) : a = a := by\r\n  congr{suffix}\r\n");
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        let mut pending = vec![parsed.syntax()];
        let mut count = 0;
        while let Some(node) = pending.pop() {
            if let Syntax::Node { kind, args, .. } = node {
                if kind == &Name::from_components(["Lean", "Parser", "Tactic", "congr"]) {
                    count += 1;
                    assert_eq!(args.len(), 2);
                    assert!(matches!(&args[0], Syntax::Atom {val, ..} if val == "congr"));
                    let Syntax::Node { args: depth, .. } = &args[1] else {
                        panic!("optional depth");
                    };
                    assert_eq!(depth.len(), usize::from(!suffix.is_empty()));
                    if let Some(number) = depth.first() {
                        assert_eq!(number.kind(), Some(&Name::from_components(["num"])));
                    }
                }
                pending.extend(args);
            }
        }
        assert_eq!(count, 1);
    }
}

#[test]
fn malformed_depth_arguments_are_not_ignored() {
    for suffix in [" -1", " missing", " 1 2", " (1)", " 1.5", " 1 using other"] {
        let source = format!("theorem t (a : Nat) : a = a := by congr{suffix}");
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}

#[test]
fn nested_congruence_controls_do_not_capture_ordinary_term_names() {
    for source in [
        "def congr : Nat := 7",
        "theorem t (P : Prop) (congr : P) : P := by exact congr",
        "/-- λ -/\r\ntheorem t (a : Nat) : a = a := by\r\n  first | (congr 0; fail) | congr 1\r\n",
        "theorem t (a : Nat) : (a = a) ∧ (a = a) := by constructor <;> congr 1",
    ] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
}
