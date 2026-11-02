//! External expansion keeps the parser's source view and command boundary.
//! These tests exercise only the parser handoff, not macro execution or proof admission.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::{SourceCommandKind, parse_source_command};
use fln_syntax::source::SourceInfo;
use fln_syntax::tree::{Preresolved, Syntax};

fn replace_identifier_metadata(tree: &mut Syntax, requested: &str) {
    let requested = Name::from_components([requested]);
    let mut pending = vec![tree];
    let mut replaced = 0;
    while let Some(syntax) = pending.pop() {
        match syntax {
            Syntax::Node { args, .. } => pending.extend(args.iter_mut()),
            Syntax::Ident {
                info,
                val,
                preresolved,
                ..
            } if *val == requested => {
                let SourceInfo::Original { pos, end_pos, .. } = *info else {
                    panic!("the parsed identifier must carry original coordinates");
                };
                *info = SourceInfo::Synthetic {
                    pos,
                    end_pos,
                    canonical: false,
                };
                *val = Name::num(Name::from_components(["Expansion", "proof"]), 23);
                *preresolved = vec![Preresolved::Decl {
                    name: Name::from_components(["Imported", "checkedProof"]),
                    fields: vec!["value".into()],
                }];
                replaced += 1;
            }
            _ => {}
        }
    }
    assert_eq!(replaced, 1, "the replacement fixture must change one leaf");
}

#[test]
fn expanded_example_keeps_original_bytes_coordinates_and_hygiene() {
    let source = "-- λ🦀\r\nexample (n : Nat) : n = n := proof\r\n";
    let parsed = parse_source_command(source.as_bytes()).unwrap();
    let source_view = parsed.source_view().clone();
    let epilogue = parsed.epilogue();
    let mut syntax = parsed.syntax().clone();
    replace_identifier_metadata(&mut syntax, "proof");
    assert_ne!(&syntax, parsed.syntax());

    let expanded = parsed.with_expanded_example(syntax.clone()).unwrap();
    assert_eq!(expanded.kind(), SourceCommandKind::Example);
    assert_eq!(expanded.syntax(), &syntax);
    assert_eq!(expanded.source_view(), &source_view);
    assert_eq!(expanded.epilogue(), epilogue);
    assert_eq!(expanded.reconstruct_original(), source.as_bytes());
    assert_eq!(
        expanded.source_view().normalized().as_bytes(),
        source.replace("\r\n", "\n").as_bytes()
    );
    assert!(expanded.query_term_normalized().is_none());
    assert!(!expanded.query_is_identifier());
    assert!(expanded.into_definition().is_none());
}

#[test]
fn expanded_example_cannot_become_a_named_declaration_or_query() {
    let example = parse_source_command(b"example : Nat := 7").unwrap();
    for source in [
        b"def escaped : Nat := 7".as_slice(),
        b"theorem escaped : True := True.intro",
        b"#check Nat",
        b"#eval 7",
    ] {
        let other = parse_source_command(source).unwrap();
        assert!(
            example
                .clone()
                .with_expanded_example(other.syntax().clone())
                .is_none(),
            "an example cannot change its command identity: {source:?}"
        );
        assert!(
            other
                .with_expanded_example(example.syntax().clone())
                .is_none(),
            "an unrelated original command cannot enter the example handoff"
        );
    }
}

#[test]
fn expanded_example_requires_both_canonical_wrapper_arities() {
    let example = parse_source_command(b"example : Nat := 7").unwrap();
    for change_outer in [false, true] {
        for add_child in [false, true] {
            let mut malformed = example.syntax().clone();
            let Syntax::Node { args, .. } = &mut malformed else {
                panic!("canonical declaration");
            };
            let children = if change_outer {
                args
            } else {
                let Syntax::Node { args, .. } = &mut args[1] else {
                    panic!("canonical example");
                };
                args
            };
            if add_child {
                children.push(Syntax::Missing);
            } else {
                children.pop();
            }
            assert!(
                example.clone().with_expanded_example(malformed).is_none(),
                "outer={change_outer}, extra_child={add_child}"
            );
        }
    }
    assert!(example.with_expanded_example(Syntax::Missing).is_none());
}

#[test]
fn declaration_transfer_retains_expanded_syntax_and_original_source_metadata() {
    let source = "-- λ🦀\r\nprivate def chosen : Nat := value\r\n";
    let parsed = parse_source_command(source.as_bytes()).unwrap();
    let source_view = parsed.source_view().clone();
    let epilogue = parsed.epilogue();
    let mut syntax = parsed.syntax().clone();
    replace_identifier_metadata(&mut syntax, "value");
    assert_ne!(&syntax, parsed.syntax());

    let definition = parsed
        .with_expanded_declaration(syntax.clone())
        .unwrap()
        .into_definition()
        .unwrap();
    assert_eq!(definition.syntax(), &syntax);
    assert_eq!(definition.source_view(), &source_view);
    assert_eq!(definition.epilogue(), epilogue);
    assert_eq!(definition.reconstruct_original(), source.as_bytes());

    for source in [b"example : Nat := 7".as_slice(), b"#check Nat", b"#eval 7"] {
        assert!(
            parse_source_command(source)
                .unwrap()
                .into_definition()
                .is_none()
        );
    }
}
