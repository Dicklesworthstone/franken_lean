use super::*;

fn range(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(BytePos(start), BytePos(end)).unwrap()
}

#[test]
fn syntax_roundtrip_preserves_unicode_trivia_scopes_and_preresolution() {
    let source = SourceText::from_utf8("  α /-🙂-/\n".as_bytes()).unwrap();
    let ident = Syntax::Ident {
        info: SourceInfo::Original {
            leading: range(0, 2),
            pos: BytePos(2),
            trailing: range(4, source.len_bytes()),
            end_pos: BytePos(4),
        },
        raw_val: range(2, 4),
        val: Name::num(Name::from_components(["α", "_hyg", "Main"]), 17),
        preresolved: vec![
            Preresolved::Namespace {
                ns: Name::from_components(["A", "B"]),
            },
            Preresolved::Decl {
                name: Name::from_components(["A", "value"]),
                fields: vec!["first".into(), "α\0🙂".into()],
            },
        ],
    };
    let tree = Syntax::Node {
        info: SourceInfo::Synthetic {
            pos: BytePos(2),
            end_pos: BytePos(4),
            canonical: true,
        },
        kind: Name::from_components(["Lean", "Parser", "Term", "app"]),
        args: vec![
            ident,
            Syntax::Missing,
            Syntax::Atom {
                info: SourceInfo::None,
                val: "\0🙂".into(),
            },
            Syntax::Atom {
                info: SourceInfo::Synthetic {
                    pos: BytePos(usize::MAX),
                    end_pos: BytePos(usize::MAX),
                    canonical: false,
                },
                val: "generated".into(),
            },
        ],
    };
    let object = inject(&tree, &source, SyntaxLimits::default()).unwrap();
    let projected = project(&object, &source, SyntaxLimits::default()).unwrap();
    assert_eq!(tree, projected);
    let second = inject(&projected, &source, SyntaxLimits::default()).unwrap();
    assert_eq!(
        project(&second, &source, SyntaxLimits::default()).unwrap(),
        tree
    );
}

#[test]
fn deep_trees_use_bounded_explicit_stacks() {
    let source = SourceText::from_utf8(b"x").unwrap();
    let mut tree = Syntax::Ident {
        info: SourceInfo::None,
        raw_val: range(0, 1),
        val: Name::from_components(["x"]),
        preresolved: Vec::new(),
    };
    for _ in 0..2048 {
        tree = Syntax::node(Name::from_components(["nested"]), vec![tree]);
    }
    let object = inject(&tree, &source, SyntaxLimits::default()).unwrap();
    assert_eq!(
        project(&object, &source, SyntaxLimits::default()).unwrap(),
        tree
    );
    assert!(matches!(
        project(
            &object,
            &source,
            SyntaxLimits {
                max_nodes: 64,
                max_bytes: 4096
            }
        ),
        Err(SyntaxConversionError::Limit {
            resource: "nodes",
            ..
        })
    ));
    assert!(matches!(
        inject(
            &tree,
            &source,
            SyntaxLimits {
                max_nodes: 64,
                max_bytes: 4096
            }
        ),
        Err(SyntaxConversionError::Limit {
            resource: "nodes",
            ..
        })
    ));
}

#[test]
fn malformed_runtime_values_and_foreign_sources_are_typed_failures() {
    let source = SourceText::from_utf8("α".as_bytes()).unwrap();
    for value in [
        Obj::mk_nat(7),
        Obj::mk_string("not syntax"),
        Obj::mk_ctor(abi::SYNTAX_NODE.tag, vec![], &[]),
        Obj::mk_ctor(
            abi::SYNTAX_NODE.tag,
            vec![
                Obj::mk_nat(abi::SOURCE_NONE_TAG),
                inject_name(&Name::anonymous()),
                Obj::mk_nat(0),
            ],
            &[],
        ),
        Obj::mk_ctor(
            abi::SYNTAX_ATOM.tag,
            vec![
                Obj::mk_ctor(abi::SOURCE_SYNTHETIC.tag, vec![nat(0), nat(2)], &[2]),
                Obj::mk_string("α"),
            ],
            &[],
        ),
    ] {
        assert!(matches!(
            project(&value, &source, SyntaxLimits::default()),
            Err(SyntaxConversionError::Malformed(_))
        ));
    }
    let ident = Syntax::Ident {
        info: SourceInfo::None,
        raw_val: range(0, 2),
        val: Name::from_components(["α"]),
        preresolved: Vec::new(),
    };
    let object = inject(&ident, &source, SyntaxLimits::default()).unwrap();
    let other = SourceText::from_utf8("β".as_bytes()).unwrap();
    assert_eq!(
        project(&object, &other, SyntaxLimits::default()),
        Err(SyntaxConversionError::Malformed(
            "foreign substring source buffer"
        ))
    );
    let malformed = Syntax::Ident {
        info: SourceInfo::None,
        raw_val: range(1, 2),
        val: Name::from_components(["α"]),
        preresolved: Vec::new(),
    };
    assert!(matches!(
        inject(&malformed, &source, SyntaxLimits::default()),
        Err(SyntaxConversionError::Malformed(_))
    ));
}

#[test]
fn source_and_nested_text_cannot_escape_conversion_budgets() {
    let source = SourceText::from_utf8(b"source").unwrap();
    let tree = Syntax::atom(SourceInfo::None, "payload");
    for limits in [
        SyntaxLimits {
            max_nodes: 0,
            max_bytes: 1024,
        },
        SyntaxLimits {
            max_nodes: 1024,
            max_bytes: 5,
        },
        SyntaxLimits {
            max_nodes: 1024,
            max_bytes: 12,
        },
    ] {
        assert!(matches!(
            inject(&tree, &source, limits),
            Err(SyntaxConversionError::Limit { .. })
        ));
    }
    let object = inject(&tree, &source, SyntaxLimits::default()).unwrap();
    assert!(matches!(
        project(
            &object,
            &source,
            SyntaxLimits {
                max_nodes: 1024,
                max_bytes: 12
            }
        ),
        Err(SyntaxConversionError::Limit {
            resource: "text bytes",
            ..
        })
    ));
}
