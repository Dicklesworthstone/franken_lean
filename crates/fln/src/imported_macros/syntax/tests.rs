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
        raw_val: range(2, 4).into(),
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
fn distinct_source_backings_pay_for_each_validation() {
    let source = SourceText::from_utf8(b"source backing").unwrap();
    let ident = Syntax::Ident {
        info: SourceInfo::None,
        raw_val: range(0, 1).into(),
        val: Name::anonymous(),
        preresolved: Vec::new(),
    };
    let first = inject(&ident, &source, SyntaxLimits::default()).unwrap();
    let second = inject(&ident, &source, SyntaxLimits::default()).unwrap();
    let node = |children| {
        Obj::mk_ctor(
            abi::SYNTAX_NODE.tag,
            vec![
                Obj::mk_nat(abi::SOURCE_NONE_TAG),
                inject_name(&Name::anonymous()),
                Obj::mk_array(children),
            ],
            &[],
        )
    };
    let shared = node(vec![first.clone_ref(), first.clone_ref()]);
    let separate = node(vec![first, second]);
    let (expected, shared_usage) =
        project_counted(&shared, &source, SyntaxLimits::default()).unwrap();
    let (actual, separate_usage) =
        project_counted(&separate, &source, SyntaxLimits::default()).unwrap();
    assert_eq!(actual, expected);
    assert_eq!(separate_usage.max_nodes, shared_usage.max_nodes);
    assert_eq!(
        separate_usage.max_bytes,
        shared_usage.max_bytes + source.len_bytes()
    );
    assert_eq!(project(&shared, &source, shared_usage).unwrap(), expected);
    assert!(matches!(
        project(&separate, &source, shared_usage),
        Err(SyntaxConversionError::Limit {
            resource: "text bytes",
            limit,
            observed,
        }) if limit == shared_usage.max_bytes && observed == separate_usage.max_bytes
    ));
    assert_eq!(
        project(&separate, &source, separate_usage).unwrap(),
        expected
    );
}

#[test]
fn deep_trees_use_bounded_explicit_stacks() {
    let source = SourceText::from_utf8(b"x").unwrap();
    let mut tree = Syntax::Ident {
        info: SourceInfo::None,
        raw_val: range(0, 1).into(),
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
fn malformed_runtime_values_and_foreign_source_info_are_typed_failures() {
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
        info: SourceInfo::Original {
            leading: range(0, 0),
            pos: BytePos(0),
            trailing: range(2, 2),
            end_pos: BytePos(2),
        },
        raw_val: range(0, 2).into(),
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
        raw_val: range(1, 2).into(),
        val: Name::from_components(["α"]),
        preresolved: Vec::new(),
    };
    assert!(matches!(
        inject(&malformed, &source, SyntaxLimits::default()),
        Err(SyntaxConversionError::Malformed(_))
    ));
}

#[test]
fn owned_identifier_backings_roundtrip_with_mixed_sources_and_exact_offsets() {
    let source = SourceText::from_utf8(b"x").unwrap();
    let backing: Arc<str> = Arc::from("prefix β suffix");
    let generated = Syntax::Ident {
        info: SourceInfo::Synthetic {
            pos: BytePos(0),
            end_pos: BytePos(1),
            canonical: false,
        },
        raw_val: RawIdentifier::owned(backing.clone(), range(7, 9)).unwrap(),
        val: fln_core::name::hygiene::add_macro_scope(
            &Name::from_components(["Main"]),
            &Name::from_components(["β"]),
            17,
        )
        .unwrap(),
        preresolved: vec![Preresolved::Decl {
            name: Name::from_components(["Library", "value"]),
            fields: vec![],
        }],
    };
    let original = Syntax::Ident {
        info: SourceInfo::Original {
            leading: range(0, 0),
            pos: BytePos(0),
            trailing: range(1, 1),
            end_pos: BytePos(1),
        },
        raw_val: range(0, 1).into(),
        val: Name::from_components(["x"]),
        preresolved: vec![],
    };
    let mixed = Syntax::node(
        Name::from_components(["mixed"]),
        vec![original, generated.clone()],
    );
    let first = inject(&mixed, &source, SyntaxLimits::default()).unwrap();
    let projected = project(&first, &source, SyntaxLimits::default()).unwrap();
    assert_eq!(projected, mixed);
    let second = inject(&projected, &source, SyntaxLimits::default()).unwrap();
    assert_eq!(
        project(&second, &source, SyntaxLimits::default()).unwrap(),
        mixed
    );

    // A later macro can receive this quotation under another caller source.
    // Its raw offsets still refer to the complete original backing string.
    let generated_object = inject(&generated, &source, SyntaxLimits::default()).unwrap();
    let other_source = SourceText::from_utf8(b"a different caller").unwrap();
    let transferred = project(&generated_object, &other_source, SyntaxLimits::default()).unwrap();
    assert_eq!(transferred, generated);
    let object = inject(&transferred, &other_source, SyntaxLimits::default()).unwrap();
    let raw = child(&object, 1).unwrap();
    assert_eq!(string(&child(&raw, 0).unwrap()).unwrap(), backing.as_ref());
    assert_eq!(position(&child(&raw, 1).unwrap()).unwrap(), BytePos(7));
    assert_eq!(position(&child(&raw, 2).unwrap()).unwrap(), BytePos(9));
}

#[test]
fn foreign_identifier_spans_and_full_backing_obey_conversion_limits() {
    let source = SourceText::from_utf8(b"call").unwrap();
    let object = |backing: &str, start: usize, end: usize| {
        Obj::mk_ctor(
            abi::SYNTAX_IDENT.tag,
            vec![
                Obj::mk_nat(abi::SOURCE_NONE_TAG),
                Obj::mk_ctor(
                    abi::SUBSTRING_RAW.tag,
                    vec![Obj::mk_string(backing), nat(start), nat(end)],
                    &[],
                ),
                inject_name(&Name::anonymous()),
                Obj::mk_nat(abi::LIST_NIL_TAG),
            ],
            &[],
        )
    };
    for (start, end) in [(1, 2), (0, 1), (2, 1), (0, 4), (usize::MAX, usize::MAX)] {
        assert!(
            matches!(
                project(&object("βx", start, end), &source, SyntaxLimits::default()),
                Err(SyntaxConversionError::Malformed(
                    "identifier substring is not a UTF-8 range"
                ))
            ),
            "accepted foreign range {start}..{end}"
        );
    }
    // Only β is selected, but the entire foreign backing is observable to
    // metaprograms and must be charged, including the unrelated suffix.
    let backing = format!("β{}", "unused".repeat(100));
    let (syntax, usage) =
        project_counted(&object(&backing, 0, 2), &source, SyntaxLimits::default()).unwrap();
    assert_eq!(usage.max_bytes, source.len_bytes() + backing.len());
    assert_eq!(
        project(&object(&backing, 0, 2), &source, usage).unwrap(),
        syntax
    );
    let short = SyntaxLimits {
        max_bytes: usage.max_bytes - 1,
        ..usage
    };
    assert!(matches!(
        project(&object(&backing, 0, 2), &source, short),
        Err(SyntaxConversionError::Limit {
            resource: "text bytes",
            ..
        })
    ));
    let (_, generated) = inject_counted(&syntax, &source, SyntaxLimits::default()).unwrap();
    assert_eq!(generated.max_bytes, backing.len());
    assert!(matches!(
        inject(&syntax, &source, short),
        Err(SyntaxConversionError::Limit {
            resource: "text bytes",
            ..
        })
    ));
    let reinjected = inject(&syntax, &source, SyntaxLimits::default()).unwrap();
    let (_, second) = project_counted(&reinjected, &source, SyntaxLimits::default()).unwrap();
    assert_eq!(
        second.max_bytes, usage.max_bytes,
        "reinjection cannot erase backing charges"
    );
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
