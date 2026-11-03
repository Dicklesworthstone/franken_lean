use super::*;
use fln_rt::convert::inject_name;
use fln_rt::region::compact;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn scoped(entry: Obj, scope: Option<&Name>) -> Obj {
    match scope {
        None => Obj::mk_ctor(format::SCOPE_GLOBAL, vec![entry], &[]),
        Some(scope) => Obj::mk_ctor(format::SCOPE_SCOPED, vec![inject_name(scope), entry], &[]),
    }
}

fn token(text: &str) -> Obj {
    Obj::mk_ctor(format::PARSER_ENTRY_TOKEN, vec![Obj::mk_string(text)], &[])
}

fn kind(value: &Name) -> Obj {
    Obj::mk_ctor(format::PARSER_ENTRY_KIND, vec![inject_name(value)], &[])
}

fn category(value: &Name, declaration: &Name, behavior: u8) -> Obj {
    Obj::mk_ctor(
        format::PARSER_ENTRY_CATEGORY,
        vec![inject_name(value), inject_name(declaration)],
        &[behavior],
    )
}

fn parser(value: &Name, declaration: &Name, priority: Obj) -> Obj {
    Obj::mk_ctor(
        format::PARSER_ENTRY_PARSER,
        vec![inject_name(value), inject_name(declaration), priority],
        &[],
    )
}

fn block(objects: &[Obj]) -> OpaqueExtensionBlock {
    OpaqueExtensionBlock {
        name: extension_name(),
        entries: objects
            .iter()
            .map(|object| compact(object, 0).unwrap())
            .collect(),
    }
}

#[test]
fn complete_journal_preserves_all_variants_scopes_repetitions_and_structural_names() {
    let category_name = Name::str(Name::anonymous(), "a.b");
    let category_declaration = name("User.Category.literal");
    let declaration = Name::str(Name::num(name("_private.User"), 7), "syntax");
    let scope = name("User.Enabled");
    let input = block(&[
        scoped(token("λ%\0"), None),
        scoped(kind(&category_name), None),
        scoped(
            category(
                &category_name,
                &category_declaration,
                format::PARSER_IDENT_DEFAULT,
            ),
            None,
        ),
        scoped(
            parser(&category_name, &declaration, Obj::mk_nat(1000)),
            None,
        ),
        scoped(token("λ%\0"), Some(&scope)),
        scoped(kind(&category_name), Some(&scope)),
        scoped(
            category(
                &category_name,
                &category_declaration,
                format::PARSER_IDENT_SYMBOL,
            ),
            Some(&scope),
        ),
        scoped(
            parser(&category_name, &declaration, Obj::mk_nat(17)),
            Some(&scope),
        ),
        scoped(
            category(
                &category_name,
                &category_declaration,
                format::PARSER_IDENT_BOTH,
            ),
            None,
        ),
        scoped(
            parser(&category_name, &declaration, Obj::mk_nat(1000)),
            None,
        ),
    ]);
    let result = decode(&[input], DecodeLimits::default()).unwrap();
    assert_eq!(
        result.entries,
        [
            ParserEntry {
                scope: None,
                kind: ParserEntryKind::Token("λ%\0".into()),
            },
            ParserEntry {
                scope: None,
                kind: ParserEntryKind::Kind(category_name.clone()),
            },
            ParserEntry {
                scope: None,
                kind: ParserEntryKind::Category {
                    category: category_name.clone(),
                    declaration: category_declaration.clone(),
                    behavior: LeadingIdentBehavior::Default,
                },
            },
            ParserEntry {
                scope: None,
                kind: ParserEntryKind::Parser {
                    category: category_name.clone(),
                    declaration: declaration.clone(),
                    priority: 1000,
                },
            },
            ParserEntry {
                scope: Some(scope.clone()),
                kind: ParserEntryKind::Token("λ%\0".into()),
            },
            ParserEntry {
                scope: Some(scope.clone()),
                kind: ParserEntryKind::Kind(category_name.clone()),
            },
            ParserEntry {
                scope: Some(scope.clone()),
                kind: ParserEntryKind::Category {
                    category: category_name.clone(),
                    declaration: category_declaration.clone(),
                    behavior: LeadingIdentBehavior::Symbol,
                },
            },
            ParserEntry {
                scope: Some(scope),
                kind: ParserEntryKind::Parser {
                    category: category_name.clone(),
                    declaration: declaration.clone(),
                    priority: 17,
                },
            },
            ParserEntry {
                scope: None,
                kind: ParserEntryKind::Category {
                    category: category_name.clone(),
                    declaration: category_declaration,
                    behavior: LeadingIdentBehavior::Both,
                },
            },
            ParserEntry {
                scope: None,
                kind: ParserEntryKind::Parser {
                    category: category_name.clone(),
                    declaration,
                    priority: 1000,
                },
            },
        ]
    );
    assert_ne!(category_name, name("a.b"));
}

#[test]
fn decoding_keeps_data_separate_from_grammar_activation_policy() {
    let anonymous = Name::anonymous();
    let input = block(&[
        scoped(token(""), None),
        scoped(kind(&anonymous), Some(&anonymous)),
    ]);
    assert_eq!(
        decode(&[input], DecodeLimits::default()).unwrap().entries,
        [
            ParserEntry {
                scope: None,
                kind: ParserEntryKind::Token(String::new()),
            },
            ParserEntry {
                scope: Some(anonymous.clone()),
                kind: ParserEntryKind::Kind(anonymous),
            },
        ]
    );
}

#[test]
fn cumulative_limits_have_exact_boundaries_and_refused_decoders_remain_poisoned() {
    let input = block(&[scoped(token("keyword%"), None)]);
    let bytes = input.entries[0].len();
    let objects = audit(&input.entries[0], 0).unwrap().objects;
    for (limits, resource) in [
        (
            DecodeLimits {
                max_bytes: bytes,
                ..DecodeLimits::default()
            },
            "parser payload bytes",
        ),
        (
            DecodeLimits {
                max_objects: objects,
                ..DecodeLimits::default()
            },
            "parser objects",
        ),
        (
            DecodeLimits {
                max_entries: 1,
                ..DecodeLimits::default()
            },
            "parser entries",
        ),
    ] {
        let mut decoder = Decoder::new(limits);
        assert_eq!(
            decoder
                .decode(std::slice::from_ref(&input))
                .unwrap()
                .entries
                .len(),
            1
        );
        assert!(matches!(decoder.decode(std::slice::from_ref(&input)),
            Err(DecodeError::Limit { resource: actual }) if actual == resource));
        assert!(decoder.decode(&[]).unwrap_err().is_resource());
    }
    let exact = DecodeLimits {
        max_bytes: bytes,
        max_objects: objects,
        max_entries: 1,
        ..DecodeLimits::default()
    };
    let mut decoder = Decoder::new(exact);
    assert_eq!(
        decoder
            .decode(std::slice::from_ref(&input))
            .unwrap()
            .entries
            .len(),
        1
    );
    let remaining = decoder.remaining_limits();
    assert_eq!(remaining.max_bytes, 0);
    assert_eq!(remaining.max_objects, 0);
    assert_eq!(remaining.max_entries, 0);
    assert!(decoder.decode(&[]).unwrap().is_empty());
    for limits in [
        DecodeLimits {
            max_bytes: bytes - 1,
            ..exact
        },
        DecodeLimits {
            max_objects: objects - 1,
            ..exact
        },
        DecodeLimits {
            max_entries: 0,
            ..exact
        },
    ] {
        assert!(
            decode(std::slice::from_ref(&input), limits)
                .unwrap_err()
                .is_resource()
        );
    }
}

#[test]
fn malformed_suffix_and_duplicate_blocks_publish_no_prefix() {
    let valid = scoped(token("valid%"), None);
    let input = block(&[valid.clone_ref(), Obj::mk_nat(0)]);
    let mut decoder = Decoder::new(DecodeLimits::default());
    assert!(matches!(
        decoder.decode(&[input]),
        Err(DecodeError::Shape { .. })
    ));
    assert!(matches!(
        decoder.decode(&[block(&[valid.clone_ref()])]),
        Err(DecodeError::Shape {
            detail: "parser decoder reused after refusal"
        })
    ));
    let input = block(&[valid]);
    assert!(matches!(
        decode(&[input.clone(), input], DecodeLimits::default()),
        Err(DecodeError::Shape {
            detail: "duplicate parser metadata extension block"
        })
    ));
}

#[test]
fn malformed_wrappers_payloads_names_priorities_and_behaviors_refuse() {
    let category_name = name("term");
    let declaration = name("User.syntax");
    let invalid = [
        Obj::mk_nat(0),
        Obj::mk_ctor(9, vec![token("x")], &[]),
        Obj::mk_ctor(format::SCOPE_GLOBAL, vec![], &[]),
        Obj::mk_ctor(
            format::SCOPE_SCOPED,
            vec![Obj::mk_string("not a Name"), token("x")],
            &[],
        ),
        scoped(Obj::mk_nat(0), None),
        scoped(Obj::mk_ctor(9, vec![], &[]), None),
        scoped(
            Obj::mk_ctor(format::PARSER_ENTRY_TOKEN, vec![Obj::mk_nat(0)], &[]),
            None,
        ),
        scoped(
            Obj::mk_ctor(format::PARSER_ENTRY_KIND, vec![Obj::mk_string("kind")], &[]),
            None,
        ),
        scoped(
            Obj::mk_ctor(
                format::PARSER_ENTRY_CATEGORY,
                vec![inject_name(&category_name), inject_name(&declaration)],
                &[],
            ),
            None,
        ),
        scoped(category(&category_name, &declaration, 9), None),
        scoped(
            parser(&category_name, &declaration, Obj::mk_string("1000")),
            None,
        ),
        scoped(
            parser(&category_name, &declaration, Obj::mk_mpz(&[1], true)),
            None,
        ),
        scoped(
            Obj::mk_ctor(
                format::PARSER_ENTRY_PARSER,
                vec![
                    inject_name(&category_name),
                    Obj::mk_nat(3),
                    Obj::mk_nat(1000),
                ],
                &[],
            ),
            None,
        ),
    ];
    for object in invalid {
        let error = decode(&[block(&[object])], DecodeLimits::default()).unwrap_err();
        assert!(
            !error.is_resource(),
            "malformed input was misclassified: {error}"
        );
    }
}

#[test]
fn priority_overflow_is_a_resource_limit_and_never_truncates() {
    let category_name = name("term");
    let declaration = name("User.syntax");
    let input = block(&[scoped(
        parser(
            &category_name,
            &declaration,
            Obj::mk_mpz(&[u64::from(u32::MAX)], false),
        ),
        None,
    )]);
    assert!(matches!(
        decode(&[input], DecodeLimits::default()).unwrap().entries[0].kind,
        ParserEntryKind::Parser {
            priority: u32::MAX,
            ..
        }
    ));
    for priority in [
        Obj::mk_nat(u32::MAX as usize + 1),
        Obj::mk_mpz(&[u64::from(u32::MAX) + 1], false),
        Obj::mk_mpz(&[0, 1], false),
    ] {
        let mut decoder = Decoder::new(DecodeLimits::default());
        assert!(
            decoder
                .decode(&[block(&[scoped(
                    parser(&category_name, &declaration, priority),
                    None,
                )])])
                .unwrap_err()
                .is_resource()
        );
        assert!(decoder.decode(&[]).unwrap_err().is_resource());
    }
}

#[test]
fn unrelated_extensions_do_not_gain_parser_authority_or_spend_selected_limits() {
    let input = OpaqueExtensionBlock {
        name: name("User.parserExtension"),
        entries: vec![vec![0xff]],
    };
    let limits = DecodeLimits {
        max_entries: 0,
        max_bytes: 0,
        max_objects: 0,
        ..DecodeLimits::default()
    };
    assert!(decode(&[input], limits).unwrap().is_empty());
    assert!(decode(&[block(&[])], limits).unwrap().is_empty());
}

#[path = "tests/reference.rs"]
mod reference;
