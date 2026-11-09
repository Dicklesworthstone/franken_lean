use super::*;

fn literal_atom(value: &Obj) -> Obj {
    check_layout(value, layout::SYNTAX_NODE).unwrap();
    assert_eq!(child(value, 0).unwrap().unbox(), layout::SOURCE_NONE_TAG);
    let args = child(value, 2).unwrap();
    assert_eq!(args.try_array_view().unwrap().0, 1);
    let atom = args.array_child(0);
    check_layout(&atom, layout::SYNTAX_ATOM).unwrap();
    atom
}

fn option_string(value: &Obj) -> Option<String> {
    if value.is_scalar() {
        assert_eq!(value.unbox(), expansion_layout::OPTION_NONE_TAG);
        None
    } else {
        check_layout(value, expansion_layout::OPTION_SOME).unwrap();
        Some(string(&child(value, 0).unwrap()).unwrap().to_owned())
    }
}

#[test]
fn literal_construction_keeps_atom_source_and_shared_kind_and_text() {
    let kind = inject_name(&Name::str(Name::anonymous(), "custom.literal"));
    let text = Obj::mk_string("raw\0λ🙂");
    for info in [
        Obj::mk_nat(layout::SOURCE_NONE_TAG),
        synthetic_info(Obj::mk_mpz(&[0, 1], false), Obj::mk_nat(7), false),
        Obj::mk_ctor(
            layout::SOURCE_ORIGINAL.tag,
            vec![
                Obj::mk_ctor(
                    layout::SUBSTRING_RAW.tag,
                    vec![Obj::mk_string(" α "), Obj::mk_nat(0), Obj::mk_nat(1)],
                    &[],
                ),
                Obj::mk_nat(1),
                Obj::mk_ctor(
                    layout::SUBSTRING_RAW.tag,
                    vec![Obj::mk_string(" α "), Obj::mk_nat(3), Obj::mk_nat(4)],
                    &[],
                ),
                Obj::mk_nat(3),
            ],
            &[],
        ),
    ] {
        let result = invoke(
            Intrinsic::MkLit,
            &[kind.clone_ref(), text.clone_ref(), info.clone_ref()],
        );
        let atom = literal_atom(&result);
        assert_eq!(
            child(&atom, 0).unwrap().identity_token(),
            info.identity_token()
        );
        assert_eq!(
            child(&atom, 1).unwrap().identity_token(),
            text.identity_token()
        );
        assert_eq!(
            child(&result, 1).unwrap().identity_token(),
            kind.identity_token()
        );
        let projected = invoke(Intrinsic::IsLit, &[kind.clone_ref(), result]);
        assert_eq!(
            child(&projected, 0).unwrap().identity_token(),
            text.identity_token()
        );
        assert_eq!(string(&text).unwrap(), "raw\0λ🙂");
    }
}

#[test]
fn string_constructor_uses_pin_escapes_without_changing_source_or_unicode() {
    let cases = [
        ("", "\"\""),
        ("'", "\"'\""),
        ("\n\r\t\\\"", "\"\\n\\x0d\\t\\\\\\\"\""),
        ("\0\u{1f}\u{7f}", "\"\\x00\\x1f\\x7f\""),
        ("λ🙂é\u{a0}", "\"λ🙂é\u{a0}\""),
    ];
    let info = synthetic_info(Obj::mk_nat(0), Obj::mk_nat(99), true);
    for (value, spelling) in cases {
        let original = Obj::mk_string(value);
        let result = invoke(
            Intrinsic::MkStrLit,
            &[original.clone_ref(), info.clone_ref()],
        );
        let atom = literal_atom(&result);
        assert_eq!(
            child(&atom, 0).unwrap().identity_token(),
            info.identity_token()
        );
        assert_eq!(string(&child(&atom, 1).unwrap()).unwrap(), spelling);
        assert_eq!(
            Conversion::new()
                .project_name(&child(&result, 1).unwrap())
                .unwrap(),
            Name::str(Name::anonymous(), "str")
        );
        assert_eq!(
            option_string(&invoke(Intrinsic::IsStrLit, &[result])),
            Some(value.into())
        );
        assert_eq!(string(&original).unwrap(), value);
    }
}

#[test]
fn literal_inspection_requires_exact_node_kind_one_child_and_atom() {
    let str_kind = Name::str(Name::anonymous(), "str");
    for syntax in [
        Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
        atom("str"),
        node(str_kind.clone(), vec![]),
        node(str_kind.clone(), vec![atom("\"x\""), atom("\"y\"")]),
        node(
            str_kind.clone(),
            vec![Obj::mk_nat(layout::SYNTAX_MISSING_TAG)],
        ),
        node(
            str_kind.clone(),
            vec![node(str_kind.clone(), vec![atom("\"x\"")])],
        ),
        node(Name::from_components(["Lean", "str"]), vec![atom("\"x\"")]),
        invoke(Intrinsic::MkIdent, &[inject_name(&str_kind)]),
    ] {
        assert_eq!(
            option_string(&invoke(Intrinsic::IsStrLit, &[syntax.clone_ref()])),
            None
        );
        assert_eq!(
            string(&invoke(Intrinsic::GetString, &[syntax])).unwrap(),
            ""
        );
    }
    let generic = node(Name::str(Name::anonymous(), "A.B"), vec![atom("raw")]);
    assert_eq!(
        option_string(&invoke(
            Intrinsic::IsLit,
            &[
                inject_name(&Name::str(Name::anonymous(), "A.B")),
                generic.clone_ref(),
            ]
        )),
        Some("raw".into())
    );
    assert_eq!(
        option_string(&invoke(
            Intrinsic::IsLit,
            &[inject_name(&Name::from_components(["A", "B"])), generic,]
        )),
        None
    );
}

#[test]
fn string_api_decoder_preserves_permissive_pin_behavior_and_empty_default() {
    let cases = [
        ("\"\"", Some("")),
        ("\"λ🙂\"", Some("λ🙂")),
        ("\"a\\n\\r\\t\\\\\\\"\\'b\"", Some("a\n\r\t\\\"'b")),
        ("\"\\x00\\x7F\\u03BB\\uD800\"", Some("\0\u{7f}λ\0")),
        ("\"a\\ b\"", Some("ab")),
        ("\"a\\\n\nb\"", Some("ab")),
        ("\"a\\\r\t b\"", Some("ab")),
        ("\"a\\\u{a0}b\"", None),
        ("\"abc\"trailing", Some("abc")),
        ("a\"", Some("")),
        ("λ\"", Some("A")),
        ("🙂x\"", Some("AAAx")),
        ("r", Some("")),
        ("r#", Some("")),
        ("rabc", Some("b")),
        ("r#abc", Some("")),
        ("r\"a\\n\"", Some("a\\n")),
        ("r##\"a\"#b\"##", Some("a\"#b")),
        ("r\"🙂", Some("🙂")),
        ("r#\"λ", Some("")),
        ("r#\"🙂", Some("🙂")),
        ("rλ🙂", Some("🙂")),
        ("", None),
        ("x", None),
        ("λ", None),
        ("\"unterminated", None),
        ("\"\\q\"", None),
        ("\"\\x0g\"", None),
        ("\"\\u0xyz\"", None),
    ];
    for (spelling, expected) in cases {
        let syntax = node(Name::str(Name::anonymous(), "str"), vec![atom(spelling)]);
        assert_eq!(
            option_string(&invoke(Intrinsic::IsStrLit, &[syntax.clone_ref()])),
            expected.map(str::to_owned),
            "{spelling:?}"
        );
        assert_eq!(
            string(&invoke(Intrinsic::GetString, &[syntax])).unwrap(),
            expected.unwrap_or(""),
            "{spelling:?}"
        );
    }
}

#[test]
fn malformed_literal_carriers_are_refused_instead_of_decoded_as_none() {
    let kind = inject_name(&Name::str(Name::anonymous(), "str"));
    for (operation, row, arguments) in [
        (
            Intrinsic::MkLit,
            "mirror:Lean.Syntax.mkLit",
            vec![
                Obj::mk_nat(1),
                Obj::mk_string("x"),
                Obj::mk_nat(layout::SOURCE_NONE_TAG),
            ],
        ),
        (
            Intrinsic::MkLit,
            "mirror:Lean.Syntax.mkLit",
            vec![
                kind.clone_ref(),
                Obj::mk_nat(0),
                Obj::mk_nat(layout::SOURCE_NONE_TAG),
            ],
        ),
        (
            Intrinsic::MkStrLit,
            "mirror:Lean.Syntax.mkStrLit",
            vec![
                Obj::mk_string("x"),
                Obj::mk_ctor(layout::SOURCE_SYNTHETIC.tag, vec![], &[]),
            ],
        ),
        (
            Intrinsic::IsLit,
            "mirror:Lean.Syntax.isLit?",
            vec![
                kind.clone_ref(),
                Obj::mk_ctor(layout::SYNTAX_NODE.tag, vec![], &[]),
            ],
        ),
    ] {
        assert!(matches!(
            operation.invoke(row, &arguments),
            Err(IntrinsicFailure::Refused(_))
        ));
    }
    let invalid_array = Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![Obj::mk_nat(layout::SOURCE_NONE_TAG), kind, Obj::mk_nat(0)],
        &[],
    );
    let invalid_string = node(
        Name::str(Name::anonymous(), "str"),
        vec![Obj::mk_ctor(
            layout::SYNTAX_ATOM.tag,
            vec![Obj::mk_nat(layout::SOURCE_NONE_TAG), Obj::mk_nat(0)],
            &[],
        )],
    );
    for syntax in [
        invalid_array,
        invalid_string,
        Obj::mk_nat(layout::SYNTAX_MISSING_TAG + 1),
    ] {
        for (operation, row) in [
            (Intrinsic::IsStrLit, "mirror:Lean.Syntax.isStrLit?"),
            (Intrinsic::GetString, "mirror:Lean.TSyntax.getString"),
        ] {
            assert!(matches!(
                operation.invoke(row, &[syntax.clone_ref()]),
                Err(IntrinsicFailure::Refused(_))
            ));
            assert!(matches!(
                operation.invoke(row, &[]),
                Err(IntrinsicFailure::Refused(VmRefusal::IntrinsicArity { .. }))
            ));
        }
    }
}

#[test]
fn literal_limits_and_cancellation_stay_outside_option_and_default_results() {
    let huge = Obj::mk_string(&"x".repeat(16 * 1024 * 1024 + 1));
    let syntax = node(
        Name::str(Name::anonymous(), "str"),
        vec![Obj::mk_ctor(
            layout::SYNTAX_ATOM.tag,
            vec![Obj::mk_nat(layout::SOURCE_NONE_TAG), huge.clone_ref()],
            &[],
        )],
    );
    let cases = [
        (
            "mirror:Lean.Syntax.mkLit",
            vec![
                inject_name(&Name::anonymous()),
                huge.clone_ref(),
                Obj::mk_nat(layout::SOURCE_NONE_TAG),
            ],
        ),
        (
            "mirror:Lean.Syntax.mkStrLit",
            vec![huge, Obj::mk_nat(layout::SOURCE_NONE_TAG)],
        ),
        (
            "mirror:Lean.Syntax.isLit?",
            vec![
                inject_name(&Name::str(Name::anonymous(), "str")),
                syntax.clone_ref(),
            ],
        ),
        ("mirror:Lean.Syntax.isStrLit?", vec![syntax.clone_ref()]),
        ("mirror:Lean.TSyntax.getString", vec![syntax]),
    ];
    for (row, arguments) in cases {
        assert!(matches!(
            Intrinsic::for_row(row).unwrap().invoke(row, &arguments),
            Err(IntrinsicFailure::MirrorResource {
                resource: "literal input bytes",
                ..
            })
        ));
        let program = lookup::callable_program(row);
        assert!(matches!(
            execute_function(
                &program,
                flbc::FunctionId::new(1),
                arguments,
                ExecutionLimits::default(),
                None
            ),
            Outcome::Inconclusive(_)
        ));
        let literal = node(Name::str(Name::anonymous(), "str"), vec![atom("\"ok\"")]);
        let valid = match row {
            "mirror:Lean.Syntax.mkLit" => vec![
                inject_name(&Name::anonymous()),
                Obj::mk_string("ok"),
                Obj::mk_nat(layout::SOURCE_NONE_TAG),
            ],
            "mirror:Lean.Syntax.mkStrLit" => {
                vec![Obj::mk_string("ok"), Obj::mk_nat(layout::SOURCE_NONE_TAG)]
            }
            "mirror:Lean.Syntax.isLit?" => {
                vec![inject_name(&Name::str(Name::anonymous(), "str")), literal]
            }
            _ => vec![literal],
        };
        for (limits, cancelled) in [
            (
                ExecutionLimits {
                    max_steps: 0,
                    ..ExecutionLimits::default()
                },
                false,
            ),
            (ExecutionLimits::default(), true),
        ] {
            assert!(matches!(
                execute_function(
                    &program,
                    flbc::FunctionId::new(1),
                    valid.iter().map(Obj::clone_ref).collect(),
                    limits,
                    Some(&|| cancelled)
                ),
                Outcome::Inconclusive(_)
            ));
        }
        assert!(matches!(
            execute_function(
                &program,
                flbc::FunctionId::new(1),
                valid,
                ExecutionLimits::default(),
                None
            ),
            Outcome::Complete(VmExit::Returned(_))
        ));
    }
    // Expanding escapes can exceed the output budget while the input fits.
    let escaped = Obj::mk_string(&"\0".repeat(4 * 1024 * 1024));
    assert!(matches!(
        Intrinsic::MkStrLit.invoke(
            "mirror:Lean.Syntax.mkStrLit",
            &[escaped, Obj::mk_nat(layout::SOURCE_NONE_TAG)]
        ),
        Err(IntrinsicFailure::MirrorResource {
            resource: "literal constructor bytes",
            ..
        })
    ));
}
