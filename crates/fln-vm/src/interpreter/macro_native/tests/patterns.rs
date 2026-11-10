use super::*;

fn ident(value: &Name) -> Obj {
    invoke(Intrinsic::MkIdent, &[inject_name(value)])
}

#[test]
fn scope_predicates_follow_the_terminal_marker_and_nearest_separator() {
    let plain = Name::from_components(["A", "x"]);
    let scoped = Name::num(Name::from_components(["A", "x", "_@", "Main", "_hyg"]), 7);
    let nested = Name::num(
        Name::from_components(["A", "_@", "B", "_@", "Main", "_hyg"]),
        9,
    );
    for (value, has_scopes, erased) in [
        (Name::anonymous(), false, Name::anonymous()),
        (plain.clone(), false, plain.clone()),
        (Name::num(plain.clone(), 7), false, Name::num(plain, 7)),
        (scoped.clone(), true, Name::from_components(["A", "x"])),
        (
            Name::num(scoped.clone(), 8),
            true,
            Name::from_components(["A", "x"]),
        ),
        (nested, true, Name::from_components(["A", "_@", "B"])),
        (Name::from_components(["_hyg"]), true, Name::anonymous()),
        (
            Name::num(Name::from_components(["A", "_hyg"]), 3),
            true,
            Name::anonymous(),
        ),
        (
            Name::str(scoped.clone(), "field"),
            false,
            Name::str(scoped, "field"),
        ),
    ] {
        let carrier = inject_name(&value);
        assert_eq!(
            invoke(Intrinsic::NameHasMacroScopes, &[carrier.clone_ref()]).unbox(),
            usize::from(has_scopes),
            "{value:?}"
        );
        let result = invoke(Intrinsic::NameEraseMacroScopes, &[carrier.clone_ref()]);
        assert_eq!(Conversion::new().project_name(&result).unwrap(), erased);
        assert_eq!(Conversion::new().project_name(&carrier).unwrap(), value);
        if !has_scopes {
            assert_eq!(result.identity_token(), carrier.identity_token());
        }
    }
}

#[test]
fn node_patterns_include_pseudo_kinds_and_arbitrary_natural_arities() {
    for (value, kind, size) in [
        (Obj::mk_nat(layout::SYNTAX_MISSING_TAG), "missing", 0),
        (ident(&Name::from_components(["x"])), "ident", 0),
        (atom("λ\0🙂"), "λ\0🙂", 0),
        (node(Name::from_components(["k"]), vec![atom("a")]), "k", 1),
        (node(Name::from_components(["k"]), vec![]), "k", 0),
    ] {
        for (requested_kind, requested_size, expected) in [
            (kind, Obj::mk_nat(size), true),
            (kind, Obj::mk_nat(size + 1), false),
            ("other", Obj::mk_nat(size), false),
            (kind, Obj::mk_mpz(&[0, 1], false), false),
        ] {
            assert_eq!(
                invoke(
                    Intrinsic::IsNodeOf,
                    &[
                        value.clone_ref(),
                        inject_name(&Name::str(Name::anonymous(), requested_kind)),
                        requested_size,
                    ],
                )
                .unbox(),
                usize::from(expected),
                "{kind} with {size} arguments"
            );
        }
    }
    // Like isNodeOf, matchesNull includes the matching atom pseudo-kind.
    for (value, size, expected) in [
        (atom("null"), 0, true),
        (node(Name::from_components(["null"]), vec![]), 0, true),
        (
            node(Name::from_components(["null"]), vec![atom("x")]),
            1,
            true,
        ),
        (atom("null"), 1, false),
        (Obj::mk_nat(layout::SYNTAX_MISSING_TAG), 0, false),
    ] {
        assert_eq!(
            invoke(Intrinsic::MatchesNull, &[value, Obj::mk_nat(size)]).unbox(),
            usize::from(expected)
        );
    }
}

#[test]
fn identifier_patterns_compare_structural_names_modulo_each_scope() {
    let plain = Name::from_components(["A", "λ"]);
    let first =
        fln_core::name::hygiene::add_macro_scope(&Name::from_components(["First"]), &plain, 7)
            .unwrap();
    let second =
        fln_core::name::hygiene::add_macro_scope(&Name::from_components(["Second"]), &plain, 9)
            .unwrap();
    for actual in [&plain, &first, &second] {
        for expected in [&plain, &first, &second] {
            assert_eq!(
                invoke(
                    Intrinsic::MatchesIdent,
                    &[ident(actual), inject_name(expected)],
                )
                .unbox(),
                1
            );
        }
        assert_eq!(
            invoke(
                Intrinsic::MatchesIdent,
                &[
                    ident(actual),
                    inject_name(&Name::str(Name::anonymous(), "A.λ"))
                ],
            )
            .unbox(),
            0
        );
    }
    for value in [
        atom("A.λ"),
        Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
        node(Name::from_components(["ident"]), vec![]),
    ] {
        assert_eq!(
            invoke(Intrinsic::MatchesIdent, &[value, inject_name(&plain)]).unbox(),
            0
        );
    }
}

#[test]
fn literal_patterns_match_raw_first_atom_and_allow_following_arguments() {
    let kind = Name::from_components(["str"]);
    for (value, text, expected) in [
        (node(kind.clone(), vec![atom("\"λ\\n\"")]), "\"λ\\n\"", true),
        (node(kind.clone(), vec![atom("\"λ\\n\"")]), "λ\n", false),
        (
            node(kind.clone(), vec![atom("x"), atom("ignored")]),
            "x",
            true,
        ),
        (node(kind.clone(), vec![]), "", false),
        (
            node(kind.clone(), vec![Obj::mk_nat(layout::SYNTAX_MISSING_TAG)]),
            "",
            false,
        ),
        (
            node(Name::from_components(["num"]), vec![atom("x")]),
            "x",
            false,
        ),
        (atom("x"), "x", false),
    ] {
        assert_eq!(
            invoke(
                Intrinsic::MatchesLit,
                &[value, inject_name(&kind), Obj::mk_string(text)],
            )
            .unbox(),
            usize::from(expected)
        );
    }
}

#[test]
fn optional_syntax_requires_exact_null_node_shape_and_preserves_the_child() {
    let kind = Name::from_components(["null"]);
    for inner in [atom("λ"), Obj::mk_nat(layout::SYNTAX_MISSING_TAG)] {
        let original = node(kind.clone(), vec![inner.clone_ref()]);
        let result = invoke(Intrinsic::GetOptional, &[original.clone_ref()]);
        check_layout(&result, expansion_layout::OPTION_SOME).unwrap();
        assert_eq!(
            result.try_ctor_child(0).unwrap().identity_token(),
            inner.identity_token()
        );
        assert_eq!(
            child(&original, 2).unwrap().array_child(0).identity_token(),
            inner.identity_token()
        );
    }
    for value in [
        node(kind.clone(), vec![]),
        node(kind, vec![atom("x"), atom("y")]),
        node(Name::from_components(["other"]), vec![atom("x")]),
        atom("null"),
        ident(&Name::from_components(["null"])),
        Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
    ] {
        assert_eq!(
            invoke(Intrinsic::GetOptional, &[value]).unbox(),
            expansion_layout::OPTION_NONE_TAG
        );
    }
}

#[test]
fn pattern_services_refuse_malformed_carriers_and_recover_after_resource_limits() {
    let null = inject_name(&Name::from_components(["null"]));
    let broken_array = Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            null.clone_ref(),
            Obj::mk_nat(0),
        ],
        &[],
    );
    let broken_ident = Obj::mk_ctor(
        layout::SYNTAX_IDENT.tag,
        vec![
            Obj::mk_nat(0),
            Obj::mk_nat(0),
            Obj::mk_nat(1),
            Obj::mk_nat(0),
        ],
        &[],
    );
    for (intrinsic, row, arguments) in [
        (
            Intrinsic::NameHasMacroScopes,
            "mirror:Lean.Name.hasMacroScopes",
            vec![Obj::mk_nat(1)],
        ),
        (
            Intrinsic::NameEraseMacroScopes,
            "mirror:Lean.Name.eraseMacroScopes",
            vec![Obj::mk_string("not Name")],
        ),
        (
            Intrinsic::IsNodeOf,
            "mirror:Lean.Syntax.isNodeOf",
            vec![broken_array.clone_ref(), null.clone_ref(), Obj::mk_nat(0)],
        ),
        (
            Intrinsic::IsNodeOf,
            "mirror:Lean.Syntax.isNodeOf",
            vec![atom("null"), Obj::mk_nat(1), Obj::mk_nat(0)],
        ),
        (
            Intrinsic::MatchesNull,
            "mirror:Lean.Syntax.matchesNull",
            vec![atom("null"), Obj::mk_mpz(&[1], true)],
        ),
        (
            Intrinsic::MatchesIdent,
            "mirror:Lean.Syntax.matchesIdent",
            vec![broken_ident, null.clone_ref()],
        ),
        (
            Intrinsic::MatchesLit,
            "mirror:Lean.Syntax.matchesLit",
            vec![
                broken_array.clone_ref(),
                null.clone_ref(),
                Obj::mk_string("x"),
            ],
        ),
        (
            Intrinsic::MatchesLit,
            "mirror:Lean.Syntax.matchesLit",
            vec![
                node(Name::from_components(["null"]), vec![atom("x")]),
                null.clone_ref(),
                Obj::mk_nat(0),
            ],
        ),
        (
            Intrinsic::GetOptional,
            "mirror:Lean.Syntax.getOptional?",
            vec![broken_array],
        ),
        (
            Intrinsic::GetOptional,
            "mirror:Lean.Syntax.getOptional?",
            vec![node(Name::from_components(["null"]), vec![Obj::mk_nat(99)])],
        ),
    ] {
        assert!(
            matches!(
                intrinsic.invoke(row, &arguments),
                Err(IntrinsicFailure::Refused(_))
            ),
            "{row}"
        );
    }
    let huge_name = inject_name(&Name::str(
        Name::anonymous(),
        "n".repeat(MAX_NAME_BYTES as usize),
    ));
    for (intrinsic, row) in [
        (
            Intrinsic::NameHasMacroScopes,
            "mirror:Lean.Name.hasMacroScopes",
        ),
        (
            Intrinsic::NameEraseMacroScopes,
            "mirror:Lean.Name.eraseMacroScopes",
        ),
    ] {
        assert!(matches!(
            intrinsic.invoke(row, &[huge_name.clone_ref()]),
            Err(IntrinsicFailure::MirrorResource { .. })
        ));
    }
    let huge_text = Obj::mk_string(&"x".repeat(MAX_NAME_BYTES as usize + 1));
    assert!(matches!(
        Intrinsic::MatchesLit.invoke(
            "mirror:Lean.Syntax.matchesLit",
            &[
                node(Name::from_components(["null"]), vec![atom("x")]),
                null.clone_ref(),
                huge_text
            ],
        ),
        Err(IntrinsicFailure::MirrorResource { .. })
    ));
    assert_eq!(
        invoke(Intrinsic::MatchesNull, &[atom("null"), Obj::mk_nat(0)]).unbox(),
        1
    );
    assert_eq!(invoke(Intrinsic::NameHasMacroScopes, &[null]).unbox(), 0);
}

#[test]
fn pattern_mirror_rows_execute_through_canonical_bytecode() {
    let plain = Name::from_components(["x"]);
    let scoped = Name::num(Name::from_components(["x", "_@", "M", "_hyg"]), 7);
    for (row, args, expected_scalar) in [
        (
            "mirror:Lean.Name.hasMacroScopes",
            vec![inject_name(&scoped)],
            Some(1),
        ),
        (
            "mirror:Lean.Name.eraseMacroScopes",
            vec![inject_name(&scoped)],
            None,
        ),
        (
            "mirror:Lean.Syntax.isNodeOf",
            vec![
                atom("null"),
                inject_name(&Name::from_components(["null"])),
                Obj::mk_nat(0),
            ],
            Some(1),
        ),
        (
            "mirror:Lean.Syntax.matchesNull",
            vec![atom("null"), Obj::mk_nat(0)],
            Some(1),
        ),
        (
            "mirror:Lean.Syntax.matchesIdent",
            vec![ident(&scoped), inject_name(&plain)],
            Some(1),
        ),
        (
            "mirror:Lean.Syntax.matchesLit",
            vec![
                node(
                    Name::from_components(["str"]),
                    vec![atom("x"), atom("extra")],
                ),
                inject_name(&Name::from_components(["str"])),
                Obj::mk_string("x"),
            ],
            Some(1),
        ),
        (
            "mirror:Lean.Syntax.getOptional?",
            vec![node(Name::from_components(["null"]), vec![atom("x")])],
            None,
        ),
    ] {
        let program = lookup::callable_program(row);
        let bytes = flbc::encode_canonical(&program, flbc::CodecLimits::default()).unwrap();
        let decoded = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
        for program in [&program, &decoded] {
            let outcome = execute_function(
                program,
                flbc::FunctionId::new(1),
                args.iter().map(Obj::clone_ref).collect(),
                ExecutionLimits::default(),
                None,
            );
            let Outcome::Complete(VmExit::Returned(result)) = outcome else {
                panic!("{row}: {outcome:?}");
            };
            if let Some(expected) = expected_scalar {
                assert_eq!(result.value.unbox(), expected, "{row}");
            } else if row.ends_with("eraseMacroScopes") {
                assert_eq!(
                    Conversion::new().project_name(&result.value).unwrap(),
                    plain
                );
            } else {
                check_layout(&result.value, expansion_layout::OPTION_SOME).unwrap();
                assert_eq!(
                    string(&child(&child(&result.value, 0).unwrap(), 1).unwrap()).unwrap(),
                    "x"
                );
            }
        }
    }
}
