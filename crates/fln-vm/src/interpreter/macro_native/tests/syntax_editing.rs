use super::*;

fn synthetic_info() -> Obj {
    Obj::mk_ctor(
        layout::SOURCE_SYNTHETIC.tag,
        vec![Obj::mk_nat(2), Obj::mk_nat(7)],
        &[1],
    )
}

fn ident(info: Obj) -> Obj {
    Obj::mk_ctor(
        layout::SYNTAX_IDENT.tag,
        vec![
            info,
            Obj::mk_ctor(
                layout::SUBSTRING_RAW.tag,
                vec![Obj::mk_string("α"), Obj::mk_nat(0), Obj::mk_nat(2)],
                &[],
            ),
            inject_name(&Name::num(Name::from_components(["α", "_hyg"]), 41)),
            Obj::mk_nat(layout::LIST_NIL_TAG),
        ],
        &[],
    )
}

fn with_info(value: &Obj, info: &Obj) -> Obj {
    invoke(Intrinsic::SetInfo, &[info.clone_ref(), value.clone_ref()])
}

#[test]
fn token_inspection_and_rewriting_preserve_source_and_shared_inputs() {
    let info = synthetic_info();
    let original = with_info(&atom("λ\0🙂"), &info);
    let rewritten = invoke(
        Intrinsic::SetAtomVal,
        &[original.clone_ref(), Obj::mk_string("改\0β")],
    );
    assert_eq!(
        child(&rewritten, 0).unwrap().identity_token(),
        info.identity_token()
    );
    for (value, expected) in [(&original, "λ\0🙂"), (&rewritten, "改\0β")] {
        assert_eq!(invoke(Intrinsic::IsAtom, &[value.clone_ref()]).unbox(), 1);
        assert_eq!(
            string(&invoke(Intrinsic::GetAtomVal, &[value.clone_ref()])).unwrap(),
            expected
        );
        assert_eq!(
            invoke(Intrinsic::GetAtomVal, &[value.clone_ref()]).identity_token(),
            child(value, 1).unwrap().identity_token()
        );
    }
    for value in [
        Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
        ident(info),
        node(Name::from_components(["atom"]), vec![original]),
    ] {
        assert_eq!(invoke(Intrinsic::IsAtom, &[value.clone_ref()]).unbox(), 0);
        assert_eq!(
            string(&invoke(Intrinsic::GetAtomVal, &[value.clone_ref()])).unwrap(),
            ""
        );
        assert_eq!(
            invoke(
                Intrinsic::SetAtomVal,
                &[value.clone_ref(), Obj::mk_string("unused")]
            )
            .identity_token(),
            value.identity_token()
        );
    }
}

#[test]
fn replacing_arguments_preserves_aliases_kind_info_and_out_of_bounds_behavior() {
    let info = synthetic_info();
    let original = with_info(
        &node(
            Name::num(Name::from_components(["kind", "_hyg"]), 53),
            vec![atom("left"), atom("right")],
        ),
        &info,
    );
    let old_children = child(&original, 2).unwrap();
    let replacement = ident(Obj::mk_nat(layout::SOURCE_NONE_TAG));
    let changed = invoke(
        Intrinsic::SetArg,
        &[
            original.clone_ref(),
            Obj::mk_nat(1),
            replacement.clone_ref(),
        ],
    );
    let changed_children = child(&changed, 2).unwrap();
    assert_ne!(
        changed_children.identity_token(),
        old_children.identity_token()
    );
    assert_eq!(
        changed_children.array_child(0).identity_token(),
        old_children.array_child(0).identity_token()
    );
    assert_eq!(
        changed_children.array_child(1).identity_token(),
        replacement.identity_token()
    );
    assert_eq!(
        string(&child(&old_children.array_child(1), 1).unwrap()).unwrap(),
        "right"
    );
    for index in [Obj::mk_nat(2), Obj::mk_nat(99), Obj::mk_mpz(&[0, 1], false)] {
        assert_eq!(
            invoke(
                Intrinsic::SetArg,
                &[original.clone_ref(), index, replacement.clone_ref()]
            )
            .identity_token(),
            original.identity_token()
        );
    }
    let replacement_children = Obj::mk_array(vec![replacement]);
    let replaced = invoke(
        Intrinsic::SetArgs,
        &[original.clone_ref(), replacement_children.clone_ref()],
    );
    assert_eq!(
        child(&replaced, 2).unwrap().identity_token(),
        replacement_children.identity_token()
    );
    for updated in [changed, replaced] {
        for field in [0, 1] {
            assert_eq!(
                child(&updated, field).unwrap().identity_token(),
                child(&original, field).unwrap().identity_token()
            );
        }
    }
    for value in [
        atom("leaf"),
        ident(info),
        Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
    ] {
        for (operation, args) in [
            (
                Intrinsic::SetArgs,
                vec![value.clone_ref(), Obj::mk_array(vec![])],
            ),
            (
                Intrinsic::SetArg,
                vec![value.clone_ref(), Obj::mk_nat(0), atom("unused")],
            ),
        ] {
            assert_eq!(
                invoke(operation, &args).identity_token(),
                value.identity_token()
            );
        }
    }
}

#[test]
fn root_info_updates_preserve_all_other_fields_and_do_not_rewrite_descendants() {
    let info = synthetic_info();
    for (original, fields) in [
        (atom("token"), layout::SYNTAX_ATOM.object_fields),
        (
            ident(Obj::mk_nat(layout::SOURCE_NONE_TAG)),
            layout::SYNTAX_IDENT.object_fields,
        ),
        (
            node(Name::from_components(["node"]), vec![atom("nested")]),
            layout::SYNTAX_NODE.object_fields,
        ),
    ] {
        let updated = with_info(&original, &info);
        assert_eq!(
            child(&updated, 0).unwrap().identity_token(),
            info.identity_token()
        );
        assert_eq!(
            child(&original, 0).unwrap().unbox(),
            layout::SOURCE_NONE_TAG
        );
        for field in 1..fields {
            assert_eq!(
                child(&updated, field).unwrap().identity_token(),
                child(&original, field).unwrap().identity_token()
            );
        }
        assert_eq!(
            invoke(Intrinsic::GetHeadInfo, &[updated]).identity_token(),
            info.identity_token()
        );
    }
    assert_eq!(
        with_info(&Obj::mk_nat(layout::SYNTAX_MISSING_TAG), &info).unbox(),
        layout::SYNTAX_MISSING_TAG
    );
}

#[test]
fn head_info_follows_pin_token_order_including_none_metadata() {
    let info = synthetic_info();
    let informed = with_info(&atom("positioned"), &info);
    let empty = node(Name::from_components(["empty"]), vec![]);
    let missing = Obj::mk_nat(layout::SYNTAX_MISSING_TAG);
    let nested = node(
        Name::from_components(["outer"]),
        vec![
            node(
                Name::from_components(["inner"]),
                vec![missing.clone_ref(), empty.clone_ref()],
            ),
            informed.clone_ref(),
        ],
    );
    assert_eq!(
        invoke(Intrinsic::GetHeadInfo, &[nested]).identity_token(),
        info.identity_token()
    );
    for first in [
        atom("unpositioned"),
        ident(Obj::mk_nat(layout::SOURCE_NONE_TAG)),
    ] {
        let syntax = node(Name::anonymous(), vec![first, informed.clone_ref()]);
        assert_eq!(
            invoke(Intrinsic::GetHeadInfo, &[syntax]).unbox(),
            layout::SOURCE_NONE_TAG
        );
    }
    for syntax in [missing, empty, node(Name::anonymous(), vec![atom("")])] {
        assert_eq!(
            invoke(Intrinsic::GetHeadInfo, &[syntax]).unbox(),
            layout::SOURCE_NONE_TAG
        );
    }
    // A node's own metadata wins without descending into its children.
    let whitespace = Obj::mk_ctor(
        layout::SUBSTRING_RAW.tag,
        vec![Obj::mk_string(""), Obj::mk_nat(0), Obj::mk_nat(0)],
        &[],
    );
    let own_info = Obj::mk_ctor(
        layout::SOURCE_ORIGINAL.tag,
        vec![
            whitespace.clone_ref(),
            Obj::mk_nat(0),
            whitespace,
            Obj::mk_nat(0),
        ],
        &[],
    );
    let syntax = with_info(&node(Name::anonymous(), vec![informed]), &own_info);
    assert_eq!(
        invoke(Intrinsic::GetHeadInfo, &[syntax]).identity_token(),
        own_info.identity_token()
    );
}

#[test]
fn malformed_native_syntax_operations_refuse_without_mutating_valid_inputs() {
    let valid = node(Name::anonymous(), vec![atom("untouched")]);
    let invalid_syntax = Obj::mk_ctor(layout::SYNTAX_NODE.tag, vec![], &[]);
    let cases = [
        (
            Intrinsic::IsAtom,
            "mirror:Lean.Syntax.isAtom",
            vec![invalid_syntax.clone_ref()],
        ),
        (
            Intrinsic::GetAtomVal,
            "mirror:Lean.Syntax.getAtomVal",
            vec![invalid_syntax.clone_ref()],
        ),
        (
            Intrinsic::GetHeadInfo,
            "mirror:Lean.Syntax.getHeadInfo",
            vec![invalid_syntax.clone_ref()],
        ),
        (
            Intrinsic::SetAtomVal,
            "mirror:Lean.Syntax.setAtomVal",
            vec![atom("x"), Obj::mk_nat(0)],
        ),
        (
            Intrinsic::SetArgs,
            "mirror:Lean.Syntax.setArgs",
            vec![valid.clone_ref(), Obj::mk_string("not an array")],
        ),
        (
            Intrinsic::SetArg,
            "mirror:Lean.Syntax.setArg",
            vec![valid.clone_ref(), Obj::mk_mpz(&[1], true), atom("bad")],
        ),
        (
            Intrinsic::SetArg,
            "mirror:Lean.Syntax.setArg",
            vec![valid.clone_ref(), Obj::mk_nat(0), invalid_syntax],
        ),
        (
            Intrinsic::SetInfo,
            "mirror:Lean.Syntax.setInfo",
            vec![Obj::mk_nat(0), valid.clone_ref()],
        ),
        (
            Intrinsic::GetHeadInfo,
            "mirror:Lean.Syntax.getHeadInfo",
            vec![Obj::mk_ctor(
                layout::SYNTAX_ATOM.tag,
                vec![Obj::mk_nat(0), Obj::mk_string("x")],
                &[],
            )],
        ),
    ];
    for (operation, row, args) in cases {
        assert!(
            matches!(
                operation.invoke(row, &args),
                Err(IntrinsicFailure::Refused(_))
            ),
            "{row}"
        );
    }
    assert_eq!(
        string(&invoke(
            Intrinsic::GetAtomVal,
            &[child(&valid, 2).unwrap().array_child(0)]
        ))
        .unwrap(),
        "untouched"
    );
}

#[test]
fn shared_syntax_dags_exhaust_a_typed_budget_and_leave_later_calls_usable() {
    let mut syntax = Obj::mk_nat(layout::SYNTAX_MISSING_TAG);
    // Only 21 allocated nodes, but over a million visits if naively expanded.
    for _ in 0..21 {
        syntax = node(Name::anonymous(), vec![syntax.clone_ref(), syntax]);
    }
    let row = "mirror:Lean.Syntax.getHeadInfo";
    assert!(matches!(
        Intrinsic::GetHeadInfo.invoke(row, &[syntax.clone_ref()]),
        Err(IntrinsicFailure::MirrorResource {
            resource: "syntax head-info nodes",
            allowed: MAX_SYNTAX_NODES,
            observed,
        }) if observed == MAX_SYNTAX_NODES + 1
    ));
    let program = lookup::callable_program(row);
    assert!(matches!(
        execute_function(
            &program,
            flbc::FunctionId::new(1),
            vec![syntax],
            ExecutionLimits::default(),
            None,
        ),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(
        invoke(Intrinsic::GetHeadInfo, &[atom("recovered")]).unbox(),
        layout::SOURCE_NONE_TAG
    );
}
