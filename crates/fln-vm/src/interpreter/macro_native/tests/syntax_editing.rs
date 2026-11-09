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

fn position_info(pos: Obj, end_pos: Obj, canonical: u8) -> Obj {
    Obj::mk_ctor(
        layout::SOURCE_SYNTHETIC.tag,
        vec![pos, end_pos],
        &[canonical],
    )
}

fn position_result(value: &Obj) -> Option<Obj> {
    if value.is_scalar() {
        assert_eq!(value.unbox(), expansion_layout::OPTION_NONE_TAG);
        None
    } else {
        check_layout(value, expansion_layout::OPTION_SOME).unwrap();
        Some(child(value, 0).unwrap())
    }
}

fn syntax_position(operation: Intrinsic, syntax: &Obj, canonical: bool) -> Option<usize> {
    position_result(&invoke(
        operation,
        &[syntax.clone_ref(), Obj::mk_nat(usize::from(canonical))],
    ))
    .map(|position| position.unbox())
}

#[test]
fn source_positions_preserve_nat_values_and_filter_only_noncanonical_synthetic_info() {
    let pos = Obj::mk_mpz(&[13, 1], false);
    let end_pos = Obj::mk_mpz(&[21, 2], false);
    let whitespace = Obj::mk_ctor(
        layout::SUBSTRING_RAW.tag,
        vec![Obj::mk_string(""), Obj::mk_nat(0), Obj::mk_nat(0)],
        &[],
    );
    let original = Obj::mk_ctor(
        layout::SOURCE_ORIGINAL.tag,
        vec![
            whitespace.clone_ref(),
            pos.clone_ref(),
            whitespace,
            end_pos.clone_ref(),
        ],
        &[],
    );
    for (info, synthetic_canonical) in [
        (original, None),
        (
            position_info(pos.clone_ref(), end_pos.clone_ref(), 0),
            Some(false),
        ),
        (
            position_info(pos.clone_ref(), end_pos.clone_ref(), 1),
            Some(true),
        ),
    ] {
        for canonical_only in [false, true] {
            for (operation, expected) in [
                (Intrinsic::SourceInfoGetPos, &pos),
                (Intrinsic::SourceInfoGetTailPos, &end_pos),
            ] {
                let result = position_result(&invoke(
                    operation,
                    &[info.clone_ref(), Obj::mk_nat(usize::from(canonical_only))],
                ));
                if canonical_only && synthetic_canonical == Some(false) {
                    assert!(result.is_none());
                } else {
                    assert_eq!(result.unwrap().identity_token(), expected.identity_token());
                }
            }
        }
    }
    for operation in [Intrinsic::SourceInfoGetPos, Intrinsic::SourceInfoGetTailPos] {
        for canonical in [0, 1] {
            assert!(
                position_result(&invoke(
                    operation,
                    &[Obj::mk_nat(layout::SOURCE_NONE_TAG), Obj::mk_nat(canonical)],
                ))
                .is_none()
            );
        }
    }
}

#[test]
fn syntax_positions_follow_head_token_and_reverse_tail_search_semantics() {
    let canonical = position_info(Obj::mk_nat(2), Obj::mk_nat(7), 1);
    let noncanonical = position_info(Obj::mk_nat(1), Obj::mk_nat(9), 0);
    let informed = with_info(&atom("positioned"), &canonical);
    let missing = Obj::mk_nat(layout::SYNTAX_MISSING_TAG);
    let empty = node(Name::anonymous(), vec![]);
    let tree = node(
        Name::anonymous(),
        vec![
            missing.clone_ref(),
            empty.clone_ref(),
            informed.clone_ref(),
            node(Name::anonymous(), vec![empty, missing]),
        ],
    );
    for only in [false, true] {
        assert_eq!(syntax_position(Intrinsic::GetPos, &tree, only), Some(2));
        assert_eq!(syntax_position(Intrinsic::GetTailPos, &tree, only), Some(7));
        for unpositioned in [atom("none"), ident(Obj::mk_nat(layout::SOURCE_NONE_TAG))] {
            let first = node(
                Name::anonymous(),
                vec![unpositioned.clone_ref(), informed.clone_ref()],
            );
            assert_eq!(syntax_position(Intrinsic::GetPos, &first, only), None);
            let last = node(Name::anonymous(), vec![informed.clone_ref(), unpositioned]);
            assert_eq!(syntax_position(Intrinsic::GetTailPos, &last, only), Some(7));
        }
    }
    let filtered_node = with_info(&tree, &noncanonical);
    assert_eq!(
        syntax_position(Intrinsic::GetPos, &filtered_node, false),
        Some(1)
    );
    assert_eq!(
        syntax_position(Intrinsic::GetTailPos, &filtered_node, false),
        Some(9)
    );
    // getPos? obtains the first info, then filters it. getTailPos? filters a
    // node before descending, so it can still find a canonical child.
    assert_eq!(
        syntax_position(Intrinsic::GetPos, &filtered_node, true),
        None
    );
    assert_eq!(
        syntax_position(Intrinsic::GetTailPos, &filtered_node, true),
        Some(7)
    );
    let last = node(
        Name::anonymous(),
        vec![
            informed,
            with_info(&ident(noncanonical.clone_ref()), &noncanonical),
        ],
    );
    assert_eq!(
        syntax_position(Intrinsic::GetTailPos, &last, false),
        Some(9)
    );
    assert_eq!(syntax_position(Intrinsic::GetTailPos, &last, true), Some(7));
    let own = with_info(&last, &position_info(Obj::mk_nat(0), Obj::mk_nat(11), 1));
    assert_eq!(syntax_position(Intrinsic::GetPos, &own, true), Some(0));
    assert_eq!(syntax_position(Intrinsic::GetTailPos, &own, true), Some(11));
}

#[test]
fn source_position_methods_reject_malformed_values_and_recover() {
    let source_row = "mirror:Lean.SourceInfo.getPos?";
    for info in [
        Obj::mk_nat(layout::SOURCE_NONE_TAG + 1),
        Obj::mk_ctor(layout::SOURCE_SYNTHETIC.tag, vec![], &[]),
        position_info(Obj::mk_nat(0), Obj::mk_nat(1), 2),
        position_info(Obj::mk_string("not a position"), Obj::mk_nat(1), 1),
        position_info(Obj::mk_mpz(&[1], true), Obj::mk_nat(1), 1),
    ] {
        assert!(matches!(
            Intrinsic::SourceInfoGetPos.invoke(source_row, &[info, Obj::mk_nat(0)]),
            Err(IntrinsicFailure::Refused(_))
        ));
    }
    let row = "mirror:Lean.Syntax.getTailPos?";
    let malformed_children = Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            inject_name(&Name::anonymous()),
            Obj::mk_nat(0),
        ],
        &[],
    );
    for syntax in [
        Obj::mk_ctor(layout::SYNTAX_NODE.tag, vec![], &[]),
        malformed_children,
        with_info(
            &atom("bad"),
            &position_info(Obj::mk_nat(0), Obj::mk_mpz(&[1], true), 1),
        ),
    ] {
        assert!(matches!(
            Intrinsic::GetTailPos.invoke(row, &[syntax, Obj::mk_nat(0)]),
            Err(IntrinsicFailure::Refused(_))
        ));
    }
    let valid = with_info(&atom("ok"), &synthetic_info());
    assert!(matches!(
        Intrinsic::GetTailPos.invoke(row, &[valid.clone_ref(), Obj::mk_nat(2)]),
        Err(IntrinsicFailure::Refused(
            VmRefusal::InvalidBoolScalar { .. }
        ))
    ));
    assert!(matches!(
        Intrinsic::GetTailPos.invoke(row, &[valid.clone_ref()]),
        Err(IntrinsicFailure::Refused(VmRefusal::IntrinsicArity { .. }))
    ));
    assert_eq!(
        syntax_position(Intrinsic::GetTailPos, &valid, true),
        Some(7)
    );
}

#[test]
fn position_methods_keep_resource_and_cancellation_stops_outside_option_results() {
    let mut syntax = Obj::mk_nat(layout::SYNTAX_MISSING_TAG);
    for _ in 0..21 {
        syntax = node(Name::anonymous(), vec![syntax.clone_ref(), syntax]);
    }
    for (operation, row, resource) in [
        (
            Intrinsic::GetPos,
            "mirror:Lean.Syntax.getPos?",
            "syntax head-info nodes",
        ),
        (
            Intrinsic::GetTailPos,
            "mirror:Lean.Syntax.getTailPos?",
            "syntax tail-position nodes",
        ),
    ] {
        assert!(matches!(
            operation.invoke(row, &[syntax.clone_ref(), Obj::mk_nat(1)]),
            Err(IntrinsicFailure::MirrorResource { resource: actual, allowed: MAX_SYNTAX_NODES, observed })
                if actual == resource && observed == MAX_SYNTAX_NODES + 1
        ));
        let program = lookup::callable_program(row);
        assert!(matches!(
            execute_function(
                &program,
                flbc::FunctionId::new(1),
                vec![syntax.clone_ref(), Obj::mk_nat(1)],
                ExecutionLimits::default(),
                None
            ),
            Outcome::Inconclusive(_)
        ));
        let valid = with_info(&atom("recovered"), &synthetic_info());
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
                    vec![valid.clone_ref(), Obj::mk_nat(1)],
                    limits,
                    Some(&|| cancelled)
                ),
                Outcome::Inconclusive(_)
            ));
        }
        let report = execute_function(
            &program,
            flbc::FunctionId::new(1),
            vec![valid, Obj::mk_nat(1)],
            ExecutionLimits::default(),
            None,
        );
        let Outcome::Complete(VmExit::Returned(result)) = report else {
            panic!("{report:?}")
        };
        assert_eq!(
            position_result(&result.value).unwrap().unbox(),
            if operation == Intrinsic::GetPos { 2 } else { 7 }
        );
    }
}

fn reference_range(info: &Obj) -> Option<(usize, usize, bool)> {
    if source_info(info).unwrap() {
        return None;
    }
    check_layout(info, layout::SOURCE_SYNTHETIC).unwrap();
    let offset = layout::SOURCE_SYNTHETIC_CANONICAL_OBJECT_FIELDS * std::mem::size_of::<usize>()
        + layout::SOURCE_SYNTHETIC_CANONICAL_BYTE_OFFSET;
    Some((
        child(info, layout::SOURCE_SYNTHETIC_POS_FIELD)
            .unwrap()
            .unbox(),
        child(info, layout::SOURCE_SYNTHETIC_TAIL_POS_FIELD)
            .unwrap()
            .unbox(),
        info.try_ctor_scalar_u32(offset).unwrap().to_ne_bytes()[0] == 1,
    ))
}

#[test]
fn reference_construction_prefers_canonical_ranges_then_retries_both_endpoints() {
    let canonical = with_info(&atom("canonical"), &synthetic_info());
    let noncanonical_info = position_info(Obj::mk_nat(1), Obj::mk_nat(9), 0);
    let noncanonical = with_info(&ident(noncanonical_info.clone_ref()), &noncanonical_info);
    let known = Some((2, 7, false));
    let canonical_known = Some((2, 7, true));
    for (input, ordinary, preferred) in [
        (Obj::mk_nat(layout::SYNTAX_MISSING_TAG), None, None),
        (atom("no source"), None, None),
        (canonical.clone_ref(), known, canonical_known),
        (
            noncanonical.clone_ref(),
            Some((1, 9, false)),
            Some((1, 9, false)),
        ),
        (
            with_info(
                &node(Name::anonymous(), vec![canonical.clone_ref()]),
                &noncanonical_info,
            ),
            Some((1, 9, false)),
            Some((1, 9, false)),
        ),
        (
            node(
                Name::anonymous(),
                vec![canonical.clone_ref(), noncanonical.clone_ref()],
            ),
            Some((2, 9, false)),
            canonical_known,
        ),
        (
            node(Name::anonymous(), vec![noncanonical, canonical.clone_ref()]),
            Some((1, 7, false)),
            Some((1, 7, false)),
        ),
        (
            node(
                Name::anonymous(),
                vec![atom("no head"), canonical.clone_ref()],
            ),
            None,
            None,
        ),
        (
            node(Name::anonymous(), vec![canonical, atom("no tail")]),
            known,
            canonical_known,
        ),
    ] {
        for (flag, expected) in [(0, ordinary), (1, preferred)] {
            let info = invoke(
                Intrinsic::SourceInfoFromRef,
                &[input.clone_ref(), Obj::mk_nat(flag)],
            );
            assert_eq!(reference_range(&info), expected);
            let text = Obj::mk_string("改\0🙂");
            let output = invoke(
                Intrinsic::MkAtomFrom,
                &[input.clone_ref(), text.clone_ref(), Obj::mk_nat(flag)],
            );
            check_layout(&output, layout::SYNTAX_ATOM).unwrap();
            assert_eq!(reference_range(&child(&output, 0).unwrap()), expected);
            assert_eq!(
                child(&output, 1).unwrap().identity_token(),
                text.identity_token()
            );
            assert_eq!(string(&child(&output, 1).unwrap()).unwrap(), "改\0🙂");
        }
    }
}

#[test]
fn atom_construction_preserves_large_positions_and_exact_shared_string_bytes() {
    let pos = Obj::mk_mpz(&[13, 1], false);
    let tail = Obj::mk_mpz(&[21, 2], false);
    let whitespace = Obj::mk_ctor(
        layout::SUBSTRING_RAW.tag,
        vec![Obj::mk_string(""), Obj::mk_nat(0), Obj::mk_nat(0)],
        &[],
    );
    let original = Obj::mk_ctor(
        layout::SOURCE_ORIGINAL.tag,
        vec![
            whitespace.clone_ref(),
            pos.clone_ref(),
            whitespace,
            tail.clone_ref(),
        ],
        &[],
    );
    for input_info in [
        original,
        position_info(pos.clone_ref(), tail.clone_ref(), 1),
    ] {
        let input = with_info(&atom("unchanged"), &input_info);
        for canonical in [0, 1] {
            let info = invoke(
                Intrinsic::SourceInfoFromRef,
                &[input.clone_ref(), Obj::mk_nat(canonical)],
            );
            for (field, expected) in [
                (layout::SOURCE_SYNTHETIC_POS_FIELD, &pos),
                (layout::SOURCE_SYNTHETIC_TAIL_POS_FIELD, &tail),
            ] {
                assert_eq!(
                    child(&info, field).unwrap().identity_token(),
                    expected.identity_token()
                );
            }
        }
        assert_eq!(
            child(&input, 0).unwrap().identity_token(),
            input_info.identity_token()
        );
        assert_eq!(string(&child(&input, 1).unwrap()).unwrap(), "unchanged");
    }
    for text in ["", "λ\0🙂", "different length from the source span"] {
        let value = Obj::mk_string(text);
        let result = invoke(Intrinsic::MkAtom, &[value.clone_ref()]);
        check_layout(&result, layout::SYNTAX_ATOM).unwrap();
        assert_eq!(child(&result, 0).unwrap().unbox(), layout::SOURCE_NONE_TAG);
        assert_eq!(
            child(&result, 1).unwrap().identity_token(),
            value.identity_token()
        );
        assert_eq!(string(&child(&result, 1).unwrap()).unwrap(), text);
    }
}

#[test]
fn reference_construction_rejects_bad_shapes_even_after_an_absent_head() {
    let bad_info = |info| {
        Obj::mk_ctor(
            layout::SYNTAX_ATOM.tag,
            vec![info, Obj::mk_string("bad")],
            &[],
        )
    };
    for input in [
        Obj::mk_nat(layout::SYNTAX_MISSING_TAG + 1),
        Obj::mk_ctor(layout::SYNTAX_NODE.tag, vec![], &[]),
        bad_info(Obj::mk_ctor(layout::SOURCE_SYNTHETIC.tag, vec![], &[])),
        bad_info(position_info(Obj::mk_nat(0), Obj::mk_nat(1), 2)),
        bad_info(position_info(Obj::mk_nat(0), Obj::mk_mpz(&[1], true), 1)),
        bad_info(position_info(Obj::mk_string("not Nat"), Obj::mk_nat(1), 1)),
        // A missing start does not make a malformed tail into SourceInfo.none.
        node(Name::anonymous(), vec![atom("no head"), Obj::mk_nat(999)]),
    ] {
        for canonical in [0, 1] {
            for (operation, row, args) in [
                (
                    Intrinsic::SourceInfoFromRef,
                    "mirror:Lean.SourceInfo.fromRef",
                    vec![input.clone_ref(), Obj::mk_nat(canonical)],
                ),
                (
                    Intrinsic::MkAtomFrom,
                    "mirror:Lean.mkAtomFrom",
                    vec![
                        input.clone_ref(),
                        Obj::mk_string("new"),
                        Obj::mk_nat(canonical),
                    ],
                ),
            ] {
                assert!(matches!(
                    operation.invoke(row, &args),
                    Err(IntrinsicFailure::Refused(_))
                ));
            }
        }
    }
    for (operation, row, args) in [
        (
            Intrinsic::MkAtom,
            "mirror:Lean.mkAtom",
            vec![Obj::mk_nat(0)],
        ),
        (
            Intrinsic::MkAtomFrom,
            "mirror:Lean.mkAtomFrom",
            vec![atom("ok"), Obj::mk_nat(0), Obj::mk_nat(0)],
        ),
        (
            Intrinsic::MkAtomFrom,
            "mirror:Lean.mkAtomFrom",
            vec![atom("ok"), Obj::mk_string("ok"), Obj::mk_nat(2)],
        ),
        (
            Intrinsic::SourceInfoFromRef,
            "mirror:Lean.SourceInfo.fromRef",
            vec![atom("ok"), Obj::mk_nat(2)],
        ),
        (
            Intrinsic::SourceInfoFromRef,
            "mirror:Lean.SourceInfo.fromRef",
            vec![atom("ok")],
        ),
    ] {
        assert!(matches!(
            operation.invoke(row, &args),
            Err(IntrinsicFailure::Refused(_))
        ));
    }
    assert_eq!(
        reference_range(&invoke(
            Intrinsic::SourceInfoFromRef,
            &[
                with_info(&atom("recovered"), &synthetic_info()),
                Obj::mk_nat(1)
            ],
        )),
        Some((2, 7, true))
    );
}

#[test]
fn reference_construction_shares_walk_budget_and_keeps_stops_non_authoritative() {
    let mut empty = Obj::mk_nat(layout::SYNTAX_MISSING_TAG);
    for _ in 0..18 {
        empty = node(Name::anonymous(), vec![empty.clone_ref(), empty]);
    }
    let valid = with_info(&atom("ok"), &synthetic_info());
    let input = node(
        Name::anonymous(),
        vec![empty.clone_ref(), valid.clone_ref(), empty],
    );
    // Each endpoint alone fits. Constructing the range must charge both walks
    // to one invocation budget rather than granting each a fresh allowance.
    assert_eq!(syntax_position(Intrinsic::GetPos, &input, false), Some(2));
    assert_eq!(
        syntax_position(Intrinsic::GetTailPos, &input, false),
        Some(7)
    );
    for (operation, row, args) in [
        (
            Intrinsic::SourceInfoFromRef,
            "mirror:Lean.SourceInfo.fromRef",
            vec![input.clone_ref(), Obj::mk_nat(0)],
        ),
        (
            Intrinsic::MkAtomFrom,
            "mirror:Lean.mkAtomFrom",
            vec![input, Obj::mk_string("new"), Obj::mk_nat(0)],
        ),
    ] {
        assert!(
            matches!(operation.invoke(row, &args), Err(IntrinsicFailure::MirrorResource {
            resource: "syntax source-info nodes", allowed: MAX_SYNTAX_NODES, observed,
        }) if observed == MAX_SYNTAX_NODES + 1)
        );
        assert!(matches!(
            execute_function(
                &lookup::callable_program(row),
                flbc::FunctionId::new(1),
                args,
                ExecutionLimits::default(),
                None,
            ),
            Outcome::Inconclusive(_)
        ));
    }
    for (row, args) in [
        (
            "mirror:Lean.SourceInfo.fromRef",
            vec![valid.clone_ref(), Obj::mk_nat(1)],
        ),
        (
            "mirror:Lean.mkAtomFrom",
            vec![valid, Obj::mk_string("new"), Obj::mk_nat(1)],
        ),
        ("mirror:Lean.mkAtom", vec![Obj::mk_string("new")]),
    ] {
        let program = lookup::callable_program(row);
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
                    args.iter().map(Obj::clone_ref).collect(),
                    limits,
                    Some(&|| cancelled),
                ),
                Outcome::Inconclusive(_)
            ));
        }
        assert!(matches!(
            execute_function(
                &program,
                flbc::FunctionId::new(1),
                args,
                ExecutionLimits::default(),
                None,
            ),
            Outcome::Complete(VmExit::Returned(_))
        ));
    }
}

fn diagnostic_context(reference: &Obj) -> Obj {
    let mut fields: Vec<_> = (0..layout::MACRO_CONTEXT.object_fields)
        .map(|_| Obj::mk_nat(0))
        .collect();
    // MethodsRef is deliberately opaque: reporting an error requires no
    // environment or recursive-expansion authority.
    fields[layout::MACRO_CONTEXT_METHODS_FIELD as usize] = Obj::mk_string("opaque methods");
    fields[expansion_layout::MACRO_CONTEXT_REF_FIELD] = reference.clone_ref();
    Obj::mk_ctor(layout::MACRO_CONTEXT.tag, fields, &[])
}

fn diagnostic_state() -> Obj {
    let trace = Obj::mk_ctor(
        layout::PROD.tag,
        vec![
            inject_name(&Name::from_components(["Trace"])),
            Obj::mk_string("λ\0trace"),
        ],
        &[],
    );
    let list = |value| {
        Obj::mk_ctor(
            layout::LIST_CONS.tag,
            vec![value, Obj::mk_nat(layout::LIST_NIL_TAG)],
            &[],
        )
    };
    Obj::mk_ctor(
        layout::MACRO_STATE.tag,
        vec![
            Obj::mk_nat(23),
            list(trace),
            list(inject_name(&Name::from_components(["Earlier", "macro"]))),
        ],
        &[],
    )
}

#[test]
fn reference_replacement_uses_only_the_first_head_position_and_returns_original_objects() {
    let old = ident(synthetic_info());
    let positioned = with_info(
        &atom("zero"),
        &position_info(Obj::mk_nat(0), Obj::mk_nat(4), 0),
    );
    let missing = Obj::mk_nat(layout::SYNTAX_MISSING_TAG);
    let empty = node(Name::anonymous(), vec![]);
    for (value, selects_new) in [
        (missing.clone_ref(), false),
        (empty.clone_ref(), false),
        (atom("unpositioned"), false),
        (
            node(
                Name::anonymous(),
                vec![atom("no head"), positioned.clone_ref()],
            ),
            false,
        ),
        (
            node(
                Name::anonymous(),
                vec![missing, empty, positioned.clone_ref()],
            ),
            true,
        ),
        (positioned, true),
        (ident(synthetic_info()), true),
        // A tail is irrelevant, including when its foreign representation is
        // invalid; only the selected head Nat is inspected.
        (
            with_info(
                &atom("large"),
                &position_info(
                    Obj::mk_mpz(&[17, 1], false),
                    Obj::mk_string("unused tail"),
                    0,
                ),
            ),
            true,
        ),
    ] {
        let output = invoke(Intrinsic::ReplaceRef, &[value.clone_ref(), old.clone_ref()]);
        assert_eq!(
            output.identity_token(),
            if selects_new {
                value.identity_token()
            } else {
                old.identity_token()
            }
        );
    }
}

#[test]
fn public_macro_errors_preserve_exact_state_message_and_selected_reference() {
    let old = ident(synthetic_info());
    let context = diagnostic_context(&old);
    let state = diagnostic_state();
    let message = Obj::mk_string("located\0λ🙂");
    let noncanonical = with_info(
        &atom("new"),
        &position_info(Obj::mk_nat(0), Obj::mk_nat(4), 0),
    );
    let no_head = node(
        Name::anonymous(),
        vec![atom("none"), noncanonical.clone_ref()],
    );
    for (operation, args, expected) in [
        (
            Intrinsic::ThrowError,
            vec![message.clone_ref(), context.clone_ref(), state.clone_ref()],
            old.clone_ref(),
        ),
        (
            Intrinsic::ThrowErrorAt,
            vec![
                noncanonical.clone_ref(),
                message.clone_ref(),
                context.clone_ref(),
                state.clone_ref(),
            ],
            noncanonical,
        ),
        (
            Intrinsic::ThrowErrorAt,
            vec![
                no_head,
                message.clone_ref(),
                context.clone_ref(),
                state.clone_ref(),
            ],
            old.clone_ref(),
        ),
    ] {
        let output = invoke(operation, &args);
        check_layout(&output, layout::RESULT_ERROR).unwrap();
        assert_eq!(
            child(&output, 1).unwrap().identity_token(),
            state.identity_token()
        );
        let exception = child(&output, 0).unwrap();
        check_layout(&exception, layout::EXCEPTION_ERROR).unwrap();
        assert_eq!(
            child(&exception, 0).unwrap().identity_token(),
            expected.identity_token()
        );
        assert_eq!(
            child(&exception, 1).unwrap().identity_token(),
            message.identity_token()
        );
        assert_eq!(
            string(&child(&exception, 1).unwrap()).unwrap(),
            "located\0λ🙂"
        );
        assert_eq!(
            child(&context, expansion_layout::MACRO_CONTEXT_REF_FIELD)
                .unwrap()
                .identity_token(),
            old.identity_token()
        );
    }
    let unsupported = invoke(Intrinsic::ThrowUnsupported, &[state.clone_ref()]);
    check_layout(&unsupported, layout::RESULT_ERROR).unwrap();
    assert_eq!(
        child(&unsupported, 0).unwrap().unbox(),
        layout::EXCEPTION_UNSUPPORTED_TAG
    );
    assert_eq!(
        child(&unsupported, 1).unwrap().identity_token(),
        state.identity_token()
    );
}

#[test]
fn public_macro_error_rows_refuse_malformed_inputs_without_becoming_lean_errors() {
    let old = ident(synthetic_info());
    let context = diagnostic_context(&old);
    let state = diagnostic_state();
    for value in [
        Obj::mk_nat(999),
        Obj::mk_ctor(layout::SYNTAX_NODE.tag, vec![], &[]),
        with_info(
            &atom("bad"),
            &position_info(Obj::mk_string("not Nat"), Obj::mk_nat(1), 1),
        ),
        with_info(
            &atom("bad"),
            &position_info(Obj::mk_mpz(&[1], true), Obj::mk_nat(1), 1),
        ),
        with_info(
            &atom("bad"),
            &position_info(Obj::mk_nat(0), Obj::mk_nat(1), 2),
        ),
    ] {
        for (operation, row, args) in [
            (
                Intrinsic::ReplaceRef,
                "mirror:Lean.replaceRef",
                vec![value.clone_ref(), old.clone_ref()],
            ),
            (
                Intrinsic::ThrowErrorAt,
                "mirror:Lean.Macro.throwErrorAt._redArg",
                vec![
                    value,
                    Obj::mk_string("message"),
                    context.clone_ref(),
                    state.clone_ref(),
                ],
            ),
        ] {
            assert!(matches!(
                operation.invoke(row, &args),
                Err(IntrinsicFailure::Refused(_))
            ));
        }
    }
    for (operation, row, args) in [
        (
            Intrinsic::ReplaceRef,
            "mirror:Lean.replaceRef",
            vec![old.clone_ref(), Obj::mk_nat(99)],
        ),
        (
            Intrinsic::ThrowError,
            "mirror:Lean.Macro.throwError._redArg",
            vec![Obj::mk_nat(0), context.clone_ref(), state.clone_ref()],
        ),
        (
            Intrinsic::ThrowError,
            "mirror:Lean.Macro.throwError._redArg",
            vec![Obj::mk_string("m"), Obj::mk_nat(0), state.clone_ref()],
        ),
        (
            Intrinsic::ThrowError,
            "mirror:Lean.Macro.throwError._redArg",
            vec![
                Obj::mk_string("m"),
                diagnostic_context(&Obj::mk_nat(999)),
                state.clone_ref(),
            ],
        ),
        (
            Intrinsic::ThrowError,
            "mirror:Lean.Macro.throwError._redArg",
            vec![Obj::mk_string("m"), context, Obj::mk_nat(0)],
        ),
        (
            Intrinsic::ThrowErrorAt,
            "mirror:Lean.Macro.throwErrorAt._redArg",
            vec![],
        ),
        (
            Intrinsic::ThrowUnsupported,
            "mirror:Lean.Macro.throwUnsupported._redArg",
            vec![Obj::mk_ctor(layout::MACRO_STATE.tag, vec![], &[])],
        ),
    ] {
        assert!(matches!(
            operation.invoke(row, &args),
            Err(IntrinsicFailure::Refused(_))
        ));
    }
    check_layout(
        &invoke(Intrinsic::ThrowUnsupported, &[state]),
        layout::RESULT_ERROR,
    )
    .unwrap();
}

#[test]
fn reference_errors_keep_resource_and_cancellation_stops_outside_macro_fallback() {
    let old = ident(synthetic_info());
    let context = diagnostic_context(&old);
    let state = diagnostic_state();
    let mut costly = Obj::mk_nat(layout::SYNTAX_MISSING_TAG);
    for _ in 0..20 {
        costly = node(Name::anonymous(), vec![costly.clone_ref(), costly]);
    }
    for (row, args) in [
        (
            "mirror:Lean.replaceRef",
            vec![costly.clone_ref(), old.clone_ref()],
        ),
        (
            "mirror:Lean.Macro.throwErrorAt._redArg",
            vec![
                costly,
                Obj::mk_string("m"),
                context.clone_ref(),
                state.clone_ref(),
            ],
        ),
    ] {
        assert!(matches!(
            execute_function(
                &lookup::callable_program(row),
                flbc::FunctionId::new(1),
                args,
                ExecutionLimits::default(),
                None
            ),
            Outcome::Inconclusive(_)
        ));
    }
    for (row, args) in [
        (
            "mirror:Lean.replaceRef",
            vec![old.clone_ref(), old.clone_ref()],
        ),
        (
            "mirror:Lean.Macro.throwError._redArg",
            vec![Obj::mk_string("m"), context.clone_ref(), state.clone_ref()],
        ),
        (
            "mirror:Lean.Macro.throwErrorAt._redArg",
            vec![old, Obj::mk_string("m"), context, state.clone_ref()],
        ),
        ("mirror:Lean.Macro.throwUnsupported._redArg", vec![state]),
    ] {
        let program = lookup::callable_program(row);
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
                    args.iter().map(Obj::clone_ref).collect(),
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
                args,
                ExecutionLimits::default(),
                None
            ),
            Outcome::Complete(VmExit::Returned(_))
        ));
    }
}
