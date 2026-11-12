use super::*;

fn optional(value: Obj) -> Option<Obj> {
    if value.is_scalar() {
        assert_eq!(value.unbox(), expansion_layout::OPTION_NONE_TAG);
        None
    } else {
        check_layout(&value, expansion_layout::OPTION_SOME).unwrap();
        Some(child(&value, 0).unwrap())
    }
}

fn positioned(value: Obj, info: Obj) -> Obj {
    invoke(Intrinsic::SetInfo, &[info, value])
}

fn raw(text: &str, start: Obj, stop: Obj) -> Obj {
    Obj::mk_ctor(
        layout::SUBSTRING_RAW.tag,
        vec![Obj::mk_string(text), start, stop],
        &[],
    )
}

fn identifier(raw: Obj, info: Obj) -> Obj {
    Obj::mk_ctor(
        layout::SYNTAX_IDENT.tag,
        vec![
            info,
            raw,
            inject_name(&Name::from_components(["Resolved", "not_the_spelling"])),
            Obj::mk_nat(layout::LIST_NIL_TAG),
        ],
        &[],
    )
}

fn printed(value: &Obj) -> Option<String> {
    optional(invoke(Intrinsic::Reprint, &[value.clone_ref()]))
        .map(|value| string(&value).unwrap().to_owned())
}

fn choice(values: Vec<Obj>) -> Obj {
    node(Name::from_components(["choice"]), values)
}

#[test]
fn optional_info_distinguishes_no_token_from_a_token_without_positions() {
    let missing = Obj::mk_nat(layout::SYNTAX_MISSING_TAG);
    let empty = node(Name::anonymous(), vec![]);
    for value in [missing.clone_ref(), empty.clone_ref()] {
        assert!(optional(invoke(Intrinsic::GetHeadInfoOptional, &[value])).is_none());
    }
    assert!(optional(invoke(Intrinsic::GetInfo, &[missing.clone_ref()])).is_none());
    assert_eq!(
        optional(invoke(Intrinsic::GetInfo, &[empty.clone_ref()]))
            .unwrap()
            .unbox(),
        layout::SOURCE_NONE_TAG
    );
    let info = synthetic_info(Obj::mk_nat(2), Obj::mk_nat(7), true);
    let syntax = node(
        Name::anonymous(),
        vec![
            missing,
            empty,
            atom("first"),
            positioned(atom("later"), info.clone_ref()),
        ],
    );
    assert_eq!(
        optional(invoke(
            Intrinsic::GetHeadInfoOptional,
            &[syntax.clone_ref()]
        ))
        .unwrap()
        .unbox(),
        layout::SOURCE_NONE_TAG
    );
    let located = positioned(syntax, info.clone_ref());
    for operation in [Intrinsic::GetInfo, Intrinsic::GetHeadInfoOptional] {
        assert_eq!(
            optional(invoke(operation, &[located.clone_ref()]))
                .unwrap()
                .identity_token(),
            info.identity_token()
        );
    }
}

#[test]
fn ranges_keep_big_nat_endpoints_and_canonical_filtering_without_host_narrowing() {
    let start = Obj::mk_mpz(&[7, 11, 1], false);
    let stop = Obj::mk_mpz(&[5, 9, 1], false);
    // Range is an observation of the caller's syntax, not validation of a
    // source span: even reversed arbitrary Nat endpoints must survive.
    let value = positioned(
        atom("x"),
        synthetic_info(start.clone_ref(), stop.clone_ref(), false),
    );
    let range = optional(invoke(
        Intrinsic::GetRange,
        &[value.clone_ref(), Obj::mk_nat(0)],
    ))
    .unwrap();
    check_layout(&range, layout::SYNTAX_RANGE).unwrap();
    for (index, expected) in [
        (layout::SYNTAX_RANGE_START_FIELD, &start),
        (layout::SYNTAX_RANGE_STOP_FIELD, &stop),
    ] {
        assert_eq!(
            child(&range, index).unwrap().identity_token(),
            expected.identity_token()
        );
    }
    assert!(optional(invoke(Intrinsic::GetRange, &[value, Obj::mk_nat(1)])).is_none());

    let first = positioned(
        atom("first"),
        synthetic_info(Obj::mk_nat(1), Obj::mk_nat(2), true),
    );
    let tail = positioned(
        atom("tail"),
        synthetic_info(Obj::mk_nat(8), Obj::mk_nat(9), false),
    );
    let value = node(Name::anonymous(), vec![first, atom("gap"), tail]);
    for (canonical, expected_stop) in [(0, 9), (1, 2)] {
        let range = optional(invoke(
            Intrinsic::GetRange,
            &[value.clone_ref(), Obj::mk_nat(canonical)],
        ))
        .unwrap();
        assert_eq!(
            child(&range, layout::SYNTAX_RANGE_START_FIELD)
                .unwrap()
                .unbox(),
            1
        );
        assert_eq!(
            child(&range, layout::SYNTAX_RANGE_STOP_FIELD)
                .unwrap()
                .unbox(),
            expected_stop
        );
    }
    let unpositioned_head = node(Name::anonymous(), vec![atom("first"), value]);
    assert!(
        optional(invoke(
            Intrinsic::GetRange,
            &[unpositioned_head, Obj::mk_nat(0)]
        ))
        .is_none()
    );
}

#[test]
fn has_missing_visits_all_choice_alternatives_and_short_circuits_in_order() {
    let missing = Obj::mk_nat(layout::SYNTAX_MISSING_TAG);
    let absent = choice(vec![
        atom("first"),
        node(Name::anonymous(), vec![missing.clone_ref()]),
    ]);
    assert_eq!(invoke(Intrinsic::HasMissing, &[absent]).unbox(), 1);
    let complete = node(
        Name::anonymous(),
        vec![atom("x"), node(Name::anonymous(), vec![])],
    );
    assert_eq!(invoke(Intrinsic::HasMissing, &[complete]).unbox(), 0);
    let later_malformed = node(Name::anonymous(), vec![missing, Obj::mk_nat(99)]);
    assert_eq!(invoke(Intrinsic::HasMissing, &[later_malformed]).unbox(), 1);
}

#[test]
fn reprint_retains_original_trivia_raw_identifiers_and_synthetic_spacing() {
    let info = Obj::mk_ctor(
        layout::SOURCE_ORIGINAL.tag,
        vec![
            raw("/*λ*/", Obj::mk_nat(0), Obj::mk_nat(6)),
            Obj::mk_nat(6),
            raw("\n\0tail", Obj::mk_nat(0), Obj::mk_nat(2)),
            Obj::mk_nat(9),
        ],
        &[],
    );
    let identifier = identifier(raw("xλ🙂z", Obj::mk_nat(1), Obj::mk_nat(7)), info);
    let value = positioned(
        node(
            Name::from_components(["term"]),
            vec![identifier, atom("+"), Obj::mk_nat(0)],
        ),
        synthetic_info(Obj::mk_nat(0), Obj::mk_nat(9), true),
    );
    assert_eq!(printed(&value).as_deref(), Some("/*λ*/λ🙂\n\0 + "));
    assert_eq!(
        printed(&Obj::mk_nat(layout::SYNTAX_MISSING_TAG)).as_deref(),
        Some("")
    );
    assert_eq!(printed(&atom("")).as_deref(), Some("  "));
}

#[test]
fn reprint_uses_the_pins_raw_substring_endpoint_rules() {
    for (start, stop, expected) in [
        (Obj::mk_nat(2), Obj::mk_nat(4), "  "),
        (Obj::mk_nat(0), Obj::mk_nat(2), " aλz "),
        (Obj::mk_nat(1), Obj::mk_nat(3), " λ "),
        (Obj::mk_nat(3), Obj::mk_nat(90), " z "),
        (Obj::mk_mpz(&[0, 1], false), Obj::mk_nat(0), " aλz "),
        (Obj::mk_nat(3), Obj::mk_mpz(&[0, 1], false), " aλz "),
    ] {
        let value = identifier(
            raw("aλz", start, stop),
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
        );
        assert_eq!(printed(&value).as_deref(), Some(expected));
    }
}

#[test]
fn reprint_checks_nested_ambiguities_but_emits_only_the_first_agreeing_choice() {
    let left = node(Name::from_components(["left"]), vec![atom("a"), atom("b")]);
    let right = node(Name::from_components(["right"]), vec![atom("a"), atom("b")]);
    let equal = choice(vec![left.clone_ref(), right]);
    let nested = choice(vec![equal, left]);
    assert_eq!(printed(&nested).as_deref(), Some(" a  b "));
    let different = choice(vec![nested, atom("a b")]);
    assert_eq!(printed(&different), None);
    let unresolved = choice(vec![choice(vec![atom("a"), atom("b")]), atom("a")]);
    assert_eq!(printed(&unresolved), None);
}

#[test]
fn empty_choices_preserve_recoverable_panic_count_and_output_capture_limits() {
    use fln_rt::obj::StdoutCapture;
    let empty = choice(vec![]);
    let scope = StdoutCapture::begin_evaluation(1024 * 1024).unwrap();
    // The outer choice checks the empty alternative, then prints it again.
    assert_eq!(
        printed(&choice(vec![empty.clone_ref()])).as_deref(),
        Some("")
    );
    let capture = scope.finish();
    assert_eq!(capture.error, None);
    // Native backtrace text depends on the build, but the language reports
    // the same bounds error four times and keeps every report in the capture.
    assert_eq!(
        String::from_utf8(capture.bytes)
            .unwrap()
            .lines()
            .filter(|line| *line == "Error: index out of bounds")
            .count(),
        4
    );
    let scope = StdoutCapture::begin_evaluation(1).unwrap();
    assert!(matches!(
        Intrinsic::Reprint.invoke("mirror:Lean.Syntax.reprint", &[empty]),
        Err(IntrinsicFailure::Refused(
            VmRefusal::NativeStdoutCapture { .. }
        ))
    ));
    assert!(scope.finish().error.is_some());
}

#[test]
fn source_queries_refuse_malformed_observed_carriers_and_recover() {
    let broken_array = Obj::mk_ctor(
        layout::SYNTAX_NODE.tag,
        vec![
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
            inject_name(&Name::anonymous()),
            Obj::mk_nat(0),
        ],
        &[],
    );
    for (operation, row) in [
        (Intrinsic::HasMissing, "mirror:Lean.Syntax.hasMissing"),
        (
            Intrinsic::GetHeadInfoOptional,
            "mirror:Lean.Syntax.getHeadInfo?",
        ),
        (Intrinsic::Reprint, "mirror:Lean.Syntax.reprint"),
    ] {
        assert!(matches!(
            operation.invoke(row, &[broken_array.clone_ref()]),
            Err(IntrinsicFailure::Refused(_))
        ));
    }
    for value in [
        Obj::mk_nat(99),
        Obj::mk_ctor(
            layout::SYNTAX_ATOM.tag,
            vec![Obj::mk_nat(99), Obj::mk_string("x")],
            &[],
        ),
        identifier(Obj::mk_nat(0), Obj::mk_nat(layout::SOURCE_NONE_TAG)),
        identifier(
            raw("x", Obj::mk_string("bad Nat"), Obj::mk_nat(1)),
            Obj::mk_nat(layout::SOURCE_NONE_TAG),
        ),
    ] {
        assert!(matches!(
            Intrinsic::Reprint.invoke("mirror:Lean.Syntax.reprint", &[value]),
            Err(IntrinsicFailure::Refused(_))
        ));
    }
    // getRange? must evaluate its tail even after an unpositioned first token.
    let bad_tail = node(
        Name::anonymous(),
        vec![atom("no position"), Obj::mk_nat(99)],
    );
    assert!(matches!(
        Intrinsic::GetRange.invoke("mirror:Lean.Syntax.getRange?", &[bad_tail, Obj::mk_nat(0)]),
        Err(IntrinsicFailure::Refused(_))
    ));
    assert_eq!(printed(&atom("recovered")).as_deref(), Some(" recovered "));
}

#[test]
fn source_queries_bound_shared_dags_and_reprint_bytes_and_avoid_host_recursion() {
    let mut empty_dag = node(Name::anonymous(), vec![]);
    for _ in 0..21 {
        empty_dag = node(Name::anonymous(), vec![empty_dag.clone_ref(), empty_dag]);
    }
    for (operation, row, args) in [
        (
            Intrinsic::HasMissing,
            "mirror:Lean.Syntax.hasMissing",
            vec![empty_dag.clone_ref()],
        ),
        (
            Intrinsic::GetHeadInfoOptional,
            "mirror:Lean.Syntax.getHeadInfo?",
            vec![empty_dag.clone_ref()],
        ),
        (
            Intrinsic::GetRange,
            "mirror:Lean.Syntax.getRange?",
            vec![empty_dag.clone_ref(), Obj::mk_nat(0)],
        ),
        (
            Intrinsic::Reprint,
            "mirror:Lean.Syntax.reprint",
            vec![empty_dag],
        ),
    ] {
        assert!(
            matches!(
                operation.invoke(row, &args),
                Err(IntrinsicFailure::MirrorResource { .. })
            ),
            "{row}"
        );
    }
    let oversized = atom(&"x".repeat((MAX_NAME_BYTES / 2) as usize));
    assert!(matches!(
        Intrinsic::Reprint.invoke("mirror:Lean.Syntax.reprint", &[oversized]),
        Err(IntrinsicFailure::MirrorResource {
            resource: "syntax reprint bytes",
            ..
        })
    ));
    let mut deep = atom("x");
    for _ in 0..10_000 {
        deep = node(Name::anonymous(), vec![deep]);
    }
    assert_eq!(printed(&deep).as_deref(), Some(" x "));
    assert_eq!(invoke(Intrinsic::HasMissing, &[deep]).unbox(), 0);
    assert_eq!(printed(&atom("again")).as_deref(), Some(" again "));
}

#[test]
fn source_query_rows_execute_with_extracted_ownership_and_preserve_vm_stops() {
    let info = synthetic_info(Obj::mk_nat(1), Obj::mk_nat(3), true);
    let value = positioned(atom("x"), info.clone_ref());
    for row in [
        "mirror:Lean.Syntax.getInfo?",
        "mirror:Lean.Syntax.getHeadInfo?",
        "mirror:Lean.Syntax.getRange?",
        "mirror:Lean.Syntax.hasMissing",
        "mirror:Lean.Syntax.reprint",
    ] {
        // This includes canonical serialization, ownership insertion, and the
        // generated borrowed/owned/Bool contract at the actual VM boundary.
        let program = lookup::callable_program(row);
        let arguments = || {
            let mut args = vec![value.clone_ref()];
            if row == "mirror:Lean.Syntax.getRange?" {
                args.push(Obj::mk_nat(1));
            }
            args
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
            assert!(
                matches!(
                    execute_function(
                        &program,
                        flbc::FunctionId::new(1),
                        arguments(),
                        limits,
                        Some(&|| cancelled),
                    ),
                    Outcome::Inconclusive(_)
                ),
                "{row}"
            );
        }
        for _ in 0..2 {
            let report = execute_function(
                &program,
                flbc::FunctionId::new(1),
                arguments(),
                ExecutionLimits::default(),
                None,
            );
            let Outcome::Complete(VmExit::Returned(result)) = report else {
                panic!("{row}: {report:?}");
            };
            match row {
                "mirror:Lean.Syntax.getInfo?" | "mirror:Lean.Syntax.getHeadInfo?" => {
                    assert_eq!(
                        optional(result.value).unwrap().identity_token(),
                        info.identity_token()
                    );
                }
                "mirror:Lean.Syntax.getRange?" => {
                    let range = optional(result.value).unwrap();
                    assert_eq!(
                        child(&range, layout::SYNTAX_RANGE_START_FIELD)
                            .unwrap()
                            .unbox(),
                        1
                    );
                    assert_eq!(
                        child(&range, layout::SYNTAX_RANGE_STOP_FIELD)
                            .unwrap()
                            .unbox(),
                        3
                    );
                }
                "mirror:Lean.Syntax.hasMissing" => assert_eq!(result.value.unbox(), 0),
                "mirror:Lean.Syntax.reprint" => {
                    assert_eq!(string(&optional(result.value).unwrap()).unwrap(), " x ")
                }
                _ => unreachable!(),
            }
        }
        assert_eq!(
            string(&child(&value, 1).unwrap()).unwrap(),
            "x",
            "{row} preserves retained inputs"
        );
    }
}
