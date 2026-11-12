use super::*;
use fln_bignum::nat::BigNat;

const HUGE: &str = "115792089237316195423570985008687907853269984665640564039457584007913129639937";

fn number(text: &str) -> Obj {
    node(Name::str(Name::anonymous(), "num"), vec![atom(text)])
}

fn decimal(value: &Obj) -> String {
    crate::interpreter::nat_decimal(value).expect("a native Nat result")
}

fn option_decimal(value: &Obj) -> Option<String> {
    if value.is_scalar() {
        assert_eq!(value.unbox(), expansion_layout::OPTION_NONE_TAG);
        None
    } else {
        check_layout(value, expansion_layout::OPTION_SOME).unwrap();
        Some(decimal(&child(value, 0).unwrap()))
    }
}

fn literal_spelling(value: &Obj) -> String {
    check_layout(value, layout::SYNTAX_NODE).unwrap();
    assert_eq!(child(value, 0).unwrap().unbox(), layout::SOURCE_NONE_TAG);
    assert_eq!(
        Conversion::new()
            .project_name(&child(value, 1).unwrap())
            .unwrap(),
        Name::str(Name::anonymous(), "num")
    );
    let args = child(value, 2).unwrap();
    assert_eq!(args.try_array_view().unwrap().0, 1);
    let atom = args.array_child(0);
    check_layout(&atom, layout::SYNTAX_ATOM).unwrap();
    string(&child(&atom, 1).unwrap()).unwrap().to_owned()
}

#[test]
fn numeric_spelling_constructor_retains_raw_text_and_child_source_info() {
    let info = synthetic_info(Obj::mk_mpz(&[0, 1], false), Obj::mk_nat(9), true);
    for spelling in ["", "0_1", "0x", "1_", "not a numeral λ\0🙂", HUGE] {
        let text = Obj::mk_string(spelling);
        let value = invoke(Intrinsic::MkNumLit, &[text.clone_ref(), info.clone_ref()]);
        assert_eq!(literal_spelling(&value), spelling);
        let atom = child(&value, 2).unwrap().array_child(0);
        assert_eq!(
            child(&atom, 0).unwrap().identity_token(),
            info.identity_token()
        );
        assert_eq!(
            child(&atom, 1).unwrap().identity_token(),
            text.identity_token()
        );
        assert_eq!(string(&text).unwrap(), spelling);
    }
}

#[test]
fn numeric_inspectors_match_radix_separator_and_arbitrary_precision_semantics() {
    for (spelling, expected) in [
        ("0", Some("0")),
        ("00_1", Some("1")),
        ("1_", Some("1")),
        ("1__2", Some("12")),
        ("001_", Some("1")),
        ("0x", Some("0")),
        ("0X__", Some("0")),
        ("0b", Some("0")),
        ("0B__", Some("0")),
        ("0o", Some("0")),
        ("0O_", Some("0")),
        ("0x_f_", Some("15")),
        ("0Xff", Some("255")),
        ("0b_101_", Some("5")),
        ("0o_77_", Some("63")),
        ("18446744073709551615", Some("18446744073709551615")),
        ("18446744073709551616", Some("18446744073709551616")),
        ("0x1_0000_0000_0000_0000_", Some("18446744073709551616")),
        ("0o2000000000000000000000", Some("18446744073709551616")),
        (HUGE, Some(HUGE)),
        (
            "0x10000000000000000000000000000000000000000000000000000000000000001",
            Some(HUGE),
        ),
        ("", None),
        ("_1", None),
        ("0_", None),
        ("0_1", None),
        ("0__1", None),
        ("-1", None),
        ("+1", None),
        (" 1", None),
        ("1 ", None),
        ("1.0", None),
        ("1e2", None),
        ("0b2", None),
        ("0o8", None),
        ("0xg", None),
        ("٠1", None),
        ("１２", None),
        ("1λ", None),
        ("0x\0", None),
    ] {
        let syntax = number(spelling);
        assert_eq!(
            option_decimal(&invoke(Intrinsic::IsNatLit, &[syntax.clone_ref()])),
            expected.map(str::to_owned),
            "{spelling:?}"
        );
        assert_eq!(
            decimal(&invoke(Intrinsic::GetNat, &[syntax])),
            expected.unwrap_or("0"),
            "{spelling:?}"
        );
    }
}

#[test]
fn numeric_formatters_preserve_full_magnitudes_and_emit_canonical_decimal() {
    let info = synthetic_info(Obj::mk_nat(1), Obj::mk_nat(7), false);
    for expected in [
        "0",
        "1",
        "9223372036854775807",
        "9223372036854775808",
        "18446744073709551615",
        "18446744073709551616",
        HUGE,
    ] {
        let magnitude = BigNat::from_decimal(expected).unwrap();
        let value = crate::interpreter::nat_from_big_nat(&magnitude);
        let formatted = invoke(Intrinsic::NatReprFast, &[value.clone_ref()]);
        assert_eq!(string(&formatted).unwrap(), expected);
        let syntax = invoke(Intrinsic::MkNatLit, &[value.clone_ref(), info.clone_ref()]);
        assert_eq!(literal_spelling(&syntax), expected);
        let atom = child(&syntax, 2).unwrap().array_child(0);
        assert_eq!(
            child(&atom, 0).unwrap().identity_token(),
            info.identity_token()
        );
        assert_eq!(
            decimal(&value),
            expected,
            "formatting must leave shared input unchanged"
        );
    }
    let magnitude = BigNat::from_u64(1).shl(4096).add(&BigNat::from_u64(17));
    let value = crate::interpreter::nat_from_big_nat(&magnitude);
    assert_eq!(
        string(&invoke(Intrinsic::NatReprFast, &[value])).unwrap(),
        magnitude.to_decimal()
    );
}

#[test]
fn numeric_malformed_carriers_refuse_but_nonliteral_shapes_default_normally() {
    for syntax in [
        Obj::mk_nat(layout::SYNTAX_MISSING_TAG),
        atom("num"),
        node(Name::str(Name::anonymous(), "num"), vec![]),
        node(
            Name::str(Name::anonymous(), "num"),
            vec![atom("1"), atom("2")],
        ),
        node(
            Name::str(Name::anonymous(), "num"),
            vec![Obj::mk_nat(layout::SYNTAX_MISSING_TAG)],
        ),
        node(Name::str(Name::anonymous(), "str"), vec![atom("12")]),
    ] {
        assert_eq!(
            option_decimal(&invoke(Intrinsic::IsNatLit, &[syntax.clone_ref()])),
            None
        );
        assert_eq!(decimal(&invoke(Intrinsic::GetNat, &[syntax])), "0");
    }
    for value in [
        Obj::mk_string("123"),
        Obj::mk_mpz(&[1], true),
        Obj::mk_array(vec![]),
    ] {
        assert!(matches!(
            Intrinsic::NatReprFast.invoke("mirror:Nat.reprFast", &[value.clone_ref()]),
            Err(IntrinsicFailure::Refused(_))
        ));
        assert!(matches!(
            Intrinsic::MkNatLit.invoke(
                "mirror:Lean.Syntax.mkNatLit",
                &[value, Obj::mk_nat(layout::SOURCE_NONE_TAG)]
            ),
            Err(IntrinsicFailure::Refused(_))
        ));
    }
    for syntax in [
        Obj::mk_ctor(layout::SYNTAX_NODE.tag, vec![], &[]),
        node(
            Name::str(Name::anonymous(), "num"),
            vec![Obj::mk_ctor(
                layout::SYNTAX_ATOM.tag,
                vec![Obj::mk_nat(layout::SOURCE_NONE_TAG), Obj::mk_nat(0)],
                &[],
            )],
        ),
    ] {
        for (operation, row) in [
            (Intrinsic::IsNatLit, "mirror:Lean.Syntax.isNatLit?"),
            (Intrinsic::GetNat, "mirror:Lean.TSyntax.getNat"),
        ] {
            assert!(matches!(
                operation.invoke(row, &[syntax.clone_ref()]),
                Err(IntrinsicFailure::Refused(_))
            ));
        }
    }
    assert!(matches!(
        Intrinsic::MkNumLit.invoke(
            "mirror:Lean.Syntax.mkNumLit",
            &[
                Obj::mk_string("1"),
                Obj::mk_nat(layout::SOURCE_NONE_TAG + 1)
            ]
        ),
        Err(IntrinsicFailure::Refused(_))
    ));
}

#[test]
fn numeric_native_rows_receive_the_callers_magnitude_allowance() {
    for row in ["mirror:Lean.Syntax.isNatLit?", "mirror:Lean.TSyntax.getNat"] {
        let program = lookup::callable_program(row);
        for (spelling, allowed, complete) in [
            ("9223372036854775807", 0, true),
            ("9223372036854775808", 0, false),
            ("18446744073709551615", 7, false),
            ("18446744073709551615", 8, true),
            ("18446744073709551616", 8, false),
            ("18446744073709551616", 16, true),
            ("0xffffffffffffffffffffffffffffffff", 16, true),
            // Decimal preflight is conservatively rounded; a stop is not zero
            // or none. The same value completes with the next limb allowance.
            ("340282366920938463463374607431768211455", 16, false),
            ("340282366920938463463374607431768211455", 24, true),
        ] {
            let report = execute_function(
                &program,
                flbc::FunctionId::new(1),
                vec![number(spelling)],
                ExecutionLimits {
                    max_nat_magnitude_bytes: allowed,
                    ..ExecutionLimits::default()
                },
                None,
            );
            if complete {
                assert!(
                    matches!(report, Outcome::Complete(VmExit::Returned(_))),
                    "{row}: {spelling} {report:?}"
                );
            } else {
                assert!(
                    matches!(report, Outcome::Inconclusive(_)),
                    "{row}: {spelling} {report:?}"
                );
            }
        }
    }
    for row in ["mirror:Lean.Syntax.mkNatLit", "mirror:Nat.reprFast"] {
        let program = lookup::callable_program(row);
        let value = crate::interpreter::nat_from_big_nat(&BigNat::from_decimal(HUGE).unwrap());
        let arguments = if row == "mirror:Nat.reprFast" {
            vec![value]
        } else {
            vec![value, Obj::mk_nat(layout::SOURCE_NONE_TAG)]
        };
        assert!(matches!(
            execute_function(
                &program,
                flbc::FunctionId::new(1),
                arguments,
                ExecutionLimits {
                    max_nat_magnitude_bytes: 32,
                    ..ExecutionLimits::default()
                },
                None
            ),
            Outcome::Inconclusive(_)
        ));
    }
}

#[test]
fn numeric_arithmetic_work_is_bounded_before_large_conversion_and_recovers() {
    let text = "9".repeat(100_000);
    let syntax = number(&text);
    for (operation, row) in [
        (Intrinsic::IsNatLit, "mirror:Lean.Syntax.isNatLit?"),
        (Intrinsic::GetNat, "mirror:Lean.TSyntax.getNat"),
    ] {
        assert!(matches!(
            operation.invoke(row, &[syntax.clone_ref()]),
            Err(IntrinsicFailure::MirrorResource {
                resource: "numeric literal arithmetic work",
                ..
            })
        ));
        let program = lookup::callable_program(row);
        assert!(matches!(
            execute_function(
                &program,
                flbc::FunctionId::new(1),
                vec![syntax.clone_ref()],
                ExecutionLimits::default(),
                None
            ),
            Outcome::Inconclusive(_)
        ));
    }
    let huge = Obj::mk_mpz(&vec![u64::MAX; 10_000], false);
    for (operation, row, args) in [
        (
            Intrinsic::NatReprFast,
            "mirror:Nat.reprFast",
            vec![huge.clone_ref()],
        ),
        (
            Intrinsic::MkNatLit,
            "mirror:Lean.Syntax.mkNatLit",
            vec![huge, Obj::mk_nat(layout::SOURCE_NONE_TAG)],
        ),
    ] {
        assert!(matches!(
            operation.invoke(row, &args),
            Err(IntrinsicFailure::MirrorResource {
                resource: "numeric literal arithmetic work",
                ..
            })
        ));
    }
    // The spelling constructor performs no arithmetic or numeric validation.
    assert_eq!(
        literal_spelling(&invoke(
            Intrinsic::MkNumLit,
            &[Obj::mk_string(&text), Obj::mk_nat(layout::SOURCE_NONE_TAG)]
        )),
        text
    );
    assert_eq!(
        decimal(&invoke(Intrinsic::GetNat, &[number("0xff")])),
        "255"
    );
}

#[test]
fn numeric_native_calls_keep_cancellation_and_step_stops_outside_values() {
    for row in [
        "mirror:Lean.Syntax.mkNumLit",
        "mirror:Lean.Syntax.mkNatLit",
        "mirror:Lean.Syntax.isNatLit?",
        "mirror:Lean.TSyntax.getNat",
        "mirror:Nat.reprFast",
    ] {
        let program = lookup::callable_program(row);
        let arguments = match row {
            "mirror:Lean.Syntax.mkNumLit" => {
                vec![Obj::mk_string("42"), Obj::mk_nat(layout::SOURCE_NONE_TAG)]
            }
            "mirror:Lean.Syntax.mkNatLit" => {
                vec![Obj::mk_nat(42), Obj::mk_nat(layout::SOURCE_NONE_TAG)]
            }
            "mirror:Nat.reprFast" => vec![Obj::mk_nat(42)],
            _ => vec![number("42")],
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
                    arguments.iter().map(Obj::clone_ref).collect(),
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
                arguments,
                ExecutionLimits::default(),
                None
            ),
            Outcome::Complete(VmExit::Returned(_))
        ));
    }
}
