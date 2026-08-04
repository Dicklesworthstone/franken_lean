#![forbid(unsafe_code)]

use std::process::Command;

use fln_checker::numeric::{
    NatBudget, NatComparison, NatLimit, NatOperation, NatOutcome, NatProgress, NatRefusal,
    NatResult, NatStop, NatValue, NatValueError, REDUCE_POW_MAX_EXP, binary, binary_with, compare,
    successor,
};

fn from_u128(value: u128) -> NatValue {
    let low = value as u64;
    let high = (value >> 64) as u64;
    if high == 0 {
        NatValue::from_u64(low)
    } else {
        NatValue::from_limbs_le(vec![low, high]).expect("u128 limbs are canonical")
    }
}

fn to_u128(value: &NatValue) -> u128 {
    match value.limbs_le() {
        [] => 0,
        [low] => u128::from(*low),
        [low, high] => u128::from(*low) | (u128::from(*high) << 64),
        limbs => panic!("value has {} limbs and does not fit u128", limbs.len()),
    }
}

fn complete_value(outcome: NatOutcome<NatValue>) -> NatResult<NatValue> {
    match outcome {
        NatOutcome::Complete(result) => result,
        other => panic!("numeric operation did not complete: {other:?}"),
    }
}

fn calculate(operation: NatOperation, left: &NatValue, right: &NatValue) -> NatResult<NatValue> {
    complete_value(binary(operation, left, right, NatBudget::unlimited()))
}

fn gcd_u128(mut left: u128, mut right: u128) -> u128 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

#[test]
fn canonical_values_and_comparison_use_numeric_little_endian_order() {
    assert_eq!(
        NatValue::from_limbs_le(vec![1, 0]),
        Err(NatValueError::NonCanonical)
    );
    assert_eq!(
        NatValue::from_limbs_le(Vec::new()).expect("empty limbs are canonical zero"),
        NatValue::zero()
    );
    assert_eq!(NatValue::from_u64(0).to_u64(), Some(0));
    assert_eq!(NatValue::from_u64(9).to_u64(), Some(9));

    let two_to_64 = NatValue::from_limbs_le(vec![0, 1]).expect("canonical two-limb value");
    let max_u64 = NatValue::from_u64(u64::MAX);
    let result = match compare(&two_to_64, &max_u64, NatBudget::unlimited()) {
        NatOutcome::Complete(result) => result,
        other => panic!("comparison did not complete: {other:?}"),
    };
    assert_eq!(result.value, NatComparison::Greater);
    assert!(result.progress.steps >= 3);
}

#[test]
fn generated_u128_model_covers_every_numeric_operation() {
    const CASES: usize = 384;
    let mut state = 0x8c67_56a4_2b91_f03du64;
    for case in 0..CASES {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let left_u128 = u128::from(state & ((1u64 << 60) - 1));
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let right_u128 = u128::from(state & ((1u64 << 60) - 1));
        let left = from_u128(left_u128);
        let right = from_u128(right_u128);

        let comparison = match compare(&left, &right, NatBudget::unlimited()) {
            NatOutcome::Complete(result) => result.value,
            other => panic!("case {case} comparison did not complete: {other:?}"),
        };
        assert_eq!(
            comparison,
            match left_u128.cmp(&right_u128) {
                std::cmp::Ordering::Less => NatComparison::Less,
                std::cmp::Ordering::Equal => NatComparison::Equal,
                std::cmp::Ordering::Greater => NatComparison::Greater,
            },
            "case {case} comparison"
        );

        for (operation, expected) in [
            (NatOperation::Add, left_u128 + right_u128),
            (NatOperation::Subtract, left_u128.saturating_sub(right_u128)),
            (NatOperation::Multiply, left_u128 * right_u128),
            (
                NatOperation::Divide,
                left_u128.checked_div(right_u128).unwrap_or(0),
            ),
            (
                NatOperation::Modulo,
                if right_u128 == 0 {
                    left_u128
                } else {
                    left_u128 % right_u128
                },
            ),
            (NatOperation::Gcd, gcd_u128(left_u128, right_u128)),
            (NatOperation::BitAnd, left_u128 & right_u128),
            (NatOperation::BitOr, left_u128 | right_u128),
            (NatOperation::BitXor, left_u128 ^ right_u128),
        ] {
            assert_eq!(
                to_u128(&calculate(operation, &left, &right).value),
                expected,
                "case {case} operation {operation:?}"
            );
        }

        let shift = (case % 60) as u64;
        let shift_value = NatValue::from_u64(shift);
        assert_eq!(
            to_u128(&calculate(NatOperation::ShiftLeft, &left, &shift_value).value),
            left_u128 << shift,
            "case {case} shift left"
        );
        assert_eq!(
            to_u128(&calculate(NatOperation::ShiftRight, &left, &shift_value).value),
            left_u128 >> shift,
            "case {case} shift right"
        );

        let base_u128 = left_u128 % 100;
        let exponent_u128 = (case % 12) as u128;
        assert_eq!(
            to_u128(
                &calculate(
                    NatOperation::Power,
                    &from_u128(base_u128),
                    &from_u128(exponent_u128),
                )
                .value
            ),
            base_u128.pow(exponent_u128 as u32),
            "case {case} power"
        );
        assert_eq!(
            to_u128(
                &match successor(&left, NatBudget::unlimited()) {
                    NatOutcome::Complete(result) => result,
                    other => panic!("case {case} successor did not complete: {other:?}"),
                }
                .value
            ),
            left_u128 + 1,
            "case {case} successor"
        );
    }
}

#[test]
fn generated_full_width_u128_model_exercises_two_limb_division() {
    const CASES: usize = 512;
    let mut state = 0x59d2_07f3_a681_c4beu64;
    let mut next = || {
        state = state
            .wrapping_mul(2_862_933_555_777_941_757)
            .wrapping_add(3_037_000_493);
        state
    };

    for case in 0..CASES {
        let left_u128 = u128::from(next()) | (u128::from(next()) << 64);
        let mut right_u128 = u128::from(next()) | (u128::from(next()) << 64);
        if case % 37 == 0 {
            right_u128 = 0;
        }
        let left = from_u128(left_u128);
        let right = from_u128(right_u128);

        for (operation, expected) in [
            (NatOperation::Subtract, left_u128.saturating_sub(right_u128)),
            (
                NatOperation::Divide,
                left_u128.checked_div(right_u128).unwrap_or(0),
            ),
            (
                NatOperation::Modulo,
                left_u128.checked_rem(right_u128).unwrap_or(left_u128),
            ),
            (NatOperation::Gcd, gcd_u128(left_u128, right_u128)),
            (NatOperation::BitAnd, left_u128 & right_u128),
            (NatOperation::BitOr, left_u128 | right_u128),
            (NatOperation::BitXor, left_u128 ^ right_u128),
        ] {
            assert_eq!(
                to_u128(&calculate(operation, &left, &right).value),
                expected,
                "case {case} operation {operation:?}"
            );
        }

        if let Some(expected) = left_u128.checked_add(right_u128) {
            assert_eq!(
                to_u128(&calculate(NatOperation::Add, &left, &right).value),
                expected,
                "case {case} addition"
            );
        }
        let small = u128::from((next() & 15) + 1);
        let bounded_left = left_u128 >> 4;
        assert_eq!(
            to_u128(
                &calculate(
                    NatOperation::Multiply,
                    &from_u128(bounded_left),
                    &from_u128(small),
                )
                .value
            ),
            bounded_left * small,
            "case {case} multiplication"
        );

        let shift = next() % 128;
        assert_eq!(
            to_u128(&calculate(NatOperation::ShiftRight, &left, &NatValue::from_u64(shift),).value),
            left_u128 >> shift,
            "case {case} shift right"
        );
        let bounded_left = left_u128 >> shift;
        assert_eq!(
            to_u128(
                &calculate(
                    NatOperation::ShiftLeft,
                    &from_u128(bounded_left),
                    &NatValue::from_u64(shift),
                )
                .value
            ),
            bounded_left << shift,
            "case {case} shift left"
        );
    }
}

#[test]
fn large_limb_carry_borrow_multiplication_and_bitwise_are_exact() {
    let all_two =
        NatValue::from_limbs_le(vec![u64::MAX, u64::MAX]).expect("canonical two-limb maximum");
    assert_eq!(
        calculate(NatOperation::Add, &all_two, &NatValue::one())
            .value
            .limbs_le(),
        &[0, 0, 1]
    );
    assert_eq!(
        calculate(
            NatOperation::Subtract,
            &NatValue::from_limbs_le(vec![0, 0, 1]).expect("canonical power"),
            &NatValue::one(),
        )
        .value
        .limbs_le(),
        &[u64::MAX, u64::MAX]
    );

    let two_to_64 = NatValue::from_limbs_le(vec![0, 1]).expect("canonical power");
    assert_eq!(
        calculate(NatOperation::Multiply, &two_to_64, &two_to_64)
            .value
            .limbs_le(),
        &[0, 0, 1]
    );

    let left = NatValue::from_limbs_le(vec![0xf0f0_f0f0_f0f0_f0f0, 0xaaaa_aaaa_aaaa_aaaa])
        .expect("canonical left");
    let right = NatValue::from_limbs_le(vec![0x0ff0_0ff0_0ff0_0ff0, 0x5555_5555_5555_5555, 1])
        .expect("canonical right");
    assert_eq!(
        calculate(NatOperation::BitAnd, &left, &right)
            .value
            .limbs_le(),
        &[0x00f0_00f0_00f0_00f0, 0x0000_0000_0000_0000,][..1]
    );
    assert_eq!(
        calculate(NatOperation::BitOr, &left, &right)
            .value
            .limbs_le(),
        &[0xfff0_fff0_fff0_fff0, 0xffff_ffff_ffff_ffff, 1,]
    );
    assert_eq!(
        calculate(NatOperation::BitXor, &left, &right)
            .value
            .limbs_le(),
        &[0xff00_ff00_ff00_ff00, 0xffff_ffff_ffff_ffff, 1,]
    );
}

#[test]
fn division_remainder_gcd_and_zero_laws_hold_for_large_values() {
    let seven = NatValue::from_u64(7);
    let zero = NatValue::zero();
    assert_eq!(calculate(NatOperation::Divide, &seven, &zero).value, zero);
    assert_eq!(
        calculate(NatOperation::Modulo, &seven, &NatValue::zero()).value,
        seven
    );

    let numerator = NatValue::from_limbs_le(vec![5, 0, 1]).expect("canonical large numerator");
    let two = NatValue::from_u64(2);
    assert_eq!(
        calculate(NatOperation::Divide, &numerator, &two)
            .value
            .limbs_le(),
        &[2, 1u64 << 63]
    );
    assert_eq!(
        calculate(NatOperation::Modulo, &numerator, &two).value,
        NatValue::one()
    );

    let left = NatValue::from_limbs_le(vec![0x195a_62a1_673c_492d, 0x9f83_a002_4e11_bdc7, 3])
        .expect("canonical left factor");
    let right =
        NatValue::from_limbs_le(vec![0xd15c_a722_9180_40ab, 7]).expect("canonical right factor");
    let product = calculate(NatOperation::Multiply, &left, &right).value;
    assert_eq!(
        calculate(NatOperation::Divide, &product, &left).value,
        right
    );
    assert!(
        calculate(NatOperation::Modulo, &product, &left)
            .value
            .is_zero()
    );

    let common =
        NatValue::from_limbs_le(vec![0x8d1f_42b7_0973_c615, 11]).expect("canonical common factor");
    let twelve_common = calculate(NatOperation::Multiply, &NatValue::from_u64(12), &common).value;
    let eighteen_common = calculate(NatOperation::Multiply, &NatValue::from_u64(18), &common).value;
    let six_common = calculate(NatOperation::Multiply, &NatValue::from_u64(6), &common).value;
    assert_eq!(
        calculate(NatOperation::Gcd, &twelve_common, &eighteen_common).value,
        six_common
    );
}

#[test]
fn power_and_arbitrary_precision_shift_boundaries_are_typed_and_exact() {
    assert_eq!(
        calculate(
            NatOperation::Power,
            &NatValue::from_u64(2),
            &NatValue::from_u64(100),
        )
        .value
        .limbs_le(),
        &[0, 1u64 << 36]
    );
    assert_eq!(
        calculate(NatOperation::Power, &NatValue::zero(), &NatValue::zero(),).value,
        NatValue::one()
    );
    assert_eq!(
        calculate(
            NatOperation::Power,
            &NatValue::from_u64(1),
            &NatValue::from_u64(REDUCE_POW_MAX_EXP),
        )
        .value,
        NatValue::one()
    );
    assert_eq!(
        binary(
            NatOperation::Power,
            &NatValue::from_u64(1),
            &NatValue::from_u64(REDUCE_POW_MAX_EXP + 1),
            NatBudget::unlimited(),
        ),
        NatOutcome::Refused {
            refusal: NatRefusal::PowExponentAbovePinCap {
                cap: REDUCE_POW_MAX_EXP,
            },
            progress: NatProgress {
                steps: 3,
                materialized_limbs: 0,
            },
        }
    );

    let shifted = calculate(
        NatOperation::ShiftLeft,
        &NatValue::one(),
        &NatValue::from_u64(65),
    )
    .value;
    assert_eq!(shifted.limbs_le(), &[0, 2]);
    assert_eq!(
        calculate(NatOperation::ShiftRight, &shifted, &NatValue::from_u64(65),).value,
        NatValue::one()
    );

    let huge_count = NatValue::from_limbs_le(vec![0, 1]).expect("canonical count beyond u64");
    assert!(
        calculate(NatOperation::ShiftRight, &NatValue::one(), &huge_count,)
            .value
            .is_zero()
    );
    assert!(matches!(
        binary(
            NatOperation::ShiftLeft,
            &NatValue::one(),
            &huge_count,
            NatBudget::unlimited(),
        ),
        NatOutcome::Inconclusive(NatStop::OutputSizeOverflow {
            task: fln_checker::numeric::NatTask::Binary(NatOperation::ShiftLeft),
            ..
        })
    ));
}

#[test]
fn resource_cancellation_failure_atomicity_and_recovery_are_exact() {
    let left = NatValue::from_limbs_le(vec![
        0x5d13_c809_f2a4_6107,
        0xf229_d6a1_0305_4c8b,
        0x8fa6_1b97_275d_3181,
        9,
    ])
    .expect("canonical left");
    let right = NatValue::from_limbs_le(vec![
        0xe4b7_8305_31cb_0a41,
        0x1746_d3e9_4c80_9f2d,
        0x6411_b0a3_f950_7207,
        13,
    ])
    .expect("canonical right");
    let exact = calculate(NatOperation::Multiply, &left, &right);
    assert!(exact.progress.steps > 1);
    assert_eq!(exact.progress.materialized_limbs, 8);

    let allowed_steps = exact.progress.steps - 1;
    assert!(matches!(
        binary(
            NatOperation::Multiply,
            &left,
            &right,
            NatBudget::new(allowed_steps, u64::MAX),
        ),
        NatOutcome::Inconclusive(NatStop::Resource {
            limit: NatLimit::Steps,
            allowed,
            observed,
            progress: NatProgress { steps, .. },
            ..
        }) if allowed == allowed_steps && observed == allowed_steps + 1 && steps == allowed_steps
    ));
    assert!(matches!(
        binary(
            NatOperation::Multiply,
            &left,
            &right,
            NatBudget::new(u64::MAX, 7),
        ),
        NatOutcome::Inconclusive(NatStop::Resource {
            limit: NatLimit::MaterializedLimbs,
            allowed: 7,
            observed: 8,
            progress: NatProgress {
                materialized_limbs: 0,
                ..
            },
            ..
        })
    ));

    let mut cancellation_inside_product = false;
    for cancel_at in 1_u64..=512 {
        let mut polls = 0_u64;
        let interrupted = binary_with(
            NatOperation::Multiply,
            &left,
            &right,
            NatBudget::unlimited(),
            || {
                polls = polls.saturating_add(1);
                polls >= cancel_at
            },
        );
        if matches!(
            interrupted,
            NatOutcome::Inconclusive(NatStop::Cancelled {
                progress: NatProgress {
                    steps,
                    materialized_limbs: 8,
                },
                ..
            }) if steps > 10
        ) {
            cancellation_inside_product = true;
            break;
        }
    }
    assert!(
        cancellation_inside_product,
        "cancellation must be observable inside the multiplication loops"
    );
    assert_eq!(
        calculate(NatOperation::Multiply, &left, &right).value,
        exact.value
    );
}

fn deep_numeric_child() -> Result<(), String> {
    const LIMBS: usize = 50_000;
    let mut limbs = vec![u64::MAX; LIMBS];
    limbs[LIMBS - 1] = 1;
    let value = NatValue::from_limbs_le(limbs)
        .map_err(|error| format!("deep value was not canonical: {error:?}"))?;
    let result = match binary(
        NatOperation::BitOr,
        &value,
        &NatValue::zero(),
        NatBudget::unlimited(),
    ) {
        NatOutcome::Complete(result) => result,
        other => return Err(format!("deep operation did not complete: {other:?}")),
    };
    if result.value != value
        || result.value.limbs_le().len() != LIMBS
        || result.progress.materialized_limbs != LIMBS as u64
    {
        return Err(format!(
            "deep operation drifted: limbs={} progress={:?}",
            result.value.limbs_le().len(),
            result.progress
        ));
    }
    Ok(())
}

#[test]
fn fifty_thousand_limbs_fit_a_64k_stack() {
    const CHILD_ENV: &str = "FLN_CHECKER_NUMERIC_DEEP_CHILD";
    if std::env::var_os(CHILD_ENV).is_some() {
        let result = std::thread::Builder::new()
            .name("fln-checker-numeric-deep".to_owned())
            .stack_size(64 * 1024)
            .spawn(deep_numeric_child)
            .expect("spawn bounded-stack numeric child thread")
            .join()
            .expect("bounded-stack numeric child thread did not panic");
        result.expect("bounded-stack numeric operation");
        return;
    }

    let executable = std::env::current_exe().expect("current test executable");
    let output = Command::new(executable)
        .env(CHILD_ENV, "1")
        .args([
            "--exact",
            "fifty_thousand_limbs_fit_a_64k_stack",
            "--nocapture",
        ])
        .output()
        .expect("run bounded-stack numeric child process");
    assert!(
        output.status.success(),
        "bounded-stack numeric child failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn numeric_production_has_no_primary_or_shared_semantic_path() {
    let source = include_str!("../src/numeric.rs");
    for forbidden in [
        "fln_core::",
        "fln_kernel::",
        "fln_bignum",
        "BigNat",
        "nat_add(",
        "nat_mul(",
    ] {
        assert!(
            !source.contains(forbidden),
            "checker numeric source shares forbidden semantic path `{forbidden}`"
        );
    }
    let manifest = include_str!("../Cargo.toml");
    for forbidden in ["fln-bignum", "fln-kernel"] {
        assert!(
            !manifest.contains(forbidden),
            "checker manifest reaches forbidden numeric dependency `{forbidden}`"
        );
    }
}
