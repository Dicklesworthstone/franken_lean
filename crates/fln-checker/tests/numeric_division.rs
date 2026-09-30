#![forbid(unsafe_code)]

use fln_checker::numeric::{
    NatBudget, NatOperation, NatOutcome, NatResult, NatStop, NatValue, binary, binary_with,
};

fn nat(mut words: Vec<u64>) -> NatValue {
    while words.last() == Some(&0) {
        words.pop();
    }
    NatValue::from_limbs_le(words).expect("trimmed words are canonical")
}

fn from_u128(value: u128) -> NatValue {
    nat(vec![value as u64, (value >> 64) as u64])
}

fn complete(outcome: NatOutcome<NatValue>) -> NatResult<NatValue> {
    match outcome {
        NatOutcome::Complete(result) => result,
        other => panic!("division must complete: {other:?}"),
    }
}

fn run(operation: NatOperation, left: &NatValue, right: &NatValue) -> NatValue {
    complete(binary(operation, left, right, NatBudget::unlimited())).value
}

fn check_identity(dividend: &NatValue, divisor: &NatValue) {
    let quotient = run(NatOperation::Divide, dividend, divisor);
    let remainder = run(NatOperation::Modulo, dividend, divisor);
    let product = run(NatOperation::Multiply, &quotient, divisor);
    assert_eq!(run(NatOperation::Add, &product, &remainder), *dividend);
    assert_eq!(
        run(NatOperation::Subtract, &remainder, divisor),
        NatValue::zero(),
    );
    assert_ne!(
        remainder, *divisor,
        "the remainder must be strictly smaller"
    );
}

fn next(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

#[test]
fn word_division_matches_full_width_u128_arithmetic() {
    let mut state = 0x7e57_913b_48a5_2301;
    for case in 0..512 {
        let dividend = (u128::from(next(&mut state)) << 64) | u128::from(next(&mut state));
        let divisors = [
            1,
            2,
            3,
            97,
            256,
            1 << 32,
            1 << 63,
            u64::MAX,
            next(&mut state) | 1,
        ];
        for divisor in divisors {
            let n = from_u128(dividend);
            let d = NatValue::from_u64(divisor);
            assert_eq!(
                run(NatOperation::Divide, &n, &d),
                from_u128(dividend / u128::from(divisor)),
                "case {case}, divisor {divisor}",
            );
            assert_eq!(
                run(NatOperation::Modulo, &n, &d),
                from_u128(dividend % u128::from(divisor)),
                "case {case}, divisor {divisor}",
            );
        }
    }
}

#[test]
fn word_division_and_modulo_fit_linear_work_and_storage_budgets() {
    let dividend = nat(vec![u64::MAX; 256]);
    let divisor = NatValue::from_u64(97);
    let quotient = complete(binary(
        NatOperation::Divide,
        &dividend,
        &divisor,
        NatBudget::new(1024, 257),
    ));
    let remainder = complete(binary(
        NatOperation::Modulo,
        &dividend,
        &divisor,
        NatBudget::new(512, 1),
    ));
    assert!(quotient.progress.steps < 600);
    assert!(remainder.progress.steps < 300);
    assert_eq!(remainder.progress.materialized_limbs, 1);
    check_identity(&dividend, &divisor);
}

#[test]
fn exact_word_modulo_does_not_materialize_a_quotient_or_remainder() {
    let dividend = nat(vec![u64::MAX; 256]);
    let result = complete(binary(
        NatOperation::Modulo,
        &dividend,
        &NatValue::from_u64(u64::MAX),
        NatBudget::new(300, 0),
    ));
    assert_eq!(result.value, NatValue::zero());
    assert_eq!(result.progress.materialized_limbs, 0);
}

#[test]
fn multiword_power_of_two_division_splits_at_exact_bit_boundaries() {
    let mut state = 0x1234_5678_9abc_def1;
    for exponent in [64, 65, 95, 127, 128, 129, 191, 192, 257, 511] {
        let mut words: Vec<u64> = (0..12).map(|_| next(&mut state)).collect();
        words[11] |= 1;
        let dividend = nat(words.clone());
        let divisor = run(
            NatOperation::ShiftLeft,
            &NatValue::one(),
            &NatValue::from_u64(exponent),
        );
        let word = exponent as usize / 64;
        let bits = exponent as u32 % 64;
        let mut low = words[..word].to_vec();
        if bits != 0 {
            low.push(words[word] & ((1_u64 << bits) - 1));
        }
        let quotient = complete(binary(
            NatOperation::Divide,
            &dividend,
            &divisor,
            NatBudget::new(100, 24),
        ));
        assert_eq!(
            quotient.value,
            run(
                NatOperation::ShiftRight,
                &dividend,
                &NatValue::from_u64(exponent)
            ),
        );
        assert_eq!(
            complete(binary(
                NatOperation::Modulo,
                &dividend,
                &divisor,
                NatBudget::new(100, (word + usize::from(bits != 0)) as u64),
            ))
            .value,
            nat(low),
        );
        check_identity(&dividend, &divisor);
    }
}

#[test]
fn a_power_of_two_high_word_does_not_hide_nonzero_low_words() {
    for divisor in [(1_u128 << 64) + 1, (1_u128 << 95) + 17, (1_u128 << 127) + 1] {
        let dividend = u128::MAX;
        let n = from_u128(dividend);
        let d = from_u128(divisor);
        assert_eq!(
            run(NatOperation::Divide, &n, &d),
            from_u128(dividend / divisor)
        );
        assert_eq!(
            run(NatOperation::Modulo, &n, &d),
            from_u128(dividend % divisor)
        );
    }
}

#[test]
fn division_fast_paths_preserve_zero_less_and_equal_cases() {
    let values = [
        NatValue::zero(),
        NatValue::one(),
        nat(vec![0, 1]),
        nat(vec![u64::MAX, 1]),
    ];
    for value in values {
        assert_eq!(
            run(NatOperation::Divide, &value, &NatValue::zero()),
            NatValue::zero()
        );
        assert_eq!(run(NatOperation::Modulo, &value, &NatValue::zero()), value);
        if !value.is_zero() {
            assert_eq!(run(NatOperation::Divide, &value, &value), NatValue::one());
            assert_eq!(run(NatOperation::Modulo, &value, &value), NatValue::zero());
            check_identity(&NatValue::zero(), &value);
        }
    }
}

#[test]
fn each_fast_path_observes_cancellation_and_work_exhaustion() {
    let dividend = nat(vec![u64::MAX; 64]);
    for divisor in [
        NatValue::from_u64(97),
        nat(vec![0; 16].into_iter().chain([8]).collect()),
    ] {
        for operation in [NatOperation::Divide, NatOperation::Modulo] {
            let mut polls = 0;
            assert!(matches!(
                binary_with(
                    operation,
                    &dividend,
                    &divisor,
                    NatBudget::unlimited(),
                    || {
                        polls += 1;
                        polls == 12
                    }
                ),
                NatOutcome::Inconclusive(NatStop::Cancelled { polls: 12, .. }),
            ));
            assert!(matches!(
                binary(operation, &dividend, &divisor, NatBudget::new(8, 1024)),
                NatOutcome::Inconclusive(NatStop::Resource { .. }),
            ));
        }
    }
}

// Deliberately bit-at-a-time: this test model does not estimate quotient words,
// normalize divisors, or call any checker arithmetic to obtain its answer.
fn binary_model(dividend: &NatValue, divisor: &NatValue) -> (NatValue, NatValue) {
    use std::cmp::Ordering;
    if divisor.is_zero() {
        return (NatValue::zero(), dividend.clone());
    }
    let words = dividend.limbs_le();
    let denominator = divisor.limbs_le();
    let mut quotient = vec![0_u64; words.len()];
    let mut remainder = vec![0_u64; denominator.len() + 1];
    for bit in (0..words.len() * 64).rev() {
        let mut carry = (words[bit / 64] >> (bit % 64)) & 1;
        for word in &mut remainder {
            let high = *word >> 63;
            *word = (*word << 1) | carry;
            carry = high;
        }
        let order = if remainder[denominator.len()] != 0 {
            Ordering::Greater
        } else {
            remainder[..denominator.len()]
                .iter()
                .rev()
                .cmp(denominator.iter().rev())
        };
        if order != Ordering::Less {
            let mut borrow = false;
            for (index, word) in remainder.iter_mut().enumerate() {
                let (partial, first) =
                    word.overflowing_sub(denominator.get(index).copied().unwrap_or(0));
                let (result, second) = partial.overflowing_sub(u64::from(borrow));
                *word = result;
                borrow = first || second;
            }
            assert!(!borrow, "the model subtracts only from a larger remainder");
            quotient[bit / 64] |= 1_u64 << (bit % 64);
        }
    }
    (nat(quotient), nat(remainder))
}

#[test]
fn normalized_multiword_division_matches_an_independent_bitwise_model() {
    let mut state = 0x68ca_9921_56bb_71ef;
    for case in 0..384 {
        let divisor_width = 2 + case % 16;
        let dividend_width = divisor_width + (case / 16) % 16;
        let mut divisor: Vec<_> = (0..divisor_width).map(|_| next(&mut state)).collect();
        // Exercise every normalization shift, including no shift and 63 bits.
        divisor[divisor_width - 1] = (next(&mut state) >> (case % 64)) | 1;
        let mut dividend: Vec<_> = (0..dividend_width).map(|_| next(&mut state)).collect();
        dividend[dividend_width - 1] |= 1;
        let n = nat(dividend);
        let d = nat(divisor);
        let (q, r) = binary_model(&n, &d);
        assert_eq!(run(NatOperation::Divide, &n, &d), q, "quotient case {case}");
        assert_eq!(
            run(NatOperation::Modulo, &n, &d),
            r,
            "remainder case {case}"
        );
        check_identity(&n, &d);
    }
}

#[test]
fn quotient_estimates_handle_add_back_and_full_word_clamping() {
    // (v * B + (v - 1)) / v has low quotient digit zero, although its top
    // three-word prefix predicts one. The subtraction must borrow and add back.
    let top = (1_u64 << 63) + 17;
    let d = nat(vec![7, 11, top]);
    let n = nat(vec![6, 18, top + 11, top]);
    assert_eq!(run(NatOperation::Divide, &n, &d), nat(vec![0, 1]));
    assert_eq!(run(NatOperation::Modulo, &n, &d), nat(vec![6, 11, top]));
    // Here a later window's leading word equals the leading divisor word.
    // The two-word estimate must be clamped, not narrowed through a u64 cast.
    let d = nat(vec![u64::MAX, 1_u64 << 63]);
    let n = nat(vec![0, u64::MAX - 1, 1_u64 << 63]);
    assert_eq!(
        run(NatOperation::Divide, &n, &d),
        NatValue::from_u64(u64::MAX)
    );
    assert_eq!(
        run(NatOperation::Modulo, &n, &d),
        nat(vec![u64::MAX, (1_u64 << 63) - 1])
    );
    check_identity(&n, &d);
}

#[test]
fn general_division_completes_with_word_scale_work_budgets() {
    let n = nat(vec![u64::MAX; 256]);
    let d = nat(vec![0x9876_5432_10fe_dcba; 16]);
    let quotient = complete(binary(
        NatOperation::Divide,
        &n,
        &d,
        NatBudget::new(12_000, 274),
    ));
    let remainder = complete(binary(
        NatOperation::Modulo,
        &n,
        &d,
        NatBudget::new(12_000, 33),
    ));
    assert_eq!(quotient.progress.materialized_limbs, 274);
    assert_eq!(remainder.progress.materialized_limbs, 33);
    let expected = binary_model(&n, &d);
    assert_eq!(quotient.value, expected.0);
    assert_eq!(remainder.value, expected.1);
}

#[test]
fn multiword_division_stops_at_each_budget_boundary_and_recovers() {
    use fln_checker::numeric::NatLimit;
    let n = nat(vec![u64::MAX, 0, 42, 19, 1]);
    let d = nat(vec![u64::MAX, 1, 1]);
    let original_n = n.clone();
    let original_d = d.clone();
    for operation in [
        NatOperation::Divide,
        NatOperation::Modulo,
        NatOperation::Gcd,
    ] {
        let expected = complete(binary(operation, &n, &d, NatBudget::unlimited()));
        assert!(expected.progress.steps > 0);
        for allowed in [0, expected.progress.steps / 2, expected.progress.steps - 1] {
            assert!(matches!(
                binary(operation, &n, &d, NatBudget::new(allowed, u64::MAX)),
                NatOutcome::Inconclusive(NatStop::Resource { limit: NatLimit::Steps, observed, .. })
                    if observed == allowed + 1
            ));
        }
        assert!(matches!(
            binary(
                operation,
                &n,
                &d,
                NatBudget::new(u64::MAX, expected.progress.materialized_limbs - 1)
            ),
            NatOutcome::Inconclusive(NatStop::Resource {
                limit: NatLimit::MaterializedLimbs,
                ..
            })
        ));
        let mut polls = 0;
        let cancelled = binary_with(operation, &n, &d, NatBudget::unlimited(), || {
            polls += 1;
            polls == 24
        });
        assert!(matches!(
            cancelled,
            NatOutcome::Inconclusive(NatStop::Cancelled { polls: 24, .. })
        ));
        assert_eq!(n, original_n);
        assert_eq!(d, original_d);
        assert_eq!(
            complete(binary(
                operation,
                &n,
                &d,
                NatBudget::new(
                    expected.progress.steps,
                    expected.progress.materialized_limbs
                )
            )),
            expected
        );
    }
}

#[test]
fn a_two_digit_overestimate_is_corrected_before_subtraction() {
    // Frozen full-width case with two corrections of the leading-word estimate.
    // The expected values were independently calculated with integer divmod.
    let n = nat(vec![
        0x5d11_0dd3_974d_7141,
        0x3b3f_410d_e523_b1de,
        0x94da_d278_bb07_f9be,
    ]);
    let d = nat(vec![0xe11e_d9d0_2a6b_0cc0, 0x9a77_cbf1_85da_2a1f]);
    assert_eq!(
        run(NatOperation::Divide, &n, &d),
        NatValue::from_u64(0xf6b2_7ff0_fbe4_5cf3)
    );
    assert_eq!(
        run(NatOperation::Modulo, &n, &d),
        nat(vec![0x4255_8d25_401b_5701, 0x78fa_45c3_d351_acc9])
    );
    assert_eq!(
        binary_model(&n, &d),
        (
            run(NatOperation::Divide, &n, &d),
            run(NatOperation::Modulo, &n, &d)
        )
    );
}

#[test]
fn normalized_division_and_add_back_can_be_cancelled_at_every_poll() {
    let top = (1_u64 << 63) + 17;
    for (n, d) in [
        (nat(vec![6, 18, top + 11, top]), nat(vec![7, 11, top])),
        (nat(vec![u64::MAX, 3, 0, 1]), nat(vec![u64::MAX, 1])),
    ] {
        for operation in [NatOperation::Divide, NatOperation::Modulo] {
            let mut total_polls = 0;
            let expected = complete(binary_with(
                operation,
                &n,
                &d,
                NatBudget::unlimited(),
                || {
                    total_polls += 1;
                    false
                },
            ));
            for cancel_at in 1..=total_polls {
                let mut polls = 0;
                assert!(matches!(
                    binary_with(operation, &n, &d, NatBudget::unlimited(), || {
                        polls += 1;
                        polls == cancel_at
                    }),
                    NatOutcome::Inconclusive(NatStop::Cancelled { polls, .. }) if polls == cancel_at
                ));
            }
            assert_eq!(
                complete(binary(operation, &n, &d, NatBudget::unlimited())),
                expected
            );
        }
    }
}

#[test]
fn division_production_does_not_share_primary_semantic_implementations() {
    let source = include_str!("../src/numeric/division.rs");
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
            "division reaches forbidden path {forbidden}"
        );
    }
}

#[test]
fn streaming_division_of_thousands_of_limbs_fits_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(64 * 1024)
        .spawn(|| {
            // For even k, (B^k - 1) / (B + 1) has alternating B-1 and zero
            // words, starting and ending with B-1; its remainder is zero.
            const WIDTH: usize = 8192;
            let n = nat(vec![u64::MAX; WIDTH]);
            let d = nat(vec![1, 1]);
            let result = complete(binary(
                NatOperation::Divide,
                &n,
                &d,
                NatBudget::new(200_000, (WIDTH + 4) as u64),
            ));
            assert_eq!(result.value.limbs_le().len(), WIDTH - 1);
            for (index, word) in result.value.limbs_le().iter().enumerate() {
                assert_eq!(*word, if index % 2 == 0 { u64::MAX } else { 0 });
            }
            let remainder = complete(binary(
                NatOperation::Modulo,
                &n,
                &d,
                NatBudget::new(200_000, 5),
            ));
            assert_eq!(remainder.value, NatValue::zero());
            assert_eq!(remainder.progress.materialized_limbs, 5);
        })
        .expect("spawn small-stack division worker")
        .join()
        .expect("small-stack division completes without recursion");
}
