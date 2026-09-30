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
