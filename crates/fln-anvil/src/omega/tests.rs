use super::*;

fn row(coeffs: &[i64], bound: i64) -> LinearConstraint {
    LinearConstraint {
        coeffs: coeffs.iter().map(|&n| BigInt::from_i64(n)).collect(),
        bound: BigInt::from_i64(bound),
    }
}

fn unsat(inputs: &[LinearConstraint]) -> OmegaCertificate {
    let outcome = solve(inputs, OmegaLimits::default());
    let OmegaOutcome::Unsat { certificate, .. } = outcome else {
        panic!("expected contradiction: {inputs:?}\n{outcome:?}");
    };
    let rows = check_certificate(inputs, &certificate, OmegaLimits::default()).unwrap();
    assert!(rows.last().unwrap().coeffs.iter().all(BigInt::is_zero));
    assert!(rows.last().unwrap().bound.is_negative());
    certificate
}

#[test]
fn linear_combinations_close_multivariable_and_constant_contradictions() {
    unsat(&[row(&[], -1)]);
    unsat(&[row(&[1, -1], 0), row(&[0, 1, -1], 0), row(&[-1, 0, 1], -1)]);
    unsat(&[row(&[2, -3], 4), row(&[-2, 3], -5)]);
    let cert = unsat(&[row(&[1], 100), row(&[1], 0), row(&[-1], -1)]);
    assert!(
        !cert
            .steps
            .iter()
            .any(|step| matches!(step, OmegaStep::Input { index: 0 }))
    );
}

#[test]
fn gcd_tightening_uses_integer_floor_including_negative_bounds() {
    for inputs in [
        vec![row(&[2], 1), row(&[-2], -1)],
        vec![row(&[2], -1), row(&[-1], 0)],
        vec![row(&[3, 3], 5), row(&[-1, -1], -2)],
    ] {
        let certificate = unsat(&inputs);
        assert!(
            certificate
                .steps
                .iter()
                .any(|step| matches!(step, OmegaStep::DivideGcd { .. }))
        );
    }
}

#[test]
fn integer_witnesses_reconstruct_negative_and_one_sided_bounds() {
    for inputs in [
        vec![],
        vec![row(&[], 0)],
        vec![row(&[2], -3), row(&[-3], 6)],
        vec![row(&[0, 1], -5)],
        vec![row(&[1, -1], -2), row(&[0, 1], 5), row(&[-1, 0], 0)],
    ] {
        let outcome = solve(&inputs, OmegaLimits::default());
        let OmegaOutcome::Sat { witness, .. } = outcome else {
            panic!("{inputs:?}: {outcome:?}");
        };
        assert_eq!(
            check_witness(&inputs, &witness, OmegaLimits::default()),
            Ok(true)
        );
    }
    assert_eq!(
        check_witness(
            &[row(&[1], 0)],
            &[BigInt::from_i64(1)],
            OmegaLimits::default()
        ),
        Ok(false)
    );
    assert_eq!(
        check_witness(&[row(&[1], 0)], &[], OmegaLimits::default()),
        Ok(false)
    );
}

#[test]
fn arbitrary_precision_values_are_not_limited_by_i64_or_i128() {
    let huge = BigInt::from_decimal("340282366920938463463374607431768211507").unwrap();
    let inputs = [
        LinearConstraint {
            coeffs: vec![huge.clone(), BigInt::from_i64(1)],
            bound: BigInt::zero(),
        },
        row(&[-1, 0], 0),
        row(&[0, -1], -1),
    ];
    let certificate = unsat(&inputs);
    let bytes = encode_certificate(&certificate, OmegaLimits::default()).unwrap();
    assert_eq!(
        decode_certificate(&bytes, OmegaLimits::default()).unwrap(),
        certificate
    );

    let inputs = [LinearConstraint {
        coeffs: vec![BigInt::from_i64(-1)],
        bound: huge.neg(),
    }];
    let OmegaOutcome::Sat { witness, .. } = solve(&inputs, OmegaLimits::default()) else {
        panic!("unbounded integer witness");
    };
    assert_eq!(witness, vec![huge]);
    assert_eq!(
        check_witness(&inputs, &witness, OmegaLimits::default()),
        Ok(true)
    );
}

#[test]
fn unresolved_integer_residue_is_not_reported_as_satisfiable() {
    // 2*x+3*y=1 is satisfiable, but choosing y=0 in the rational projection
    // leaves no integer x. Balanced-mod equality solving is a remaining lane.
    let inputs = [row(&[2, 3], 1), row(&[-2, -3], -1)];
    assert_eq!(
        check_witness(
            &inputs,
            &[BigInt::from_i64(-1), BigInt::from_i64(1)],
            OmegaLimits::default()
        ),
        Ok(true)
    );
    assert!(matches!(
        solve(&inputs, OmegaLimits::default()),
        OmegaOutcome::Inconclusive {
            reason: OmegaInconclusive::IntegerSearchRequired,
            ..
        }
    ));
}

#[test]
fn certificate_checker_rejects_wrong_inputs_scales_parents_and_conclusions() {
    let inputs = [row(&[1], 0), row(&[-1], -1)];
    let valid = unsat(&inputs);
    let mut bad = valid.clone();
    bad.version += 1;
    assert!(matches!(
        check_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::UnsupportedVersion(_))
    ));
    let mut bad = valid.clone();
    bad.inputs[0].bound = BigInt::from_i64(1);
    assert_eq!(
        check_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::InputMismatch)
    );
    let mut bad = valid.clone();
    if let OmegaStep::Combine { left_scale, .. } = bad.steps.last_mut().unwrap() {
        *left_scale = BigNat::zero();
    }
    assert!(matches!(
        check_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::NonPositiveScale(_))
    ));
    let mut bad = valid.clone();
    if let OmegaStep::Combine { left, .. } = bad.steps.last_mut().unwrap() {
        *left = bad.conclusion;
    }
    assert!(matches!(
        check_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::Parent { .. })
    ));
    let mut bad = valid.clone();
    if let OmegaStep::Combine { left_scale, .. } = bad.steps.last_mut().unwrap() {
        *left_scale = BigNat::from_u64(2);
    }
    assert_eq!(
        check_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::Conclusion)
    );
    let mut bad = valid.clone();
    bad.conclusion = 0;
    assert_eq!(
        check_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::Conclusion)
    );
    let bad = OmegaCertificate {
        version: OMEGA_CERTIFICATE_VERSION,
        inputs: vec![row(&[], 0)],
        steps: vec![
            OmegaStep::Input { index: 0 },
            OmegaStep::DivideGcd { source: 0 },
        ],
        conclusion: 1,
    };
    assert_eq!(
        check_certificate(&bad.inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::ZeroDivisor(1))
    );
}

#[test]
fn certificate_codec_is_canonical_bounded_and_rejects_corrupt_framing() {
    let certificate = unsat(&[row(&[2], -1), row(&[-1], 0)]);
    let bytes = encode_certificate(&certificate, OmegaLimits::default()).unwrap();
    let decoded = decode_certificate(&bytes, OmegaLimits::default()).unwrap();
    assert_eq!(decoded, certificate);
    assert_eq!(
        encode_certificate(&decoded, OmegaLimits::default()).unwrap(),
        bytes
    );
    for end in 0..bytes.len() {
        assert!(
            decode_certificate(&bytes[..end], OmegaLimits::default()).is_err(),
            "accepted prefix {end}"
        );
    }
    let mut extended = bytes.clone();
    extended.push(0);
    assert_eq!(
        decode_certificate(&extended, OmegaLimits::default()),
        Err(CertificateError::Encoding("trailing bytes"))
    );
    let mut changed = bytes.clone();
    changed[8..12].copy_from_slice(&99u32.to_le_bytes());
    assert_eq!(
        decode_certificate(&changed, OmegaLimits::default()),
        Err(CertificateError::UnsupportedVersion(99))
    );
    let mut changed = bytes.clone();
    changed[20] = 2; // First signed coefficient's sign byte.
    assert_eq!(
        decode_certificate(&changed, OmegaLimits::default()),
        Err(CertificateError::Encoding("integer sign"))
    );
    let mut changed = bytes.clone();
    changed[21..25].copy_from_slice(&u32::MAX.to_le_bytes());
    assert!(matches!(
        decode_certificate(&changed, OmegaLimits::default()),
        Err(CertificateError::Inconclusive(_))
    ));
    let tiny = OmegaLimits {
        max_certificate_bytes: bytes.len() - 1,
        ..OmegaLimits::default()
    };
    assert!(matches!(
        decode_certificate(&bytes, tiny),
        Err(CertificateError::Inconclusive(_))
    ));
    assert!(matches!(
        encode_certificate(&certificate, tiny),
        Err(CertificateError::Inconclusive(_))
    ));
}

#[test]
fn resource_and_cancellation_stops_preserve_clean_recovery() {
    let inputs = [row(&[2], -1), row(&[-1], 0)];
    let baseline = solve(&inputs, OmegaLimits::default());
    for limits in [
        OmegaLimits {
            max_steps: 0,
            ..OmegaLimits::default()
        },
        OmegaLimits {
            max_variables: 0,
            ..OmegaLimits::default()
        },
        OmegaLimits {
            max_rows: 1,
            ..OmegaLimits::default()
        },
        OmegaLimits {
            max_coefficient_limbs: 0,
            ..OmegaLimits::default()
        },
        OmegaLimits {
            max_certificate_bytes: 0,
            ..OmegaLimits::default()
        },
    ] {
        assert!(matches!(
            solve(&inputs, limits),
            OmegaOutcome::Inconclusive {
                reason: OmegaInconclusive::ResourceLimit { .. },
                ..
            }
        ));
    }
    let mut calls = 0;
    assert!(matches!(
        solve_with_cancel(&inputs, OmegaLimits::default(), &mut || {
            calls += 1;
            calls > 7
        }),
        OmegaOutcome::Inconclusive {
            reason: OmegaInconclusive::Cancelled,
            ..
        }
    ));
    let coefficient = BigInt::from_decimal("18446744073709551615").unwrap();
    let growing = [
        LinearConstraint {
            coeffs: vec![coefficient.clone(), BigInt::from_i64(1)],
            bound: BigInt::zero(),
        },
        LinearConstraint {
            coeffs: vec![BigInt::from_i64(-1), coefficient],
            bound: BigInt::zero(),
        },
        row(&[0, -1], -1),
    ];
    assert!(matches!(
        solve(
            &growing,
            OmegaLimits {
                max_coefficient_limbs: 1,
                ..OmegaLimits::default()
            }
        ),
        OmegaOutcome::Inconclusive {
            reason: OmegaInconclusive::ResourceLimit {
                resource: OmegaResource::CoefficientLimbs,
                ..
            },
            ..
        }
    ));
    unsat(&growing);
    assert_eq!(solve(&inputs, OmegaLimits::default()), baseline);
    let OmegaOutcome::Unsat { certificate, .. } = baseline else {
        panic!("baseline");
    };
    assert!(matches!(
        check_certificate(
            &inputs,
            &certificate,
            OmegaLimits {
                max_steps: 0,
                ..OmegaLimits::default()
            }
        ),
        Err(CertificateError::Inconclusive(_))
    ));
}

fn model_satisfies(rows: &[LinearConstraint], values: &[i128]) -> bool {
    rows.iter().all(|row| {
        let total: i128 = row
            .coeffs
            .iter()
            .zip(values)
            .map(|(coefficient, value)| coefficient.to_i128().unwrap() * value)
            .sum();
        total <= row.bound.to_i128().unwrap()
    })
}

#[test]
fn generated_bounded_systems_agree_with_independent_exhaustive_model() {
    let mut state = 0x7f4a_7c15_9e37_79b9u64;
    let mut next = || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((state >> 32) % 7) as i64 - 3
    };
    let (mut sat, mut unsatisfiable) = (0, 0);
    for case in 0..256 {
        let mut inputs = vec![
            row(&[1, 0], 3),
            row(&[-1, 0], 3),
            row(&[0, 1], 3),
            row(&[0, -1], 3),
        ];
        for _ in 0..4 {
            inputs.push(row(&[next(), next()], next() * 2));
        }
        let exists = (-3..=3).any(|x| (-3..=3).any(|y| model_satisfies(&inputs, &[x, y])));
        match solve(&inputs, OmegaLimits::default()) {
            OmegaOutcome::Sat { witness, .. } => {
                sat += 1;
                assert!(exists, "case {case}");
                let values: Vec<_> = witness.iter().map(|n| n.to_i128().unwrap()).collect();
                assert!(model_satisfies(&inputs, &values), "case {case}");
            }
            OmegaOutcome::Unsat { certificate, .. } => {
                unsatisfiable += 1;
                assert!(!exists, "case {case}");
                check_certificate(&inputs, &certificate, OmegaLimits::default()).unwrap();
            }
            OmegaOutcome::Inconclusive {
                reason: OmegaInconclusive::IntegerSearchRequired,
                ..
            } => {}
            stopped => panic!("unexpected stop at {case}: {stopped:?}"),
        }
    }
    assert!(sat > 0 && unsatisfiable > 0);
}

#[test]
fn schedule_widths_keep_certificates_and_consumption_identical() {
    let inputs = vec![row(&[2, -3], 4), row(&[0, 1, -1], 0), row(&[-2, 0, 3], -5)];
    let baseline = solve(&inputs, OmegaLimits::default());
    assert!(matches!(&baseline, OmegaOutcome::Unsat { .. }));
    for width in [1, 8, 32] {
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..width)
                .map(|_| scope.spawn(|| solve(&inputs, OmegaLimits::default())))
                .collect();
            for handle in handles {
                assert_eq!(handle.join().unwrap(), baseline);
            }
        });
    }
}

#[test]
fn certificate_codec_refuses_noncanonical_integers_and_unknown_steps() {
    let zero = unsat(&[row(&[0], -1)]);
    let mut bytes = encode_certificate(&zero, OmegaLimits::default()).unwrap();
    bytes[20] = 1; // The zero coefficient has a zero limb count.
    assert_eq!(
        decode_certificate(&bytes, OmegaLimits::default()),
        Err(CertificateError::Encoding("negative zero"))
    );

    let constant = unsat(&[row(&[], -1)]);
    let original = encode_certificate(&constant, OmegaLimits::default()).unwrap();
    let mut bytes = original.clone();
    bytes[25..33].fill(0); // A one-limb magnitude cannot end in a zero limb.
    assert_eq!(
        decode_certificate(&bytes, OmegaLimits::default()),
        Err(CertificateError::Encoding("noncanonical integer"))
    );
    let mut bytes = original;
    bytes[37] = 255; // First step follows the constant row and step count.
    assert_eq!(
        decode_certificate(&bytes, OmegaLimits::default()),
        Err(CertificateError::Encoding("step tag"))
    );
}

#[test]
fn certificate_scale_storage_is_bounded_even_when_the_result_is_zero() {
    // Huge multipliers can survive in a justification whose recomputed
    // coefficients and bound are all zero. Small resulting rows cannot pay
    // for those retained magnitudes.
    let magnitude = BigNat::from_limbs_le(vec![1; 128]);
    let inputs = vec![row(&[], 0), row(&[], -1)];
    let certificate = OmegaCertificate {
        version: OMEGA_CERTIFICATE_VERSION,
        inputs: inputs.clone(),
        steps: vec![
            OmegaStep::Input { index: 0 },
            OmegaStep::Combine {
                left: 0,
                right: 0,
                left_scale: magnitude.clone(),
                right_scale: magnitude,
            },
            OmegaStep::Input { index: 1 },
        ],
        conclusion: 2,
    };
    check_certificate(&inputs, &certificate, OmegaLimits::default()).unwrap();
    assert!(matches!(
        check_certificate(
            &inputs,
            &certificate,
            OmegaLimits {
                max_certificate_bytes: 512,
                ..OmegaLimits::default()
            }
        ),
        Err(CertificateError::Inconclusive(
            OmegaInconclusive::ResourceLimit {
                resource: OmegaResource::CertificateBytes,
                ..
            }
        ))
    ));
}
