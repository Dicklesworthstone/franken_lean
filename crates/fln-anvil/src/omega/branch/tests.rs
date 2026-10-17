use super::*;

fn row(coeffs: &[i64], bound: i64) -> LinearConstraint {
    LinearConstraint {
        coeffs: coeffs.iter().copied().map(BigInt::from_i64).collect(),
        bound: BigInt::from_i64(bound),
    }
}

fn gap() -> Vec<LinearConstraint> {
    vec![
        row(&[-1, 0], 0),
        row(&[0, -1], 0),
        row(&[5, -2], 7),
        row(&[-4, 5], -5),
    ]
}

fn nonnegative_coin_gap() -> Vec<LinearConstraint> {
    vec![
        row(&[-1, 0], 0),
        row(&[0, -1], 0),
        row(&[2, 3], 1),
        row(&[-2, -3], -1),
    ]
}

fn branches(inputs: &[LinearConstraint]) -> OmegaBranchCertificate {
    let outcome = solve_with_integer_search(inputs, OmegaLimits::default());
    let OmegaOutcome::UnsatBranches { certificate, .. } = outcome else {
        panic!("expected integer branches for {inputs:?}: {outcome:?}");
    };
    check_branch_certificate(inputs, &certificate, OmegaLimits::default()).unwrap();
    let bytes = encode_branch_certificate(&certificate, OmegaLimits::default()).unwrap();
    assert_eq!(
        decode_branch_certificate(&bytes, OmegaLimits::default()).unwrap(),
        certificate
    );
    certificate
}

#[test]
fn integer_search_is_explicit_and_closes_rationally_feasible_gaps() {
    // The opt-in solver must not perturb existing linear answers or their
    // certificate bytes, deterministic work counts and witnesses.
    for linear in [
        vec![row(&[1], 0), row(&[-1], -1)],
        vec![row(&[2], -3), row(&[-3], 6)],
    ] {
        assert_eq!(
            solve_with_integer_search(&linear, OmegaLimits::default()),
            super::super::solve(&linear, OmegaLimits::default()),
        );
    }
    let inputs = gap();
    assert!(matches!(
        super::super::solve(&inputs, OmegaLimits::default()),
        OmegaOutcome::Inconclusive {
            reason: OmegaInconclusive::IntegerSearchRequired,
            ..
        }
    ));
    let certificate = branches(&inputs);
    assert!(
        certificate
            .nodes
            .iter()
            .any(|node| matches!(node, OmegaBranchNode::Split { .. }))
    );

    let inputs = nonnegative_coin_gap();
    let certificate = branches(&inputs);
    assert!(
        certificate
            .nodes
            .iter()
            .filter(|node| matches!(node, OmegaBranchNode::Split { .. }))
            .count()
            >= 2
    );
}

#[test]
fn integer_search_reconstructs_actual_solutions_after_fractional_choices() {
    for inputs in [
        vec![row(&[2, 3], 1), row(&[-2, -3], -1)],
        vec![row(&[3, 5], 1), row(&[-3, -5], -1)],
        vec![
            row(&[-1, 0], 0),
            row(&[0, -1], 0),
            row(&[5, -2], 7),
            row(&[-4, 5], -4),
        ],
    ] {
        let outcome = solve_with_integer_search(&inputs, OmegaLimits::default());
        let OmegaOutcome::Sat { witness, .. } = outcome else {
            panic!("expected a validated integer solution: {inputs:?}, {outcome:?}");
        };
        assert_eq!(
            check_witness(&inputs, &witness, OmegaLimits::default()),
            Ok(true)
        );
    }
}

#[test]
fn negative_floor_cuts_and_arbitrary_precision_translations_are_exact() {
    let negative: Vec<_> = gap()
        .into_iter()
        .map(|mut row| {
            row.coeffs[0] = row.coeffs[0].neg();
            row
        })
        .collect();
    let certificate = branches(&negative);
    assert!(certificate.nodes.iter().any(|node| matches!(node,
        OmegaBranchNode::Split { cut, .. } if cut.is_negative()
    )));
    let huge = BigInt::from_decimal("340282366920938463463374607431768211507").unwrap();
    let translated: Vec<_> = gap()
        .into_iter()
        .map(|mut row| {
            row.bound = row.bound.add(&row.coeffs[0].mul(&huge));
            row
        })
        .collect();
    let certificate = branches(&translated);
    assert!(certificate.nodes.iter().any(|node| matches!(node,
        OmegaBranchNode::Split { cut, .. } if cut > &huge
    )));
}

#[test]
fn branch_checker_rejects_context_substitution_and_malformed_trees() {
    let inputs = nonnegative_coin_gap();
    let certificate = branches(&inputs);
    let invalid = |bad: &OmegaBranchCertificate| {
        assert!(check_branch_certificate(&inputs, bad, OmegaLimits::default()).is_err());
    };
    let mut bad = certificate.clone();
    bad.version += 1;
    invalid(&bad);
    let mut bad = certificate.clone();
    bad.inputs[0].bound = BigInt::from_i64(1);
    invalid(&bad);
    let mut bad = certificate.clone();
    let OmegaBranchNode::Split { cut, .. } = bad.nodes.last_mut().unwrap() else {
        panic!()
    };
    *cut = cut.add(&BigInt::from_i64(1));
    assert_eq!(
        check_branch_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::InputMismatch)
    );
    let mut bad = certificate.clone();
    let OmegaBranchNode::Split { le, gt, .. } = bad.nodes.last_mut().unwrap() else {
        panic!()
    };
    std::mem::swap(le, gt);
    invalid(&bad);
    let mut bad = certificate.clone();
    let OmegaBranchNode::Split { variable, .. } = bad.nodes.last_mut().unwrap() else {
        panic!()
    };
    *variable = 2;
    assert_eq!(
        check_branch_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::BranchVariable(2))
    );
    let mut bad = certificate.clone();
    let OmegaBranchNode::Split { le, gt, .. } = bad.nodes.last_mut().unwrap() else {
        panic!()
    };
    *gt = *le;
    assert_eq!(
        check_branch_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::BranchShape)
    );
    let mut bad = certificate.clone();
    let root = bad.conclusion;
    let OmegaBranchNode::Split { le, .. } = bad.nodes.last_mut().unwrap() else {
        panic!()
    };
    *le = root;
    invalid(&bad);
    let mut bad = certificate.clone();
    bad.nodes.push(bad.nodes.last().unwrap().clone());
    bad.conclusion += 1;
    invalid(&bad);
    let mut bad = certificate.clone();
    let leaf = bad
        .nodes
        .iter_mut()
        .find_map(|node| match node {
            OmegaBranchNode::Leaf { certificate }
                if certificate.inputs.len() >= inputs.len() + 2 =>
            {
                Some(certificate)
            }
            _ => None,
        })
        .expect("nested branch leaf");
    let length = leaf.inputs.len();
    leaf.inputs.swap(length - 1, length - 2);
    assert_eq!(
        check_branch_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::InputMismatch)
    );
    let mut bad = certificate.clone();
    let OmegaBranchNode::Leaf { certificate: leaf } = &mut bad.nodes[0] else {
        panic!()
    };
    leaf.inputs.last_mut().unwrap().bound = BigInt::from_i64(99);
    invalid(&bad);
    let mut bad = certificate.clone();
    let OmegaBranchNode::Leaf { certificate: leaf } = &mut bad.nodes[0] else {
        panic!()
    };
    leaf.inputs.pop();
    assert_eq!(
        check_branch_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::InputMismatch)
    );
    let mut bad = certificate.clone();
    let OmegaBranchNode::Leaf { certificate: leaf } = &mut bad.nodes[0] else {
        panic!()
    };
    leaf.inputs.push(row(&[-1, 0], -100));
    assert_eq!(
        check_branch_certificate(&inputs, &bad, OmegaLimits::default()),
        Err(CertificateError::InputMismatch)
    );
    let mut bad = certificate.clone();
    let OmegaBranchNode::Leaf { certificate: leaf } = &mut bad.nodes[0] else {
        panic!()
    };
    leaf.conclusion = 0;
    invalid(&bad);
    // All failure paths are read-only and a fresh check still succeeds.
    check_branch_certificate(&inputs, &certificate, OmegaLimits::default()).unwrap();
}

#[test]
fn branch_codec_rejects_truncation_unknown_versions_tags_and_lengths() {
    let certificate = branches(&gap());
    let bytes = encode_branch_certificate(&certificate, OmegaLimits::default()).unwrap();
    for end in [0, 1, 8, 12, 16, bytes.len() / 2, bytes.len() - 1] {
        assert!(decode_branch_certificate(&bytes[..end], OmegaLimits::default()).is_err());
    }
    let mut bad = bytes.clone();
    bad.push(0);
    assert_eq!(
        decode_branch_certificate(&bad, OmegaLimits::default()),
        Err(CertificateError::Encoding("trailing bytes"))
    );
    let mut bad = bytes.clone();
    bad[8..12].copy_from_slice(&2u32.to_le_bytes());
    assert_eq!(
        decode_branch_certificate(&bad, OmegaLimits::default()),
        Err(CertificateError::UnsupportedVersion(2))
    );
    let integer_length = |value: &BigInt| 5 + 8 * value.magnitude().limbs_le().len();
    let first_node = 20
        + certificate
            .inputs
            .iter()
            .map(|row| {
                4 + row
                    .coeffs
                    .iter()
                    .chain(std::iter::once(&row.bound))
                    .map(integer_length)
                    .sum::<usize>()
            })
            .sum::<usize>();
    let mut bad = bytes.clone();
    bad[first_node] = 2;
    assert_eq!(
        decode_branch_certificate(&bad, OmegaLimits::default()),
        Err(CertificateError::Encoding("branch node tag"))
    );
    let mut bad = bytes.clone();
    bad[first_node + 1..first_node + 5].copy_from_slice(&u32::MAX.to_le_bytes());
    assert_eq!(
        decode_branch_certificate(&bad, OmegaLimits::default()),
        Err(CertificateError::Encoding("truncated"))
    );
    let mut bad = bytes.clone();
    bad[0] ^= 1;
    assert_eq!(
        decode_branch_certificate(&bad, OmegaLimits::default()),
        Err(CertificateError::Encoding("branch magic"))
    );
    assert_eq!(
        decode_branch_certificate(&bytes, OmegaLimits::default()).unwrap(),
        certificate
    );
}

#[test]
fn branch_resources_and_cancellation_are_cumulative_and_recoverable() {
    let inputs = nonnegative_coin_gap();
    let baseline = solve_with_integer_search(&inputs, OmegaLimits::default());
    let OmegaOutcome::UnsatBranches { certificate, .. } = &baseline else {
        panic!("{baseline:?}")
    };
    let rows = certificate.nodes.len()
        + certificate
            .nodes
            .iter()
            .map(|node| match node {
                OmegaBranchNode::Leaf { certificate } => certificate.steps.len(),
                OmegaBranchNode::Split { .. } => 0,
            })
            .sum::<usize>();
    assert!(matches!(
        check_branch_certificate(
            &inputs,
            certificate,
            OmegaLimits {
                max_rows: rows - 1,
                ..OmegaLimits::default()
            }
        ),
        Err(CertificateError::Inconclusive(
            OmegaInconclusive::ResourceLimit {
                resource: OmegaResource::Rows,
                ..
            }
        ))
    ));
    let leaves: Vec<_> = certificate
        .nodes
        .iter()
        .filter_map(|node| match node {
            OmegaBranchNode::Leaf { certificate } => Some(certificate),
            _ => None,
        })
        .collect();
    let mut leaf_budget = 64;
    loop {
        let limits = OmegaLimits {
            max_steps: leaf_budget,
            ..OmegaLimits::default()
        };
        if leaves
            .iter()
            .all(|leaf| check_certificate(&leaf.inputs, leaf, limits).is_ok())
        {
            break;
        }
        leaf_budget *= 2;
        assert!(leaf_budget < OmegaLimits::default().max_steps);
    }
    assert!(matches!(
        check_branch_certificate(
            &inputs,
            certificate,
            OmegaLimits {
                max_steps: leaf_budget,
                ..OmegaLimits::default()
            }
        ),
        Err(CertificateError::Inconclusive(
            OmegaInconclusive::ResourceLimit {
                resource: OmegaResource::Steps,
                ..
            }
        ))
    ));
    let bytes = encode_branch_certificate(certificate, OmegaLimits::default()).unwrap();
    assert!(matches!(
        decode_branch_certificate(
            &bytes,
            OmegaLimits {
                max_certificate_bytes: bytes.len() - 1,
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
    let mut initial_checks = 0;
    let initial = solve_with_cancel(&inputs, OmegaLimits::default(), &mut || {
        initial_checks += 1;
        false
    });
    let OmegaOutcome::Inconclusive { steps_used, .. } = initial else {
        panic!("expected initial integer gap")
    };
    assert!(matches!(
        solve_with_integer_search(
            &inputs,
            OmegaLimits {
                max_steps: steps_used + 1,
                ..OmegaLimits::default()
            }
        ),
        OmegaOutcome::Inconclusive {
            reason: OmegaInconclusive::ResourceLimit {
                resource: OmegaResource::Steps,
                ..
            },
            ..
        }
    ));
    let mut checks = 0;
    assert!(matches!(
        solve_with_integer_search_and_cancel(&inputs, OmegaLimits::default(), &mut || {
            checks += 1;
            checks > initial_checks + 10
        }),
        OmegaOutcome::Inconclusive {
            reason: OmegaInconclusive::Cancelled,
            ..
        }
    ));
    assert_eq!(
        solve_with_integer_search(&inputs, OmegaLimits::default()),
        baseline
    );
}

fn model_satisfies(rows: &[LinearConstraint], values: &[i128]) -> bool {
    rows.iter().all(|row| {
        row.coeffs
            .iter()
            .zip(values)
            .map(|(coefficient, value)| coefficient.to_i128().unwrap() * value)
            .sum::<i128>()
            <= row.bound.to_i128().unwrap()
    })
}

#[test]
fn generated_bounded_integer_systems_have_no_unknowns_and_match_exhaustive_model() {
    let mut state = 0x5343_4f50_4544_4341u64;
    let mut next = || {
        state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        ((state >> 32) % 11) as i64 - 5
    };
    let (mut sat, mut unsat, mut split) = (0, 0, 0);
    for case in 0..256 {
        let mut inputs = vec![
            row(&[1, 0], 3),
            row(&[-1, 0], 3),
            row(&[0, 1], 3),
            row(&[0, -1], 3),
        ];
        for _ in 0..4 {
            inputs.push(row(&[next(), next()], next()));
        }
        let exists = (-3..=3).any(|x| (-3..=3).any(|y| model_satisfies(&inputs, &[x, y])));
        match solve_with_integer_search(&inputs, OmegaLimits::default()) {
            OmegaOutcome::Sat { witness, .. } => {
                sat += 1;
                assert!(exists, "case {case}");
                let values: Vec<_> = witness
                    .iter()
                    .map(|value| value.to_i128().unwrap())
                    .collect();
                assert!(model_satisfies(&inputs, &values), "case {case}");
            }
            OmegaOutcome::Unsat { certificate, .. } => {
                unsat += 1;
                assert!(!exists, "case {case}");
                check_certificate(&inputs, &certificate, OmegaLimits::default()).unwrap();
            }
            OmegaOutcome::UnsatBranches { certificate, .. } => {
                split += 1;
                assert!(!exists, "case {case}");
                check_branch_certificate(&inputs, &certificate, OmegaLimits::default()).unwrap();
            }
            stopped => panic!("unexpected incomplete bounded case {case}: {inputs:?}: {stopped:?}"),
        }
    }
    assert_eq!(sat + unsat + split, 256);
    assert!(sat > 0 && unsat > 0 && split > 0);
}

#[test]
fn schedule_widths_preserve_branch_certificates_and_work_counts() {
    let inputs = nonnegative_coin_gap();
    let baseline = solve_with_integer_search(&inputs, OmegaLimits::default());
    assert!(matches!(&baseline, OmegaOutcome::UnsatBranches { .. }));
    for width in [1, 8, 32] {
        std::thread::scope(|scope| {
            let handles: Vec<_> = (0..width)
                .map(|_| scope.spawn(|| solve_with_integer_search(&inputs, OmegaLimits::default())))
                .collect();
            for handle in handles {
                assert_eq!(handle.join().unwrap(), baseline);
            }
        });
    }
}
