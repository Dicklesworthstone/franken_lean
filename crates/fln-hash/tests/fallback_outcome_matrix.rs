#![forbid(unsafe_code)]

use fln_core::expr::NatLit;
use fln_core::level::Level;
use fln_core::mode::{BuildProfileId, ContentRoot, EpochId, Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_hash::certificate::{
    CertificateBindingV1, CertificateJudgmentV1, ClaimedResultV1, ConsensusPolicyV1,
    DeclarationCertificateV1, DeclarationKindV1, FallbackPolicy, FuelProfileV1,
    GovernedRecomputeVerifier, GovernedVerificationOutcome, NatHintResultV1, NatOperationV1,
    ReductionHintV1, TermDagV1, TermNodeId, TermNodeV1, VerifierBudget, VerifierContext,
};

fn root(byte: u8) -> ContentRoot {
    ContentRoot::new([byte; 32])
}

fn name(component: &str) -> Name {
    Name::str(Name::anonymous(), component)
}

fn valid_cert_bytes() -> (Vec<u8>, VerifierContext) {
    let term_dag = TermDagV1 {
        nodes: vec![
            TermNodeV1::Sort {
                level: Level::zero(),
            },
            TermNodeV1::NatLiteral {
                value: NatLit::from_u64(10),
            },
        ],
    };
    let binding = CertificateBindingV1 {
        epoch: EpochId::new(1),
        mode: Mode::Sound,
        reproducibility: ReproducibilityProfile::Standard,
        build_profile: BuildProfileId::new(1),
        consensus_policy: ConsensusPolicyV1::Standard,
        environment_root: root(1),
        dependency_roots: vec![root(2)],
        declaration_root: root(3),
        term_root: term_dag.content_root(),
        kernel_build_root: root(4),
        checker_build_root: root(5),
        policy_root: root(6),
        engine_id: "fln-kernel-k1".to_owned(),
        engine_version: 1,
        fuel: FuelProfileV1 {
            profile_id: 1,
            heartbeats: 100,
            recursion_depth: 10,
            reduction_steps: 100,
            expanded_weight: 100,
            allocation_bytes: 1024,
        },
    };
    let cert = DeclarationCertificateV1::new(
        binding.clone(),
        CertificateJudgmentV1::CheckDeclaration {
            name: name("matrix_test"),
            kind: DeclarationKindV1::Theorem,
            type_node: TermNodeId::new(0),
            value_node: Some(TermNodeId::new(1)),
        },
        ClaimedResultV1::Accepted,
        term_dag,
        Vec::new(),
        Vec::new(),
    )
    .expect("valid cert");
    let bytes = cert.to_canonical_bytes().unwrap();
    let context = VerifierContext::matching_binding(&binding);
    (bytes, context)
}

fn tampered_cert_bytes() -> (Vec<u8>, VerifierContext) {
    let term_dag = TermDagV1 {
        nodes: vec![
            TermNodeV1::Sort {
                level: Level::zero(),
            },
            TermNodeV1::NatLiteral {
                value: NatLit::from_u64(10),
            },
        ],
    };
    let binding = CertificateBindingV1 {
        epoch: EpochId::new(1),
        mode: Mode::Sound,
        reproducibility: ReproducibilityProfile::Standard,
        build_profile: BuildProfileId::new(1),
        consensus_policy: ConsensusPolicyV1::Standard,
        environment_root: root(1),
        dependency_roots: vec![root(2)],
        declaration_root: root(3),
        term_root: term_dag.content_root(),
        kernel_build_root: root(4),
        checker_build_root: root(5),
        policy_root: root(6),
        engine_id: "fln-kernel-k1".to_owned(),
        engine_version: 1,
        fuel: FuelProfileV1 {
            profile_id: 1,
            heartbeats: 100,
            recursion_depth: 10,
            reduction_steps: 100,
            expanded_weight: 100,
            allocation_bytes: 1024,
        },
    };
    let cert = DeclarationCertificateV1::new(
        binding.clone(),
        CertificateJudgmentV1::CheckDeclaration {
            name: name("tampered"),
            kind: DeclarationKindV1::Theorem,
            type_node: TermNodeId::new(0),
            value_node: Some(TermNodeId::new(1)),
        },
        ClaimedResultV1::Accepted,
        term_dag,
        vec![ReductionHintV1::NatOperation {
            operation: NatOperationV1::Add,
            inputs: [NatLit::from_u64(1), NatLit::from_u64(1)],
            result: NatHintResultV1::Nat(NatLit::from_u64(999)), // Tampered 1 + 1 != 999
        }],
        Vec::new(),
    )
    .expect("valid struct");
    let bytes = cert.to_canonical_bytes().unwrap();
    let context = VerifierContext::matching_binding(&binding);
    (bytes, context)
}

#[test]
fn matrix_valid_cert_fast_path() {
    let (bytes, context) = valid_cert_bytes();
    let mut budget = VerifierBudget::new(1000);

    let outcome: Outcome<GovernedVerificationOutcome<&str, &str>> =
        GovernedRecomputeVerifier::verify_and_govern(
            &bytes,
            &context,
            &mut budget,
            FallbackPolicy::StrictCertificateOnly,
            |_name, _budget| panic!("should not recompute on valid fast path"),
        );

    match outcome {
        Outcome::Complete(GovernedVerificationOutcome::VerifiedFastPath {
            declaration_name,
            ..
        }) => {
            assert_eq!(declaration_name, Some(name("matrix_test")));
        }
        other => panic!("expected VerifiedFastPath, got {other:?}"),
    }
}

#[test]
fn matrix_tampered_cert_strict_no_fallback() {
    let (bytes, context) = tampered_cert_bytes();
    let mut budget = VerifierBudget::new(1000);

    let outcome: Outcome<GovernedVerificationOutcome<&str, &str>> =
        GovernedRecomputeVerifier::verify_and_govern(
            &bytes,
            &context,
            &mut budget,
            FallbackPolicy::StrictCertificateOnly,
            |_name, _budget| panic!("should not recompute under strict policy"),
        );

    match outcome {
        Outcome::Complete(GovernedVerificationOutcome::RefusedNoFallback { .. }) => {}
        other => panic!("expected RefusedNoFallback, got {other:?}"),
    }
}

#[test]
fn matrix_tampered_cert_recomputed_success() {
    let (bytes, context) = tampered_cert_bytes();
    let mut budget = VerifierBudget::new(1000);

    let outcome: Outcome<GovernedVerificationOutcome<&str, &str>> =
        GovernedRecomputeVerifier::verify_and_govern(
            &bytes,
            &context,
            &mut budget,
            FallbackPolicy::RecomputeIfRefused {
                recomputation_budget: 5000,
            },
            |_name, b| {
                assert_eq!(b, 5000);
                Outcome::Complete(Ok("admitted_by_recompute"))
            },
        );

    match outcome {
        Outcome::Complete(GovernedVerificationOutcome::RecomputedFallback { verdict, .. }) => {
            assert_eq!(verdict, "admitted_by_recompute");
        }
        other => panic!("expected RecomputedFallback, got {other:?}"),
    }
}

#[test]
fn matrix_tampered_cert_recomputation_fails() {
    let (bytes, context) = tampered_cert_bytes();
    let mut budget = VerifierBudget::new(1000);

    let outcome: Outcome<GovernedVerificationOutcome<&str, &str>> =
        GovernedRecomputeVerifier::verify_and_govern(
            &bytes,
            &context,
            &mut budget,
            FallbackPolicy::RecomputeIfRefused {
                recomputation_budget: 5000,
            },
            |_name, _b| Outcome::Complete(Err("type_error_in_body")),
        );

    match outcome {
        Outcome::Complete(GovernedVerificationOutcome::RecomputationFailed {
            recomputation_error,
            ..
        }) => {
            assert_eq!(recomputation_error, "type_error_in_body");
        }
        other => panic!("expected RecomputationFailed, got {other:?}"),
    }
}

#[test]
fn matrix_consensus_cross_check_verified() {
    let (bytes, context) = valid_cert_bytes();
    let mut budget = VerifierBudget::new(1000);

    let outcome: Outcome<GovernedVerificationOutcome<&str, &str>> =
        GovernedRecomputeVerifier::verify_and_govern(
            &bytes,
            &context,
            &mut budget,
            FallbackPolicy::ConsensusCrossCheck {
                recomputation_budget: 2000,
            },
            |name_opt, _b| {
                assert_eq!(*name_opt, Some(name("matrix_test")));
                Outcome::Complete(Ok("admitted_in_consensus"))
            },
        );

    match outcome {
        Outcome::Complete(GovernedVerificationOutcome::ConsensusVerified { verdict, .. }) => {
            assert_eq!(verdict, "admitted_in_consensus");
        }
        other => panic!("expected ConsensusVerified, got {other:?}"),
    }
}

#[test]
fn matrix_consensus_cross_check_divergence() {
    let (bytes, context) = valid_cert_bytes();
    let mut budget = VerifierBudget::new(1000);

    let outcome: Outcome<GovernedVerificationOutcome<&str, &str>> =
        GovernedRecomputeVerifier::verify_and_govern(
            &bytes,
            &context,
            &mut budget,
            FallbackPolicy::ConsensusCrossCheck {
                recomputation_budget: 2000,
            },
            |_name, _b| Outcome::Complete(Err("recomputation_rejected")),
        );

    match outcome {
        Outcome::Complete(GovernedVerificationOutcome::ConsensusDivergence {
            recomputation_error,
            ..
        }) => {
            assert_eq!(recomputation_error, "recomputation_rejected");
        }
        other => panic!("expected ConsensusDivergence, got {other:?}"),
    }
}

#[test]
fn matrix_recomputation_inconclusive_is_propagated() {
    let (bytes, context) = tampered_cert_bytes();
    let mut budget = VerifierBudget::new(1000);

    let outcome: Outcome<GovernedVerificationOutcome<&str, &str>> =
        GovernedRecomputeVerifier::verify_and_govern(
            &bytes,
            &context,
            &mut budget,
            FallbackPolicy::RecomputeIfRefused {
                recomputation_budget: 5000,
            },
            |_name, _b| {
                Outcome::Inconclusive(fln_core::outcome::Inconclusive::cancelled(
                    "recomputation interrupted",
                ))
            },
        );

    match outcome {
        Outcome::Inconclusive(inconclusive) => {
            assert!(matches!(
                inconclusive.cause,
                InconclusiveCause::Cancelled { .. }
            ));
        }
        other => panic!("expected Inconclusive propagation, got {other:?}"),
    }
}
