#![forbid(unsafe_code)]

use fln_core::expr::NatLit;
use fln_core::level::Level;
use fln_core::mode::{BuildProfileId, ContentRoot, EpochId, Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_hash::certificate::{
    CertificateBindingV1, CertificateExtensionV1, CertificateJudgmentV1,
    CertificateVerificationRefusal, CertificateVerifier, ClaimedResultV1, ConsensusPolicyV1,
    DeclarationCertificateV1, DeclarationKindV1, FastPathVerificationDecision, FuelProfileV1,
    NatHintResultV1, NatOperationV1, ReductionHintV1, TermDagV1, TermNodeId, TermNodeV1,
    VerifierBudget, VerifierContext, evaluate_nat_operation,
};

fn root(byte: u8) -> ContentRoot {
    ContentRoot::new([byte; 32])
}

fn name(component: &str) -> Name {
    Name::str(Name::anonymous(), component)
}

fn sample_valid_dag() -> TermDagV1 {
    TermDagV1 {
        nodes: vec![
            TermNodeV1::Sort {
                level: Level::zero(),
            },
            TermNodeV1::Const {
                name: name("Nat"),
                levels: Vec::new(),
            },
            TermNodeV1::NatLiteral {
                value: NatLit::from_u64(42),
            },
            TermNodeV1::App {
                function: TermNodeId::new(1),
                argument: TermNodeId::new(2),
            },
        ],
    }
}

fn sample_binding(term_dag: &TermDagV1) -> CertificateBindingV1 {
    CertificateBindingV1 {
        epoch: EpochId::new(432),
        mode: Mode::Sound,
        reproducibility: ReproducibilityProfile::Certified,
        build_profile: BuildProfileId::new(17),
        consensus_policy: ConsensusPolicyV1::Release,
        environment_root: root(10),
        dependency_roots: vec![root(11), root(12)],
        declaration_root: root(13),
        term_root: term_dag.content_root(),
        kernel_build_root: root(14),
        checker_build_root: root(15),
        policy_root: root(16),
        engine_id: "fln-kernel-k1".to_owned(),
        engine_version: 1,
        fuel: FuelProfileV1 {
            profile_id: 23,
            heartbeats: 200_000,
            recursion_depth: 512,
            reduction_steps: 1_000_000,
            expanded_weight: 2_000_000,
            allocation_bytes: 64 * 1024 * 1024,
        },
    }
}

fn sample_certificate() -> DeclarationCertificateV1 {
    let term_dag = sample_valid_dag();
    let binding = sample_binding(&term_dag);
    DeclarationCertificateV1::new(
        binding,
        CertificateJudgmentV1::CheckDeclaration {
            name: name("my_theorem"),
            kind: DeclarationKindV1::Theorem,
            type_node: TermNodeId::new(0),
            value_node: Some(TermNodeId::new(3)),
        },
        ClaimedResultV1::Accepted,
        term_dag,
        vec![
            ReductionHintV1::Unfold {
                declaration: name("Nat.rec"),
            },
            ReductionHintV1::NatOperation {
                operation: NatOperationV1::Add,
                inputs: [NatLit::from_u64(10), NatLit::from_u64(32)],
                result: NatHintResultV1::Nat(NatLit::from_u64(42)),
            },
        ],
        vec![CertificateExtensionV1::advisory(
            1,
            b"advisory_payload".to_vec(),
        )],
    )
    .expect("valid certificate")
}

#[test]
fn valid_certificate_passes_fast_path_verification() {
    let cert = sample_certificate();
    let context = VerifierContext::matching_binding(&cert.binding);
    let mut budget = VerifierBudget::new(10_000);

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Verified {
            certificate_digest,
            declaration_name,
            judgment,
            claimed_result,
            steps_consumed,
        }) => {
            assert_eq!(certificate_digest, cert.digest().unwrap());
            assert_eq!(declaration_name, Some(name("my_theorem")));
            assert_eq!(judgment, cert.judgment);
            assert_eq!(claimed_result, ClaimedResultV1::Accepted);
            assert!(steps_consumed > 0);
        }
        other => panic!("expected verified fast path, got {other:?}"),
    }
}

#[test]
fn valid_certificate_bytes_round_trip_and_verify() {
    let cert = sample_certificate();
    let bytes = cert.to_canonical_bytes().expect("canonical bytes");
    let context = VerifierContext::matching_binding(&cert.binding);
    let mut budget = VerifierBudget::new(10_000);

    let outcome = CertificateVerifier::verify_bytes(&bytes, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Verified {
            certificate_digest, ..
        }) => {
            assert_eq!(certificate_digest, cert.digest().unwrap());
        }
        other => panic!("expected verified fast path from bytes, got {other:?}"),
    }
}

#[test]
fn stale_epoch_is_refused() {
    let cert = sample_certificate();
    let context = VerifierContext::matching_binding(&cert.binding).with_epoch(EpochId::new(999));
    let mut budget = VerifierBudget::new(10_000);

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Refused(
            CertificateVerificationRefusal::StaleEpoch { expected, seen },
        )) => {
            assert_eq!(expected, EpochId::new(999));
            assert_eq!(seen, cert.binding.epoch);
        }
        other => panic!("expected StaleEpoch refusal, got {other:?}"),
    }
}

#[test]
fn mode_mismatch_is_refused() {
    let cert = sample_certificate();
    let context = VerifierContext::matching_binding(&cert.binding).with_mode(Mode::Faithful);
    let mut budget = VerifierBudget::new(10_000);

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Refused(
            CertificateVerificationRefusal::ModeMismatch { expected, seen },
        )) => {
            assert_eq!(expected, Mode::Faithful);
            assert_eq!(seen, cert.binding.mode);
        }
        other => panic!("expected ModeMismatch refusal, got {other:?}"),
    }
}

#[test]
fn environment_root_mismatch_is_refused() {
    let cert = sample_certificate();
    let context = VerifierContext::matching_binding(&cert.binding).with_environment_root(root(255));
    let mut budget = VerifierBudget::new(10_000);

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Refused(
            CertificateVerificationRefusal::EnvironmentRootMismatch { expected, seen },
        )) => {
            assert_eq!(expected, root(255));
            assert_eq!(seen, cert.binding.environment_root);
        }
        other => panic!("expected EnvironmentRootMismatch refusal, got {other:?}"),
    }
}

#[test]
fn declaration_root_mismatch_is_refused() {
    let cert = sample_certificate();
    let context = VerifierContext::matching_binding(&cert.binding).with_declaration_root(root(200));
    let mut budget = VerifierBudget::new(10_000);

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Refused(
            CertificateVerificationRefusal::DeclarationRootMismatch { expected, seen },
        )) => {
            assert_eq!(expected, root(200));
            assert_eq!(seen, cert.binding.declaration_root);
        }
        other => panic!("expected DeclarationRootMismatch refusal, got {other:?}"),
    }
}

#[test]
fn term_root_mismatch_is_refused() {
    let term_dag = sample_valid_dag();
    let mut binding = sample_binding(&term_dag);
    binding.term_root = root(99); // Tamper term root in binding
    let cert = DeclarationCertificateV1 {
        binding,
        judgment: CertificateJudgmentV1::CheckDeclaration {
            name: name("thm"),
            kind: DeclarationKindV1::Theorem,
            type_node: TermNodeId::new(0),
            value_node: None,
        },
        claimed_result: ClaimedResultV1::Accepted,
        term_dag,
        reduction_hints: Vec::new(),
        extensions: Vec::new(),
    };
    let context = VerifierContext::matching_binding(&cert.binding);
    let mut budget = VerifierBudget::new(10_000);

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Refused(
            CertificateVerificationRefusal::TermRootMismatch { expected, .. },
        )) => {
            assert_eq!(expected, root(99));
        }
        other => panic!("expected TermRootMismatch refusal, got {other:?}"),
    }
}

#[test]
fn tampered_nat_reduction_hint_is_refused() {
    let term_dag = sample_valid_dag();
    let binding = sample_binding(&term_dag);
    let cert = DeclarationCertificateV1::new(
        binding,
        CertificateJudgmentV1::CheckDeclaration {
            name: name("bad_hint"),
            kind: DeclarationKindV1::Theorem,
            type_node: TermNodeId::new(0),
            value_node: None,
        },
        ClaimedResultV1::Accepted,
        term_dag,
        vec![ReductionHintV1::NatOperation {
            operation: NatOperationV1::Add,
            inputs: [NatLit::from_u64(10), NatLit::from_u64(20)],
            result: NatHintResultV1::Nat(NatLit::from_u64(999)), // 10 + 20 != 999!
        }],
        Vec::new(),
    )
    .expect("valid candidate structure");

    let context = VerifierContext::matching_binding(&cert.binding);
    let mut budget = VerifierBudget::new(10_000);

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Refused(
            CertificateVerificationRefusal::InvalidReductionHint { hint_index, .. },
        )) => {
            assert_eq!(hint_index, 0);
        }
        other => panic!("expected InvalidReductionHint refusal, got {other:?}"),
    }
}

#[test]
fn all_fifteen_nat_operations_verify_correctly_under_model() {
    let pairs = [
        (NatLit::from_u64(0), NatLit::from_u64(0)),
        (NatLit::from_u64(10), NatLit::from_u64(3)),
        (NatLit::from_u64(100), NatLit::from_u64(25)),
        (NatLit::from_u64(1 << 30), NatLit::from_u64(15)),
    ];

    for op in NatOperationV1::ALL {
        for (a, b) in &pairs {
            let res = evaluate_nat_operation(op, a, b);
            assert!(res.is_some(), "operation {op:?} on {a:?}, {b:?} succeeded");
        }
    }
}

#[test]
fn budget_exhaustion_is_inconclusive() {
    let cert = sample_certificate();
    let context = VerifierContext::matching_binding(&cert.binding);
    let mut tight_budget = VerifierBudget::new(2); // Only 2 steps!

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut tight_budget);
    match outcome {
        Outcome::Inconclusive(inconclusive) => {
            assert!(matches!(
                inconclusive.cause,
                InconclusiveCause::ResourceExhausted { .. }
            ));
        }
        other => panic!("expected Inconclusive on budget exhaustion, got {other:?}"),
    }
}

#[test]
fn cooperative_cancellation_is_inconclusive() {
    let cert = sample_certificate();
    let context = VerifierContext::matching_binding(&cert.binding);
    let mut budget = VerifierBudget::new(10_000);
    budget.cancel();

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Inconclusive(inconclusive) => {
            assert!(matches!(
                inconclusive.cause,
                InconclusiveCause::Cancelled { .. }
            ));
        }
        other => panic!("expected Inconclusive on cancellation, got {other:?}"),
    }
}

#[test]
fn disallowed_advisory_extensions_are_refused() {
    let cert = sample_certificate(); // contains advisory extension id 1
    let context =
        VerifierContext::matching_binding(&cert.binding).with_allow_advisory_extensions(false);
    let mut budget = VerifierBudget::new(10_000);

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Refused(
            CertificateVerificationRefusal::AdvisoryExtensionsDisallowed { extension_ids },
        )) => {
            assert_eq!(extension_ids, vec![1]);
        }
        other => panic!("expected AdvisoryExtensionsDisallowed refusal, got {other:?}"),
    }
}
