#![forbid(unsafe_code)]

use fln_core::expr::NatLit;
use fln_core::level::Level;
use fln_core::mode::{BuildProfileId, ContentRoot, EpochId, Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::certificate::{
    CertificateBindingV1, CertificateJudgmentV1, CertificateVerifier, ClaimedResultV1,
    ConsensusPolicyV1, DeclarationCertificateV1, DeclarationKindV1, FastPathVerificationDecision,
    FuelProfileV1, TermDagV1, TermNodeId, TermNodeV1, VerifierBudget, VerifierContext,
};

fn root(byte: u8) -> ContentRoot {
    ContentRoot::new([byte; 32])
}

fn name(component: &str) -> Name {
    Name::str(Name::anonymous(), component)
}

fn make_sample_certificate(val: u64) -> DeclarationCertificateV1 {
    let term_dag = TermDagV1 {
        nodes: vec![
            TermNodeV1::Sort {
                level: Level::zero(),
            },
            TermNodeV1::NatLiteral {
                value: NatLit::from_u64(val),
            },
        ],
    };
    let binding = CertificateBindingV1 {
        epoch: EpochId::new(100),
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
            heartbeats: 1000,
            recursion_depth: 100,
            reduction_steps: 1000,
            expanded_weight: 2000,
            allocation_bytes: 1024 * 1024,
        },
    };
    DeclarationCertificateV1::new(
        binding,
        CertificateJudgmentV1::CheckDeclaration {
            name: name("isolated_decl"),
            kind: DeclarationKindV1::Theorem,
            type_node: TermNodeId::new(0),
            value_node: Some(TermNodeId::new(1)),
        },
        ClaimedResultV1::Accepted,
        term_dag,
        Vec::new(),
        Vec::new(),
    )
    .expect("valid cert")
}

#[test]
fn verifier_execution_is_pure_and_deterministic() {
    let cert1 = make_sample_certificate(10);
    let cert2 = make_sample_certificate(20);

    let context1 = VerifierContext::matching_binding(&cert1.binding);
    let context2 = VerifierContext::matching_binding(&cert2.binding);

    let mut budget1 = VerifierBudget::new(1000);
    let mut budget2 = VerifierBudget::new(1000);

    let outcome1_a = CertificateVerifier::verify_candidate(&cert1, &context1, &mut budget1);
    let outcome2_a = CertificateVerifier::verify_candidate(&cert2, &context2, &mut budget2);

    let mut budget1_b = VerifierBudget::new(1000);
    let mut budget2_b = VerifierBudget::new(1000);

    let outcome1_b = CertificateVerifier::verify_candidate(&cert1, &context1, &mut budget1_b);
    let outcome2_b = CertificateVerifier::verify_candidate(&cert2, &context2, &mut budget2_b);

    assert_eq!(outcome1_a, outcome1_b);
    assert_eq!(outcome2_a, outcome2_b);
}

#[test]
fn verifier_does_not_depend_on_or_fabricate_admission_capabilities() {
    let cert = make_sample_certificate(42);
    let context = VerifierContext::matching_binding(&cert.binding);
    let mut budget = VerifierBudget::new(1000);

    let outcome = CertificateVerifier::verify_candidate(&cert, &context, &mut budget);
    match outcome {
        Outcome::Complete(FastPathVerificationDecision::Verified {
            certificate_digest,
            declaration_name,
            judgment,
            claimed_result,
            ..
        }) => {
            // Verifier produces observational data only, not an admission token!
            assert_eq!(certificate_digest, cert.digest().unwrap());
            assert_eq!(declaration_name, Some(name("isolated_decl")));
            assert_eq!(judgment, cert.judgment);
            assert_eq!(claimed_result, ClaimedResultV1::Accepted);
        }
        other => panic!("expected verified decision, got {other:?}"),
    }
}
