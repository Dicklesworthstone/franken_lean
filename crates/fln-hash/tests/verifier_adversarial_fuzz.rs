#![forbid(unsafe_code)]

use fln_core::expr::NatLit;
use fln_core::level::Level;
use fln_core::mode::{BuildProfileId, ContentRoot, EpochId, Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::certificate::{
    CertificateBindingV1, CertificateExtensionV1, CertificateJudgmentV1, CertificateVerifier,
    ClaimedResultV1, ConsensusPolicyV1, DeclarationCertificateV1, DeclarationKindV1,
    FastPathVerificationDecision, FuelProfileV1, NatHintResultV1, NatOperationV1, ReductionHintV1,
    TermDagV1, TermNodeId, TermNodeV1, VerifierBudget, VerifierContext,
};

fn root(byte: u8) -> ContentRoot {
    ContentRoot::new([byte; 32])
}

fn name(component: &str) -> Name {
    Name::str(Name::anonymous(), component)
}

fn sample_certificate_bytes() -> Vec<u8> {
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
        binding,
        CertificateJudgmentV1::CheckDeclaration {
            name: name("fuzz_base"),
            kind: DeclarationKindV1::Theorem,
            type_node: TermNodeId::new(0),
            value_node: Some(TermNodeId::new(1)),
        },
        ClaimedResultV1::Accepted,
        term_dag,
        vec![ReductionHintV1::NatOperation {
            operation: NatOperationV1::Mul,
            inputs: [NatLit::from_u64(6), NatLit::from_u64(7)],
            result: NatHintResultV1::Nat(NatLit::from_u64(42)),
        }],
        vec![CertificateExtensionV1::advisory(1, b"ok".to_vec())],
    )
    .expect("valid cert");
    cert.to_canonical_bytes().unwrap()
}

#[test]
fn adversarial_truncation_never_panics() {
    let valid_bytes = sample_certificate_bytes();
    let context = VerifierContext::new();

    for cut_len in 0..valid_bytes.len() {
        let truncated = &valid_bytes[..cut_len];
        let mut budget = VerifierBudget::new(1000);
        let outcome = CertificateVerifier::verify_bytes(truncated, &context, &mut budget);
        match outcome {
            Outcome::Complete(FastPathVerificationDecision::Refused(..)) => {}
            Outcome::Inconclusive(..) => {}
            other => panic!("truncated prefix at {cut_len} gave unexpected {other:?}"),
        }
    }
}

#[test]
fn adversarial_single_bit_flips_never_panic() {
    let mut valid_bytes = sample_certificate_bytes();
    let context = VerifierContext::new();

    for byte_idx in 0..valid_bytes.len().min(100) {
        for bit_idx in 0..8 {
            valid_bytes[byte_idx] ^= 1 << bit_idx;
            let mut budget = VerifierBudget::new(1000);
            let outcome = CertificateVerifier::verify_bytes(&valid_bytes, &context, &mut budget);
            match outcome {
                Outcome::Complete(FastPathVerificationDecision::Refused(..))
                | Outcome::Complete(FastPathVerificationDecision::Verified { .. })
                | Outcome::Inconclusive(..) => {}
                Outcome::InternalFault(fault) => {
                    panic!(
                        "bit flip at byte {byte_idx} bit {bit_idx} produced internal fault: {fault:?}"
                    )
                }
            }
            // Restore
            valid_bytes[byte_idx] ^= 1 << bit_idx;
        }
    }
}

#[test]
fn adversarial_giant_nat_operations_handled_safely() {
    let giant_a = NatLit::from_limbs_le(vec![u64::MAX; 100]);
    let giant_b = NatLit::from_limbs_le(vec![u64::MAX; 100]);

    for op in NatOperationV1::ALL {
        let _ = fln_hash::certificate::evaluate_nat_operation(op, &giant_a, &giant_b);
    }
}
