#![forbid(unsafe_code)]

use std::panic::{AssertUnwindSafe, catch_unwind};

use fln_core::expr::NatLit;
use fln_core::mode::{BuildProfileId, ContentRoot, EpochId, Mode, ReproducibilityProfile};
use fln_core::outcome::Outcome;
use fln_hash::canon::{DecodeBudget, SCHEMA_DECLARATION_CERTIFICATE};
use fln_hash::certificate::{
    CertificateBindingV1, CertificateJudgmentV1, CertificateRefusalV1, ClaimedResultV1,
    ConsensusPolicyV1, DeclarationCertificateV1, FuelProfileV1, TermDagV1, TermNodeId, TermNodeV1,
};

fn root(byte: u8) -> ContentRoot {
    ContentRoot::new([byte; 32])
}

fn sample_bytes() -> Vec<u8> {
    let term_dag = TermDagV1 {
        nodes: vec![TermNodeV1::NatLiteral {
            value: NatLit::from_u64(42),
        }],
    };
    let binding = CertificateBindingV1 {
        epoch: EpochId::new(1),
        mode: Mode::Sound,
        reproducibility: ReproducibilityProfile::Standard,
        build_profile: BuildProfileId::new(2),
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
            heartbeats: 2,
            recursion_depth: 3,
            reduction_steps: 4,
            expanded_weight: 5,
            allocation_bytes: 6,
        },
    };
    DeclarationCertificateV1::new(
        binding,
        CertificateJudgmentV1::InferType {
            term_node: TermNodeId::new(0),
            inferred_type_node: TermNodeId::new(0),
        },
        ClaimedResultV1::Accepted,
        term_dag,
        Vec::new(),
        Vec::new(),
    )
    .expect("fuzz seed is valid")
    .to_canonical_bytes()
    .expect("fuzz seed encodes")
}

fn assert_total(bytes: &[u8], budget: DecodeBudget) {
    let outcome = catch_unwind(AssertUnwindSafe(|| {
        DeclarationCertificateV1::from_canonical_bytes_budgeted(bytes, budget)
    }))
    .expect("arbitrary certificate input must not panic");
    match outcome {
        Outcome::Complete(Ok(certificate)) => {
            assert_eq!(
                certificate
                    .to_canonical_bytes()
                    .expect("decoded candidate remains valid"),
                bytes,
                "every accepted byte string is already canonical"
            );
        }
        Outcome::Complete(Err(_)) | Outcome::Inconclusive(_) => {}
        Outcome::InternalFault(fault) => {
            panic!("ordinary arbitrary input reached InternalFault: {fault:?}"); // ubs:ignore — test-only fail-closed diagnostic.
        }
    }
}

fn next(state: &mut u64) -> u64 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    *state
}

#[test]
fn deterministic_arbitrary_bytes_are_total_under_independent_budgets() {
    let mut state = 0x8f4d_13a9_72c6_b501;
    for _case in 0..10_000 {
        let len = (next(&mut state) % 513) as usize;
        let mut bytes = vec![0; len];
        for byte in &mut bytes {
            *byte = next(&mut state) as u8;
        }
        let input_budget = next(&mut state) % 600;
        let node_budget = next(&mut state) % 64;
        assert_total(&bytes, DecodeBudget::new(input_budget, node_budget));
    }
}

#[test]
fn every_truncation_and_single_bit_change_is_total_and_canonical_if_accepted() {
    let valid = sample_bytes();
    for end in 0..valid.len() {
        assert_total(&valid[..end], DecodeBudget::unlimited());
    }
    for byte_index in 0..valid.len() {
        for bit in 0..8 {
            let mut changed = valid.clone();
            changed[byte_index] ^= 1 << bit;
            assert_total(&changed, DecodeBudget::unlimited());
        }
    }
}

#[test]
fn input_and_produced_node_stops_are_inconclusive_not_malformed() {
    let valid = sample_bytes();
    assert!(matches!(
        DeclarationCertificateV1::from_canonical_bytes_budgeted(
            &valid,
            DecodeBudget::new(valid.len() as u64 - 1, u64::MAX),
        ),
        Outcome::Inconclusive(_)
    ));
    assert!(matches!(
        DeclarationCertificateV1::from_canonical_bytes_budgeted(
            &valid,
            DecodeBudget::new(u64::MAX, 0),
        ),
        Outcome::Inconclusive(_)
    ));
}

#[test]
fn malformed_prefix_before_a_budget_boundary_is_a_completed_refusal() {
    let bytes = b"not-a-certificate";
    assert!(matches!(
        DeclarationCertificateV1::from_canonical_bytes_budgeted(
            bytes,
            DecodeBudget::new(1024, 1024),
        ),
        Outcome::Complete(Err(_))
    ));
}

#[test]
fn a_wrong_schema_name_is_a_completed_typed_refusal() {
    let mut bytes = sample_bytes();
    let schema_name_at = 8;
    assert_eq!(
        &bytes[schema_name_at..schema_name_at + SCHEMA_DECLARATION_CERTIFICATE.name.len()],
        SCHEMA_DECLARATION_CERTIFICATE.name.as_bytes(),
    );
    bytes[schema_name_at] ^= 1;
    assert_eq!(
        DeclarationCertificateV1::from_canonical_bytes(&bytes),
        Outcome::Complete(Err(CertificateRefusalV1::SchemaNameMismatch)),
    );
}
