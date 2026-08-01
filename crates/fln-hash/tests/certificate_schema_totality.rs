#![forbid(unsafe_code)]

use std::collections::BTreeSet;

use fln_core::expr::NatLit;
use fln_core::level::Level;
use fln_core::mode::{BuildProfileId, ContentRoot, EpochId, Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::canon::{SCHEMA_DECLARATION_CERTIFICATE, SCHEMA_REGISTRY, registered};
use fln_hash::certificate::{
    CandidateActionV1, CandidateStateV1, CertificateBindingV1, CertificateExtensionV1,
    CertificateJudgmentV1, CertificateRefusalV1, ClaimedRejectionV1, ClaimedResultV1,
    ConsensusPolicyV1, DeclarationCertificateV1, DeclarationKindV1, FuelProfileV1, NatHintResultV1,
    NatOperationV1, ReductionHintV1, TermDagV1, TermNodeId, TermNodeV1, candidate_action,
};

fn root(byte: u8) -> ContentRoot {
    ContentRoot::new([byte; 32])
}

fn name(component: &str) -> Name {
    Name::str(Name::anonymous(), component)
}

fn base_parts() -> (CertificateBindingV1, TermDagV1) {
    let term_dag = TermDagV1 {
        nodes: vec![
            TermNodeV1::Sort {
                level: Level::zero(),
            },
            TermNodeV1::NatLiteral {
                value: NatLit::from_u64(3),
            },
        ],
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
            profile_id: 7,
            heartbeats: 8,
            recursion_depth: 9,
            reduction_steps: 10,
            expanded_weight: 11,
            allocation_bytes: 12,
        },
    };
    (binding, term_dag)
}

fn certificate_with(
    judgment: CertificateJudgmentV1,
    claimed_result: ClaimedResultV1,
    hints: Vec<ReductionHintV1>,
) -> DeclarationCertificateV1 {
    let (binding, term_dag) = base_parts();
    DeclarationCertificateV1::new(
        binding,
        judgment,
        claimed_result,
        term_dag,
        hints,
        vec![CertificateExtensionV1::advisory(1, b"kept".to_vec())],
    )
    .expect("totality fixture is structurally valid")
}

fn check_declaration(kind: DeclarationKindV1) -> CertificateJudgmentV1 {
    CertificateJudgmentV1::CheckDeclaration {
        name: name("D"),
        kind,
        type_node: TermNodeId::new(0),
        value_node: Some(TermNodeId::new(1)),
    }
}

fn assert_round_trip(certificate: DeclarationCertificateV1) {
    let bytes = certificate
        .to_canonical_bytes()
        .expect("totality cell encodes");
    match DeclarationCertificateV1::from_canonical_bytes(&bytes) {
        Outcome::Complete(Ok(decoded)) => assert_eq!(decoded, certificate),
        other => panic!("totality cell did not decode: {other:?}"), // ubs:ignore — test-only fail-closed diagnostic.
    }
}

#[test]
fn durable_schema_is_registered_exactly_once() {
    let matching = SCHEMA_REGISTRY
        .iter()
        .filter(|row| row.id.name == SCHEMA_DECLARATION_CERTIFICATE.name)
        .collect::<Vec<_>>();
    assert_eq!(matching.len(), 1);
    assert_eq!(matching[0].id, SCHEMA_DECLARATION_CERTIFICATE);
    assert_eq!(
        registered(SCHEMA_DECLARATION_CERTIFICATE.name).map(|row| row.id),
        Some(SCHEMA_DECLARATION_CERTIFICATE)
    );
}

#[test]
fn every_judgment_declaration_result_and_hint_variant_round_trips() {
    for kind in [
        DeclarationKindV1::Axiom,
        DeclarationKindV1::Definition,
        DeclarationKindV1::Theorem,
        DeclarationKindV1::Opaque,
        DeclarationKindV1::Quotient,
        DeclarationKindV1::Inductive,
        DeclarationKindV1::Constructor,
        DeclarationKindV1::Recursor,
    ] {
        assert_round_trip(certificate_with(
            check_declaration(kind),
            ClaimedResultV1::Accepted,
            Vec::new(),
        ));
    }

    for judgment in [
        CertificateJudgmentV1::InferType {
            term_node: TermNodeId::new(1),
            inferred_type_node: TermNodeId::new(0),
        },
        CertificateJudgmentV1::DefinitionalEquality {
            left_node: TermNodeId::new(1),
            right_node: TermNodeId::new(1),
            type_node: Some(TermNodeId::new(0)),
        },
        CertificateJudgmentV1::WeakHeadNormalForm {
            input_node: TermNodeId::new(1),
            output_node: TermNodeId::new(1),
        },
        CertificateJudgmentV1::ValidateInductiveGroup {
            names: vec![name("I")],
            type_nodes: vec![TermNodeId::new(0)],
        },
        CertificateJudgmentV1::ValidateQuotientPackage {
            name: name("Quot"),
            type_node: TermNodeId::new(0),
        },
    ] {
        assert_round_trip(certificate_with(
            judgment,
            ClaimedResultV1::Accepted,
            Vec::new(),
        ));
    }

    for rejection in [
        ClaimedRejectionV1::IllTyped,
        ClaimedRejectionV1::DefinitionalMismatch,
        ClaimedRejectionV1::UniverseViolation,
        ClaimedRejectionV1::PositivityViolation,
        ClaimedRejectionV1::DeclarationConflict,
        ClaimedRejectionV1::UnsafeDeclaration,
    ] {
        assert_round_trip(certificate_with(
            check_declaration(DeclarationKindV1::Definition),
            ClaimedResultV1::Rejected(rejection),
            Vec::new(),
        ));
    }

    for operation in NatOperationV1::ALL {
        let result = if matches!(
            operation,
            NatOperationV1::Equal | NatOperationV1::LessEqual | NatOperationV1::LessThan
        ) {
            NatHintResultV1::Bool(true)
        } else {
            NatHintResultV1::Nat(NatLit::from_u64(2))
        };
        assert_round_trip(certificate_with(
            check_declaration(DeclarationKindV1::Definition),
            ClaimedResultV1::Accepted,
            vec![ReductionHintV1::NatOperation {
                operation,
                inputs: [NatLit::from_u64(1), NatLit::from_u64(1)],
                result,
            }],
        ));
    }
}

#[test]
fn every_schema_version_is_classified() {
    let certificate = certificate_with(
        check_declaration(DeclarationKindV1::Theorem),
        ClaimedResultV1::Accepted,
        Vec::new(),
    );
    let mut bytes = certificate
        .to_canonical_bytes()
        .expect("version fixture encodes");
    let version_at = 8 + SCHEMA_DECLARATION_CERTIFICATE.name.len();
    for seen in 0..=u16::MAX {
        bytes[version_at..version_at + 2].copy_from_slice(&seen.to_le_bytes());
        match DeclarationCertificateV1::from_canonical_bytes(&bytes) {
            Outcome::Complete(Ok(decoded)) if seen == 1 => {
                assert_eq!(decoded, certificate);
            }
            Outcome::Complete(Err(CertificateRefusalV1::UnsupportedVersion { seen: refused }))
                if seen != 1 =>
            {
                assert_eq!(refused, seen);
            }
            other => panic!("schema version {seen} was misclassified: {other:?}"), // ubs:ignore — test-only fail-closed diagnostic.
        }
    }
}

#[test]
fn every_boundary_failure_recomputes_and_internal_faults_quarantine() {
    let mut seen = BTreeSet::new();
    for state in CandidateStateV1::ALL {
        assert!(seen.insert(format!("{state:?}")));
        match state {
            CandidateStateV1::CurrentAndBound => {
                assert_eq!(candidate_action(state), CandidateActionV1::VerifyCandidate);
            }
            CandidateStateV1::InternalFault => {
                assert_eq!(
                    candidate_action(state),
                    CandidateActionV1::QuarantineAndRecomputeIndependently
                );
            }
            _ => assert_eq!(candidate_action(state), CandidateActionV1::Recompute),
        }
    }
    assert_eq!(seen.len(), CandidateStateV1::ALL.len());
}

#[test]
fn unknown_critical_extensions_are_never_declared_away() {
    let mut certificate = certificate_with(
        check_declaration(DeclarationKindV1::Definition),
        ClaimedResultV1::Accepted,
        Vec::new(),
    );
    certificate.extensions[0].critical = true;
    assert_eq!(
        certificate.to_canonical_bytes(),
        Err(CertificateRefusalV1::UnknownCriticalExtension { id: 1 })
    );
}

#[test]
fn codec_has_no_admission_dependency_or_authority_return_type() {
    let source = include_str!("../src/certificate.rs");
    let manifest = include_str!("../Cargo.toml");

    for forbidden in [
        "fln_kernel",
        "fln_env",
        "fln_checker",
        "pub fn admit",
        "pub fn check",
        "-> Verdict",
    ] {
        assert!(
            !source.contains(forbidden),
            "candidate codec crossed its authority boundary: {forbidden}"
        );
        assert!(
            !manifest.contains(forbidden),
            "hash crate acquired an authority dependency: {forbidden}"
        );
    }
}
