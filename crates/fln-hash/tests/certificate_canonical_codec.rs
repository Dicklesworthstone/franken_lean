#![forbid(unsafe_code)]

use fln_core::expr::NatLit;
use fln_core::level::Level;
use fln_core::mode::{BuildProfileId, ContentRoot, EpochId, Mode, ReproducibilityProfile};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::certificate::{
    CertificateBindingV1, CertificateExtensionV1, CertificateJudgmentV1, CertificateRefusalV1,
    CertificateRuleV1, ClaimedResultV1, ConsensusPolicyV1, DeclarationCertificateV1,
    DeclarationKindV1, FuelProfileV1, ReductionHintV1, TermDagV1, TermNodeId, TermNodeV1,
};

fn root(byte: u8) -> ContentRoot {
    ContentRoot::new([byte; 32])
}

fn name(component: &str) -> Name {
    Name::str(Name::anonymous(), component)
}

fn sample_certificate() -> DeclarationCertificateV1 {
    let term_dag = TermDagV1 {
        nodes: vec![
            TermNodeV1::Sort {
                level: Level::zero(),
            },
            TermNodeV1::Const {
                name: name("Nat"),
                levels: Vec::new(),
            },
            TermNodeV1::NatLiteral {
                value: NatLit::from_u64(7),
            },
            TermNodeV1::App {
                function: TermNodeId::new(1),
                argument: TermNodeId::new(2),
            },
        ],
    };
    let binding = CertificateBindingV1 {
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
    };
    DeclarationCertificateV1::new(
        binding,
        CertificateJudgmentV1::CheckDeclaration {
            name: name("sample"),
            kind: DeclarationKindV1::Theorem,
            type_node: TermNodeId::new(0),
            value_node: Some(TermNodeId::new(3)),
        },
        ClaimedResultV1::Accepted,
        term_dag,
        vec![ReductionHintV1::Unfold {
            declaration: name("Nat.rec"),
        }],
        vec![
            CertificateExtensionV1::advisory(10, b"alpha".to_vec()),
            CertificateExtensionV1::advisory(20, b"beta".to_vec()),
        ],
    )
    .expect("sample certificate is structurally valid")
}

fn decode_certificate(bytes: &[u8]) -> DeclarationCertificateV1 {
    match DeclarationCertificateV1::from_canonical_bytes(bytes) {
        Outcome::Complete(Ok(certificate)) => certificate,
        other => panic!("canonical sample did not decode: {other:?}"), // ubs:ignore — test-only fail-closed diagnostic.
    }
}

#[test]
fn canonical_round_trip_is_byte_exact_and_digest_stable() {
    let certificate = sample_certificate();
    let first = certificate
        .to_canonical_bytes()
        .expect("valid certificate encodes");
    let decoded = decode_certificate(&first);
    let second = decoded
        .to_canonical_bytes()
        .expect("decoded certificate re-encodes");

    assert_eq!(decoded, certificate);
    assert_eq!(second, first);
    assert_eq!(
        decoded.digest().expect("decoded digest"),
        certificate.digest().expect("source digest")
    );
}

#[test]
fn order_claims_are_enforced_instead_of_normalized_silently() {
    let mut dependency_permutation = sample_certificate();
    dependency_permutation.binding.dependency_roots.reverse();
    assert_eq!(
        dependency_permutation.to_canonical_bytes(),
        Err(CertificateRefusalV1::InvalidStructure {
            rule: CertificateRuleV1::DependencyRootsNotStrictlySorted,
            index: 0,
        })
    );

    let mut extension_permutation = sample_certificate();
    extension_permutation.extensions.reverse();
    assert_eq!(
        extension_permutation.to_canonical_bytes(),
        Err(CertificateRefusalV1::InvalidStructure {
            rule: CertificateRuleV1::ExtensionsNotStrictlySorted,
            index: 0,
        })
    );
}

#[test]
fn topological_edges_and_term_root_binding_are_checked() {
    let mut forward_edge = sample_certificate();
    forward_edge.term_dag.nodes[1] = TermNodeV1::App {
        function: TermNodeId::new(0),
        argument: TermNodeId::new(2),
    };
    assert!(matches!(
        forward_edge.to_canonical_bytes(),
        Err(CertificateRefusalV1::InvalidStructure {
            rule: CertificateRuleV1::DagReferenceNotBackward,
            index: 1,
        })
    ));

    let mut wrong_root = sample_certificate();
    wrong_root.binding.term_root = root(99);
    assert_eq!(
        wrong_root.to_canonical_bytes(),
        Err(CertificateRefusalV1::InvalidStructure {
            rule: CertificateRuleV1::TermRootMismatch,
            index: 0,
        })
    );
}

#[test]
fn productive_1_8_32_thread_encodes_are_schedule_independent() {
    let certificate = sample_certificate();
    let jobs = 256usize;
    let expected = (0..jobs)
        .map(|_| {
            (
                certificate
                    .to_canonical_bytes()
                    .expect("single-thread encode"),
                certificate.digest().expect("single-thread digest"),
            )
        })
        .collect::<Vec<_>>();

    for worker_count in [1usize, 8, 32] {
        let actual = std::thread::scope(|scope| {
            let mut handles = Vec::new();
            for worker in 0..worker_count {
                let certificate = &certificate;
                handles.push(scope.spawn(move || {
                    let mut rows = Vec::new();
                    for job in (worker..jobs).step_by(worker_count) {
                        rows.push((
                            job,
                            certificate.to_canonical_bytes().expect("parallel encode"),
                            certificate.digest().expect("parallel digest"),
                        ));
                    }
                    assert!(!rows.is_empty(), "every worker must do productive work");
                    rows
                }));
            }
            let mut rows = Vec::new();
            for handle in handles {
                rows.extend(handle.join().expect("codec worker did not panic"));
            }
            rows.sort_by_key(|(job, _, _)| *job);
            rows.into_iter()
                .map(|(_, bytes, digest)| (bytes, digest))
                .collect::<Vec<_>>()
        });
        assert_eq!(actual, expected, "worker_count={worker_count}");
    }
}
