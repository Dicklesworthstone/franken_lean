//! `no_mock_attestation` — the named suite for td9's sixth campaign framework:
//! no-mock evidence attestation (`fln_conformance::campaign`'s
//! `NoMockAttestation`, `BoundaryKind`, `ClosureLevel`).
//!
//! # The laws proven here
//!
//! The closure law (§18 verbatim: a mock may support a unit test but may not close
//! an L-level, PG gate, or public claim — the refusal names the boundary), the
//! evidence law (a `Real*` boundary without evidence is a label, not an
//! attestation — refused at construction, which is the mock-substitution
//! self-mutant made inexpressible), the binding law (the attestation's digest
//! matches the artifact's bytes or the attestation describes a different run and
//! is refused), the blank-field law, the NDJSON artifact laws, and the real
//! controlled target: an attestation over a genuinely committed evidence artifact
//! verifies, and the same attestation over one altered byte is refused.

#![forbid(unsafe_code)]

use std::fs;
use std::path::PathBuf;

use fln_conformance::campaign::{
    ATTESTATION_SCHEMA, AttestationError, BoundaryAttestation, BoundaryKind, ClosureLevel,
    NoMockAttestation,
};

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

fn real(boundary: &str, evidence: &str) -> BoundaryAttestation {
    BoundaryAttestation {
        boundary: boundary.to_string(),
        kind: BoundaryKind::RealFilesystem,
        evidence: evidence.to_string(),
    }
}

fn attestation(boundaries: Vec<BoundaryAttestation>) -> NoMockAttestation {
    NoMockAttestation::new(
        "crates/fln-conformance/evidence/mandated_mutants/kills.jsonl",
        "a1b2c3d4e5f60718",
        "test-suite",
        boundaries,
    )
    .expect("the fixture attestation is well-formed")
}

// ---------------------------------------------------------------------------
// The closure law
// ---------------------------------------------------------------------------

#[test]
fn a_mock_permits_unit_and_nothing_stronger() {
    let attested = attestation(vec![
        real("cas-store", "sha256 of the real store dir"),
        BoundaryAttestation {
            boundary: "editor-client".to_string(),
            kind: BoundaryKind::Mock,
            evidence: String::new(),
        },
    ]);
    assert_eq!(attested.permits_closure(ClosureLevel::Unit), Ok(()));
    for level in [
        ClosureLevel::EvidenceLevel,
        ClosureLevel::PerformanceGate,
        ClosureLevel::PublicClaim,
    ] {
        match attested.permits_closure(level) {
            Err(AttestationError::MockBeyondUnit { boundary, .. }) => {
                assert_eq!(boundary, "editor-client", "the refusal names the mock");
            }
            other => panic!("a mock cannot close {level:?}, got {other:?}"),
        }
    }
}

#[test]
fn an_all_real_attestation_permits_every_level() {
    let attested = attestation(vec![
        BoundaryAttestation {
            boundary: "reference-binary".to_string(),
            kind: BoundaryKind::RealReference,
            evidence: "sha256 of the pinned lean binary".to_string(),
        },
        BoundaryAttestation {
            boundary: "editor-client".to_string(),
            kind: BoundaryKind::RealEditor,
            evidence: "the LSP handshake transcript".to_string(),
        },
    ]);
    for level in [
        ClosureLevel::Unit,
        ClosureLevel::EvidenceLevel,
        ClosureLevel::PerformanceGate,
        ClosureLevel::PublicClaim,
    ] {
        assert_eq!(
            attested.permits_closure(level),
            Ok(()),
            "real closes {level:?}"
        );
    }
}

// ---------------------------------------------------------------------------
// The evidence law
// ---------------------------------------------------------------------------

#[test]
fn a_real_boundary_without_evidence_is_refused() {
    // The mock-substitution self-mutant: a boundary declared real with nothing to
    // show is exactly how a mock dresses up, and it cannot be constructed.
    let err = NoMockAttestation::new(
        "artifact",
        "digest",
        "producer",
        vec![BoundaryAttestation {
            boundary: "reference-binary".to_string(),
            kind: BoundaryKind::RealReference,
            evidence: "   ".to_string(),
        }],
    )
    .expect_err("a real boundary needs its evidence");
    assert_eq!(
        err,
        AttestationError::RealBoundaryWithoutEvidence {
            boundary: "reference-binary".to_string()
        }
    );
    // Every Real* kind is held to it, not just one.
    for kind in [
        BoundaryKind::RealFilesystem,
        BoundaryKind::RealProcess,
        BoundaryKind::RealEditor,
        BoundaryKind::RealCorruption,
    ] {
        let err = NoMockAttestation::new(
            "artifact",
            "digest",
            "producer",
            vec![BoundaryAttestation {
                boundary: "b".to_string(),
                kind,
                evidence: String::new(),
            }],
        )
        .expect_err("blank evidence on a real boundary");
        assert!(matches!(
            err,
            AttestationError::RealBoundaryWithoutEvidence { .. }
        ));
    }
}

#[test]
fn blank_required_fields_are_refused_naming_the_field() {
    for (artifact, digest, producer, field) in [
        ("", "d", "p", "artifact"),
        ("a", "", "p", "artifact_digest"),
        ("a", "d", "", "producer"),
    ] {
        let err = NoMockAttestation::new(artifact, digest, producer, vec![])
            .expect_err("a blank field is refused");
        assert_eq!(err, AttestationError::BlankField { field });
    }
}

// ---------------------------------------------------------------------------
// The binding law, on the real committed artifact
// ---------------------------------------------------------------------------

#[test]
fn the_attestation_binds_to_the_real_artifact_and_refuses_a_different_run() {
    let path = root().join("crates/fln-conformance/evidence/mandated_mutants/kills.jsonl");
    let bytes = fs::read(&path)
        .unwrap_or_else(|e| panic!("the real kill receipts exist at {}: {e}", path.display()));
    let digest = fln_hash::domain::hash(fln_hash::domain::Domain::Fixture, &bytes).to_hex();
    let attested = NoMockAttestation::new(
        "crates/fln-conformance/evidence/mandated_mutants/kills.jsonl",
        &digest,
        "fln-conformance::mandated_mutants campaign (uagk)",
        vec![
            BoundaryAttestation {
                boundary: "host-filesystem".to_string(),
                kind: BoundaryKind::RealFilesystem,
                evidence: "the committed receipt's own bytes, read from the checkout".to_string(),
            },
            BoundaryAttestation {
                boundary: "campaign-process".to_string(),
                kind: BoundaryKind::RealProcess,
                evidence: "the receipt rows carry head_commit and observed_unix_s".to_string(),
            },
        ],
    )
    .expect("the attestation constructs");
    assert_eq!(
        attested.verify_artifact_binding(&bytes),
        Ok(()),
        "the attestation binds to the run it describes"
    );
    assert_eq!(
        attested.permits_closure(ClosureLevel::PublicClaim),
        Ok(()),
        "an all-real attestation over the real artifact closes"
    );

    // One altered byte: the attestation now describes a different run, and the
    // binding refuses it rather than re-signing.
    let mut altered = bytes.clone();
    let last = altered.len() - 2;
    altered[last] ^= 0x01;
    assert_eq!(
        attested.verify_artifact_binding(&altered),
        Err(AttestationError::ArtifactBindingMismatch {
            artifact: "crates/fln-conformance/evidence/mandated_mutants/kills.jsonl".to_string()
        })
    );
}

// ---------------------------------------------------------------------------
// The artifact laws: schema-versioned, canonical, round-tripping
// ---------------------------------------------------------------------------

#[test]
fn the_attestation_row_is_schema_versioned_and_canonical() {
    let attested = attestation(vec![
        real("cas-store", "sha256 of the store"),
        BoundaryAttestation {
            boundary: "editor-client".to_string(),
            kind: BoundaryKind::Mock,
            evidence: String::new(),
        },
    ]);
    let line = attested.to_ndjson();
    assert!(
        line.starts_with(&format!("{{\"schema\":\"{ATTESTATION_SCHEMA}\",")),
        "the row leads with its schema token: {line}"
    );
    assert!(
        line.contains("\"boundaries\":["),
        "the boundary list is part of the row"
    );
    assert!(
        line.contains("\"kind\":\"mock\""),
        "the mock is declared, counted, and visible — never laundered: {line}"
    );
    // The golden shape for one boundary entry, byte-exact.
    assert!(
        line.contains(
            "{\"boundary\":\"cas-store\",\"kind\":\"real-filesystem\",\"evidence\":\"sha256 of the store\"}"
        ),
        "the boundary entry is canonical: {line}"
    );
}
