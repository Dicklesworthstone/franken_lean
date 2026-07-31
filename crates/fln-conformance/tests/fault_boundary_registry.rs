//! `fault_boundary_registry` — the named suite for td9's fourth campaign framework:
//! the frozen fault census (`ci/FAULT_BOUNDARY_REGISTRY.txt` and
//! `fln_conformance::campaign::FaultRegistry`).
//!
//! # The laws proven here
//!
//! The registration law (no duplicates; no faultpoint without a product-by-product
//! expected final state — restart-as-pass is refused at the door), the completeness
//! law (a drill claiming an unregistered faultpoint, or a subset of a boundary's
//! registered points, is refused with the unclaimed ids named), the final-state law
//! (the observed vector matches the expected vector product-for-product; a missing
//! product is named, never averaged away), the platform law (capabilities are
//! platform-neutral; the row is chosen by target_os at compile time), and the
//! committed census itself (parses, non-empty, every boundary claimed by the bead's
//! own fault-drill domains covered).

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;

use fln_conformance::campaign::{
    FaultCapability, FaultError, FaultPoint, FaultRegistry, StateMismatch,
};

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

fn point(boundary: &str, id: &str, capability: FaultCapability) -> FaultPoint {
    FaultPoint {
        boundary: boundary.to_string(),
        id: id.to_string(),
        capability,
        expected: BTreeMap::from([
            ("store".to_string(), "old-or-new-never-torn".to_string()),
            ("receipt".to_string(), "intact-or-absent".to_string()),
        ]),
    }
}

// ---------------------------------------------------------------------------
// The registration law
// ---------------------------------------------------------------------------

#[test]
fn a_duplicate_faultpoint_is_refused() {
    let mut registry = FaultRegistry::new();
    registry
        .register(point(
            "cas",
            "kill-mid-write",
            FaultCapability::AbruptTermination,
        ))
        .expect("first");
    let err = registry
        .register(point(
            "cas",
            "kill-mid-write",
            FaultCapability::AbruptTermination,
        ))
        .expect_err("second registration of the same id must be refused");
    assert_eq!(
        err,
        FaultError::DuplicateFaultPoint {
            id: "kill-mid-write".to_string()
        }
    );
}

#[test]
fn a_faultpoint_without_an_expected_state_is_refused() {
    // The restart-as-pass refusal: with no vector, "the process restarted" passes.
    let mut registry = FaultRegistry::new();
    let mut empty = point("cas", "p1", FaultCapability::AbruptTermination);
    empty.expected.clear();
    assert_eq!(
        registry.register(empty),
        Err(FaultError::MissingExpectedState {
            id: "p1".to_string()
        })
    );
    let mut blank = point("cas", "p2", FaultCapability::AbruptTermination);
    blank
        .expected
        .insert("store".to_string(), "   ".to_string());
    assert_eq!(
        registry.register(blank),
        Err(FaultError::MissingExpectedState {
            id: "p2".to_string()
        })
    );
}

// ---------------------------------------------------------------------------
// The completeness law
// ---------------------------------------------------------------------------

#[test]
fn a_subset_claim_is_refused_with_the_unclaimed_named() {
    let mut registry = FaultRegistry::new();
    registry
        .register(point("cas", "p1", FaultCapability::AbruptTermination))
        .expect("p1");
    registry
        .register(point("cas", "p2", FaultCapability::CorruptStore))
        .expect("p2");
    let errors = registry.judge_claim("cas", &BTreeMap::from([("p1".to_string(), ())]));
    assert_eq!(
        errors,
        vec![FaultError::IncompleteBoundaryClaim {
            boundary: "cas".to_string(),
            unclaimed: vec!["p2".to_string()],
        }],
        "the census is frozen before the drill; a subset cannot read as the whole"
    );
}

#[test]
fn an_unregistered_claim_is_refused() {
    let registry = FaultRegistry::new();
    let errors = registry.judge_claim("cas", &BTreeMap::from([("ghost".to_string(), ())]));
    assert_eq!(
        errors,
        vec![FaultError::UnregisteredClaim {
            id: "ghost".to_string()
        }],
        "the drill exceeds its own census"
    );
}

#[test]
fn a_complete_claim_passes() {
    let mut registry = FaultRegistry::new();
    registry
        .register(point("cas", "p1", FaultCapability::AbruptTermination))
        .expect("p1");
    registry
        .register(point("cas", "p2", FaultCapability::CorruptStore))
        .expect("p2");
    let errors = registry.judge_claim(
        "cas",
        &BTreeMap::from([("p1".to_string(), ()), ("p2".to_string(), ())]),
    );
    assert!(errors.is_empty(), "a complete claim is clean: {errors:?}");
}

// ---------------------------------------------------------------------------
// The final-state law
// ---------------------------------------------------------------------------

#[test]
fn the_final_state_must_match_product_for_product() {
    let mut registry = FaultRegistry::new();
    registry
        .register(point("cas", "p1", FaultCapability::AbruptTermination))
        .expect("p1");
    let expected = BTreeMap::from([
        ("store".to_string(), "old-or-new-never-torn".to_string()),
        ("receipt".to_string(), "intact-or-absent".to_string()),
    ]);
    assert_eq!(registry.judge_final_state("p1", &expected), Ok(()));

    let torn = BTreeMap::from([
        ("store".to_string(), "torn".to_string()),
        ("receipt".to_string(), "intact-or-absent".to_string()),
    ]);
    match registry.judge_final_state("p1", &torn) {
        Err(FaultError::UnexpectedFinalState { id, mismatches }) => {
            assert_eq!(id, "p1");
            assert_eq!(
                mismatches,
                vec![StateMismatch {
                    product: "store".to_string(),
                    expected: "old-or-new-never-torn".to_string(),
                    observed: Some("torn".to_string()),
                }]
            );
        }
        other => panic!("a torn state is refused, got {other:?}"),
    }

    // "The process restarted" answers no product's expected state: an empty
    // observation is named for every product, never averaged away.
    match registry.judge_final_state("p1", &BTreeMap::new()) {
        Err(FaultError::UnexpectedFinalState { mismatches, .. }) => {
            assert_eq!(mismatches.len(), 2);
            assert!(
                mismatches.iter().all(|m| m.observed.is_none()),
                "every unobserved product is named with observed: None"
            );
        }
        other => panic!("a restart-only observation fails, got {other:?}"),
    }

    assert!(matches!(
        registry.judge_final_state("ghost", &expected),
        Err(FaultError::UnregisteredClaim { .. })
    ));
}

// ---------------------------------------------------------------------------
// The platform law
// ---------------------------------------------------------------------------

#[test]
fn every_capability_has_a_platform_row_chosen_at_compile_time() {
    for capability in [
        FaultCapability::AbruptTermination,
        FaultCapability::CorruptStore,
        FaultCapability::DiskFull,
        FaultCapability::BoundaryCrash,
    ] {
        let row = capability.platform_row();
        assert!(!row.is_empty(), "{} has a row", capability.token());
        assert_ne!(
            row,
            "unsupported-platform",
            "{} is realized on this host",
            capability.token()
        );
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        assert!(
            row.starts_with("unix:"),
            "on unix the row is a unix row, never a projected Windows API: {row}"
        );
        #[cfg(any(target_os = "linux", target_os = "macos"))]
        assert!(
            !row.contains("TerminateProcess"),
            "no Windows row is projected onto unix: {row}"
        );
        #[cfg(target_os = "windows")]
        assert!(
            row.starts_with("windows:"),
            "on Windows the row is a Windows row, never a projected signal: {row}"
        );
        #[cfg(target_os = "windows")]
        assert!(
            !row.contains("SIGKILL"),
            "no Unix signal is projected onto Windows: {row}"
        );
    }
}

// ---------------------------------------------------------------------------
// The committed census
// ---------------------------------------------------------------------------

#[test]
fn the_committed_census_parses_and_covers_the_drill_domains() {
    let path = root().join("ci/FAULT_BOUNDARY_REGISTRY.txt");
    let text = fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the fault census must exist at {}: {e}", path.display()));
    let registry = FaultRegistry::parse(&text).expect("the committed census parses");
    assert!(
        !registry.is_empty(),
        "an empty census is a broken scan, not a clean tree"
    );
    assert_eq!(registry.len(), 8, "the eight frozen faultpoints");

    // Every boundary the bead's fault drills name is covered, with the capabilities
    // AGENTS.md's testing policy lists (kill -9 at every CAS promotion step,
    // corrupted caches, disk-full mid-build, plugin crashes).
    for boundary in [
        "cas-promotion",
        "session-store",
        "plugin-door",
        "evidence-finalization",
    ] {
        assert!(
            !registry.boundary_points(boundary).is_empty(),
            "boundary {boundary} has registered faultpoints"
        );
    }
    for capability in [
        FaultCapability::AbruptTermination,
        FaultCapability::CorruptStore,
        FaultCapability::DiskFull,
        FaultCapability::BoundaryCrash,
    ] {
        // Each capability is exercised by at least one registered faultpoint — a
        // declared capability with no instance is an empty referent.
        let mut found = false;
        for boundary in [
            "cas-promotion",
            "session-store",
            "plugin-door",
            "evidence-finalization",
        ] {
            found |= registry
                .boundary_points(boundary)
                .iter()
                .any(|point| point.capability == capability);
        }
        assert!(
            found,
            "capability {} has a registered instance",
            capability.token()
        );
    }
}

#[test]
fn the_parser_refuses_drift_with_its_line() {
    let wrong_schema = FaultRegistry::parse("schema fln-fault-boundary-registry/0\n");
    assert!(matches!(
        wrong_schema,
        Err(FaultError::UnregisteredClaim { .. })
    ));

    let bad_capability = FaultRegistry::parse(
        "schema fln-fault-boundary-registry/1\nfault b | p1 | alchemy | s=x\n",
    );
    match bad_capability {
        Err(FaultError::UnregisteredClaim { id }) => {
            assert!(id.contains("line 2"), "the refusal names its line: {id}");
            assert!(id.contains("alchemy"), "the refusal names the token: {id}");
        }
        other => panic!("an unknown capability is refused, got {other:?}"),
    }

    let no_state =
        FaultRegistry::parse("schema fln-fault-boundary-registry/1\nfault b | p1 | disk-full | \n");
    assert!(matches!(
        no_state,
        Err(FaultError::MissingExpectedState { .. }) | Err(FaultError::UnregisteredClaim { .. })
    ));
}
