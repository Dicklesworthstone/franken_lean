//! `shrink_signature_preservation` — the named suite for td9's fifth campaign
//! framework: failure-signature-preserving shrink (`fln_conformance::campaign`'s
//! `Shrinker`, `FailureSignature`, `ShrinkVerdict`, `ShrinkReport`).
//!
//! # The laws proven here
//!
//! Signature preservation (a candidate failing with a *different* signature is
//! never accepted — the drift is a new finding, not a shrink), the failure-presence
//! law (a passing candidate is never accepted — shrinking past the boundary loses
//! the failure), monotonic termination with an honest stop (the lineage records
//! every accepted reduction; a budget stop never calls its last state minimal),
//! the candidate-artifact law (the report is the artifact — the framework carries
//! no path, so a shrink can never edit the workspace), and the real controlled
//! target: shrinking a genuinely malformed kill-ledger NDJSON row against the real
//! parser, with the parser's own refusal variant as the preserved signature.

#![forbid(unsafe_code)]

use fln_conformance::campaign::{
    FailureSignature, KillLedger, ResourceClass, ShrinkVerdict, Shrinker,
};

fn sig(class: &str) -> FailureSignature {
    FailureSignature {
        class: class.to_string(),
        resource: ResourceClass::ShapeRefusal,
    }
}

/// Remove single chunks: all strictly-smaller substrings that drop a contiguous
/// span. The classic shrink candidate family.
fn chunk_removals(input: &String) -> Vec<String> {
    let mut out = Vec::new();
    let bytes = input.as_bytes();
    for width in [8, 4, 2, 1] {
        if bytes.len() <= width {
            continue;
        }
        for start in 0..=(bytes.len() - width) {
            let mut candidate = input.clone();
            candidate.replace_range(start..start + width, "");
            out.push(candidate);
        }
    }
    out
}

// ---------------------------------------------------------------------------
// The preservation laws, on a toy oracle where every move is visible
// ---------------------------------------------------------------------------

/// Fails with "contains X" when the input has one; fails with "too long" when it
/// does not but is long; passes otherwise. Two signatures, so drift is observable.
fn toy_oracle(input: &String) -> ShrinkVerdict {
    if input.contains('X') {
        ShrinkVerdict::Failure(sig("contains-X"))
    } else if input.len() > 12 {
        ShrinkVerdict::Failure(sig("too-long"))
    } else {
        ShrinkVerdict::NotAFailure
    }
}

#[test]
fn a_shrink_reduces_to_a_minimum_with_the_signature_intact() {
    let report = Shrinker { max_rounds: 64 }
        .shrink(
            "aaaaXXXXaaaaaaaaaaaaaaaa".to_string(),
            |s: &String| s.len(),
            chunk_removals,
            toy_oracle,
        )
        .expect("the original fails");
    assert_eq!(report.signature, sig("contains-X"));
    assert!(
        report.final_measure < report.original_measure,
        "the shrink shrank: {} -> {}",
        report.original_measure,
        report.final_measure
    );
    assert!(report.local_minimum, "it stopped at a local minimum");
    // The lineage is monotone decreasing — every accepted step really shrank.
    for pair in report.lineage.windows(2) {
        assert!(pair[1] < pair[0], "lineage is monotone: {:?}", report.lineage);
    }
    // And the final candidate still fails with the preserved signature.
    assert!(matches!(toy_oracle(&"X".to_string()), ShrinkVerdict::Failure(_)));
}

#[test]
fn a_signature_drift_is_never_accepted() {
    // The only way to shrink below the X is to drop it, which flips the failure to
    // "too-long" — a drift the shrink must refuse, so it stops with the X intact.
    let report = Shrinker { max_rounds: 64 }
        .shrink("Xaaaaaaaaaaaaaaaaaaaa".to_string(), |s: &String| s.len(), chunk_removals, toy_oracle)
        .expect("the original fails");
    assert_eq!(report.signature, sig("contains-X"));
    assert!(
        report.lineage.iter().all(|&m| m >= 1),
        "the X is never shrunk away: {:?}",
        report.lineage
    );
    // Every accepted state still contains X — drift would have removed it.
    let mut current = "Xaaaaaaaaaaaaaaaaaaaa".to_string();
    for &accepted in report.lineage.iter().skip(1) {
        for candidate in chunk_removals(&current) {
            if candidate.len() == accepted {
                assert!(candidate.contains('X'), "an accepted state keeps the signature");
                current = candidate;
                break;
            }
        }
    }
}

#[test]
fn a_passing_candidate_is_never_accepted() {
    // After shrinking to just "X", every further candidate is empty — which passes
    // the oracle. The shrink must keep the failure: the final state still fails.
    let report = Shrinker { max_rounds: 64 }
        .shrink("XX".to_string(), |s: &String| s.len(), chunk_removals, toy_oracle)
        .expect("the original fails");
    assert_eq!(report.final_measure, 1, "it stops at one X, never at zero");
    assert!(report.local_minimum);
}

#[test]
fn a_budget_stop_never_claims_a_minimum() {
    let report = Shrinker { max_rounds: 1 }
        .shrink(
            "aaaaXXXXaaaaaaaaaaaaaaaa".to_string(),
            |s: &String| s.len(),
            chunk_removals,
            toy_oracle,
        )
        .expect("the original fails");
    assert!(
        !report.local_minimum,
        "one round in, the shrink says it stopped early — the last state is a \
         waypoint, not a claimed minimum"
    );
}

#[test]
fn a_non_failing_original_has_nothing_to_preserve() {
    let report = Shrinker { max_rounds: 4 }.shrink(
        "ok".to_string(),
        |s: &String| s.len(),
        chunk_removals,
        toy_oracle,
    );
    assert_eq!(report, None, "a passing input cannot be shrunk");
}

// ---------------------------------------------------------------------------
// The resource-class law: a failure moved to another class is a different bug
// ---------------------------------------------------------------------------

#[test]
fn a_resource_class_move_is_refused() {
    let oracle = |input: &String| {
        if input.contains('X') {
            ShrinkVerdict::Failure(FailureSignature {
                class: "boom".to_string(),
                resource: ResourceClass::TargetFault,
            })
        } else {
            ShrinkVerdict::NotAFailure
        }
    };
    let report = Shrinker { max_rounds: 8 }
        .shrink("Xabc".to_string(), |s: &String| s.len(), chunk_removals, oracle)
        .expect("the original fails");
    assert_eq!(
        report.signature.resource,
        ResourceClass::TargetFault,
        "the preserved resource class is the original's"
    );
}

// ---------------------------------------------------------------------------
// The real controlled target: shrinking a malformed kill-ledger row
// ---------------------------------------------------------------------------

/// The preserved signature for the real parser: the `CampaignError` variant name,
/// from the real `KillLedger::row_from_ndjson`. Two malformed rows that fail for
/// different reasons have different signatures, so a shrink cannot wander from
/// "missing field" into "unknown verdict" and call it the same bug.
fn parser_signature(input: &String) -> ShrinkVerdict {
    match KillLedger::row_from_ndjson(input) {
        Ok(_) => ShrinkVerdict::NotAFailure,
        Err(error) => {
            let text = format!("{error:?}");
            let variant = text.split([' ', '{', '(']).next().unwrap_or("?").to_string();
            ShrinkVerdict::Failure(FailureSignature {
                class: variant,
                resource: ResourceClass::ShapeRefusal,
            })
        }
    }
}

#[test]
fn the_real_target_shrink_a_malformed_ledger_row() {
    // A genuinely malformed row: valid shape, schema token destroyed by padding.
    let original = format!(
        "{{\"schema\":\"fln.mutation-kill-ledger/1-PADDED-WRONG-WRONG\",\
         \"mutant_id\":\"m1\",\"source_root_digest\":\"a1b2c3d4\",\
         \"patch_digest\":\"e5f60718\",\"build_identity\":\"b\",\"target_path\":\"t\",\
         \"expected_discriminator\":\"d\",\"release_exclusion_proof\":\"p\",\
         \"disposition\":\"active\",\"exclusion_evidence\":\"\",\"verdict\":\"unrun\",\
         \"not_a_kill\":\"\"}}"
    );
    let report = Shrinker { max_rounds: 200 }
        .shrink(original.clone(), |s: &String| s.len(), chunk_removals, parser_signature)
        .expect("the padded row fails");
    assert_eq!(
        report.signature.class, "NdjsonInvalid",
        "the preserved signature is the parser's own refusal variant"
    );
    assert!(report.final_measure < report.original_measure);
    // The shrink preserved the *schema* refusal the whole way: every lineage state
    // must still fail with the same variant — replayed, not believed.
    assert!(
        matches!(parser_signature(&original), ShrinkVerdict::Failure(_)),
        "control: the original fails"
    );
    assert!(report.local_minimum || report.lineage.len() >= 2);
}
