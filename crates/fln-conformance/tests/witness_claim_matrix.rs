//! The Witness claim-matrix gate (bead `franken_lean-claim-matrix-doc-ci-mhew`, Bet B8).
//!
//! B8 promises documentation CI that rejects wording stronger than the evidence permits. A
//! docs gate that cannot demonstrate it **catches known-bad and passes known-good** is itself
//! an unenforced claim, which would be a self-defeating thing to ship on this particular
//! bead. So both directions are proved here, and both are proved against real repairs rather
//! than fixtures written to make a test pass:
//!
//! * commit `86035037` repaired `crates/fln-olean/src/lib.rs`, whose header asserted
//!   "byte-compatible `.olean` read and write" while deferring writing four lines later;
//! * commit `a368ea0b` repaired `README.md`, which offered a `curl … | bash` to a
//!   `scripts/install.sh` that does not exist — in **two** places.
//!
//! The anchors for those two rows were recovered verbatim from `86035037^` and `a368ea0b^`,
//! not retyped, so the planted cases replay text this repository actually shipped.
//!
//! Every planted case drives the production [`fln_conformance::witness::scan`] over synthetic
//! documents. A harness that re-implements the thing it mutates can report a false green.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use fln_conformance::witness::{
    CLAIM_MATRIX, ClaimRow, ClaimState, Enforcement, GOVERNED_SCOPE, WitnessFault, scan,
};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root is two levels above the crate manifest")
}

/// Reader over the real tree.
fn real_reader() -> impl FnMut(&str) -> Result<String, String> {
    let root = workspace_root();
    move |document: &str| fs::read_to_string(root.join(document)).map_err(|error| error.to_string())
}

/// Reader over synthetic documents, for the planted cases.
fn planted(docs: BTreeMap<&'static str, String>) -> impl FnMut(&str) -> Result<String, String> {
    move |document: &str| {
        docs.get(document)
            .cloned()
            .ok_or_else(|| format!("no planted document for {document}"))
    }
}

/// The real tree with one document's text replaced — so a plant is one edit away from
/// reality rather than a hand-built world where anything could be true.
fn real_with(document: &'static str, text: String) -> impl FnMut(&str) -> Result<String, String> {
    let root = workspace_root();
    move |wanted: &str| {
        if wanted == document {
            Ok(text.clone())
        } else {
            fs::read_to_string(root.join(wanted)).map_err(|error| error.to_string())
        }
    }
}

fn row(id: &str) -> &'static ClaimRow {
    let found = CLAIM_MATRIX.iter().find(|row| row.id == id);
    assert!(found.is_some(), "no claim row {id}");
    found.expect("asserted Some immediately above")
}

fn render(faults: &[WitnessFault]) -> String {
    faults
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n\n")
}

// ---------------------------------------------------------------------------
// Known-good: the gate does not fire on the tree as it stands
// ---------------------------------------------------------------------------

#[test]
fn the_matrix_is_clean_against_the_real_tree() {
    let outcome = scan(&CLAIM_MATRIX, real_reader());
    let report = outcome.as_ref().err().map(|faults| render(faults));
    assert!(
        outcome.is_ok(),
        "the claim matrix disagrees with the documents it governs:\n\n{}",
        report.unwrap_or_default()
    );
    let report = outcome.expect("asserted Ok immediately above");

    assert_eq!(report.rows(), CLAIM_MATRIX.len(), "every row was decided");
    assert_eq!(
        report.enforced, 2,
        "two repairs are protected: the fln-olean header (86035037) and the README install \
         one-liner (a368ea0b)"
    );
    assert_eq!(
        report.acknowledged, 8,
        "eight measured overclaims are standing and recorded; if this number falls, a repair \
         happened and its row must be promoted rather than the count edited"
    );
    assert_eq!(report.documents.len(), 3, "{:?}", report.documents);
}

/// The scope statement is data, not a doc comment, so a failure prints it.
#[test]
fn the_matrix_states_what_it_does_not_govern() {
    assert!(
        GOVERNED_SCOPE.contains("NOT covered"),
        "a partial projection that does not declare its edges reads as total coverage"
    );
    assert!(
        GOVERNED_SCOPE.contains("does not mean the documentation is accurate"),
        "the scope statement must refuse the reading a green run invites"
    );
}

// ---------------------------------------------------------------------------
// Known-bad: the gate fires on wording this project already repaired
// ---------------------------------------------------------------------------

#[test]
fn a_repaired_overclaim_coming_back_is_caught() {
    // Both anchors are the real prior text, recovered from 86035037^ and a368ea0b^.
    for id in ["OLEAN-WRITE-CRATE-HEADER", "INSTALL-ONELINER-RUNNABLE"] {
        let target = row(id);
        assert_eq!(
            target.enforcement,
            Enforcement::Enforced,
            "{id} is the regression corpus and must be enforced"
        );

        // Confirm the repair is real before proving the plant fires, so this cannot pass by
        // testing a claim that was never fixed.
        let live = fs::read_to_string(workspace_root().join(target.document))
            .expect("governed document is readable");
        assert!(
            !live.contains(target.anchor),
            "{id}: the anchor is still in {} — the repair this test depends on did not happen",
            target.document
        );

        let regressed = format!(
            "{live}\n\nand then someone put it back: {}\n",
            target.anchor
        );
        let faults = scan(&CLAIM_MATRIX, real_with(target.document, regressed))
            .expect_err("restored wording must fail the gate");
        assert!(
            faults.iter().any(|fault| matches!(
                fault,
                WitnessFault::Regressed { id: found, .. } if found == id
            )),
            "expected a Regressed fault for {id}: {faults:?}"
        );
    }
}

/// The install one-liner occurred **twice**; a fix that repaired one site would have left the
/// other. An enforced row must fail on any occurrence and report how many.
#[test]
fn a_partial_repair_cannot_pass() {
    let target = row("INSTALL-ONELINER-RUNNABLE");
    let doc = format!(
        "hero block:\n{}\n\n...prose...\n\ninstallation section:\n{}\n",
        target.anchor, target.anchor
    );
    let faults = scan(
        &[*target],
        planted(BTreeMap::from([(target.document, doc)])),
    )
    .expect_err("two sites");
    let first = faults.first();
    assert!(
        matches!(first, Some(WitnessFault::Regressed { occurrences: 2, .. })),
        "expected Regressed carrying occurrences=2 — the count is what tells a repairer a \
         second site exists — got {first:?}"
    );
}

// ---------------------------------------------------------------------------
// The other direction: a silent repair is also a failure
// ---------------------------------------------------------------------------

#[test]
fn a_silently_repaired_overclaim_is_caught() {
    let target = row("DAEMON-WARM-ATTACH-SLO");
    assert_eq!(target.enforcement, Enforcement::Acknowledged);

    let live = fs::read_to_string(workspace_root().join(target.document))
        .expect("governed document is readable");
    let repaired = live.replace(target.anchor, "warm attach is not yet measured");
    assert!(
        !repaired.contains(target.anchor),
        "the plant did not apply — check the anchor text"
    );

    let faults = scan(&CLAIM_MATRIX, real_with(target.document, repaired))
        .expect_err("a repair the matrix did not follow must fail");
    assert!(
        faults.iter().any(|fault| matches!(
            fault,
            WitnessFault::StaleAcknowledgement { id, .. } if id == target.id
        )),
        "expected StaleAcknowledgement for {}: {faults:?}",
        target.id
    );
    assert!(
        render(&faults).contains("Promote the row"),
        "the refusal must say what to do about it"
    );
}

// ---------------------------------------------------------------------------
// Structural failures
// ---------------------------------------------------------------------------

#[test]
fn an_unreadable_governed_document_is_inconclusive_never_a_pass() {
    let target = row("B3-KERNEL-DUAL-ENGINE");
    let faults = scan(&[*target], |_document| Err("permission denied".to_string()))
        .expect_err("a document that cannot be read establishes nothing");
    assert!(
        matches!(
            faults.first(),
            Some(WitnessFault::UnreadableDocument { .. })
        ),
        "{faults:?}"
    );
    assert!(
        render(&faults).contains("inconclusive, never a pass"),
        "FL-INV-07: an unestablished claim is not a satisfied one"
    );
}

#[test]
fn a_duplicate_claim_id_is_refused() {
    let target = *row("TACTICS-ON-GOLEM");
    let faults =
        scan(&[target, target], real_reader()).expect_err("one row would shadow the other");
    assert!(
        faults.iter().any(|fault| matches!(
            fault,
            WitnessFault::DuplicateClaimId { id } if id == target.id
        )),
        "{faults:?}"
    );
}

#[test]
fn the_gate_reports_every_disagreement_at_once_and_deterministically() {
    let enforced = row("OLEAN-WRITE-CRATE-HEADER");
    let acknowledged = row("DAEMON-WARM-ATTACH-SLO");
    let docs = BTreeMap::from([
        // enforced wording restored, acknowledged wording removed: one fault of each kind
        (enforced.document, format!("regressed: {}", enforced.anchor)),
        (acknowledged.document, "nothing to see here".to_string()),
    ]);
    let faults = scan(&[*enforced, *acknowledged], planted(docs.clone())).expect_err("two faults");
    assert_eq!(
        faults.len(),
        2,
        "the gate must report both directions in one run, not stop at the first: {faults:?}"
    );

    let again = scan(&[*enforced, *acknowledged], planted(docs)).expect_err("two faults");
    assert_eq!(faults, again, "same inputs, same report (FL-INV-01)");
    let mut sorted = faults.clone();
    sorted.sort();
    assert_eq!(faults, sorted, "faults come back sorted");
}

// ---------------------------------------------------------------------------
// Row hygiene
// ---------------------------------------------------------------------------

#[test]
fn every_row_carries_what_a_reviewer_needs() {
    for row in &CLAIM_MATRIX {
        assert!(!row.id.is_empty(), "a row needs a citable id");
        assert!(
            row.id
                .chars()
                .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '-'),
            "{}: ids are SCREAMING-KEBAB so they read as citations in a bead",
            row.id
        );
        assert!(
            !row.anchor.is_empty(),
            "{}: an anchor is the whole mechanism",
            row.id
        );
        assert!(
            row.evidence.len() > 60,
            "{}: evidence must say what the tree supports, not merely restate the state",
            row.id
        );

        // A claim the tree demonstrably does not support cannot sit at OBSERVED or PROVEN
        // while being carried as a standing overclaim; that combination would be the matrix
        // certifying the thing it is supposed to be recording as unsupported.
        if row.enforcement == Enforcement::Acknowledged {
            assert!(
                !matches!(row.state, ClaimState::Observed | ClaimState::Proven),
                "{}: an acknowledged overclaim cannot be OBSERVED or PROVEN",
                row.id
            );
        }
    }
}
