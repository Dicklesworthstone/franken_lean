//! The Witness claim-matrix gate (bead `franken_lean-claim-matrix-doc-ci-mhew`, Bet B8).
//!
//! B8 promises documentation CI that rejects wording stronger than the evidence permits. A
//! docs gate that cannot demonstrate it **catches known-bad and passes known-good** is itself
//! an unenforced claim. Both directions are proved here against real repairs:
//!
//! * commit `86035037` repaired `crates/fln-olean/src/lib.rs`, whose header asserted
//!   "byte-compatible `.olean` read and write" while deferring writing four lines later;
//! * commit `a368ea0b` repaired `README.md`, which offered a `curl … | bash` to a
//!   `scripts/install.sh` that does not exist — in **two** places.
//!
//! Those anchors were recovered verbatim from `86035037^` and `a368ea0b^`, not retyped, so
//! the planted cases replay text this repository actually shipped.
//!
//! Slice 2 adds the two properties slice 1 could not express: **multi-site rows**, because
//! "disagreement halts, never outvotes" is asserted seven times in four phrasings and a
//! repair of six of them must not pass; and the **conservation census**, because multi-site
//! rows without it would look comprehensive without proving they enumerated every site.
//!
//! Every planted case drives the production [`fln_conformance::witness::scan`].

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use fln_conformance::witness::{
    CLAIM_MATRIX, CONCEPT_CENSUS, ClaimRow, ClaimState, EVIDENCE_CITATIONS, Enforcement,
    GOVERNED_SCOPE, WitnessFault, governed_occurrences, scan,
};

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
        .expect("workspace root is two levels above the crate manifest")
}

fn real_reader() -> impl FnMut(&str) -> Result<String, String> {
    let root = workspace_root();
    move |document: &str| fs::read_to_string(root.join(document)).map_err(|e| e.to_string())
}

fn planted(docs: BTreeMap<&'static str, String>) -> impl FnMut(&str) -> Result<String, String> {
    move |document: &str| {
        docs.get(document)
            .cloned()
            .ok_or_else(|| format!("no planted document for {document}"))
    }
}

/// The real tree with one document's text replaced — a plant one edit away from reality
/// rather than a hand-built world where anything could be true.
fn real_with(document: &'static str, text: String) -> impl FnMut(&str) -> Result<String, String> {
    let root = workspace_root();
    move |wanted: &str| {
        if wanted == document {
            Ok(text.clone())
        } else {
            fs::read_to_string(root.join(wanted)).map_err(|e| e.to_string())
        }
    }
}

/// Like [`real_with`] but for a non-`'static` path, which citation paths are.
fn real_with_path(document: &str, text: String) -> impl FnMut(&str) -> Result<String, String> {
    let root = workspace_root();
    let document = document.to_string();
    move |wanted: &str| {
        if wanted == document {
            Ok(text.clone())
        } else {
            fs::read_to_string(root.join(wanted)).map_err(|e| e.to_string())
        }
    }
}

fn row(id: &str) -> &'static ClaimRow {
    let found = CLAIM_MATRIX.iter().find(|row| row.id == id);
    assert!(found.is_some(), "no claim row {id}");
    found.expect("asserted Some immediately above")
}

fn read_doc(document: &str) -> String {
    fs::read_to_string(workspace_root().join(document)).expect("governed document is readable")
}

fn render(faults: &[WitnessFault]) -> String {
    faults
        .iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>()
        .join("\n\n")
}

// ---------------------------------------------------------------------------
// Known-good
// ---------------------------------------------------------------------------

#[test]
fn the_matrix_and_the_censuses_are_clean_against_the_real_tree() {
    let outcome = scan(
        &CLAIM_MATRIX,
        &CONCEPT_CENSUS,
        &EVIDENCE_CITATIONS,
        real_reader(),
    );
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
        report.supported, 1,
        "the <= 12 KLOC covenant is earned and recorded as such, so the matrix does not imply \
         the whole B3 sentence is unsupported"
    );
    assert_eq!(report.acknowledged, 12, "the standing overclaims");
    assert_eq!(
        report.censuses,
        CONCEPT_CENSUS.len(),
        "every conservation law balanced"
    );
    assert!(
        report.sites > CLAIM_MATRIX.len(),
        "multi-site rows exist, so sites must exceed rows: {} sites, {} rows",
        report.sites,
        CLAIM_MATRIX.len()
    );
    assert_eq!(
        report.citations,
        EVIDENCE_CITATIONS.len(),
        "every cited fact still holds; if this falls, a row's evidence has rotted and the \
         prose needs re-reading, not the citation adjusting"
    );
}

/// The failure this whole mechanism was added for.
///
/// On 2026-07-25 two rows in this matrix were factually false — `B3-INDEPENDENT-CHECKER`
/// called `fln-checker` "a 6-line charter stub" after it reached 149 lines, and
/// `B3-CONSENSUS-HALTS` said "there is no council to disagree" after `council.rs` landed —
/// and every anchor still matched, so the gate stayed green. The wording in the documents
/// had not changed; the tree had. Nothing here could see that until citations existed.
#[test]
fn evidence_that_has_gone_stale_is_caught_even_though_the_anchors_still_match() {
    let target = row("DAEMON-WARM-ATTACH-SLO");
    let citation = EVIDENCE_CITATIONS
        .iter()
        .find(|(id, _)| *id == target.id)
        .map(|(_, citation)| *citation);
    assert!(citation.is_some(), "{} has a cited fact", target.id);
    let citation = citation.expect("asserted Some above");

    // The row's evidence says crates/fln-server is a stub. Implement it, and the row is
    // wrong while its anchor in README.md is untouched.
    let implemented = "x\n".repeat(400);
    let faults = scan(
        &[*target],
        &[],
        &[(target.id, citation)],
        real_with_path(citation.path(), implemented),
    )
    .expect_err("a row whose cited fact moved must fail");

    assert!(
        faults.iter().any(|fault| matches!(
            fault,
            WitnessFault::StaleEvidence { id, .. } if id == target.id
        )),
        "expected StaleEvidence for {}: {faults:?}",
        target.id
    );
    assert!(
        render(&faults).contains("the wording in the documents did not change, the tree did"),
        "the refusal must name why nothing else caught it"
    );
    assert!(
        render(&faults).contains("Do not adjust the citation to match reality"),
        "the refusal must close the obvious escape, which is to move the number"
    );
}

/// The ratchet: no row may be added without a tripwire.
///
/// **This is a floor, not coverage**, and the distinction is the whole finding. It guarantees
/// every row has *a* checkable fact; it does not make the row current. A citation catches only
/// rot someone anticipated well enough to cite, and both rows that rotted on 2026-07-25 rotted
/// in ways nobody anticipated — found by re-reading prose, not by any check. Reading a green
/// run here as "the evidence is current" is exactly the over-reading this matrix exists to
/// refuse.
#[test]
fn every_row_cites_at_least_one_checkable_fact() {
    for row in &CLAIM_MATRIX {
        let cited = EVIDENCE_CITATIONS.iter().any(|(id, _)| *id == row.id);
        assert!(
            cited,
            "{} has no citation: its evidence is prose that nothing checks, so it can go \
             factually false while every anchor still matches — which is precisely how \
             B3-INDEPENDENT-CHECKER and B3-CONSENSUS-HALTS rotted. Add a Citation naming one \
             load-bearing fact the evidence asserts.",
            row.id
        );
    }
}

/// A citation whose fact is *already* false at authoring time would be a tripwire that fires
/// on day one and gets deleted rather than heeded, so the live table must be clean — which the
/// clean-tree scan asserts — and every row must be reachable, which this asserts.
#[test]
fn a_citation_naming_no_row_is_refused() {
    let citation = EVIDENCE_CITATIONS
        .first()
        .map(|(_, citation)| *citation)
        .expect("the table is non-empty");
    let faults = scan(
        &CLAIM_MATRIX,
        &[],
        &[("NO-SUCH-CLAIM-ROW", citation)],
        real_reader(),
    )
    .expect_err("a citation that checks nothing");
    assert!(
        faults
            .iter()
            .any(|fault| matches!(fault, WitnessFault::CitationForUnknownRow { .. })),
        "{faults:?}"
    );
}

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
    assert!(
        GOVERNED_SCOPE.contains("every other repeated claim in these documents is unwatched"),
        "the censuses cover three concepts; the scope must say the rest are not covered, or \
         the census itself becomes a false all-clear"
    );
}

// ---------------------------------------------------------------------------
// Known-bad: repaired wording returning
// ---------------------------------------------------------------------------

#[test]
fn a_repaired_overclaim_coming_back_is_caught() {
    for id in ["OLEAN-WRITE-CRATE-HEADER", "INSTALL-ONELINER-RUNNABLE"] {
        let target = row(id);
        assert_eq!(target.enforcement, Enforcement::Enforced);
        let site = target.sites.first().expect("enforced rows have a site");

        // Confirm the repair is real before proving the plant fires, so this cannot pass by
        // testing a claim that was never fixed.
        let live = read_doc(site.document);
        assert!(
            !live.contains(site.text),
            "{id}: the anchor is still in {} — the repair this test depends on did not happen",
            site.document
        );

        let regressed = format!("{live}\n\nand then someone put it back: {}\n", site.text);
        let faults = scan(&[*target], &[], &[], real_with(site.document, regressed))
            .expect_err("restored wording must fail the gate");
        assert!(
            faults.iter().any(|fault| matches!(
                fault,
                WitnessFault::Regressed { id: found, .. } if found == id
            )),
            "expected Regressed for {id}: {faults:?}"
        );
    }
}

/// The install one-liner occurred **twice** in one document; a repair of one site would have
/// left the other. An enforced row fails on any occurrence and reports how many.
#[test]
fn a_partial_repair_within_one_document_cannot_pass() {
    let target = row("INSTALL-ONELINER-RUNNABLE");
    let site = target.sites.first().expect("has a site");
    let doc = format!(
        "hero:\n{}\n\nprose\n\ninstall section:\n{}\n",
        site.text, site.text
    );
    let faults = scan(
        &[*target],
        &[],
        &[],
        planted(BTreeMap::from([(site.document, doc)])),
    )
    .expect_err("two sites in one document");
    let first = faults.first();
    assert!(
        matches!(first, Some(WitnessFault::Regressed { occurrences: 2, .. })),
        "expected Regressed carrying occurrences=2 — the count is what tells a repairer a \
         second site exists — got {first:?}"
    );
}

// ---------------------------------------------------------------------------
// Slice 2: multi-site rows
// ---------------------------------------------------------------------------

/// The property slice 1 could not express. "Disagreement halts" is asserted seven times in
/// four phrasings; repairing all but one must fail.
#[test]
fn repairing_all_but_one_site_of_a_multi_site_claim_fails() {
    let target = row("B3-CONSENSUS-HALTS");
    assert!(
        target.sites.len() >= 5,
        "the consensus claim spans at least five governed sites, got {}",
        target.sites.len()
    );

    // Repair every README site; leave the other documents alone.
    let readme = read_doc("README.md");
    let mut repaired = readme.clone();
    for site in target.sites.iter().filter(|s| s.document == "README.md") {
        repaired = repaired.replace(site.text, "the consensus story is not yet earned");
    }
    assert_ne!(repaired, readme, "the plant did not apply");

    let faults = scan(&[*target], &[], &[], real_with("README.md", repaired))
        .expect_err("a partial repair across sites must not pass");
    assert!(
        faults.iter().any(|fault| matches!(
            fault,
            WitnessFault::StaleAcknowledgement { id, .. } if id == target.id
        )),
        "expected StaleAcknowledgement for the repaired sites: {faults:?}"
    );
    assert!(
        render(&faults).contains("Promote the row"),
        "the refusal must say what to do about it"
    );
}

#[test]
fn a_silently_repaired_overclaim_is_caught() {
    let target = row("DAEMON-WARM-ATTACH-SLO");
    assert_eq!(target.enforcement, Enforcement::Acknowledged);
    let site = target.sites.first().expect("has a site");

    let repaired = read_doc(site.document).replace(site.text, "warm attach is not yet measured");
    let faults = scan(&[*target], &[], &[], real_with(site.document, repaired))
        .expect_err("a repair the matrix did not follow must fail");
    assert!(
        faults.iter().any(|fault| matches!(
            fault,
            WitnessFault::StaleAcknowledgement { id, .. } if id == target.id
        )),
        "{faults:?}"
    );
}

/// A supported claim disappearing is a different failure with a different repair: either a
/// true claim was dropped, or the capability regressed.
#[test]
fn a_vanishing_supported_claim_is_caught() {
    let target = row("B3-KERNEL-LOC-COVENANT");
    assert_eq!(target.enforcement, Enforcement::Supported);
    assert_eq!(
        target.state,
        ClaimState::Observed,
        "a Supported row records an earned claim"
    );
    let site = target.sites.first().expect("has a site");

    let stripped = read_doc(site.document).replace(site.text, "the kernel is small");
    let faults = scan(&[*target], &[], &[], real_with(site.document, stripped))
        .expect_err("a supported claim vanishing must fail");
    assert!(
        matches!(
            faults.first(),
            Some(WitnessFault::SupportedClaimVanished { .. })
        ),
        "{faults:?}"
    );
    assert!(
        render(&faults).contains("do not delete the row to make this pass"),
        "the refusal must close the obvious escape"
    );
}

// ---------------------------------------------------------------------------
// Slice 2: the conservation census
// ---------------------------------------------------------------------------

#[test]
fn a_new_ungoverned_assertion_breaks_the_census() {
    let census = CONCEPT_CENSUS
        .iter()
        .find(|c| c.keyword == "dual-engine")
        .expect("the dual-engine census exists");

    let readme = format!(
        "{}\n\nand elsewhere someone wrote about the dual-engine kernel again.\n",
        read_doc("README.md")
    );
    let faults = scan(
        &CLAIM_MATRIX,
        &CONCEPT_CENSUS,
        &EVIDENCE_CITATIONS,
        real_with("README.md", readme),
    )
    .expect_err("an assertion added anywhere must break conservation");
    assert!(
        faults.iter().any(|fault| matches!(
            fault,
            WitnessFault::CensusDrift { concept, counted, governed, allowance }
                if concept == census.concept
                    && *counted == *governed + *allowance + 1
        )),
        "expected CensusDrift showing exactly one unaccounted assertion: {faults:?}"
    );
    assert!(
        render(&faults).contains("Do not adjust the number without deciding which happened"),
        "the refusal must refuse the lazy repair"
    );
}

#[test]
fn deleting_an_ungoverned_assertion_also_breaks_the_census() {
    // Conservation is an equality, not a ceiling: silent removal is caught too.
    let readme = read_doc("README.md").replacen("dual-engine", "two-engine", 1);
    let faults = scan(
        &CLAIM_MATRIX,
        &CONCEPT_CENSUS,
        &EVIDENCE_CITATIONS,
        real_with("README.md", readme),
    )
    .expect_err("an assertion removed anywhere must break conservation");
    assert!(
        faults
            .iter()
            .any(|fault| matches!(fault, WitnessFault::CensusDrift { .. })),
        "{faults:?}"
    );
}

#[test]
fn the_governed_half_of_the_census_is_computed_not_declared() {
    // If this were a hand-maintained number it could drift from the matrix it describes.
    let from_matrix = governed_occurrences(&CLAIM_MATRIX, "dual-engine");
    let by_hand: usize = CLAIM_MATRIX
        .iter()
        .flat_map(|row| row.sites.iter())
        .filter(|site| site.text.contains("dual-engine"))
        .count();
    assert_eq!(
        from_matrix, by_hand,
        "the census's governed count must come from the rows themselves"
    );
    assert!(
        from_matrix > 0,
        "the dual-engine claim is governed somewhere"
    );
}

// ---------------------------------------------------------------------------
// Structural failures
// ---------------------------------------------------------------------------

#[test]
fn an_unreadable_governed_document_is_inconclusive_never_a_pass() {
    let target = row("B3-DUAL-ENGINE");
    let faults = scan(&[*target], &[], &[], |_document| {
        Err("permission denied".to_string())
    })
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
    let faults = scan(&[target, target], &[], &[], real_reader())
        .expect_err("one row would shadow the other");
    assert!(
        faults.iter().any(|fault| matches!(
            fault,
            WitnessFault::DuplicateClaimId { id } if id == target.id
        )),
        "{faults:?}"
    );
}

#[test]
fn a_row_with_no_sites_is_refused() {
    let empty = ClaimRow {
        sites: &[],
        ..*row("TACTICS-ON-GOLEM")
    };
    let faults = scan(&[empty], &[], &[], real_reader()).expect_err("a row that decides nothing");
    assert!(
        matches!(faults.first(), Some(WitnessFault::EmptyClaimRow { .. })),
        "{faults:?}"
    );
}

#[test]
fn the_gate_reports_every_disagreement_at_once_and_deterministically() {
    let enforced = row("OLEAN-WRITE-CRATE-HEADER");
    let acknowledged = row("DAEMON-WARM-ATTACH-SLO");
    let docs = BTreeMap::from([
        (
            enforced.sites[0].document,
            format!("regressed: {}", enforced.sites[0].text),
        ),
        (acknowledged.sites[0].document, "nothing here".to_string()),
    ]);
    let faults =
        scan(&[*enforced, *acknowledged], &[], &[], planted(docs.clone())).expect_err("two faults");
    assert_eq!(
        faults.len(),
        2,
        "both directions in one run, not stop at the first: {faults:?}"
    );

    let again = scan(&[*enforced, *acknowledged], &[], &[], planted(docs)).expect_err("two faults");
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
        assert!(!row.sites.is_empty(), "{}: a row without sites", row.id);
        for site in row.sites {
            assert!(!site.text.is_empty(), "{}: empty anchor", row.id);
            assert!(!site.document.is_empty(), "{}: empty document", row.id);
        }
        assert!(
            row.evidence.len() > 60,
            "{}: evidence must say what the tree supports, not restate the state",
            row.id
        );

        match row.enforcement {
            // A standing overclaim cannot be certified by the matrix that records it.
            Enforcement::Acknowledged => assert!(
                !matches!(row.state, ClaimState::Observed | ClaimState::Proven),
                "{}: an acknowledged overclaim cannot be OBSERVED or PROVEN",
                row.id
            ),
            // A supported row is the opposite: it exists to record an earned claim.
            Enforcement::Supported => assert!(
                matches!(row.state, ClaimState::Observed | ClaimState::Proven),
                "{}: a Supported row must be OBSERVED or PROVEN, else it is not supported",
                row.id
            ),
            Enforcement::Enforced => {}
        }
    }
}

#[test]
fn every_census_declares_why_its_remainder_is_ungoverned() {
    for census in &CONCEPT_CENSUS {
        assert!(
            !census.keyword.is_empty(),
            "{}: empty keyword",
            census.concept
        );
        assert!(
            !census.documents.is_empty(),
            "{}: a census over no documents",
            census.concept
        );
        assert!(
            census.allowance_reason.len() > 60,
            "{}: an undeclared remainder is a silent gap, which is the failure the census \
             exists to prevent",
            census.concept
        );
    }
}
