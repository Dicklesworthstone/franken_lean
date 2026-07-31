//! `campaign_owner_matrix` — the named suite for td9's second campaign framework:
//! the machine-checked downstream owner matrix (`ci/CAMPAIGN_OWNER_MATRIX.txt` and
//! `fln_conformance::campaign::OwnerMatrix`).
//!
//! # The laws proven here
//!
//! The gate law in both directions (a registered-but-inactive adapter satisfies
//! nothing; only green satisfies, and green is unwritable without evidence), the
//! totality law (every bead-assigned domain adapted; every FL-INV id fed), the
//! real-owner law (every owner bead exists in the tracker), and the parse honesty
//! laws (unknown tokens refused with their line; duplicates are findings; the
//! schema token is exact). The committed matrix is validated against the real
//! tracker, and its current all-registered state is pinned so the first
//! activation is a deliberate, evidenced, disclosed edit — never a silent green.

#![forbid(unsafe_code)]

use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

use fln_conformance::campaign::{
    AdapterState, CampaignFamily, MatrixError, OwnerMatrix, all_inv_ids, MATRIX_DOMAINS,
    OWNER_MATRIX_SCHEMA,
};

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

fn matrix_text() -> String {
    let path = root().join("ci/CAMPAIGN_OWNER_MATRIX.txt");
    fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the owner matrix must exist at {}: {e}", path.display()))
}

fn real_bead_ids() -> BTreeSet<String> {
    let path = root().join(".beads/issues.jsonl");
    let text = fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the tracker export must exist at {}: {e}", path.display()));
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| {
            let needle = "\"id\":\"";
            let at = l.find(needle).expect("every tracker row carries an id") + needle.len();
            let rest = &l[at..];
            rest[..rest.find('"').expect("the id is quoted")].to_string()
        })
        .collect()
}

// ---------------------------------------------------------------------------
// The committed matrix, against the real tracker
// ---------------------------------------------------------------------------

#[test]
fn the_committed_matrix_parses_and_validates_clean() {
    let text = matrix_text();
    let matrix = OwnerMatrix::parse(&text).expect("the committed matrix must parse");
    assert_eq!(
        matrix.adapters.len(),
        12,
        "the twelve adapter rows are the bead's own mapping: grammar-source x3, \
         kernel-terms x1, olean-read x2, olean-write x2, vm-opcodes x2, \
         cas-manifest x1, server-editor x1"
    );
    assert_eq!(matrix.invariants.len(), 6, "six invariant campaign bindings");
    let beads = real_bead_ids();
    let errors = matrix.validate(|id| beads.contains(id));
    assert!(
        errors.is_empty(),
        "the committed matrix must validate against the real tracker:\n{}",
        errors
            .iter()
            .map(|e| format!("  {e}"))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn every_declared_domain_is_adapted_and_every_invariant_is_fed() {
    let matrix = OwnerMatrix::parse(&matrix_text()).expect("parse");
    for domain in MATRIX_DOMAINS {
        assert!(
            matrix.adapters.iter().any(|row| row.domain == domain),
            "domain {domain} has no adapter row"
        );
    }
    for inv_id in all_inv_ids() {
        assert!(
            matrix
                .invariants
                .iter()
                .any(|row| row.inv_ids.iter().any(|id| *id == inv_id)),
            "{inv_id} is fed by no campaign row"
        );
    }
    // The design law's named bindings, exactly: the thread matrix is the standing
    // FL-INV-01 lane; facade perturbations feed FL-INV-03; codec corruption feeds
    // FL-INV-04; stale/forged/cache-input feeds FL-INV-05; engine-admission feeds
    // FL-INV-02 and FL-INV-06; cancellation/resource promotion feeds FL-INV-07.
    let expect: [(&str, &str); 7] = [
        ("thread-matrix", "FL-INV-01"),
        ("facade-perturbation", "FL-INV-03"),
        ("codec-corruption", "FL-INV-04"),
        ("stale-forged-cache", "FL-INV-05"),
        ("engine-admission", "FL-INV-02"),
        ("engine-admission", "FL-INV-06"),
        ("cancellation-resource", "FL-INV-07"),
    ];
    for (campaign, inv_id) in expect {
        assert!(
            matrix
                .invariants
                .iter()
                .any(|row| row.campaign == campaign && row.inv_ids.iter().any(|id| id == inv_id)),
            "the design law binds {campaign} to {inv_id}"
        );
    }
}

#[test]
fn the_committed_matrix_is_honestly_all_registered_today() {
    // The anti-overclaim pin: nothing is active, nothing is green, no downstream
    // gate is satisfied by this file today. Moving a row to active/green requires
    // evidence (parse-enforced) AND updating this pin in the same change — the
    // first activation is a deliberate, disclosed edit, matching the bead's law
    // that a downstream gate cannot close until its adapter is active and green.
    let matrix = OwnerMatrix::parse(&matrix_text()).expect("parse");
    for row in &matrix.adapters {
        assert_eq!(
            row.state,
            AdapterState::Registered,
            "line {}: ({}, {}) claims more than registered — that move needs evidence \
             and this pin updated in the same change",
            row.line,
            row.domain,
            row.family.token()
        );
        assert!(
            !matrix.satisfies_downstream_gate(&row.domain, row.family),
            "no gate is satisfied today, and ({}, {}) must not be the first silent one",
            row.domain,
            row.family.token()
        );
    }
}

// ---------------------------------------------------------------------------
// The gate law, both directions, on planted matrices
// ---------------------------------------------------------------------------

fn planted(state_line: &str) -> String {
    format!(
        "schema {OWNER_MATRIX_SCHEMA}\n\
         adapter grammar-source | mutation | fln-7li | {state_line}\n\
         adapter kernel-terms | mutation | b1 | registered |\n\
         adapter olean-read | mutation | b1 | registered |\n\
         adapter olean-write | mutation | b1 | registered |\n\
         adapter vm-opcodes | mutation | b1 | registered |\n\
         adapter cas-manifest | fault-drill | b1 | registered |\n\
         adapter server-editor | fault-drill | b1 | registered |\n\
         invariant a | FL-INV-01\ninvariant b | FL-INV-02\ninvariant c | FL-INV-03\n\
         invariant d | FL-INV-04\ninvariant e | FL-INV-05\ninvariant f | FL-INV-06\n\
         invariant g | FL-INV-07\n"
    )
}

#[test]
fn a_registered_adapter_cannot_satisfy_but_a_green_one_can() {
    let registered = OwnerMatrix::parse(&planted("registered |")).expect("parse");
    assert!(
        !registered.satisfies_downstream_gate("grammar-source", CampaignFamily::Mutation),
        "a registered-but-inactive adapter satisfies nothing — the bead's exact law"
    );
    let active = OwnerMatrix::parse(&planted("active | wired in commit abc123 |")).expect("parse");
    assert!(
        !active.satisfies_downstream_gate("grammar-source", CampaignFamily::Mutation),
        "active is necessary but not sufficient: only green satisfies"
    );
    let green = OwnerMatrix::parse(&planted("green | run receipt sha256:deadbeef |")).expect("parse");
    assert!(
        green.satisfies_downstream_gate("grammar-source", CampaignFamily::Mutation),
        "a green adapter with named run evidence satisfies its gate"
    );
}

#[test]
fn the_gate_is_unsatisfiable_by_an_undeclared_adapter() {
    let matrix = OwnerMatrix::parse(&planted("registered |")).expect("parse");
    assert!(
        !matrix.satisfies_downstream_gate("grammar-source", CampaignFamily::Fuzz),
        "the planted matrix declares no fuzz adapter for grammar-source; an absent \
         adapter satisfies nothing"
    );
}

// ---------------------------------------------------------------------------
// The parse honesty laws, planted
// ---------------------------------------------------------------------------

#[test]
fn an_active_or_green_row_without_evidence_is_refused() {
    let err = OwnerMatrix::parse(&planted("active |")).expect_err("evidence-less active");
    assert_eq!(
        err,
        MatrixError::StateWithoutEvidence {
            line: 2,
            state: "active"
        }
    );
    let err = OwnerMatrix::parse(&planted("green |")).expect_err("evidence-less green");
    assert_eq!(
        err,
        MatrixError::StateWithoutEvidence {
            line: 2,
            state: "green"
        }
    );
}

#[test]
fn unknown_tokens_are_refused_with_their_line() {
    let mut text = planted("registered |");
    text = text.replacen("mutation | fln-7li", "alchemy | fln-7li");
    assert_eq!(
        OwnerMatrix::parse(&text),
        Err(MatrixError::UnknownFamily {
            line: 2,
            token: "alchemy".to_string()
        })
    );

    let mut text = planted("registered |");
    text = text.replacen("FL-INV-03", "FL-INV-99");
    assert_eq!(
        OwnerMatrix::parse(&text),
        Err(MatrixError::UnknownInvariant {
            line: 11,
            token: "FL-INV-99".to_string()
        })
    );

    let mut text = planted("registered |");
    text = text.replacen("registered |\nadapter kernel-terms", "golden |\nadapter kernel-terms");
    assert_eq!(
        OwnerMatrix::parse(&text),
        Err(MatrixError::UnknownState {
            line: 2,
            token: "golden".to_string()
        })
    );
}

#[test]
fn a_missing_schema_or_a_wrong_token_is_refused() {
    let text = planted("registered |");
    let no_schema = text.replacen(&format!("schema {OWNER_MATRIX_SCHEMA}\n"), "");
    assert!(matches!(
        OwnerMatrix::parse(&no_schema),
        Err(MatrixError::Schema { .. })
    ));
    let wrong = text.replacen(OWNER_MATRIX_SCHEMA, "fln-campaign-owner-matrix/0");
    assert!(matches!(
        OwnerMatrix::parse(&wrong),
        Err(MatrixError::Schema { .. })
    ));
}

#[test]
fn semantic_findings_are_all_reported_not_just_the_first() {
    // A duplicate adapter AND an unknown domain AND an unknown bead: three findings
    // in one pass, each with its line — a broken matrix is diagnosed whole.
    let mut text = planted("registered |");
    text.push_str("adapter grammar-source | mutation | fln-7li | registered |\n");
    text.push_str("adapter nowhere-ville | mutation | ghost-bead | registered |\n");
    let matrix = OwnerMatrix::parse(&text).expect("parse succeeds; validation finds");
    let errors = matrix.validate(|id| id == "fln-7li" || id == "b1");
    let kinds: Vec<String> = errors.iter().map(|e| e.to_string()).collect();
    assert!(
        kinds.iter().any(|k| k.contains("already declared")),
        "the duplicate is a finding: {kinds:?}"
    );
    assert!(
        kinds.iter().any(|k| k.contains("nowhere-ville")),
        "the unknown domain is a finding: {kinds:?}"
    );
    assert!(
        kinds.iter().any(|k| k.contains("ghost-bead")),
        "the unknown owner bead is a finding: {kinds:?}"
    );
}
