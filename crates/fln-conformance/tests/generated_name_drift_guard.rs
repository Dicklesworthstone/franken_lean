//! Suite `generated_name_drift_guard` (bead fln-7gr6): governed machine artifacts
//! — the ci/ text artifacts (closure allowlist, workspace graph, parity ledger,
//! contract-ownership rows) and the extracted contracts/ inventories — can never
//! reintroduce a reserved subsystem name. Machine artifacts carry labels, not
//! prose, so any reserved-name occurrence without an owner citation is drift.
//! Each seeded drift mutant is killed by this lane for its intended reason.

#![forbid(unsafe_code)]

use fln_conformance::naming::{self, SurfaceClass};

fn contract_registry() -> naming::Registry {
    naming::load_registry(&naming::scan_root()).expect("real registry loads")
}

/// Scan, refusing an unreadable governed surface rather than censusing what is left.
///
/// One site per suite: `scan_tree` reports the condition typed (`fln-y0f7` R2), and the
/// panic belongs at the test boundary, not in `src/`.
fn scan(root: &std::path::Path, registry: &naming::Registry) -> naming::ScanReport {
    naming::scan_tree(root, registry)
        .unwrap_or_else(|error| panic!("the governed surfaces must all be readable: {error}"))
}

#[test]
fn real_ci_artifacts_are_drift_free() {
    let root = naming::scan_root();
    let registry = contract_registry();
    let report = scan(&root, &registry);
    let ci_findings: Vec<_> = report
        .stale
        .iter()
        .filter(|finding| finding.class == SurfaceClass::Ci)
        .collect();
    assert!(ci_findings.is_empty(), "ci artifact drift: {ci_findings:?}");
    assert!(
        report
            .scanned
            .iter()
            .any(|(class, path)| *class == SurfaceClass::Ci && path == "ci/CLOSURE_ALLOWLIST.txt"),
        "the closure allowlist was in the census"
    );
}

#[test]
fn real_contract_inventories_are_drift_free() {
    let root = naming::scan_root();
    let registry = contract_registry();
    let report = scan(&root, &registry);
    let contract_findings: Vec<_> = report
        .stale
        .iter()
        .filter(|finding| finding.class == SurfaceClass::Contracts)
        .collect();
    assert!(
        contract_findings.is_empty(),
        "generated contract drift: {contract_findings:?}"
    );
}

#[test]
fn the_closure_allowlist_carries_the_vellum_label() {
    let root = naming::scan_root();
    let allowlist =
        std::fs::read_to_string(root.join("ci/CLOSURE_ALLOWLIST.txt")).expect("allowlist exists");
    let row = allowlist
        .lines()
        .find(|line| line.starts_with("package fln-parse "))
        .expect("fln-parse row exists");
    assert!(
        row.contains("reason=§21 crate map: Vellum parser engine"),
        "fln-parse label regressed: {row}"
    );
}

// --- named drift mutants ---------------------------------------------------------

#[test]
fn mutant_generated_artifact_label_is_killed() {
    // "… one generated artifact …": the allowlist reason label flips back.
    let root = naming::scan_root();
    let registry = contract_registry();
    let real =
        std::fs::read_to_string(root.join("ci/CLOSURE_ALLOWLIST.txt")).expect("allowlist exists");
    let mutated = real.replace(
        "reason=§21 crate map: Vellum parser engine",
        "reason=§21 crate map: Quill parser engine",
    );
    assert_ne!(mutated, real, "mutant must change the artifact");
    let findings = naming::scan_text(
        SurfaceClass::Ci,
        "ci/CLOSURE_ALLOWLIST.txt",
        &mutated,
        &registry,
    );
    assert_eq!(
        findings.len(),
        1,
        "exactly the flipped label is drift: {findings:?}"
    );
    assert!(findings[0].excerpt.contains("fln-parse"));
}

#[test]
fn mutant_dashboard_row_is_killed() {
    // "… one dashboard row …": evidence dashboards are governed row-per-symbol
    // text artifacts; a row label adopting the reserved name is drift.
    let registry = contract_registry();
    let mutated = "schema fln-parity-ledger/1\n\
        row source | Quill.parse.example | decl | parity | L2 | sound | reference \
        | syntactic | fixtures/example.txt | D0 | OBSERVED | run-000\n";
    let findings = naming::scan_text(SurfaceClass::Ci, "ci/PARITY_LEDGER.txt", mutated, &registry);
    assert_eq!(
        findings.len(),
        1,
        "the dashboard row is drift: {findings:?}"
    );
    assert_eq!(findings[0].line, 2);
}

#[test]
fn mutant_schema_identifier_is_killed() {
    // "… one schema label …": a generated schema identifier exposing a subsystem
    // name must use current vocabulary.
    let registry = contract_registry();
    let mutated = "{\"schema\":\"fln-quill-syntax-tree/1\",\"nodes\":[]}\n";
    let findings = naming::scan_text(
        SurfaceClass::Contracts,
        "contracts/syntax_inventory.json",
        mutated,
        &registry,
    );
    assert_eq!(findings.len(), 1, "the schema label is drift: {findings:?}");
    assert_eq!(findings[0].name.to_ascii_lowercase(), "quill");
}

#[test]
fn owner_cited_registry_rows_are_not_drift() {
    // The registry's own Quill row cites frankensearch — that is the reservation,
    // not drift (and the registry file itself is a validated exemption).
    let registry = contract_registry();
    let row = registry.find("Quill").expect("Quill row exists");
    assert!(
        naming::reserved_use_is_cited(
            &format!("row Quill | {} | lexical engine", row.owner),
            &row.owner
        ),
        "the owner-context law accepts the reservation row"
    );
}
