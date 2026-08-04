//! Suite `subsystem_name_registry` (bead fln-7gr6): the REAL suite-wide registry
//! must parse, collision-validate, carry the Vellum/Quill reservation contract, and
//! refuse interrupted candidate publications — and every malformed-registry mutant
//! must be killed for its intended, typed reason.
//!
//! The scan root honors `FLN_NAMING_ROOT` (the e2e harness's scratch-fixture
//! override, recorded in evidence per step); default is the workspace root.

#![forbid(unsafe_code)]

use fln_conformance::naming::{self, REGISTRY_PATH, REGISTRY_SCHEMA, RegistryError, Status};

fn registry_text() -> String {
    std::fs::read_to_string(naming::scan_root().join(REGISTRY_PATH)).expect("registry exists")
}

#[test]
fn the_real_registry_parses_and_validates() {
    let registry = naming::load_registry(&naming::scan_root()).unwrap_or_else(|error| {
        panic!("registry gate failed: {error}");
    });
    assert!(!registry.rows.is_empty(), "the registry has rows");
}

#[test]
fn the_vellum_and_quill_contract_rows_are_present() {
    let registry = naming::load_registry(&naming::scan_root()).unwrap_or_else(|error| {
        panic!("registry gate failed: {error}");
    });

    let vellum = registry.find("Vellum").expect("Vellum row exists");
    assert_eq!(vellum.owner, "franken_lean");
    assert_eq!(vellum.status, Status::Active);
    assert!(
        vellum.crates.iter().any(|krate| krate == "fln-parse")
            && vellum.crates.iter().any(|krate| krate == "fln-syntax"),
        "Vellum governs fln-parse and fln-syntax, found {:?}",
        vellum.crates
    );

    let quill = registry.find("Quill").expect("Quill row exists");
    assert_eq!(
        quill.owner, "frankensearch",
        "Quill is reserved for the Frankensearch lexical engine"
    );
    assert_eq!(quill.status, Status::Reserved);
}

#[test]
fn every_load_bearing_codename_is_registered() {
    let registry = naming::load_registry(&naming::scan_root()).unwrap_or_else(|error| {
        panic!("registry gate failed: {error}");
    });
    for name in [
        "Marrow",
        "Grimoire",
        "Crucible",
        "Vellum",
        "Athanor",
        "Synod",
        "Golem",
        "Iron",
        "Anvil",
        "Verdict",
        "Ledger",
        "Lantern",
        "Palimpsest",
        "Bloodhound",
        "Folio",
        "Envoy",
        "WASM Judge",
        "Tribunal",
    ] {
        let row = registry
            .find(name)
            .unwrap_or_else(|| panic!("codename `{name}` is unregistered"));
        assert_eq!(
            row.owner, "franken_lean",
            "`{name}` is a FrankenLean codename"
        );
        assert_eq!(row.status, Status::Active);
    }
}

#[test]
fn registered_crates_exist_in_the_closure_allowlist() {
    let root = naming::scan_root();
    let registry = naming::load_registry(&root).unwrap_or_else(|error| {
        panic!("registry gate failed: {error}");
    });
    let allowlist =
        std::fs::read_to_string(root.join("ci/CLOSURE_ALLOWLIST.txt")).expect("allowlist exists");
    for row in &registry.rows {
        for krate in &row.crates {
            assert!(
                allowlist.lines().any(|line| line.starts_with("package ")
                    && line.split_whitespace().nth(1) == Some(krate.as_str())),
                "registry row `{}` claims crate `{krate}` absent from the closure allowlist",
                row.name
            );
        }
    }
    let fln_parse_row = allowlist
        .lines()
        .find(|line| line.starts_with("package fln-parse "))
        .expect("fln-parse allowlist row exists");
    assert!(
        fln_parse_row.contains("Vellum parser engine"),
        "the fln-parse allowlist label uses the Vellum vocabulary: {fln_parse_row}"
    );
}

#[test]
fn no_interrupted_candidate_publication_is_present() {
    let candidate = naming::scan_root().join(format!("{REGISTRY_PATH}.candidate"));
    assert!(
        !candidate.exists(),
        "stale candidate publication present: {}",
        candidate.display()
    );
}

// --- named mutants: each malformed registry fails for the INTENDED reason -------

#[test]
fn mutant_schema_label_is_killed() {
    let mutated = registry_text().replace(
        &format!("schema {REGISTRY_SCHEMA}"),
        "schema fln-subsystem-registry/999",
    );
    assert_ne!(mutated, registry_text(), "mutant must change the artifact");
    match naming::parse_registry(&mutated) {
        Err(RegistryError::UnsupportedSchema { found }) => {
            assert_eq!(found, "fln-subsystem-registry/999");
        }
        other => panic!("MUTANT-SURVIVED schema_label: {other:?}"),
    }
}

#[test]
fn mutant_missing_schema_is_killed() {
    let mutated: String = registry_text()
        .lines()
        .filter(|line| !line.trim().starts_with("schema "))
        .map(|line| format!("{line}\n"))
        .collect();
    match naming::parse_registry(&mutated) {
        Err(RegistryError::MissingSchema) => {}
        other => panic!("MUTANT-SURVIVED missing_schema: {other:?}"),
    }
}

#[test]
fn mutant_malformed_row_is_killed() {
    let mutated = format!("{}row OnlyThreeFields | x | y\n", registry_text());
    match naming::parse_registry(&mutated) {
        Err(RegistryError::MalformedRow { detail, .. }) => {
            assert!(detail.contains("7"), "reason names the arity law: {detail}");
        }
        other => panic!("MUTANT-SURVIVED malformed_row: {other:?}"),
    }
}

#[test]
fn mutant_unknown_status_is_killed() {
    let mutated = format!(
        "{}row Phantom | franken_lean | ghost scope | - | - | tentative | ghost row\n",
        registry_text()
    );
    match naming::parse_registry(&mutated) {
        Err(RegistryError::UnknownStatus { status, .. }) => assert_eq!(status, "tentative"),
        other => panic!("MUTANT-SURVIVED unknown_status: {other:?}"),
    }
}

#[test]
fn stale_candidate_fails_typed_and_recovery_is_exact() {
    // ubs:ignore — scratch-directory disambiguator for parallel test runs, not a secret.
    let scratch = std::path::Path::new(env!("CARGO_TARGET_TMPDIR"))
        .join(format!("naming-candidate-{}", std::process::id())); // ubs:ignore — not a token.
    let ci_dir = scratch.join("ci");
    std::fs::create_dir_all(&ci_dir).expect("scratch ci dir");
    let published = registry_text();
    std::fs::write(scratch.join(REGISTRY_PATH), &published).expect("publish registry");
    // An interrupted publication: a half-written candidate beside the published file.
    let candidate_path = scratch.join(format!("{REGISTRY_PATH}.candidate"));
    let truncated = &published.as_bytes()[..published.len() / 2];
    std::fs::write(&candidate_path, truncated).expect("write candidate");
    match naming::load_registry(&scratch) {
        Err(RegistryError::StaleCandidate { candidate }) => {
            assert_eq!(candidate, format!("{REGISTRY_PATH}.candidate"));
        }
        other => panic!("MUTANT-SURVIVED stale_candidate: {other:?}"),
    }
    // Recovery: discard the candidate; the published artifact must be byte-exact
    // and the gate green again.
    std::fs::remove_file(&candidate_path).expect("discard candidate");
    let recovered = std::fs::read_to_string(scratch.join(REGISTRY_PATH)).expect("reread");
    assert_eq!(recovered, published, "publication was not disturbed");
    naming::load_registry(&scratch).expect("recovery run is green");
}
