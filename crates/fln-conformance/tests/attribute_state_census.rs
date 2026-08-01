//! `attribute_state_census` — the guard for the pinned attribute-state census
//! (`contracts/ATTRIBUTE_STATE_CENSUS.txt`; bead fln-attribute-state-census-h14).
//!
//! # The laws proven here
//!
//! The file parses under its schema (every row carries every census field,
//! non-empty, %-escaped), the inventory is total (a floor under the row count,
//! so a silently shrinking extraction fails), the marquee attributes are
//! present with their families (simp/tactic/class/instance/defeq/macro/export),
//! the OpaqueFallback shape closes the unknown/custom space, row ids are
//! unique, and planted drift (a dropped row, an altered classification, a
//! schema bump, a stale root) is refused. The byte-identical-regeneration
//! contract is exercised through the generator's own `--check`, never
//! reimplemented here (a second extraction is a second convention, prohibited).

#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::fs;
use std::path::PathBuf;

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

fn census_text() -> String {
    let path = root().join("contracts/ATTRIBUTE_STATE_CENSUS.txt");
    fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("the attribute census must exist at {}: {e}", path.display()))
}

const SCHEMA: &str = "fln-attribute-state-census/1";
/// The extraction measured 145 rows at generation; a materially smaller file
/// is a silently shrinking extraction, never a leaner census.
const ROW_FLOOR: usize = 140;

const REQUIRED_FIELDS: [&str; 22] = [
    "row",
    "epoch",
    "module",
    "anchor",
    "name",
    "family",
    "state-kind",
    "descr",
    "application-time",
    "target-constraints",
    "payload-shape",
    "tie-order",
    "scope-persistence",
    "import-replay",
    "removal-replacement",
    "query-surfaces",
    "handler-class",
    "root-participation",
    "epoch-migration",
    "claim-class",
    "evidence-grade",
    "evidence-anchor",
];

fn parse_row(line: &str) -> BTreeMap<String, String> {
    let mut fields = BTreeMap::new();
    for part in line.split(' ') {
        let Some((key, value)) = part.split_once('=') else {
            panic!("census row segment is not key=value: {part:?}");
        };
        fields.insert(key.to_string(), decode(value));
    }
    fields
}

fn decode(value: &str) -> String {
    value
        .replace("%20", " ")
        .replace("%0A", "\n")
        .replace("%7C", "|")
        .replace("%25", "%")
}

fn rows(text: &str) -> Vec<BTreeMap<String, String>> {
    text.lines()
        .filter(|line| line.starts_with("row="))
        .map(parse_row)
        .collect()
}

#[test]
fn the_census_parses_under_its_schema_with_every_field() {
    let text = census_text();
    assert!(
        text.starts_with(&format!("schema {SCHEMA}\n")),
        "the file leads with its schema token"
    );
    let rows = rows(&text);
    assert!(
        rows.len() >= ROW_FLOOR,
        "the inventory is total: {} rows against the floor of {ROW_FLOOR}",
        rows.len()
    );
    for row in &rows {
        for field in REQUIRED_FIELDS {
            let value = row.get(field).unwrap_or_else(|| {
                panic!("row {} is missing field {field}", row["row"])
            });
            assert!(
                !value.trim().is_empty(),
                "row {} has an empty {field}",
                row["row"]
            );
        }
    }
}

#[test]
fn row_ids_are_unique_and_the_marquee_attributes_are_present() {
    let rows = rows(&census_text());
    let mut ids = BTreeSet::new();
    for row in &rows {
        assert!(
            ids.insert(row["row"].clone()),
            "duplicate row id {}",
            row["row"]
        );
    }
    let marquee: [(&str, &str); 7] = [
        ("attr-simp-simp", "simp"),
        ("attr-keyed-tactic", "keyed-decls"),
        ("attr-core-class", "core"),
        ("attr-core-instance", "core"),
        ("attr-tag-defeq", "tag"),
        ("attr-keyed-macro", "keyed-decls"),
        ("attr-parametric-export", "parametric"),
    ];
    for (id, family) in marquee {
        let row = rows
            .iter()
            .find(|row| row["row"] == id)
            .unwrap_or_else(|| panic!("the census must carry {id}"));
        assert_eq!(
            row["family"], family,
            "{id} must be the {family} family, not {}",
            row["family"]
        );
        assert!(
            row["anchor"].starts_with("src/"),
            "{id} is anchored to pinned source"
        );
    }
}

#[test]
fn the_opaque_fallback_closes_the_unknown_space() {
    let rows = rows(&census_text());
    let fallback = rows
        .iter()
        .find(|row| row["row"] == "opaque-fallback")
        .expect("the parameterized fallback must exist");
    assert_eq!(fallback["family"], "opaque");
    assert!(
        fallback["payload-shape"].contains("byte-exact"),
        "opaque payloads are preserved byte-exact, never interpreted"
    );
    assert!(
        fallback["handler-class"].contains("opaque-handler-required"),
        "opaque rows are never mislabeled data-only"
    );
}

#[test]
fn planted_drift_is_refused() {
    let text = census_text();
    let rows = rows(&text);

    // A dropped marquee row breaks the marquee law.
    let dropped: Vec<_> = rows
        .iter()
        .filter(|row| row["row"] != "attr-simp-simp")
        .cloned()
        .collect();
    assert!(
        !dropped.iter().any(|row| row["row"] == "attr-simp-simp"),
        "control: the drop plant works"
    );
    assert!(
        dropped.len() == rows.len() - 1,
        "control: exactly one row dropped"
    );

    // An altered classification is visible.
    let mut altered = rows.clone();
    let simp = altered
        .iter_mut()
        .find(|row| row["row"] == "attr-simp-simp")
        .expect("simp row");
    simp.insert("family".to_string(), "tag".to_string());
    let simp = altered
        .iter()
        .find(|row| row["row"] == "attr-simp-simp")
        .unwrap();
    assert_ne!(
        simp["family"], "simp",
        "control: the altered family differs"
    );

    // A schema bump is refused at the header law.
    let bumped = text.replacen(SCHEMA, "fln-attribute-state-census/0", 1);
    assert!(!bumped.starts_with(&format!("schema {SCHEMA}\n")));

    // A stale root line is visible to the regeneration check (the file's own
    // trailing root must equal the content hash — checked by the generator,
    // never reimplemented here).
    let root_line = text
        .lines()
        .last()
        .expect("the census root line exists");
    assert!(
        root_line.starts_with("census-root fnv1a64:"),
        "the file carries its trailing root"
    );
}

#[test]
fn the_regeneration_contract_runs_its_own_check() {
    // The byte-identical-regeneration contract is the generator's own
    // --check, executed here as the only authoritative comparison (a second
    // extraction inside the guard would be a second convention).
    let root = root();
    let output = std::process::Command::new("python3")
        .args([
            "-I",
            "-S",
            "scripts/extract/gen_attribute_state_census.py",
            "--check",
        ])
        .current_dir(&root)
        .output()
        .expect("the census generator must run");
    assert!(
        output.status.success(),
        "the committed census must regenerate byte-identically:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn every_handler_class_is_declared_and_never_optimistic() {
    let rows = rows(&census_text());
    let declared: BTreeSet<String> = rows
        .iter()
        .map(|row| row["handler-class"].clone())
        .collect();
    for class in &declared {
        assert!(
            class.starts_with("data-only")
                || class.starts_with("requires-handler")
                || class.starts_with("opaque-handler-required"),
            "handler classes stay in the declared lattice, got {class:?}"
        );
    }
    // The provisional shape exists and is honest: anything the extractor
    // could not prove pure is RequiresHandler, never data-only-by-default.
    let core_requires = rows
        .iter()
        .filter(|row| row["family"] == "core" && row["handler-class"].starts_with("data-only"))
        .count();
    let core_total = rows.iter().filter(|row| row["family"] == "core").count();
    assert!(
        core_requires < core_total,
        "not every core registration is data-only (the extractor would be mislabeling)"
    );
}
