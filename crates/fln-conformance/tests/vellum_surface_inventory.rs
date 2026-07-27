//! Suite `vellum_surface_inventory` (bead fln-7gr6): the REAL governed tree —
//! docs, source, ci artifacts, contracts, scripts, and mutable bead fields — holds
//! zero stale reserved-name references, every positive Vellum anchor is present,
//! the scan is deterministic (byte-identical canonical reports), and each seeded
//! vocabulary mutant is killed for its intended reason.
//!
//! The scan root honors `FLN_NAMING_ROOT` (the e2e scratch override); when
//! `FLN_NAMING_REPORT` is set, the canonical NDJSON report is written there for
//! the e2e determinism/byte-compare lanes.

#![forbid(unsafe_code)]

use fln_conformance::naming::{self, SurfaceClass};

/// Scan, refusing an unreadable governed surface rather than censusing what is left.
///
/// One site per suite: `scan_tree` reports the condition typed (`fln-y0f7` R2), and the
/// panic belongs at the test boundary, not in `src/`. Before that repair an absent tracker
/// was skipped in silence — `the_scan_is_deterministic` below then compared two scans that
/// had read no beads and PASSED, which the BeadsCurrent floor never covered.
fn scan(root: &std::path::Path, registry: &naming::Registry) -> naming::ScanReport {
    naming::scan_tree(root, registry)
        .unwrap_or_else(|error| panic!("the governed surfaces must all be readable: {error}"))
}

#[test]
fn the_real_tree_has_no_stale_reserved_names() {
    let root = naming::scan_root();
    naming::validate_exemptions(&root).unwrap_or_else(|missing| {
        panic!("dangling contract-definition exemptions: {missing:?}");
    });
    let registry = naming::load_registry(&root).unwrap_or_else(|error| {
        panic!("registry gate failed: {error}");
    });
    let report = scan(&root, &registry);
    assert!(
        !report.scanned.is_empty(),
        "the scan saw files (an empty census is not a clean tree)"
    );
    for required in [
        SurfaceClass::Docs,
        SurfaceClass::Source,
        SurfaceClass::Ci,
        SurfaceClass::Contracts,
        SurfaceClass::Scripts,
        SurfaceClass::BeadsCurrent,
    ] {
        assert!(
            report.scanned.iter().any(|(class, _)| *class == required),
            "the {} class was not scanned — a silently absent surface is not a \
             clean surface",
            required.label()
        );
    }
    // scripts/tribunal is governed script code, not the immutable epoch lab:
    // it must be inside the census, never name-skipped.
    assert!(
        report
            .scanned
            .iter()
            .any(|(_, path)| path.starts_with("scripts/tribunal/")),
        "scripts/tribunal fell out of the census"
    );
    let missing = naming::missing_anchors(&root);
    let rendered = naming::render_report_ndjson(&report, &missing);
    if let Ok(report_path) = std::env::var("FLN_NAMING_REPORT") {
        std::fs::write(&report_path, &rendered).expect("write canonical report");
    }
    assert!(
        report.stale.is_empty(),
        "stale reserved-name references in current vocabulary:\n{}",
        report
            .stale
            .iter()
            .map(|finding| format!(
                "  [{}] {}:{}{} `{}` — {}",
                finding.class.label(),
                finding.path,
                finding.line,
                finding
                    .field
                    .as_deref()
                    .map(|field| format!(" field={field}"))
                    .unwrap_or_default(),
                finding.name,
                finding.excerpt
            ))
            .collect::<Vec<_>>()
            .join("\n")
    );
}

#[test]
fn every_vellum_anchor_is_present() {
    let root = naming::scan_root();
    let missing = naming::missing_anchors(&root);
    assert!(
        missing.is_empty(),
        "missing Vellum anchors: {:?}",
        missing
            .iter()
            .map(|anchor| format!("{} ({})", anchor.path, anchor.what))
            .collect::<Vec<_>>()
    );
}

#[test]
fn the_scan_is_deterministic() {
    let root = naming::scan_root();
    let registry = naming::load_registry(&root).unwrap_or_else(|error| {
        panic!("registry gate failed: {error}");
    });
    let first = scan(&root, &registry);
    let second = scan(&root, &registry);
    assert_eq!(first, second, "two scans of one tree disagree");
    let rendered_first = naming::render_report_ndjson(&first, &naming::missing_anchors(&root));
    let rendered_second = naming::render_report_ndjson(&second, &naming::missing_anchors(&root));
    assert_eq!(
        rendered_first, rendered_second,
        "canonical report rendering is not byte-stable"
    );
    assert!(
        rendered_first.starts_with("{\"schema\":\"fln-naming-inventory/1\""),
        "the report carries its schema tag first"
    );
}

fn contract_registry() -> naming::Registry {
    naming::load_registry(&naming::scan_root()).expect("real registry loads")
}

// --- named vocabulary mutants: one defect each, killed for the intended reason ---

#[test]
fn mutant_bead_title_is_killed() {
    // "Mutants leave one title …": a mutable bead field re-adopts the reserved
    // name with no owner citation.
    let registry = contract_registry();
    let line = r#"{"id":"fln-mutant","title":"W4: Quill engine — Pratt parser slice","status":"open","comments":[{"id":1,"text":"immutable history may say Quill freely"}]}"#;
    let findings = naming::scan_beads_line(1, line, &registry);
    assert_eq!(
        findings.len(),
        1,
        "exactly the title is stale (comments are immutable history): {findings:?}"
    );
    assert_eq!(findings[0].field.as_deref(), Some("title"));
    assert_eq!(findings[0].name.to_ascii_lowercase(), "quill");
    assert_eq!(findings[0].path, ".beads/issues.jsonl#fln-mutant");
}

#[test]
fn bead_fields_citing_the_owner_are_legitimate() {
    // The reservation bead itself may say "Quill" — it cites Frankensearch.
    let registry = contract_registry();
    let line = r#"{"id":"fln-7gr6","title":"reserve Quill for Frankensearch and rename FrankenLean parser to Vellum","status":"in_progress"}"#;
    let findings = naming::scan_beads_line(1, line, &registry);
    assert!(
        findings.is_empty(),
        "owner-cited reservations are current vocabulary: {findings:?}"
    );
}

#[test]
fn mutant_plan_section_is_killed() {
    // "… one plan section …": a §9-style heading regresses to the reserved name.
    let registry = contract_registry();
    let mutated = "## 9. Quill: the parser & macro engine (fln-parse, fln-syntax)\n\
                   Prose that never cites the owning project.\n";
    let findings = naming::scan_text(
        SurfaceClass::Docs,
        "COMPREHENSIVE_PLAN_FOR_THE_DESIGN_OF_FRANKEN_LEAN.md",
        mutated,
        &registry,
    );
    assert_eq!(
        findings.len(),
        1,
        "the section heading is stale: {findings:?}"
    );
    assert_eq!(findings[0].line, 1);
    assert_eq!(findings[0].class, SurfaceClass::Docs);
}

#[test]
fn mutant_lowercase_variant_is_killed() {
    // "… lowercase variant …": case cannot launder a reserved name.
    let registry = contract_registry();
    let mutated = "//! the quill parser feeds the elaborator\n";
    let findings = naming::scan_text(
        SurfaceClass::Source,
        "crates/fln-parse/src/lib.rs",
        mutated,
        &registry,
    );
    assert_eq!(findings.len(), 1, "lowercase use is stale: {findings:?}");
    assert_eq!(findings[0].name.to_ascii_lowercase(), "quill");
}

#[test]
fn owner_cited_prose_is_not_flagged() {
    let registry = contract_registry();
    let text = "> Naming note: drafted as \"Quill\"; that name is reserved for the \
                Frankensearch lexical engine.\n";
    let findings = naming::scan_text(SurfaceClass::Docs, "README.md", text, &registry);
    assert!(
        findings.is_empty(),
        "owner-cited prose is legitimate: {findings:?}"
    );
}

#[test]
fn embedded_words_are_not_false_positives() {
    let registry = contract_registry();
    let text = "the tranquillity of a deterministic build\n";
    let findings = naming::scan_text(SurfaceClass::Docs, "README.md", text, &registry);
    assert!(findings.is_empty(), "word boundaries hold: {findings:?}");
}

#[test]
fn beads_json_field_extraction_is_structural() {
    // The extractor sees top-level strings only; nested comment text is invisible.
    let line = r#"{"id":"x","title":"a title","count":3,"nested":{"title":"inner"},"comments":[{"text":"deep"}],"design":"a design"}"#;
    let fields = naming::top_level_string_fields(line);
    assert_eq!(
        fields,
        vec![
            ("id".to_string(), "x".to_string()),
            ("title".to_string(), "a title".to_string()),
            ("design".to_string(), "a design".to_string()),
        ]
    );
}
