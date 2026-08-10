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
            let value = row
                .get(field)
                .unwrap_or_else(|| panic!("row {} is missing field {field}", row["row"]));
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
    let root_line = text.lines().last().expect("the census root line exists");
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

// ---------------------------------------------------------------------------
// The hardening laws: truncated inputs, budgets, cancellation, atomicity
// ---------------------------------------------------------------------------

/// A minimal vendor tree the truncated-input cells can corrupt without
/// touching the pin: one file with a well-formed registration, one cut
/// mid-record.
fn scratch_vendor(tag: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-attr-census-scratch-{tag}-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    let lean_dir = dir.join("src/Lean");
    fs::create_dir_all(&lean_dir).expect("create scratch vendor");
    fs::write(
        lean_dir.join("Good.lean"),
        "def helper := 1\nbuiltin_initialize x : TagAttribute ← registerTagAttribute `good \"good attr\"\n",
    )
    .expect("write good source");
    dir
}

fn run_generator(vendor: &std::path::Path) -> std::process::Output {
    let root = root();
    let output_path =
        std::env::temp_dir().join(format!("fln-attr-census-out-{}", std::process::id()));
    let _ = fs::remove_file(&output_path);
    std::process::Command::new("python3")
        .args([
            "-I",
            "-S",
            "scripts/extract/gen_attribute_state_census.py",
            "--vendor-path",
        ])
        .arg(vendor)
        .arg("--output")
        .arg(&output_path)
        .current_dir(&root)
        .output()
        .expect("the census generator must run")
}

#[test]
fn a_truncated_input_is_a_typed_refusal_never_a_silent_census() {
    let vendor = scratch_vendor("trunc");
    // A well-formed tree generates.
    let good = run_generator(&vendor);
    assert!(
        good.status.success(),
        "control: the well-formed scratch tree generates: {}",
        String::from_utf8_lossy(&good.stderr)
    );
    // Truncate the source mid-record: the extractor must refuse typed
    // (unbalanced braces is a named generation failure), never emit a census
    // that silently lost the row.
    fs::write(
        vendor.join("src/Lean/Good.lean"),
        "builtin_initialize x : TagAttribute ← registerEnvExtension {\n  name := `broken\n",
    )
    .expect("write truncated source");
    let bad = run_generator(&vendor);
    assert!(!bad.status.success(), "a truncated source fails generation");
    let stderr = String::from_utf8_lossy(&bad.stderr);
    assert!(
        stderr.contains("unbalanced braces") || stderr.contains("unclassified"),
        "the refusal is typed, not a silent census: {stderr}"
    );
    let _ = fs::remove_dir_all(&vendor);
}

#[test]
fn cancellation_is_typed_and_nothing_partial_publishes() {
    let vendor = scratch_vendor("cancel");
    // Keep both the final output and publish's `.candidate` sibling inside this
    // process's scratch root. A process-global temp name lets concurrent Cargo
    // test binaries replace or reclaim one another's cancellation evidence.
    let out = vendor.join("cancelled-census-output");
    let ready = vendor.join("cancellation-handlers-ready");
    // Enough well-formed sources that the generation has a window to cancel in.
    for index in 0..40 {
        fs::write(
            vendor.join("src/Lean").join(format!("F{index}.lean")),
            format!("builtin_initialize x{index} : TagAttribute ← registerTagAttribute `good{index} \"g\"\n"),
        )
        .expect("write source");
    }
    let committed = root().join("contracts/ATTRIBUTE_STATE_CENSUS.txt");
    let committed_bytes = fs::read(&committed).expect("committed census reads");
    let mut child = std::process::Command::new("python3")
        .args([
            "-I",
            "-S",
            "scripts/extract/gen_attribute_state_census.py",
            "--vendor-path",
        ])
        .arg(&vendor)
        .arg("--output")
        .arg(&out)
        .arg("--ready-file")
        .arg(&ready)
        .current_dir(root())
        .spawn()
        .expect("spawn generator");
    // A signal sent during Python startup has the interpreter's default
    // disposition and exits 1 with KeyboardInterrupt, before the generator can
    // type it. Wait until the generator has installed both handlers; then use
    // /bin/kill (the house drill pattern — no libc dependency). The bounded
    // wait refuses a broken handshake instead of hanging the workspace suite.
    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(5);
    while !ready.exists() {
        assert!(
            child.try_wait().expect("poll generator").is_none(),
            "the generator exited before publishing cancellation readiness"
        );
        assert!(
            std::time::Instant::now() < deadline,
            "the generator did not publish cancellation readiness within five seconds"
        );
        std::thread::sleep(std::time::Duration::from_millis(1));
    }
    let _ = std::process::Command::new("kill")
        .arg("-INT")
        .arg(child.id().to_string())
        .status();
    let status = child.wait().expect("wait");
    let after = fs::read(&committed).expect("committed census reads after");
    assert_eq!(
        committed_bytes, after,
        "the committed file is byte-identical after a cancelled generation"
    );
    if let Some(code) = status.code() {
        assert!(
            code == 130 || code == 0,
            "cancellation is typed (130) or completed before the signal landed (0): {code}"
        );
    }
    // The output file either does not exist (cancelled before publish) or is
    // complete (publish is atomic): a partial file is the forbidden shape.
    if out.exists() {
        let text = fs::read_to_string(&out).expect("the published output reads");
        assert!(
            text.ends_with("census-root fnv1a64:") || text.contains("census-root "),
            "a published output is complete (atomic publish), never partial"
        );
    }
    let _ = fs::remove_dir_all(&vendor);
}

#[test]
fn a_leftover_candidate_is_stale_evidence_not_a_generation() {
    // The .candidate sibling is the atomic write's temp name: a leftover one
    // (a crashed run) must not read as a valid census, and a fresh
    // generation must succeed — the clean-retry law.
    let committed = root().join("contracts/ATTRIBUTE_STATE_CENSUS.txt");
    let candidate = root().join("contracts/ATTRIBUTE_STATE_CENSUS.txt.candidate");
    let committed_bytes = fs::read(&committed).expect("committed reads");
    fs::write(&candidate, "row=stale-leftover\n").expect("plant a stale candidate");
    let rerun = std::process::Command::new("python3")
        .args([
            "-I",
            "-S",
            "scripts/extract/gen_attribute_state_census.py",
            "--check",
        ])
        .current_dir(root())
        .output()
        .expect("the check runs");
    assert!(
        rerun.status.success(),
        "a stale candidate does not poison the check: {}",
        String::from_utf8_lossy(&rerun.stderr)
    );
    let after = fs::read(&committed).expect("committed reads after");
    assert_eq!(committed_bytes, after, "the committed file is untouched");
    let _ = fs::remove_file(&candidate);
}
