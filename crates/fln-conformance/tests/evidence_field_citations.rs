//! `evidence_field_citations` — the twelve evidence fields of a coverage row, resolved against
//! real test functions (bead `franken_lean-evidence-fields-never-resolved-bs5o`).
//!
//! # What was unwatched
//!
//! A coverage row in `ci/VERIFICATION_MANIFEST.jsonl` carries twelve evidence fields — `unit`,
//! `boundary`, `error`, `property`, `metamorphic`, `mutation`, `negative_recovery`,
//! `failure_atomicity`, `resource`, `fault`, `fuzz`, `cancellation`. Until this file, nothing in
//! the repository ever resolved one of them against a function. `scripts/evidence.py` checks
//! that each is a sorted, duplicate-free list of non-empty strings and stops there; the only
//! citation-resolving path in the tree, `ci_execution_join.rs`, reads `artifacts` and nothing
//! else. A row could name a test that was renamed or deleted and no gate anywhere went red.
//!
//! # The governing figure in the bead was a SAMPLE, which is why this guard derives its own
//!
//! bs5o's description reads "786 citation-shaped entries, 765 resolve", corrected to 20
//! non-resolving. Re-derived at `e7444f10` with **every entry assigned to exactly one bucket and
//! the buckets required to sum to the total**: the function-resolvable population is over 2000,
//! and the non-resolving set is 39 entries across 14 rows and 28 distinct citations. The prior
//! scan covered under 40% of the population — a filter that skips what it cannot parse silently
//! redefines its own denominator, so [`classify`] refuses outright unless the buckets reconcile.
//!
//! My own first pass had the identical defect one layer down and is recorded because it is the
//! reason the second number is trustworthy: it accepted only left-hand sides matching a package
//! **name**, so every `tribunal/epoch-lab:target::fn` citation — whose left side is a member
//! **directory** — fell out of the population, and two rows the bead already knew about
//! disappeared. That loss is what exposed it.
//!
//! # Why the allowance is a CEILING plus one-way membership, and never an equality
//!
//! The 28 are a declared remainder of permitted violations spanning **several panes' rows**. So:
//!
//! * a non-resolving citation that is **not** declared fails — that is silent growth, the defect;
//! * the declared set may **shrink freely**. A repair by any pane must never redden this guard.
//!   An equality, or a "declared but no longer measured" rule, would make one pane's correct
//!   repair into another pane's red — a cross-pane wall, and this repository has already measured
//!   that shape reddening the commits that record good work.
//!
//! The price is stated rather than hidden: **the allowance can accumulate dead entries**. Nothing
//! here forces it to shrink, so a citation repaired months ago may still be declared. That is
//! accepted deliberately as the cheaper of two failures, and it is why the ceiling is bound to
//! the *measured* count as well as membership — the count cannot creep upward even if the
//! membership list grows stale.
//!
//! # What this does not earn
//!
//! Resolution proves the named function **exists** in tracked Rust source. It does not prove the
//! function tests what the row claims. It does not check that the function lives in the package
//! the citation names — that dimension was measured separately and is **empty** (0 mismatches
//! across 1827 citations, with a planted control proving the detector fires), so a guard on it
//! would have no live members and is deliberately not built here rather than added as decoration.
//! `#[ignore]` detection is not attempted: only six ignored test functions exist workspace-wide,
//! too few to rest a rule on without a separate measurement.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

const FIELDS: &[&str] = &[
    "boundary",
    "cancellation",
    "error",
    "failure_atomicity",
    "fault",
    "fuzz",
    "metamorphic",
    "mutation",
    "negative_recovery",
    "property",
    "resource",
    "unit",
];

/// Citations that name no test function anywhere in tracked Rust source. Measured, not guessed.
/// Membership is ONE-WAY: this list may shrink freely as rows are repaired, and a citation that
/// is not here may not be non-resolving. See the module header for why an equality would be a
/// cross-pane wall.
const NONRESOLVING_ALLOWANCE: &[&str] = &[
    "crates/fln-conformance:contract_roots::the_lane_this_suite_delegates_to_is_present_and_registered",
    "crates/fln-conformance:witness_claim_matrix::a_partial_repair_cannot_pass",
    "crates/fln-conformance:witness_claim_matrix::the_matrix_is_clean_against_the_real_tree",
    "fln-checker:environment::definition_schema_retains_hints_safety_types_values_and_mutual_membership",
    "fln-checker:environment::private_arena_corruption_is_an_internal_fault_and_recovery_is_exact",
    "fln-checker:numeric::numeric_production_has_no_primary_semantic_path",
    "fln-checker:wire_decoder::resource_and_cancellation_stops_are_nonanswers_with_exact_recovery",
    "fln-conformance:contract_roots::both_contracts_disclose_the_producer_side_tree_obligation_as_unmet",
    "fln-conformance:kernel_replay::artifact_incomplete_typed_never_verdict",
    "fln-conformance:kernel_replay::thread_matrix_stream_digest_identical_at_1_8_32",
    "fln-conformance:kernel_replay::typed_outcomes_never_panics",
    "fln-hash:root::tests::duplicate_keyed_map_refuses_set_projection",
    "fln-hash:root::tests::root_is_schedule_independent_across_thread_counts",
    "fln-kernel:budget_parity::accounting_seam_counted",
    "fln-kernel:depth_stack_calibration::typed_depth_outcomes",
    "fln-olean:region_read::corruption_sweep",
    "fln-olean:region_read::deterministic_corruption_sweep",
    "fln-olean:region_read::typed_errors_never_panics",
    "fln-syntax:tests::fln_core_name_dependency_is_real",
    "fln-syntax:tree::tests::attachment_damage_is_bounded_by_overlap_plus_one",
    "fln-syntax:tree::tests::misattached_trivia_is_visible_to_split_assertions",
    "fln-syntax:tree::tests::missing_is_visible_and_byte_empty",
    "fln-syntax:tree::tests::reconstruction_delegates_to_the_attachment_tiling",
    "fln-syntax:tree::tests::source_view_recovers_original_crlf_bytes",
    "fln-syntax:tree::tests::syntax_forms_match_the_pin",
    "structure-guard:contract_inventory::tests::canonical_generation_is_deterministic_bijective_and_not_a_second_pin_authority",
    "tribunal/epoch-lab:epoch_lab_hash_chain::a_leftover_candidate_is_typed_inconclusive_not_consumed",
    "tribunal/epoch-lab:epoch_lab_hash_chain::a_rewritten_history_is_refused_even_when_internally_consistent",
];

/// The measured count may not creep upward even if the membership list above goes stale.
const NONRESOLVING_ENTRY_CEILING: usize = 39;

/// Anti-vacuity: a scan reporting far fewer resolvable citations than this has broken. The bead's
/// own sampler reported 786 against a real population above 2000, and 786 looked entirely
/// plausible.
const RESOLVABLE_FLOOR: usize = 1500;
const TEST_FUNCTION_FLOOR: usize = 500;
const PACKAGE_FLOOR: usize = 20;

#[derive(Debug, Default)]
struct Buckets {
    total: usize,
    counts: BTreeMap<&'static str, usize>,
}

impl Buckets {
    fn hit(&mut self, name: &'static str) {
        *self.counts.entry(name).or_default() += 1;
    }

    fn sum(&self) -> usize {
        self.counts.values().sum()
    }

    fn resolvable(&self) -> usize {
        self.counts.get("citation").copied().unwrap_or_default()
            + self
                .counts
                .get("citation_test_prefix")
                .copied()
                .unwrap_or_default()
    }
}

struct Workspace {
    packages: BTreeSet<String>,
    member_dirs: BTreeSet<String>,
    test_functions: BTreeSet<String>,
}

fn tracked_files(root: &Path) -> Vec<String> {
    let out = Command::new("git")
        .arg("ls-files")
        .current_dir(root)
        .output()
        .expect("git ls-files must run");
    assert!(out.status.success(), "git ls-files failed");
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::to_owned)
        .collect()
}

fn derive(root: &Path) -> Workspace {
    let tracked = tracked_files(root);
    let mut packages = BTreeSet::new();
    let mut member_dirs = BTreeSet::new();
    for path in tracked.iter().filter(|p| p.ends_with("Cargo.toml")) {
        let Ok(text) = fs::read_to_string(root.join(path)) else {
            continue;
        };
        let Some(name) = text.lines().find_map(|line| {
            let rest = line
                .trim()
                .strip_prefix("name")?
                .trim_start()
                .strip_prefix('=')?;
            let rest = rest.trim().strip_prefix('"')?;
            rest.split('"').next().map(str::to_owned)
        }) else {
            continue;
        };
        packages.insert(name);
        member_dirs.insert(
            path.rsplit_once('/')
                .map(|(dir, _)| dir.to_owned())
                .unwrap_or_default(),
        );
    }

    let mut test_functions = BTreeSet::new();
    for path in tracked
        .iter()
        .filter(|p| p.ends_with(".rs") && !p.starts_with("vendor/"))
    {
        let Ok(text) = fs::read_to_string(root.join(path)) else {
            continue;
        };
        let lines: Vec<&str> = text.lines().collect();
        for (index, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed != "#[test]" && trimmed != "#[tokio::test]" {
                continue;
            }
            for candidate in lines.iter().skip(index + 1).take(8) {
                let t = candidate.trim();
                if t == "#[test]" || t == "#[tokio::test]" {
                    break;
                }
                let mut rest = t;
                loop {
                    let stripped = ["pub(crate) ", "pub ", "async ", "unsafe ", "const "]
                        .iter()
                        .find_map(|m| rest.strip_prefix(m));
                    match stripped {
                        Some(next) => rest = next.trim_start(),
                        None => break,
                    }
                }
                if let Some(rest) = rest.strip_prefix("fn ") {
                    let end = rest.find(['(', '<', ' ']).unwrap_or(rest.len());
                    test_functions.insert(rest[..end].to_owned());
                    break;
                }
            }
        }
    }
    Workspace {
        packages,
        member_dirs,
        test_functions,
    }
}

/// Split a citation of the form `<package-or-member-dir>:<target>(::<segment>)+`.
fn citation_function<'a>(value: &'a str, ws: &Workspace) -> Option<&'a str> {
    let (left, rest) = value.split_once(':')?;
    if !ws.packages.contains(left) && !ws.member_dirs.contains(left) {
        return None;
    }
    if !rest.contains("::") {
        return None; // target named, no function — a separate, coarser class
    }
    let function = rest.rsplit("::").next()?;
    if function.is_empty()
        || !function
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_')
    {
        return None;
    }
    Some(function)
}

/// Every entry lands in exactly one bucket. Non-resolving citations are returned with the row
/// and field that carry them.
fn classify(manifest: &str, ws: &Workspace) -> (Buckets, Vec<(String, String, String)>) {
    let mut buckets = Buckets::default();
    let mut nonresolving = Vec::new();
    for line in manifest.lines().filter(|l| !l.trim().is_empty()) {
        let Some(kind) = json_string(line, "kind") else {
            continue;
        };
        if kind != "coverage" {
            continue;
        }
        let bead = json_string(line, "bead").unwrap_or_default();
        for field in FIELDS {
            for value in json_string_array(line, field) {
                buckets.total += 1;
                if value.starts_with("not_applicable") {
                    buckets.hit("typed_not_applicable");
                } else if value.starts_with("bead:") {
                    buckets.hit("bead_reference");
                } else if value.trim().contains(' ') {
                    buckets.hit("prose");
                } else if let Some(function) = value.strip_prefix("test:") {
                    buckets.hit("citation_test_prefix");
                    let function = function.rsplit("::").next().unwrap_or_default();
                    if !ws.test_functions.contains(function) {
                        nonresolving.push((bead.clone(), (*field).to_owned(), value.clone()));
                    }
                } else if value.starts_with("scripts/")
                    || value.ends_with(".sh")
                    || value.ends_with(".py")
                {
                    buckets.hit("script_reference");
                } else if value.contains(".rs:") {
                    buckets.hit("implementation_reference");
                } else if let Some(function) = citation_function(&value, ws) {
                    buckets.hit("citation");
                    if !ws.test_functions.contains(function) {
                        nonresolving.push((bead.clone(), (*field).to_owned(), value.clone()));
                    }
                } else {
                    buckets.hit("unclassified");
                }
            }
        }
    }
    (buckets, nonresolving)
}

// --- a minimal JSONL reader; the closed dependency universe (D1) has no serde ----------------

fn json_string(line: &str, key: &str) -> Option<String> {
    let needle = format!("\"{key}\":");
    let start = line.find(&needle)? + needle.len();
    let rest = line[start..].trim_start();
    let rest = rest.strip_prefix('"')?;
    let mut out = String::new();
    let mut chars = rest.chars();
    while let Some(c) = chars.next() {
        match c {
            '\\' => out.push(chars.next()?),
            '"' => return Some(out),
            _ => out.push(c),
        }
    }
    None
}

fn json_string_array(line: &str, key: &str) -> Vec<String> {
    let needle = format!("\"{key}\":");
    let Some(start) = line.find(&needle) else {
        return Vec::new();
    };
    let rest = line[start + needle.len()..].trim_start();
    let Some(rest) = rest.strip_prefix('[') else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut chars = rest.chars();
    let mut current: Option<String> = None;
    while let Some(c) = chars.next() {
        match (c, current.as_mut()) {
            ('"', None) => current = Some(String::new()),
            ('\\', Some(buf)) => {
                if let Some(next) = chars.next() {
                    buf.push(next);
                }
            }
            ('"', Some(_)) => out.push(current.take().expect("open string")),
            (']', None) => break,
            (_, Some(buf)) => buf.push(c),
            _ => {}
        }
    }
    out
}

fn judge(
    buckets: &Buckets,
    nonresolving: &[(String, String, String)],
    allowance: &[&str],
    ceiling: usize,
    ws: &Workspace,
) -> Vec<String> {
    let mut faults = Vec::new();

    if buckets.sum() != buckets.total {
        faults.push(format!(
            "sampler: {} entries were seen but only {} landed in a bucket. A scan that skips what \
             it cannot parse silently redefines its own denominator — that is exactly how this \
             bead's governing figure came to describe 38% of the population while reading like \
             all of it.",
            buckets.total,
            buckets.sum()
        ));
    }
    if ws.packages.len() < PACKAGE_FLOOR || ws.test_functions.len() < TEST_FUNCTION_FLOOR {
        faults.push(format!(
            "broken derivation: {} packages and {} test functions, below the floors of \
             {PACKAGE_FLOOR} and {TEST_FUNCTION_FLOOR}. A walk that found almost nothing and a \
             tree with almost nothing in it are the same green.",
            ws.packages.len(),
            ws.test_functions.len()
        ));
    }
    if buckets.resolvable() < RESOLVABLE_FLOOR {
        faults.push(format!(
            "broken resolution: {} resolvable citations, below the floor of {RESOLVABLE_FLOOR}. \
             The prior scan reported 786 against a real population above 2000 and looked \
             entirely plausible doing it.",
            buckets.resolvable()
        ));
    }

    let declared: BTreeSet<&str> = allowance.iter().copied().collect();
    let undeclared: BTreeSet<&str> = nonresolving
        .iter()
        .map(|(_, _, citation)| citation.as_str())
        .filter(|citation| !declared.contains(citation))
        .collect();
    if !undeclared.is_empty() {
        let mut detail: Vec<String> = nonresolving
            .iter()
            .filter(|(_, _, c)| undeclared.contains(c.as_str()))
            .map(|(bead, field, c)| format!("    {bead} [{field}] {c}"))
            .collect();
        detail.sort();
        detail.dedup();
        faults.push(format!(
            "evidence-field-citation-grew: {} citation(s) in the twelve evidence fields name no \
             `#[test]` function anywhere in tracked Rust source, and are not declared in \
             NONRESOLVING_ALLOWANCE:\n{}\n\nA row's evidence fields are the only place it says \
             WHICH test carries its claim. A citation that resolves to nothing is a claim with no \
             referent, and nothing but this guard notices. Either repair the citation to the \
             function's current name, or declare it here and say why in the same commit.",
            undeclared.len(),
            detail.join("\n")
        ));
    }
    if nonresolving.len() > ceiling {
        faults.push(format!(
            "evidence-field-citation-ceiling: {} non-resolving entries against a ceiling of \
             {ceiling}. The declared membership may shrink freely — a repair by any pane must \
             never redden this guard — so the count is what stops the population creeping upward \
             behind a membership list that has gone stale.",
            nonresolving.len()
        ));
    }
    faults
}

#[test]
fn the_twelve_evidence_fields_resolve_to_tests_that_exist() {
    let root = root();
    let ws = derive(&root);
    let manifest = fs::read_to_string(root.join("ci/VERIFICATION_MANIFEST.jsonl"))
        .expect("the verification manifest must be readable");
    let (buckets, nonresolving) = classify(&manifest, &ws);
    let faults = judge(
        &buckets,
        &nonresolving,
        NONRESOLVING_ALLOWANCE,
        NONRESOLVING_ENTRY_CEILING,
        &ws,
    );
    assert!(
        faults.is_empty(),
        "the twelve evidence fields no longer resolve as this file declares:\n\n{}\n\n\
         measured: {} entries, {} resolvable, {} non-resolving",
        faults.join("\n\n"),
        buckets.total,
        buckets.resolvable(),
        nonresolving.len()
    );
}

#[test]
fn the_derivation_reports_a_workspace_and_not_an_empty_walk() {
    let ws = derive(&root());
    assert!(
        ws.packages.len() >= PACKAGE_FLOOR,
        "derived {} packages",
        ws.packages.len()
    );
    assert!(
        ws.test_functions.len() >= TEST_FUNCTION_FLOOR,
        "derived {} test functions",
        ws.test_functions.len()
    );
    // The positive control that makes the floors mean something: a name known to exist, and the
    // rename bs5o documents, which must NOT.
    assert!(
        ws.test_functions
            .contains("real_workspace_is_structurally_clean")
    );
    assert!(!ws.test_functions.contains("a_partial_repair_cannot_pass"));
    assert!(
        ws.test_functions
            .contains("a_partial_repair_within_one_document_cannot_pass")
    );
}

#[test]
fn the_allowance_is_sorted_unique_and_every_member_is_shaped_like_a_citation() {
    let mut sorted = NONRESOLVING_ALLOWANCE.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    assert_eq!(
        sorted.as_slice(),
        NONRESOLVING_ALLOWANCE,
        "the allowance must be sorted and duplicate-free so a diff of it is readable"
    );
    for member in NONRESOLVING_ALLOWANCE {
        assert!(
            member.contains(':') && member.contains("::"),
            "{member} is not citation-shaped"
        );
    }
}

// --- the guard's own mutants ----------------------------------------------------------------

fn fixture() -> (Buckets, Vec<(String, String, String)>, Workspace) {
    let ws = Workspace {
        packages: ["fln-demo".to_owned()].into_iter().collect(),
        member_dirs: BTreeSet::new(),
        test_functions: (0..TEST_FUNCTION_FLOOR + 1)
            .map(|i| format!("t{i}"))
            .collect(),
    };
    let mut buckets = Buckets::default();
    for _ in 0..RESOLVABLE_FLOOR + 1 {
        buckets.total += 1;
        buckets.hit("citation");
    }
    (buckets, Vec::new(), ws)
}

fn packages_at_floor(ws: &mut Workspace) {
    ws.packages = (0..PACKAGE_FLOOR).map(|i| format!("p{i}")).collect();
}

#[test]
fn an_undeclared_nonresolving_citation_is_refused() {
    let (buckets, mut nonresolving, mut ws) = fixture();
    packages_at_floor(&mut ws);
    nonresolving.push((
        "some-bead".to_owned(),
        "unit".to_owned(),
        "fln-demo:target::a_function_that_does_not_exist".to_owned(),
    ));
    let faults = judge(
        &buckets,
        &nonresolving,
        &[],
        NONRESOLVING_ENTRY_CEILING,
        &ws,
    );
    assert!(
        faults
            .iter()
            .any(|f| f.starts_with("evidence-field-citation-grew")),
        "{faults:?}"
    );
}

#[test]
fn a_declared_nonresolving_citation_is_permitted_and_a_repair_never_reddens() {
    let (buckets, mut nonresolving, mut ws) = fixture();
    packages_at_floor(&mut ws);
    let declared = ["fln-demo:target::known_rot"];
    nonresolving.push((
        "some-bead".to_owned(),
        "unit".to_owned(),
        "fln-demo:target::known_rot".to_owned(),
    ));
    assert!(
        judge(
            &buckets,
            &nonresolving,
            &declared,
            NONRESOLVING_ENTRY_CEILING,
            &ws
        )
        .is_empty(),
        "a declared debt must not fire"
    );
    // The repair: the citation stops being non-resolving while the declaration stays. This MUST
    // stay green — the allowance spans several panes' rows, and one pane's correct repair must
    // never redden another pane's guard.
    assert!(
        judge(&buckets, &[], &declared, NONRESOLVING_ENTRY_CEILING, &ws).is_empty(),
        "a repair must never redden this guard; that is why membership is one-way"
    );
}

#[test]
fn the_ceiling_refuses_creep_even_when_every_citation_is_declared() {
    let (buckets, mut nonresolving, mut ws) = fixture();
    packages_at_floor(&mut ws);
    let declared = ["fln-demo:target::known_rot"];
    for index in 0..NONRESOLVING_ENTRY_CEILING + 1 {
        nonresolving.push((
            format!("bead{index}"),
            "unit".to_owned(),
            "fln-demo:target::known_rot".to_owned(),
        ));
    }
    let faults = judge(
        &buckets,
        &nonresolving,
        &declared,
        NONRESOLVING_ENTRY_CEILING,
        &ws,
    );
    assert!(
        faults
            .iter()
            .any(|f| f.starts_with("evidence-field-citation-ceiling")),
        "membership alone cannot stop the SAME declared citation spreading to more rows: {faults:?}"
    );
}

#[test]
fn a_scan_whose_buckets_do_not_reconcile_is_refused_as_a_sampler() {
    let (mut buckets, nonresolving, mut ws) = fixture();
    packages_at_floor(&mut ws);
    buckets.total += 7; // seen but never bucketed — the sampler shape
    let faults = judge(
        &buckets,
        &nonresolving,
        &[],
        NONRESOLVING_ENTRY_CEILING,
        &ws,
    );
    assert!(
        faults.iter().any(|f| f.starts_with("sampler")),
        "{faults:?}"
    );
}

#[test]
fn an_empty_walk_is_refused_rather_than_reported_clean() {
    let ws = Workspace {
        packages: BTreeSet::new(),
        member_dirs: BTreeSet::new(),
        test_functions: BTreeSet::new(),
    };
    let faults = judge(
        &Buckets::default(),
        &[],
        &[],
        NONRESOLVING_ENTRY_CEILING,
        &ws,
    );
    assert!(
        faults.iter().any(|f| f.starts_with("broken derivation")),
        "{faults:?}"
    );
    assert!(
        faults.iter().any(|f| f.starts_with("broken resolution")),
        "an empty scan satisfies membership and the ceiling vacuously; only the floors catch it: \
         {faults:?}"
    );
}

#[test]
fn the_citation_splitter_accepts_a_member_directory_and_not_a_stranger() {
    let ws = Workspace {
        packages: ["fln-hash".to_owned()].into_iter().collect(),
        member_dirs: ["tribunal/epoch-lab".to_owned()].into_iter().collect(),
        test_functions: BTreeSet::new(),
    };
    // The 105-entry hole my own first pass had: the left side may be a member DIRECTORY.
    assert_eq!(
        citation_function(
            "tribunal/epoch-lab:hash_chain::a_rewritten_history_is_refused",
            &ws
        ),
        Some("a_rewritten_history_is_refused")
    );
    assert_eq!(
        citation_function("fln-hash:root::tests::some_name", &ws),
        Some("some_name")
    );
    // A left side belonging to no member is not a citation of this kind.
    assert_eq!(citation_function("not-a-package:target::name", &ws), None);
    // A target with no function is a coarser class, not a resolvable citation.
    assert_eq!(
        citation_function("fln-hash:grammar_effect_totality", &ws),
        None
    );
}
