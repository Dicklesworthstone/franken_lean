//! Every `artifacts` citation in `ci/VERIFICATION_MANIFEST.jsonl` is classified by whether
//! it can be **resolved to a durable referent**, and the resulting population is disclosed
//! here and bound to the measurement in **both** directions (bead `fln-0rxm`).
//!
//! **What this exists for.** The manifest validator checks that `artifacts` is a non-empty,
//! sorted, duplicate-free string array and validates its *shape* only; it never requires an
//! entry to **denote** anything, so `"artifacts": ["x"]` is a valid judgement row. Measured
//! at `2eb09ba6`: of 584 artifact citations across 190 coverage rows, **180 cannot be
//! resolved to a durable referent at all**, and 155 of those never denoted anything at the
//! moment they were written. That is `fln-bench-apparatus-empty-referent-bkw6`'s
//! empty-referent shape sitting inside the one artifact whose job is holding claims to
//! their evidence.
//!
//! **Why this DECLARES rather than repairs, which is a ruling and not a preference.**
//! Repairing means choosing what a closed bead's author meant. Measured before deciding:
//! withdrawal removes **180 of 584 citations — 31% of every artifact citation in the
//! manifest** — invalidates 18 rows outright and reduces 23 `complete` rows to a single
//! surviving citation; and 13 of the 18 belong to panes that cannot review the deletion. A
//! never-denoted citation is wrong, but `run.ndjson` still records that its author rested
//! the claim on a *lane run*, which is exactly what a future repair would need, so deleting
//! it is irreversible in the direction that matters. Withdrawal is the honest repair for an
//! **individual row** and belongs to that row's owner; declaration is the honest repair for
//! the **manifest**. This is the same ruling the evidence-field guard reached earlier on a
//! different population — a guard that discovers rot declares all of it and repairs none of
//! it — reached here independently, which is worth more than either derivation alone.
//!
//! **The shape is equality in both directions, not one-way-plus-a-floor.** That distinction
//! has already cost this repository a wall that reddened a correct repair. One-way plus a
//! floor is right for a declared remainder of *permitted violations*, which shrinks as
//! people repair it. This is a disclosure of a *measured population*, which does not shrink
//! by itself: a new unresolvable citation must **raise** the number and force its author to
//! say so, and a repair must **lower** it. Both directions fail the build.
//!
//! **The third state, said loudly because a reader will assume it does not exist.** Of the
//! rows whose every citation is unresolvable, **17 can neither be repaired nor withdrawn**:
//! repaired because no recovery method exists for a citation that never denoted anything,
//! and withdrawn because `artifacts` is required non-empty for a `complete` row, so emptying
//! them makes them *invalid* rather than honest. Every one of the 17 is blocked by a
//! **single** kind — 10 rootless-leaf-only, 4 glob-only, 3 never-existed-only — because they
//! are lane-evidence rows whose entire evidence set is the lane's own output namespace,
//! cited by name in a namespace that is unrooted and ephemeral by construction.
//!
//! **What this does not earn.** It classifies referents; it never establishes that a
//! *resolvable* citation supports the claim citing it, which is the harder join and is
//! untouched. `never_existed` rests on `git log --all`, so a path that lived only on a
//! dropped branch misclassifies. The census is a measurement of this tree at this commit,
//! re-derived per run; the *ruling* above is `bounded_model` at one host.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::process::Command;

use fln_conformance::execution::{Field, record_field};

/// The disclosed population, bound to the measurement by equality in both directions.
///
/// Every class here is one this repository **cannot check**. The resolvable classes are
/// deliberately *not* bound: a gate on "tracked citations == 217" would redden on exactly
/// the commits that add a good citation, which is the cry-wolf failure this project has
/// already measured once when an enforcement census drifted 26 → 27 → 28 while the live
/// population stood still.
const UNRESOLVABLE_CENSUS: &[(&str, usize)] = &[
    ("rootless_leaf", 120),
    ("glob", 20),
    ("never_existed", 15),
    ("commit_unreachable", 9),
    ("present_but_untracked", 9),
    ("under_target_ephemeral", 7),
    ("existed_then_removed", 0),
];

/// Rows whose every citation is unresolvable **and** whose blocking kinds are all
/// never-denoted, so neither repair nor withdrawal is available. See the module header.
const THIRD_STATE_ROWS: usize = 17;

/// Rows whose every citation is unresolvable. Larger than [`THIRD_STATE_ROWS`] by exactly
/// the rows carrying a *recoverable* class — rot, which has a known recovery method — and
/// the gap is disclosed rather than smoothed away, because a row that can be rescued by
/// repairing an anchor is not in the third state.
const FULLY_UNRESOLVABLE_ROWS: usize = 18;

/// Classes that resolve to something this repository can check.
const RESOLVABLE: &[&str] = &["tracked_exists", "bead_comment_checked", "commit_reachable"];

/// Classes that denote no file *by design* and are not defects.
const BY_DESIGN: &[&str] = &["prose_opaque_token", "structured_other"];

/// Never-denoted classes: wrong at the moment they were written, with no earlier correct
/// state to restore. These are what make a row's blockage terminal.
const NEVER_DENOTED: &[&str] = &["rootless_leaf", "glob", "never_existed"];

/// A citation whose head marks it as structured and typed rather than a filesystem path.
const STRUCTURED_HEADS: &[&str] = &[
    "sha256:",
    "test:",
    "cargo-test:",
    "not_applicable",
    "pending_active_work",
    "pinned-toolchain:",
    "hash_identity:",
];

fn git(root: &Path, args: &[&str]) -> Option<String> {
    let out = Command::new("git")
        .current_dir(root)
        .args(args)
        .output()
        .unwrap_or_else(|error| {
            panic!(
                "git must run: this census is DERIVED from the repository, so without git the \
                 population is unknown and no disclosure can be made ({error})"
            )
        });
    out.status
        .success()
        .then(|| String::from_utf8_lossy(&out.stdout).into_owned())
}

/// One artifact citation's referent kind. The classification is total: every entry lands in
/// exactly one class, which the conservation identity below asserts rather than assumes.
fn classify(root: &Path, entry: &str, tracked: &BTreeSet<String>) -> &'static str {
    if entry.starts_with("bead-comment:") {
        return "bead_comment_checked";
    }
    if entry.starts_with("bead:") {
        return "prose_opaque_token";
    }
    if let Some(sha) = entry.strip_prefix("commit:") {
        let reachable = Command::new("git")
            .current_dir(root)
            .args(["merge-base", "--is-ancestor", sha.trim(), "refs/heads/main"])
            .status()
            .map(|s| s.success())
            .unwrap_or(false);
        // Existence is NOT the test: `refs/original` makes every pre-rewrite anchor resolve
        // in this clone while stranding a fresh one, so reachability from `main` is the only
        // question worth asking (bead `fln-history-rewrite-evidence-anchor-reachability-vdi4`).
        return if reachable {
            "commit_reachable"
        } else {
            "commit_unreachable"
        };
    }
    if STRUCTURED_HEADS.iter().any(|head| entry.starts_with(head)) {
        return "structured_other";
    }
    if entry.contains('*') {
        // A glob that MATCHES is still not a referent: it does not say which file the claim
        // rests on. Unresolvable regardless of what it happens to match today.
        return "glob";
    }
    if !entry.contains('/') {
        // A rootless leaf states no root, so there is nothing to resolve it against. The
        // root must be stated in the ROW; supplying one in the checker would resolve all 120
        // against a directory the checker picked and prove nothing.
        return "rootless_leaf";
    }
    if tracked.contains(entry) {
        return "tracked_exists";
    }
    if entry.starts_with("target/") {
        return "under_target_ephemeral";
    }
    if root.join(entry).exists() {
        return "present_but_untracked";
    }
    match git(root, &["log", "--all", "--oneline", "--", entry]) {
        Some(log) if !log.trim().is_empty() => "existed_then_removed",
        _ => "never_existed",
    }
}

struct Row {
    bead: String,
    kinds: Vec<&'static str>,
}

fn scan() -> Vec<Row> {
    let root = fln_conformance::checked_workspace_root!();
    let tracked: BTreeSet<String> = git(&root, &["ls-files"])
        .expect("git ls-files must succeed: the tracked surface is derived, never listed")
        .lines()
        .map(str::to_owned)
        .collect();
    assert!(
        tracked.len() > 500,
        "git ls-files returned {} paths — a walk this short is a BROKEN SCAN, not a small \
         repository, and a broken scan classifies every path citation as unresolvable",
        tracked.len()
    );

    let manifest = std::fs::read_to_string(root.join("ci/VERIFICATION_MANIFEST.jsonl"))
        .expect("the verification manifest must be readable");
    let mut rows = Vec::new();
    for (number, line) in manifest.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let Some(Field::Text(bead)) = record_field(line, "bead") else {
            continue; // the adoption header and the scenario rows carry no bead
        };
        let Some(Field::List(artifacts)) = record_field(line, "artifacts") else {
            panic!(
                "record {} for {bead:?} yielded no artifacts list — a record this reader \
                 cannot read is a refusal, never a row with no citations",
                number + 1
            );
        };
        let kinds = artifacts
            .iter()
            .map(|entry| classify(&root, entry, &tracked))
            .collect();
        rows.push(Row { bead, kinds });
    }
    assert!(
        rows.len() >= 150,
        "scanned {} coverage rows — implausibly few; refusing a scan rather than reporting a \
         clean manifest",
        rows.len()
    );
    rows
}

fn measure(rows: &[Row]) -> (BTreeMap<&'static str, usize>, usize, usize, usize) {
    let mut counts: BTreeMap<&'static str, usize> = BTreeMap::new();
    let mut total = 0usize;
    let mut fully_unresolvable = 0usize;
    let mut third_state = 0usize;
    for row in rows {
        for kind in &row.kinds {
            *counts.entry(*kind).or_default() += 1;
            total += 1;
        }
        let unresolvable: Vec<&&str> = row
            .kinds
            .iter()
            .filter(|kind| !RESOLVABLE.contains(kind) && !BY_DESIGN.contains(kind))
            .collect();
        if unresolvable.is_empty() || unresolvable.len() != row.kinds.len() {
            continue;
        }
        fully_unresolvable += 1;
        if unresolvable.iter().all(|kind| NEVER_DENOTED.contains(kind)) {
            third_state += 1;
        }
    }
    (counts, total, fully_unresolvable, third_state)
}

/// The declared population must equal the measured one, class by class, in **both**
/// directions — and the classification must be total, which the conservation identity
/// asserts rather than assumes.
#[test]
fn the_unresolvable_citation_census_matches_the_measured_population() {
    let rows = scan();
    let (counts, total, _, _) = measure(&rows);
    assert!(
        total >= 400,
        "{total} artifact citations is implausibly few — refusing a broken scan"
    );

    let mut disagreements = Vec::new();
    let mut declared_total = 0usize;
    for (class, declared) in UNRESOLVABLE_CENSUS {
        let measured = counts.get(class).copied().unwrap_or(0);
        declared_total += declared;
        if measured != *declared {
            disagreements.push(format!(
                "  {class}: disclosed {declared}, measured {measured} ({:+})",
                measured as isize - *declared as isize
            ));
        }
    }

    // Every class the classifier can emit must be accounted for by exactly one of the three
    // lists. A new class added to `classify` and to no list would otherwise vanish from the
    // conservation identity and from the disclosure at the same time.
    let accounted: BTreeSet<&str> = UNRESOLVABLE_CENSUS
        .iter()
        .map(|(class, _)| *class)
        .chain(RESOLVABLE.iter().copied())
        .chain(BY_DESIGN.iter().copied())
        .collect();
    for class in counts.keys() {
        assert!(
            accounted.contains(class),
            "class {class:?} is emitted by the classifier and named by no list — it would be \
             invisible to both the conservation identity and this disclosure"
        );
    }

    let resolvable_and_by_design: usize = counts
        .iter()
        .filter(|(class, _)| RESOLVABLE.contains(class) || BY_DESIGN.contains(class))
        .map(|(_, n)| n)
        .sum();
    let measured_unresolvable: usize = total - resolvable_and_by_design;

    assert!(
        disagreements.is_empty(),
        "the disclosed unresolvable-citation census no longer describes this manifest:\n{}\n\
         Equality is required in BOTH directions. A new unresolvable citation must RAISE the \
         number and its author must say so; a repair must LOWER it. Do not soften a class \
         boundary to go green — that converts a measured population into a frozen one, which \
         is the defect this census exists to prevent.\n\
         Measured now: {measured_unresolvable} unresolvable of {total} citations.",
        disagreements.join("\n")
    );
    assert_eq!(
        declared_total, measured_unresolvable,
        "the per-class disclosures sum to {declared_total} but {measured_unresolvable} \
         citations are unresolvable — the conservation identity failed, so a class is being \
         double-counted or dropped"
    );
    assert_eq!(
        resolvable_and_by_design + measured_unresolvable,
        total,
        "conservation failed: the classification is not total"
    );
}

/// The third state — neither repairable nor withdrawable — bound by equality, and separated
/// from the merely-fully-unresolvable rows because a row rescuable by repairing a rotted
/// anchor is not in it.
#[test]
fn the_third_state_row_count_matches_the_measured_population() {
    let rows = scan();
    let (_, _, fully_unresolvable, third_state) = measure(&rows);
    assert_eq!(
        fully_unresolvable, FULLY_UNRESOLVABLE_ROWS,
        "rows whose every citation is unresolvable moved from {FULLY_UNRESOLVABLE_ROWS} to \
         {fully_unresolvable}"
    );
    assert_eq!(
        third_state, THIRD_STATE_ROWS,
        "the third-state population moved from {THIRD_STATE_ROWS} to {third_state}. These \
         rows can neither be repaired (no recovery exists for a citation that never denoted \
         anything) nor withdrawn (artifacts is required non-empty for a complete row), so a \
         change here is a change in what this repository can never check about itself."
    );
    assert!(
        third_state <= fully_unresolvable,
        "third state {third_state} exceeds the fully-unresolvable rows {fully_unresolvable} \
         it is a subset of"
    );
}

/// **The planted mutant.** An undeclared unresolvable citation must RAISE the census and be
/// caught, rather than joining the population silently.
///
/// It is planted against the real scan's own output rather than against a hand-built fixture,
/// because a fixture proves the comparison *fires* and says nothing about the production
/// path. And it plants **one of each** never-denoted kind: a mutant that dies at only one
/// class would leave the other two riding on a neighbour's assertion.
#[test]
fn an_undeclared_unresolvable_citation_is_caught_rather_than_joining_silently() {
    let rows = scan();
    let (baseline, _, _, _) = measure(&rows);

    for (kind, planted) in [
        ("rootless_leaf", "planted_decoy_artifact.ndjson"),
        ("glob", "env-snapshots/*/planted-decoy"),
        ("never_existed", "crates/fln-planted/src/decoy.rs"),
    ] {
        let mut mutated: Vec<Row> = rows
            .iter()
            .map(|row| Row {
                bead: row.bead.clone(),
                kinds: row.kinds.clone(),
            })
            .collect();
        let root = fln_conformance::checked_workspace_root!();
        let tracked = BTreeSet::new();
        let observed = classify(&root, planted, &tracked);
        assert_eq!(
            observed, kind,
            "the planted decoy {planted:?} classifies as {observed:?}, not {kind:?} — a decoy \
             that lands in the wrong class controls nothing"
        );
        mutated[0].kinds.push(observed);

        let (mutant, _, _, _) = measure(&mutated);
        let declared = UNRESOLVABLE_CENSUS
            .iter()
            .find(|(class, _)| *class == kind)
            .map(|(_, n)| *n)
            .expect("every never-denoted class must be disclosed");
        assert_eq!(
            mutant.get(kind).copied().unwrap_or(0),
            baseline.get(kind).copied().unwrap_or(0) + 1,
            "planting a {kind} citation did not move the measured population, so the census \
             cannot see an addition of that kind"
        );
        assert_ne!(
            mutant.get(kind).copied().unwrap_or(0),
            declared,
            "the census declares {declared} for {kind} and the mutated population measures \
             the same — the guard would stay GREEN with an undeclared citation present, which \
             is exactly the silent join it exists to refuse"
        );
    }
}

/// The anti-vacuity floor is itself reachable, because a check that exists for the day the
/// scan breaks is precisely the one a healthy tree cannot exercise.
#[test]
fn an_empty_or_shallow_scan_is_refused_rather_than_reported_clean() {
    let empty: Vec<Row> = Vec::new();
    let (counts, total, fully, third) = measure(&empty);
    assert!(counts.is_empty() && total == 0 && fully == 0 && third == 0);
    // The floors live in `scan`, so this asserts the SHAPE the floors defend: a zero
    // measurement is indistinguishable from a clean manifest, and every equality assertion
    // above would report a large disagreement rather than a pass. That direction — loud
    // rather than silent — is the one a scanner that cannot decide must fail in.
    let declared: usize = UNRESOLVABLE_CENSUS.iter().map(|(_, n)| n).sum();
    assert!(
        declared > 0,
        "an all-zero disclosure would make an empty scan agree with it, which is the vacuous \
         green this floor exists to prevent"
    );
}
