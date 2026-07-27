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
//! rows whose every citation is unresolvable, **14 can neither be repaired nor withdrawn**:
//! repaired because no recovery method exists for a citation that never denoted anything,
//! and withdrawn because `artifacts` is required non-empty for a `complete` row, so emptying
//! them makes them *invalid* rather than honest. Every one of the 14 is blocked by a
//! **single** kind — 7 rootless-leaf-only, 4 glob-only, 3 never-existed-only — because they
//! are lane-evidence rows whose entire evidence set is the lane's own output namespace,
//! cited by name in a namespace that is unrooted and ephemeral by construction.
//!
//! **That decomposition was prose, and landing the repair above without it would have made
//! it false — which is this module's own defect arriving inside this module.** Measured at
//! `60b2e176`: it read 10/4/3 against a total of 17, and the three `fln-amv` rows that
//! gained a checkable referent were *all* rootless-leaf-only, so moving only the headline
//! leaves `10 rootless-leaf-only` describing a population of 7, still summing to a total
//! that has changed. Nothing would have said so. [`THIRD_STATE_ROWS`] binds the cardinality
//! of the **population**; a decomposition is a claim about each **member**, and
//! `fln-cross-tree-baked-root-k60n` already measured what the difference costs — an
//! aggregate is a budget its own repairs refill, so three rootless-leaf rows repaired here
//! would silently fund three new glob-only ones with the total never moving.
//! [`THIRD_STATE_BY_BLOCKING_KIND`] binds it per member, in both directions.
//!
//! The sentence's *other* claim — that every third-state row is blocked by a **single** kind
//! — is bound too, by [`THIRD_STATE_MULTI_KIND_ROWS`]. It is a declared **zero**, so a
//! healthy tree can never exercise it and the guard would be decorative on live data alone;
//! the mutant test plants a synthetic multi-kind row rather than trusting the population.
//!
//! **`commit_unreachable` is ROT, not an empty referent, and the recovery method is now
//! measured rather than assumed** (bead `fln-history-rewrite-evidence-anchor-reachability-vdi4`).
//! The 2026-07-25 `filter-branch` did not make these anchors wrong; it made them unverifiable
//! from `main`, while `refs/original` keeps every pre-rewrite commit alive in this clone so a
//! naive existence check still passes. Re-derived at `84e15401`: **9 of the 9** unreachable
//! `commit:` citations recover to a content-identical twin on `main`. A twin is accepted only
//! on identical patch-id, byte-identical diff text, identical touched-path list and identical
//! resulting blob for every path — never on subject and author date, which agree here for
//! reasons that prove nothing on their own.
//!
//! The negative control came from the tree rather than from the probe, which is why the
//! method is believable: swept repository-wide the same predicate refuses `be14ee9b`, whose
//! same-subject candidate on `main` is missing exactly the four `contracts/*.tsv` shards the
//! rewrite stripped. The one commit whose content the rewrite genuinely altered is the one
//! the content check declined.
//!
//! **The class now reads 0, and the seven anchors that took it there were accepted on TWO
//! INDEPENDENT DERIVATIONS BY DIFFERENT PANES — which is strictly stronger than either
//! alone, and is recorded here as two rather than absorbed into one verdict.** Two of the
//! nine were `cc_3`'s own rows and were repaired at `c291fd91`. The remaining seven are
//! `cc_2`'s, and this module's ruling that an individual row belongs to its owner binds
//! repair exactly as it binds withdrawal — so `cc_3` routed them instead of taking them.
//! **`cc_2` re-derived all seven at `86d87486`**, and deliberately not by re-running
//! `cc_3`'s script: its own predicate written from the four content identities, its own
//! shell, and a control this file did not have. It then handed the result over as *evidence
//! rather than a decision*, because this file is `fln-conformance` and crossing into it to
//! move the constant would be the row-ownership violation one layer over. Both derivations
//! report 7 of 7 accepting on all four identities, with identical stable patch-ids.
//!
//! **`cc_2`'s added control is what makes "7 of 7" mean anything, and why the first control
//! did not suffice is the transferable part.** `be14ee9b` proves the predicate refuses a pair
//! the rewrite genuinely altered. It does not prove the predicate refuses two *unrelated*
//! commits — so a predicate that accepted everything handed to it would still have failed
//! `be14ee9b` for its own reasons while passing all seven. `cc_2` cross-paired **`fln-8zsq`'s
//! old anchor with `fln-kernel-bounded-decl-admission-ukzx`'s twin `419078c6`** — both rows
//! members of the accepted set, each with a twin of its own that passes — and the wrong
//! pairing is refused on every identity. **A negative control drawn from INSIDE the accepted
//! set is what separates a discriminating predicate from a permissive one**; a control drawn
//! only from known-bad material cannot.
//!
//! **That sentence names the rotted side by its ROW and not by its sha, and the reason is a
//! defect this file committed and `commit_anchor_reachability` caught within the minute.**
//! Writing the repaired sha into this prose *minted a fresh backup-only anchor* — the count
//! for this file went 1 to 2 against a one-way allowance, reddening the workspace, because
//! describing a rot repair in the obvious way reproduces the rot. The allowance may not be
//! raised to accommodate it; the prose has to stop creating referents it has just finished
//! proving unverifiable. **A rotted sha is not a safe thing to quote, even in a sentence
//! whose subject is that it is rotted.** `be14ee9b` remains and is the declared 1: it is the
//! one commit with no twin, so there is nothing to name it by instead.
//!
//! The class is at 0 and is not a permitted remainder: the census binds it by equality in
//! both directions, so a new unreachable anchor must RAISE it and its author must say so.
//!
//! **What this does not earn.** It classifies referents; it never establishes that a
//! *resolvable* citation supports the claim citing it, which is the harder join and is
//! untouched. A twin proves two commits carry the same *content*; it never proves the
//! sentence citing the anchor was sound. `never_existed` rests on `git log --all`, so a path
//! that lived only on a dropped branch misclassifies. The census is a measurement of this
//! tree at this commit, re-derived per run; the *ruling* above is `bounded_model` at one host.
//!
//! The header's `2eb09ba6` figures are left as measured **at that commit** rather than
//! silently refreshed, since a measurement carries the hash it was taken at. Re-derived at
//! `84e15401` after the two repairs above: **178 unresolvable of 591 citations across 191
//! coverage rows**, against 180 of 584 across 190. The manifest gained one coverage row and
//! seven citations from a peer in between, none of the seven unresolvable, so the entire
//! movement in the unresolvable figure is the two anchors repaired here.
//!
//! Re-derived again at `86d87486`, after the three `fln-amv` citations and these seven
//! twins: **171 unresolvable of 594 citations across 191 coverage rows**. The seven anchors
//! were repaired rather than withdrawn, so they moved from `commit_unreachable` to
//! `commit_reachable` and the citation total is unmoved by them — only the unresolvable
//! figure falls. [`FULLY_UNRESOLVABLE_ROWS`] and [`THIRD_STATE_ROWS`] stay at 14 and the
//! decomposition stays 7/4/3, because none of the five rows carrying a rotted anchor was
//! fully unresolvable: `cc_2` said so from its own reading and it is confirmed by
//! measurement here, which is the direction that matters — a claim about someone else's
//! arithmetic is worth re-deriving before it is landed on.

#![forbid(unsafe_code)]

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
    ("commit_unreachable", 0),
    ("present_but_untracked", 9),
    ("under_target_ephemeral", 7),
    ("existed_then_removed", 0),
];

/// Rows whose every citation is unresolvable **and** whose blocking kinds are all
/// never-denoted, so neither repair nor withdrawal is available. See the module header.
const THIRD_STATE_ROWS: usize = 14;

/// The third state decomposed by the **sole** blocking kind of each row — the same
/// disclosure as [`THIRD_STATE_ROWS`] at member granularity rather than population
/// granularity, and equality is required in both directions for the same reason it is there.
///
/// Binding only the total is a **budget**: a repair frees a slot the whole population can
/// refill, so a row moving between kinds is invisible and a new glob-only row lands green
/// the moment a rootless-leaf one is repaired. Measured, not reasoned — the mutant test
/// below moves one row between kinds and confirms the total does not budge.
const THIRD_STATE_BY_BLOCKING_KIND: &[(&str, usize)] =
    &[("rootless_leaf", 7), ("glob", 4), ("never_existed", 3)];

/// Third-state rows blocked by **more than one** never-denoted kind, which the module header
/// claims are none. Declared rather than asserted-away so that the first such row raises a
/// number its author must explain, instead of reddening as if it were a defect.
const THIRD_STATE_MULTI_KIND_ROWS: usize = 0;

/// Rows whose every citation is unresolvable.
///
/// This stood at 18 — one more than [`THIRD_STATE_ROWS`] — for as long as exactly one such
/// row carried a *recoverable* class alongside its never-denoted one: `wao6`, whose rotted
/// commit anchor sat beside a rootless leaf. That anchor is repaired, so **the gap is now
/// zero and every fully-unresolvable row is third-state**.
///
/// The two constants are deliberately kept separate rather than collapsed into one now that
/// they are equal. They measure different predicates, and merging them would make the next
/// recoverable-class row join a population this module declares *unrepairable* instead of
/// re-opening the gap and saying so.
const FULLY_UNRESOLVABLE_ROWS: usize = 14;

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

/// One pass over the classified rows. Named fields rather than a tuple because the
/// decomposition below makes six of them, and a positional `_` is how a reader stops seeing
/// which quantity a test is actually asserting on.
#[derive(Default)]
struct Measured {
    counts: BTreeMap<&'static str, usize>,
    total: usize,
    fully_unresolvable: usize,
    third_state: usize,
    /// Third-state rows keyed by their **sole** blocking kind. A row blocked by more than one
    /// kind is deliberately absent here and counted in `third_state_multi_kind` instead, so
    /// the decomposition sums to the population only together with that count — which is what
    /// makes dropping a row from one bucket a conservation failure rather than a smaller sum.
    third_state_by_kind: BTreeMap<&'static str, usize>,
    third_state_multi_kind: usize,
}

fn measure(rows: &[Row]) -> Measured {
    let mut m = Measured::default();
    for row in rows {
        for kind in &row.kinds {
            *m.counts.entry(*kind).or_default() += 1;
            m.total += 1;
        }
        let unresolvable: Vec<&&str> = row
            .kinds
            .iter()
            .filter(|kind| !RESOLVABLE.contains(kind) && !BY_DESIGN.contains(kind))
            .collect();
        if unresolvable.is_empty() || unresolvable.len() != row.kinds.len() {
            continue;
        }
        m.fully_unresolvable += 1;
        if unresolvable.iter().all(|kind| NEVER_DENOTED.contains(kind)) {
            m.third_state += 1;
            let blocking: Vec<&'static str> = unresolvable
                .iter()
                .map(|kind| **kind)
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
            // A slice pattern rather than a length test plus an unwrap: `[sole]` *is* the
            // single-kind case, so the exactly-one guarantee is carried by the type instead
            // of by a panic that the branch above has already made unreachable.
            match blocking.as_slice() {
                [sole] => *m.third_state_by_kind.entry(*sole).or_default() += 1,
                _ => m.third_state_multi_kind += 1,
            }
        }
    }
    m
}

/// The declared population must equal the measured one, class by class, in **both**
/// directions — and the classification must be total, which the conservation identity
/// asserts rather than assumes.
#[test]
fn the_unresolvable_citation_census_matches_the_measured_population() {
    let rows = scan();
    let Measured { counts, total, .. } = measure(&rows);
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
    let Measured {
        fully_unresolvable,
        third_state,
        ..
    } = measure(&rows);
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

/// The third state's **decomposition**, bound per member so a row moving between blocking
/// kinds cannot hide inside an unchanged total.
///
/// The test above binds a population's cardinality. This binds each member's, which is a
/// different guarantee and the one `fln-cross-tree-baked-root-k60n` paid to learn: an
/// aggregate is refilled by its own repairs. It is also the guard the header sentence needed
/// and did not have — that sentence read `10 rootless-leaf-only` while the total moved to 14,
/// and no grep for the total could ever have found it.
#[test]
fn the_third_state_decomposition_matches_the_measured_population() {
    let rows = scan();
    let m = measure(&rows);

    let mut disagreements = Vec::new();
    let mut declared_total = 0usize;
    for (kind, declared) in THIRD_STATE_BY_BLOCKING_KIND {
        assert!(
            NEVER_DENOTED.contains(kind),
            "the decomposition declares {kind:?}, which is not a never-denoted class — a \
             third-state row is blocked only by never-denoted kinds, so this row can never be \
             measured and would sit here permanently unfalsifiable"
        );
        declared_total += declared;
        let measured = m.third_state_by_kind.get(kind).copied().unwrap_or(0);
        if measured != *declared {
            disagreements.push(format!(
                "  {kind}: disclosed {declared}, measured {measured} ({:+})",
                measured as isize - *declared as isize
            ));
        }
    }
    for kind in m.third_state_by_kind.keys() {
        assert!(
            THIRD_STATE_BY_BLOCKING_KIND
                .iter()
                .any(|(declared, _)| declared == kind),
            "third-state rows are blocked by {kind:?} and the decomposition never mentions it \
             — an undeclared bucket is invisible to the equality above and to the conservation \
             identity below at the same time"
        );
    }

    assert!(
        disagreements.is_empty(),
        "the disclosed third-state decomposition no longer describes this manifest:\n{}\n\
         Equality is required in BOTH directions, exactly as for the census above. Note what \
         a passing TOTAL does not tell you: repairing a row of one kind frees a slot any \
         other kind can fill, so {} rows can be right while every bucket is wrong.",
        disagreements.join("\n"),
        m.third_state
    );
    assert_eq!(
        m.third_state_multi_kind, THIRD_STATE_MULTI_KIND_ROWS,
        "third-state rows blocked by more than one kind moved from \
         {THIRD_STATE_MULTI_KIND_ROWS} to {}. The module header claims every third-state row \
         is blocked by a SINGLE kind; raise this number and say so rather than softening the \
         sentence",
        m.third_state_multi_kind
    );
    assert_eq!(
        declared_total + m.third_state_multi_kind,
        m.third_state,
        "the decomposition sums to {declared_total} single-kind rows plus {} multi-kind, \
         against a third state of {} — conservation failed, so a row is double-counted or \
         dropped",
        m.third_state_multi_kind,
        m.third_state
    );
}

/// **The planted mutant for the decomposition, and the one that matters is the mutant an
/// aggregate-only guard cannot see.**
///
/// Two plants, because the two declarations fail for different reasons and a shared
/// assertion would let one ride the other:
///
/// 1. A third-state row **moved between blocking kinds**. The total is provably unmoved —
///    this test asserts that, so the claim that the old guard would have stayed green is
///    measured here rather than argued in the header.
/// 2. A **multi-kind** third-state row. [`THIRD_STATE_MULTI_KIND_ROWS`] is a declared zero,
///    so live data can never exercise it; a guard over a population driven to zero is
///    decorative, and only a synthetic member still kills the mutant.
#[test]
fn a_third_state_row_moving_between_blocking_kinds_is_caught_though_the_total_is_unmoved() {
    let rows = scan();
    let baseline = measure(&rows);
    assert!(
        baseline.third_state_by_kind.len() >= 2,
        "this plant needs at least two occupied buckets to move a row between; measured {:?} \
         — refusing a vacuous mutant rather than reporting a kill",
        baseline.third_state_by_kind
    );

    let clone = |rows: &[Row]| -> Vec<Row> {
        rows.iter()
            .map(|row| Row {
                bead: row.bead.clone(),
                kinds: row.kinds.clone(),
            })
            .collect()
    };
    let third_state_row = |rows: &[Row], kind: &str| -> usize {
        rows.iter()
            .position(|row| !row.kinds.is_empty() && row.kinds.iter().all(|k| *k == kind))
            .unwrap_or_else(|| {
                panic!(
                    "no third-state row is blocked solely by {kind:?} — the plant has no subject"
                )
            })
    };

    // 1. Move one rootless-leaf-only row to glob-only. Same row count, same total.
    let mut moved = clone(&rows);
    let subject = third_state_row(&moved, "rootless_leaf");
    moved[subject].kinds = vec!["glob"; moved[subject].kinds.len()];
    let mutant = measure(&moved);
    assert_eq!(
        mutant.third_state, baseline.third_state,
        "the plant was supposed to leave the TOTAL unmoved; if it moves the total then this \
         mutant is killed by the aggregate guard and proves nothing about this one"
    );
    assert_ne!(
        mutant.third_state_by_kind, baseline.third_state_by_kind,
        "moving a row between blocking kinds did not move the decomposition, so this guard \
         cannot see the one thing the aggregate guard is blind to"
    );
    // Asserted against the BASELINE MEASUREMENT, never against the declared constant. This
    // test's subject is the production predicate; coupling it to the declaration makes a
    // mutated constant kill it as well, and a mutant that dies at two cells has not told you
    // which one was load-bearing. Measured: doing exactly that made m2 and m4 die here too.
    let bucket = |m: &Measured, kind: &str| m.third_state_by_kind.get(kind).copied().unwrap_or(0);
    assert_eq!(
        bucket(&mutant, "rootless_leaf"),
        bucket(&baseline, "rootless_leaf") - 1,
        "the moved row did not leave the rootless_leaf bucket"
    );
    assert_eq!(
        bucket(&mutant, "glob"),
        bucket(&baseline, "glob") + 1,
        "the moved row did not arrive in the glob bucket, so the decomposition tracks the \
         row's identity rather than its blocking kind"
    );

    // 2. A synthetic multi-kind third-state row, since the declared population is zero.
    let mut multi = clone(&rows);
    multi.push(Row {
        bead: "planted-multi-kind-decoy".to_owned(),
        kinds: vec!["rootless_leaf", "glob"],
    });
    let mutant = measure(&multi);
    assert_eq!(
        mutant.third_state_multi_kind,
        baseline.third_state_multi_kind + 1,
        "a planted row blocked by two never-denoted kinds was not counted as multi-kind, so \
         the single-kind claim in the module header rests on nothing"
    );
    assert_eq!(
        mutant.third_state,
        baseline.third_state + 1,
        "the planted multi-kind row must still be a third-state row; if it is not, the decoy \
         lands outside the population it was built to probe"
    );
    assert_eq!(
        mutant.third_state_by_kind, baseline.third_state_by_kind,
        "a multi-kind row must be absent from the per-kind buckets, or it is counted twice \
         and the conservation identity is satisfied by an accident"
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
    let baseline = measure(&rows).counts;

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

        let mutant = measure(&mutated).counts;
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
    let m = measure(&empty);
    assert!(m.counts.is_empty() && m.total == 0 && m.fully_unresolvable == 0);
    assert!(
        m.third_state == 0 && m.third_state_by_kind.is_empty() && m.third_state_multi_kind == 0,
        "an empty scan must produce an empty decomposition, not a partial one"
    );
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
    let declared_third: usize = THIRD_STATE_BY_BLOCKING_KIND.iter().map(|(_, n)| n).sum();
    assert!(
        declared_third > 0,
        "an all-zero decomposition would agree with an empty scan for the same reason"
    );
}
