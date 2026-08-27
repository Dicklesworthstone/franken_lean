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
//! **`rootless_leaf` moved 121 -> 99 because the CLASSIFIER was wrong, not because anything
//! was repaired, and this is the one movement in this file that is neither.** `classify`
//! tested the *shape* rule — no `/`, therefore no root, therefore nothing to resolve against
//! — **before** it tested tracked-ness. So a citation naming a tracked file at the
//! repository root scored as never-denoted: `AGENTS.md` fourteen times, `README.md` four,
//! plus `Cargo.lock`, `rust-toolchain.toml`, `ABI_CONTRACT.md` and `OLEAN_CONTRACT.md` —
//! **22 citations across 14 rows**, every one of them denoting exactly one file. The shape
//! rule's own rationale is that supplying a root would make the *checker* pick one; nothing
//! is picked here, because `git ls-files` already contains the string verbatim.
//!
//! **What located it was two implementations disagreeing.** The `povo` population script,
//! written independently against the same manifest, tests `a in tracked` first and has been
//! reporting `rootless_leaf 99` for as long as this file reported 120. Neither number was
//! ever checked against the other, because the two scans report different totals and nobody
//! had reason to line up a sub-class. The gap is exactly the 22. A second implementation is
//! worth its cost precisely for the case where the first one is confidently wrong, and the
//! comparison that finds it is a *class*, not a total.
//!
//! Note which direction the error ran: the census **over-stated** its own defect population
//! by 22 and was never at risk of hiding one, and the constant moved DOWN as the definition
//! sharpened. That is not a repair and must not be read as one — no citation improved. It is
//! also not a class boundary softened to go green, the move this file's own failure message
//! warns about: it landed while the guard was RED for an unrelated reason, it lowers a number
//! the guard had just successfully raised, and the reclassified members are enumerable and
//! enumerated above.
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

//!
//! **A second law now lives in this file, over the same classification and in the opposite
//! direction** (bead `franken_lean-ephemeral-manifest-artifact-povo`). Everything above
//! *discloses* a measured population by equality; [`UNTRACKED_PATH_CITATION_DEBT`] *refuses* a
//! new member of one sub-population — the citations naming a repository path `git ls-files`
//! does not contain — bound per `(bead, entry)` rather than per class. The two are not
//! redundant and neither is sufficient: equality on a class total stops the population
//! growing and cannot see a repair funding a swap, and one-way membership per member sees the
//! swap and permits the total to fall. They are stated together here because a reader who
//! finds one will assume it is the whole law.
//!
//! **And that second law is itself a SECOND declaration of a population the validator already
//! knows how to judge.** `scripts/evidence.py` implements `povo`'s repair decision today, in
//! the place the bead asks for it, and validates nothing because its registry file has never
//! been minted — so the Rust law is the only one that fires, and the day the registry appears
//! there are two. [`povo_validator_is_unadopted`] carries that whole measurement and fails on
//! the event; do not re-derive it from this paragraph.
//!
//! Note what sharing the file buys and what it costs. The classifier is written once, so the
//! two laws can never disagree about what "untracked" means — the disagreement that cost this
//! census 22 citations was between two *implementations*, and there is only one here. The cost
//! is that a single red now has two possible authors, which the failure messages separate by
//! naming their bead.

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
    // 99 -> 94 at this commit: five bare run-artifact filenames on `franken_lean-rps`
    // (`run.ndjson`, `human.log`, `human.semantic.log`, `manifest.json`,
    // `bundle.complete.json`) replaced by the tracked producer that made them,
    // `scripts/e2e/hash_identity.sh`, with the run's own bytes recorded as lost. A repair
    // lowers this census and owes the same commit -- and this guard is what said so, on a
    // commit whose author had already re-derived two other populations and still missed
    // this one.
    ("rootless_leaf", 94),
    ("glob", 20),
    // 15 -> 13 at 8042d789: two citations of `crates/fln-syntax/src/syntax.rs`, a path with
    // zero commits in the object store, repointed to `crates/fln-syntax/src/tree.rs`, which
    // carries the `pub enum Syntax` and the kind/atom/node/missing forms those two beads name.
    // A repair shrinks this census, and the disclosure owes the same commit -- I did not, and
    // this guard caught it.
    ("never_existed", 13),
    ("commit_unreachable", 0),
    ("present_but_untracked", 9),
    // 7 -> 6: measured 6 unresolvable under_target_ephemeral citations.
    ("under_target_ephemeral", 6),
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
    "gh-run:",
];

/// **The `povo` debt: every untracked path citation live in the manifest, declared PER
/// MEMBER** (bead `franken_lean-ephemeral-manifest-artifact-povo`).
///
/// That bead's repair decision is one predicate: a repository path citation must "normalize
/// inside the repository, be a regular non-symlink file, and be **Git-tracked**. Existence
/// without tracked durability does not count." Its acceptance criterion was tightened on
/// 2026-07-27 from *zero `target/` citations* to **zero untracked citations**, on the
/// measurement that the original caught 3 of 18 dangling citations and tracked-ness catches
/// 18 of 18. That criterion was not met at this table's `84f35ea6` derivation — 150
/// citations across 48 rows failed it — so what lands here is the half that can be honest
/// now: the debt is **declared**, and no new member may join it silently.
///
/// **Why per member and not per class, which is the whole reason this exists beside a census
/// that already binds the totals.** [`UNRESOLVABLE_CENSUS`] pins each class by equality in
/// both directions, so the population cannot *grow*. It is still an aggregate, and
/// `fln-cross-tree-baked-root-k60n` measured what that costs over 70 commits: one repair took
/// a total from 44 to 38 and four new unprotected rigs then landed in four separate commits
/// under a guard that was green the whole time, because the total never came back. An
/// aggregate is a budget its own repairs refill. Repair one `rootless_leaf` citation here and
/// the class count frees a slot any other row may take — the census sees 99 either way. This
/// table keys on `(bead, entry)`, so a repair frees a slot only in the row that earned it and
/// a new row has no slot at all.
///
/// **The direction is one-way membership, and the missing half is disclosed rather than
/// built.** Every *measured* untracked citation must appear here; a declared entry that no
/// longer denotes one is **not** a failure. Reverse membership reddens the commit doing the
/// repair, which is a wall this repository has already paid for (`igxr`), and the reward for
/// repairing a row must not be a red build. The cost is stated plainly: this table is an
/// **upper bound** on the live debt, never a count of it. What stops it drifting upward while
/// the table drifts down is the sibling equality binding in [`UNRESOLVABLE_CENSUS`], which
/// forces the same commit to lower a class count — the two laws are load-bearing together and
/// neither is sufficient alone.
///
/// Derived at `84f35ea6` by a second implementation (`povo_population.py`, which has tested
/// tracked-ness first since before the Rust classifier did) and reconciled against this file's
/// own classifier **per class**, not per total: 99 / 20 / 15 / 9 / 7 / 0. A total that agrees
/// is worth much less — the two implementations agreed on no total for their whole
/// co-existence while disagreeing by 22 inside one class.
const UNTRACKED_PATH_CITATION_DEBT: &[(&str, &[&str])] = &[
    ("fln-1dxv", &["tribunal/epoch-lab/tests"]),
    (
        "fln-22i1",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    ("fln-23cz", &["crates/fln-syntax/src/syntax.rs"]),
    (
        "fln-3oj6",
        &["tools/structure-guard/kernel-ownership-publisher"],
    ),
    (
        "fln-3tye",
        &[
            "contracts/builtin_environment.tsv",
            "contracts/builtin_partition.tsv",
        ],
    ),
    ("fln-4l15", &["tribunal/epoch-lab/tests"]),
    ("fln-8138", &["bundle.complete.json", "run.ndjson"]),
    (
        "fln-9wya",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "fln-amv.1",
        &[
            "bundle.complete.json",
            "human.log",
            "human.semantic.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "fln-amv.12",
        &[
            "bundle.complete.json",
            "human.log",
            "human.semantic.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "fln-amv.2",
        &[
            "bundle.complete.json",
            "human.log",
            "human.semantic.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "fln-extension-history-checkpoint-identity-41s",
        &[
            "env-snapshots/*/bundle.complete.json",
            "env-snapshots/*/environment_state.out",
            "env-snapshots/*/environment_state.validation.json",
            "env-snapshots/*/run.ndjson",
        ],
    ),
    (
        "fln-extension-merge-validation-proof-debt-dt5",
        &["target/e2e/env-snapshots-20260727T001352Z-4170014"],
    ),
    ("fln-fei1", &["tribunal/epoch-lab/tests"]),
    (
        "fln-g6d1",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
            "self-test.json",
        ],
    ),
    (
        "fln-giap",
        &[
            "epoch-lab-live-verify.log",
            "epoch-lab-test.log",
            "run.ndjson",
        ],
    ),
    (
        "fln-history-rewrite-evidence-anchor-reachability-vdi4",
        &[
            "crates/fln-syntax/tests/corpus/golden_vellum.json",
            "crates/fln-syntax/tests/corpus/golden_vellum.provenance.json",
            "target/check/check-20260727T004746Z-310405",
            "target/check/check-20260727T025920Z-1712638",
        ],
    ),
    (
        "fln-identity-path-mutant-recovery-mbco",
        &[
            "env-snapshots/*/declaration-membership-fln-amv.1/bundle.complete.json",
            "env-snapshots/*/declaration-tag-matrix-fln-amv.12/bundle.complete.json",
            "env-snapshots/*/extension-descriptor-matrix-fln-amv.2/bundle.complete.json",
            "env-snapshots/*/manifest.json",
        ],
    ),
    (
        "fln-k5rr",
        &[
            "bundle.complete.json",
            "human.log",
            "human.semantic.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "fln-pu6i",
        &[
            "bundle.complete.json",
            "crates/fln-verdict/tests/CERTIFICATE_GOLDENS_PROVENANCE.md",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    ("fln-q3u4", &["tribunal/epoch-lab/MANIFEST.txt"]),
    (
        "fln-rwz",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    ("fln-rzyk", &["tribunal/epoch-lab/tests"]),
    (
        "fln-sr2z",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "fln-stc1",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    ("fln-uuuz", &["target/check/check-20260726T234804Z-3984739"]),
    ("fln-yk3t", &["run.ndjson", "ubs-inventory.json"]),
    (
        "fln-zti3",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "franken_lean-1fxz",
        &[
            "bundle.complete.json",
            "human.log",
            "human.semantic.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "franken_lean-1umc",
        &[
            "env-snapshots/*/bundle.complete.json",
            "env-snapshots/*/collision-fln-amv.10",
            "env-snapshots/*/declaration-membership-fln-amv.1",
            "env-snapshots/*/declaration-tag-matrix-fln-amv.12",
            "env-snapshots/*/extension-descriptor-matrix-fln-amv.2",
            "env-snapshots/*/resource-collision-fln-amv.13",
        ],
    ),
    (
        "franken_lean-2tcr",
        &["target/e2e/env-snapshots-20260727T021342Z-1240844"],
    ),
    (
        "franken_lean-83pz",
        &[
            "resource-collision-fln-amv.13/bundle.complete.json",
            "resource-collision-fln-amv.13/manifest.json",
            "resource-collision-fln-amv.13/run.ndjson",
        ],
    ),
    ("franken_lean-869w", &["tribunal/epoch-lab/tests"]),
    (
        "franken_lean-9iqa",
        &[
            "bundle.complete.json",
            "human.log",
            "human.semantic.log",
            "manifest.json",
            "run.ndjson",
            "ubs-inventory.json",
        ],
    ),
    (
        "franken_lean-9km",
        &[
            "target/check/check-20260801T084038Z-1040064",
            "target/e2e/dynamic-parser-no-mock-20260801T075736Z-470570",
        ],
    ),
    ("franken_lean-9pnc", &["tribunal/epoch-lab/tests"]),
    (
        "franken_lean-build-gate-lane-governed-set-98np",
        &["target/check/check-20260727T004746Z-310405"],
    ),
    (
        "franken_lean-ex54",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "franken_lean-h5z1",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "franken_lean-j8h-admission-lane-seeds-vss4",
        &[
            "env-snapshots/*/bundle.complete.json",
            "env-snapshots/*/declaration_budget_check_omission_mutant.err",
            "env-snapshots/*/declaration_bytes_unit_hardcoded_mutant.err",
            "env-snapshots/*/declaration_cancellation_as_resource_mutant.err",
            "env-snapshots/*/declaration_plan_base_binding_omission_mutant.err",
            "env-snapshots/*/run.ndjson",
        ],
    ),
    (
        "franken_lean-lsz5",
        &[
            "gate-self-test/bundle.complete.json",
            "gate-self-test/manifest.json",
            "gate-self-test/run.ndjson",
        ],
    ),
    (
        "franken_lean-lu5",
        &["target/check/check-20260725T190953Z-814126/bundle.complete.json"],
    ),
    (
        "franken_lean-mrlo",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "franken_lean-r4m8",
        &["bundle.complete.json", "manifest.json", "run.ndjson"],
    ),
    (
        "franken_lean-rps",
        &[
            "bundle.complete.json",
            "human.log",
            "human.semantic.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    (
        "franken_lean-rur",
        &[
            "bundle.complete.json",
            "human.log",
            "human.semantic.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
    ("franken_lean-tkr2", &["crates/fln-syntax/src/syntax.rs"]),
    (
        "franken_lean-vugo",
        &[
            "gate-self-test/bundle.complete.json",
            "gate-self-test/manifest.json",
            "gate-self-test/run.ndjson",
        ],
    ),
    (
        "franken_lean-w75y",
        &[
            "bundle.complete.json",
            "human.log",
            "manifest.json",
            "run.ndjson",
        ],
    ),
];

/// Does this class mean *the citation names a repository path `git ls-files` does not
/// contain*?
///
/// **Derived from [`UNRESOLVABLE_CENSUS`], never hand-listed**, so a class added to the
/// classifier joins `povo`'s law by construction instead of escaping it until somebody
/// notices — which is the failure this file's own header records for `existed_then_removed`
/// and the reason `AGENTS.md` asks that a guard's scope come from the artifact's own fields.
/// The one unresolvable class that is *not* a path is the commit anchor, and the cardinality
/// of that exclusion is asserted rather than assumed by the test below.
fn is_untracked_path_kind(kind: &str) -> bool {
    UNRESOLVABLE_CENSUS.iter().any(|(class, _)| *class == kind) && !kind.starts_with("commit_")
}

/// **This law's whole justification is that a capability is ABSENT, and that shape rots
/// silently** — the defect family `fln-disclosed-unknowns-rot` is named for.
///
/// `scripts/evidence.py` **already implements `povo`'s repair decision**, committed, in the
/// place the bead asks for it: `verification_artifact_classification` types every citation,
/// `target_path` raises unconditionally rather than on an existence probe, a legacy allowance
/// is keyed per `(bead, artifact)` with a content-addressed `pair_id`, and
/// `receipt:sha256:<64hex>` is criterion 3's durable reference. That is not this file's
/// discovery to claim; it is another pane's work.
///
/// It does **nothing today**. `ci/VERIFICATION_EVIDENCE_RECEIPTS.jsonl` does not exist, so
/// `validate-verification-manifest` reports `artifact_reference_validation:
/// not_adopted_registry_absent`, scans every artifact pair, validates none of them, and exits
/// **0** — measured at `cf9ac40f` from the committed copy and from the `h4o1` working copy
/// separately, both identical, so the orphan is not the reason either.
///
/// **So the debt is declared TWICE the moment that registry is minted** — once here, once as
/// `legacy-artifact` rows carrying `tracking_bead: povo`. Two declarations of one population,
/// free to drift, is the defect this whole module exists inside. Nothing would say so, because
/// the event that makes the duplication live is a *file appearing* rather than a line changing.
/// [`povo_validator_is_unadopted`] is that join, and it fails on exactly that event.
fn povo_validator_is_unadopted<'src>(
    root: &Path,
    evidence_source: &'src str,
) -> Result<&'src str, String> {
    // Derived from the validator's own source, never transcribed: renaming either constant
    // fails here rather than leaving this guard probing a path nobody writes any more.
    let registry = evidence_source
        .split_once("VERIFICATION_EVIDENCE_REGISTRY_PATH = (")
        .and_then(|(_, rest)| rest.split_once('"'))
        .and_then(|(_, rest)| rest.split_once('"'))
        .map(|(path, _)| path)
        .ok_or_else(|| {
            "VERIFICATION_EVIDENCE_REGISTRY_PATH is no longer readable out of \
             scripts/evidence.py, so this guard cannot name the file whose appearance it is \
             watching for — a broken scan, not an unadopted validator"
                .to_owned()
        })?;
    let tracking = evidence_source
        .split_once("VERIFICATION_LEGACY_TRACKING_BEAD = (")
        .and_then(|(_, rest)| rest.split_once('"'))
        .and_then(|(_, rest)| rest.split_once('"'))
        .map(|(bead, _)| bead)
        .ok_or_else(|| {
            "VERIFICATION_LEGACY_TRACKING_BEAD is no longer readable out of \
             scripts/evidence.py"
                .to_owned()
        })?;
    if tracking != POVO_BEAD {
        return Err(format!(
            "the validator's legacy debt is tracked by {tracking:?}, not by {POVO_BEAD:?}. The \
             two declarations of this population are no longer even pointed at the same bead"
        ));
    }
    if root.join(registry).exists() {
        return Err(format!(
            "{registry} EXISTS, so the validator's artifact-reference validation is ADOPTED and \
             this file's UNTRACKED_PATH_CITATION_DEBT is now a SECOND declaration of the same \
             population, keyed differently and free to drift from it. Reconcile them in one \
             commit: either bind this table to the registry's `legacy-artifact` rows, or delete \
             it and say in the module header that the validator carries the law. Do not raise \
             a number to go green — there is no number here to raise."
        ));
    }
    Ok(registry)
}

/// The verdict of `povo`'s law over a population: how many measured untracked citations the
/// debt above accounts for, and which ones it does not.
///
/// A `Result`-shaped pure function over the population rather than an inline
/// `assert!(…is_empty())`, because the union form the test uses — real rows **plus** planted
/// members, one assertion naming exactly the plants — needs the verdict as a value. That
/// shape is what makes gutting the refusal and gutting the plant *both* fail; two separate
/// tests leave the live assertion unkillable once the population it watches is repaired.
#[derive(Debug, Default, PartialEq, Eq)]
struct UntrackedVerdict {
    declared: usize,
    undeclared: Vec<String>,
}

fn judge_untracked_citations(rows: &[Row], debt: &[(&str, &[&str])]) -> UntrackedVerdict {
    let mut verdict = UntrackedVerdict::default();
    for row in rows {
        for cite in &row.cites {
            if !is_untracked_path_kind(cite.kind) {
                continue;
            }
            let permitted = debt
                .iter()
                .find(|(bead, _)| *bead == row.bead)
                .is_some_and(|(_, entries)| entries.contains(&cite.entry.as_str()));
            if permitted {
                verdict.declared += 1;
            } else {
                verdict
                    .undeclared
                    .push(format!("{} :: {} ({})", row.bead, cite.entry, cite.kind));
            }
        }
    }
    verdict.undeclared.sort();
    verdict
}

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
    if tracked.contains(entry) {
        // Tested BEFORE the shape rule below, and the order is the whole point. A citation
        // that is EXACTLY a tracked path denotes exactly one file whether or not it carries a
        // slash — `AGENTS.md`, `README.md`, `Cargo.lock`, `rust-toolchain.toml`. The rootless
        // rule's own rationale is that supplying a root would make the CHECKER pick one; here
        // no root is supplied and none is picked, because `git ls-files` already contains the
        // string verbatim. Shape-first misclassified 22 citations across 14 rows as
        // never-denoted, which is why this class read 121 while the independently written
        // povo population script read 99 over the same manifest. Two implementations
        // disagreeing by exactly the tracked repo-root files is what located it.
        return "tracked_exists";
    }
    if !entry.contains('/') {
        // A rootless leaf states no root, so there is nothing to resolve it against. The
        // root must be stated in the ROW; supplying one in the checker would resolve all 120
        // against a directory the checker picked and prove nothing.
        return "rootless_leaf";
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

/// One artifact citation and the class it landed in.
///
/// The entry string is retained rather than discarded after classification, because the two
/// laws in this file need different halves of it: the census arithmetic below needs only the
/// **kind**, and `povo`'s per-member debt needs the **entry** as well. A second walk that
/// re-read the manifest for the strings would be a second implementation of the classifier —
/// the defect family this file exists inside.
#[derive(Clone)]
struct Cite {
    entry: String,
    kind: &'static str,
}

struct Row {
    bead: String,
    cites: Vec<Cite>,
}

impl Row {
    fn kinds(&self) -> impl Iterator<Item = &'static str> + '_ {
        self.cites.iter().map(|cite| cite.kind)
    }
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
        let cites = artifacts
            .iter()
            .map(|entry| Cite {
                kind: classify(&root, entry, &tracked),
                entry: entry.clone(),
            })
            .collect();
        rows.push(Row { bead, cites });
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
        for kind in row.kinds() {
            *m.counts.entry(kind).or_default() += 1;
            m.total += 1;
        }
        let unresolvable: Vec<&'static str> = row
            .kinds()
            .filter(|kind| !RESOLVABLE.contains(kind) && !BY_DESIGN.contains(kind))
            .collect();
        if unresolvable.is_empty() || unresolvable.len() != row.cites.len() {
            continue;
        }
        m.fully_unresolvable += 1;
        if unresolvable.iter().all(|kind| NEVER_DENOTED.contains(kind)) {
            m.third_state += 1;
            let blocking: Vec<&'static str> = unresolvable
                .iter()
                .copied()
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
                cites: row.cites.clone(),
            })
            .collect()
    };
    let third_state_row = |rows: &[Row], kind: &str| -> usize {
        rows.iter()
            .position(|row| !row.cites.is_empty() && row.kinds().all(|k| k == kind))
            .unwrap_or_else(|| {
                panic!(
                    "no third-state row is blocked solely by {kind:?} — the plant has no subject"
                )
            })
    };

    // 1. Move one rootless-leaf-only row to glob-only. Same row count, same total.
    let mut moved = clone(&rows);
    let subject = third_state_row(&moved, "rootless_leaf");
    for cite in &mut moved[subject].cites {
        cite.kind = "glob";
    }
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
        cites: vec![
            Cite {
                entry: "planted_decoy_artifact.ndjson".to_owned(),
                kind: "rootless_leaf",
            },
            Cite {
                entry: "env-snapshots/*/planted-decoy".to_owned(),
                kind: "glob",
            },
        ],
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
                cites: row.cites.clone(),
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
        mutated[0].cites.push(Cite {
            entry: planted.to_owned(),
            kind: observed,
        });

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

/// The bead this file's second law serves, and the bead the validator's own legacy-debt design
/// names as its tracking bead. Written once so the two uses cannot drift apart.
const POVO_BEAD: &str = "franken_lean-ephemeral-manifest-artifact-povo";

/// **The join between this file's debt and the validator's, which fails the day the second one
/// goes live.** See [`povo_validator_is_unadopted`] for why that day is the hazard.
///
/// Three cells through the **same** decision the production path makes, because a live
/// assertion that the registry is absent is unkillable while it is absent — deleting it changes
/// no verdict. Cell 2 is the positive control for the probe itself: a path that certainly
/// exists must come back ADOPTED, so hardcoding the existence test to `false` fails here rather
/// than passing quietly until the real file lands.
#[test]
fn this_files_debt_is_the_second_declaration_and_says_so_the_day_the_validator_is_adopted() {
    let root = fln_conformance::checked_workspace_root!();
    let source = std::fs::read_to_string(root.join("scripts/evidence.py"))
        .expect("the validator's source must be readable; this guard is derived from it");

    let registry = povo_validator_is_unadopted(&root, &source).unwrap_or_else(|why| {
        panic!("povo (bead {POVO_BEAD}): {why}");
    });
    assert_eq!(
        registry, "ci/VERIFICATION_EVIDENCE_RECEIPTS.jsonl",
        "the registry path derived from scripts/evidence.py is not the one this module's header \
         describes, so the header's measurement no longer describes the file it was taken from"
    );

    // The probe reads the filesystem — proved against a path that certainly exists rather than
    // asserted. Without this cell the existence test can be gutted and nothing fails until the
    // real registry appears, which is exactly the moment this guard exists for.
    let control = source.replace(
        "VERIFICATION_EVIDENCE_REGISTRY_PATH = (\n    \"ci/VERIFICATION_EVIDENCE_RECEIPTS.jsonl\"",
        "VERIFICATION_EVIDENCE_REGISTRY_PATH = (\n    \"ci/VERIFICATION_MANIFEST.jsonl\"",
    );
    assert_ne!(
        control, source,
        "the positive control did not plant anything — the constant's spelling moved, so this \
         cell would pass vacuously"
    );
    let adopted = povo_validator_is_unadopted(&root, &control).expect_err(
        "a registry path that EXISTS must read as adopted, or this guard is not \
                     reading the filesystem at all",
    );
    assert!(
        adopted.contains("EXISTS") && adopted.contains("SECOND declaration"),
        "the adopted refusal must name the duplication rather than merely fail: {adopted}"
    );

    // A tracking bead that stops naming povo is the other way the join dies.
    let renamed = source.replace(POVO_BEAD, "franken_lean-some-other-bead");
    assert_ne!(
        renamed, source,
        "the tracking-bead plant did not plant anything"
    );
    let mismatch = povo_validator_is_unadopted(&root, &renamed)
        .expect_err("a tracking bead that is not povo must be refused");
    assert!(
        mismatch.contains("tracked by"),
        "the mismatch refusal must name the bead it found: {mismatch}"
    );
}

/// **The wall check: repairing a citation while leaving the debt table alone must stay
/// GREEN.**
///
/// The direction of a declared-remainder guard decides whether it survives the repair it is
/// asking for, and two of the three available directions hand the repairer a red build as the
/// reward for doing the work: "every declared entry is still measured" reddens on repair, and
/// equality on the table's length reddens on both repair and extension. Only one-way
/// membership survives, and *reviewing the law is not enough* — a precondition inside the test
/// inherits the same question and has broken this way before.
///
/// So it is measured rather than argued. The repair is simulated in memory: one declared row
/// loses every untracked citation it had, the table is untouched, and the verdict must not
/// gain an entry. Nothing writes to `ci/VERIFICATION_MANIFEST.jsonl` — it is a shared file in
/// a shared checkout and a transient edit to it is a governed-input mutation that can end
/// another pane's lane.
///
/// This cell deliberately does **not** assert that the live manifest is clean; the law's own
/// test does that. A real undeclared citation must kill exactly one test, or a reader cannot
/// tell which property was load-bearing.
#[test]
fn repairing_a_declared_citation_without_touching_the_debt_does_not_redden() {
    let rows = scan();
    let before = judge_untracked_citations(&rows, UNTRACKED_PATH_CITATION_DEBT);

    let subject = rows
        .iter()
        .position(|row| {
            row.cites
                .iter()
                .any(|cite| is_untracked_path_kind(cite.kind))
        })
        .expect(
            "no row carries an untracked path citation, so this cell simulates nothing. If \
             povo's debt is genuinely repaired to zero, this test must be rebuilt against a \
             synthetic row rather than deleted — a guard whose population has emptied stops \
             checking anything, silently.",
        );
    let repaired: Vec<Row> = rows
        .iter()
        .enumerate()
        .map(|(index, row)| Row {
            bead: row.bead.clone(),
            cites: row
                .cites
                .iter()
                .filter(|cite| index != subject || !is_untracked_path_kind(cite.kind))
                .cloned()
                .collect(),
        })
        .collect();

    let after = judge_untracked_citations(&repaired, UNTRACKED_PATH_CITATION_DEBT);
    assert!(
        after.declared < before.declared,
        "the simulated repair removed no declared citation ({} before, {} after), so this cell \
         controls nothing and would pass against any law at all",
        before.declared,
        after.declared
    );
    assert_eq!(
        after.undeclared, before.undeclared,
        "povo's law has become a WALL: repairing row {:?} — deleting untracked citations and \
         touching nothing else — made the verdict grow. A declared entry that no longer denotes \
         a live citation must be permitted, because the alternative reddens the commit doing \
         the repair. The debt table is an UPPER BOUND on the live population by design; what \
         stops it drifting upward is UNRESOLVABLE_CENSUS's equality binding, not this law.",
        rows[subject].bead
    );
}

/// **`povo`'s law: no untracked path citation may enter the manifest undeclared.**
///
/// Judged over the **union** of the real population and two planted members, in one
/// assertion, because that is the only shape in which both halves are killable per commit. A
/// separate "the real tree is clean" test plus a separate "a plant is refused" test leaves the
/// live assertion decorative the day the debt is repaired to zero — measured on
/// `fln-cross-tree-baked-root-k60n`, where a mutant survived every live guard and died only at
/// a synthetic plant. Here, gutting the refusal drops both plants from the verdict and gutting
/// a plant drops one, while a real row that gained an undeclared citation *joins* the verdict:
/// all three fail the same equality.
///
/// **Two plants, because one of them is the only cell that can tell this law from an
/// artifact-keyed one.** Plant A cites a string declared for nobody, which any matching at all
/// refuses. Plant B cites a string this table genuinely declares — **for a different bead** —
/// which a check keyed on the citation rather than on `(bead, entry)` would wave through, and
/// that is precisely the budget-refilling shape `k60n` measured. Plant B's entry is *derived*
/// from the debt table rather than written here, so it cannot rot into naming something the
/// table no longer declares.
#[test]
fn an_undeclared_untracked_path_citation_is_refused_and_a_foreign_member_cannot_borrow_a_slot() {
    // The exclusion in `is_untracked_path_kind` is a negation, and a negation over a derived
    // set is exactly where a silent widening hides: if a second `commit_*` class appeared, or
    // the only one were renamed, the law would quietly change scope with no line moving here.
    let commit_classes = UNRESOLVABLE_CENSUS
        .iter()
        .filter(|(class, _)| class.starts_with("commit_"))
        .count();
    assert_eq!(
        commit_classes, 1,
        "povo's law is `every unresolvable class EXCEPT the commit anchor`, so exactly one \
         class may be excluded; {commit_classes} match, which means the exclusion no longer \
         says what this file claims it says"
    );

    let root = fln_conformance::checked_workspace_root!();
    let mut rows = scan();

    // Classified by the PRODUCTION classifier rather than hand-labelled: a plant that carries
    // its own verdict tests the comparison and not the thing being compared.
    let unknown = "target/check/check-19700101T000000Z-0/planted-decoy.json";
    let unknown_kind = classify(&root, unknown, &BTreeSet::new());
    let foreign = UNTRACKED_PATH_CITATION_DEBT
        .iter()
        .find_map(|(_, entries)| entries.first().copied())
        .unwrap_or_else(|| {
            panic!(
                "the debt table is EMPTY, so povo's remainder is repaired and the \
                 foreign-member plant has no subject. This panic is that conversion falling \
                 due, not a defect: a membership law scoped to an empty remainder checks \
                 nothing at all, silently, exactly when the surviving rows become load-bearing \
                 published claims. Rebuild this cell against a synthetic table."
            )
        });
    let foreign_kind = classify(&root, foreign, &BTreeSet::new());
    for (entry, kind) in [(unknown, unknown_kind), (foreign, foreign_kind)] {
        assert!(
            is_untracked_path_kind(kind),
            "the planted citation {entry:?} classifies as {kind:?}, which povo's law does not \
             govern — a plant outside the population controls nothing"
        );
    }

    let plant_a = "povo-planted-decoy-unknown-citation";
    let plant_b = "povo-planted-decoy-foreign-member";
    // Plant C is the NEGATION's plant, and without it that half of the law is inert. The
    // commit-anchor exclusion is subsumed by live data — `commit_unreachable` measures 0 today
    // — so deleting it from `is_untracked_path_kind` changes no verdict and no test fails: the
    // unkillable-declaration shape this repository has already measured. Planting a citation
    // of that class puts the exclusion back in the assertion's path, where deleting it makes C
    // appear among the refusals and the equality below fail. The class is *derived* from the
    // census rather than typed, so a rename cannot leave the plant probing a class that is
    // gone. Its kind is supplied rather than classified deliberately: `classify` would need a
    // real 40-hex sha in this source, and a sha written into a tracked file is a fresh
    // commit-anchor citation — `da1adcb9`'s lesson, where prose about a rotted anchor minted
    // one.
    let plant_c = "povo-planted-decoy-commit-anchor";
    let commit_class = UNRESOLVABLE_CENSUS
        .iter()
        .find(|(class, _)| class.starts_with("commit_"))
        .map(|(class, _)| *class)
        .expect("the commit-anchor class must be disclosed for the exclusion to have a subject");
    rows.push(Row {
        bead: plant_c.to_owned(),
        cites: vec![Cite {
            entry: "commit:planted-decoy-deliberately-not-a-sha".to_owned(),
            kind: commit_class,
        }],
    });
    rows.push(Row {
        bead: plant_a.to_owned(),
        cites: vec![Cite {
            entry: unknown.to_owned(),
            kind: unknown_kind,
        }],
    });
    rows.push(Row {
        bead: plant_b.to_owned(),
        cites: vec![Cite {
            entry: foreign.to_owned(),
            kind: foreign_kind,
        }],
    });

    let verdict = judge_untracked_citations(&rows, UNTRACKED_PATH_CITATION_DEBT);
    let mut expected = vec![
        format!("{plant_a} :: {unknown} ({unknown_kind})"),
        format!("{plant_b} :: {foreign} ({foreign_kind})"),
    ];
    expected.sort();
    assert_eq!(
        verdict.undeclared, expected,
        "povo (bead franken_lean-ephemeral-manifest-artifact-povo): the verdict over the real \
         manifest plus two planted citations must name EXACTLY the two plants.\n  \
         An entry present here that is not a plant is a NEW untracked path citation: a \
         judgement row is resting on a path git does not track, so it is absent from every \
         fresh clone and from every rch worker, and the next `target/` prune or `git clean` \
         removes it with nothing going red. Cite a tracked file, or a `bead-comment:`/`test:` \
         reference, or declare the entry in UNTRACKED_PATH_CITATION_DEBT under YOUR OWN bead \
         and say so — the debt is per (bead, entry) precisely so that borrowing a peer's slot \
         is not available.\n  \
         A plant MISSING from it is the law going quiet: either the refusal stopped firing, or \
         it stopped keying on the row, and the second reads as a pass on live data forever."
    );
    assert!(
        verdict.declared + verdict.undeclared.len() >= 2,
        "the verdict accounted for {} citations in total — a walk this short cannot have \
         reached the manifest, and a broken scan reports the same clean bill as a repaired one",
        verdict.declared + verdict.undeclared.len()
    );
}
