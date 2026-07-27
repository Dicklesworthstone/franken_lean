//! **A terminal coverage row whose evidence CI never executed** — the hollow-green guard
//! (bead `fln-rgha`; AGENTS.md "Evidence & Census Pins" item 7).
//!
//! Item 7's law is that every level, digest, capture and delegation must name the thing
//! that produces it and must fail when that thing changes. Twelve terminal `complete` rows
//! in `ci/VERIFICATION_MANIFEST.jsonl` cite conformance suites as their evidence; CI runs
//! those suites **without the pinned Reference toolchain installed**, so each pin-dependent
//! rig inside them takes an early return and reports `ok`.
//!
//! This is a harder instance than `franken_lean-worktree-gitdir-refusal-hugg`, and the
//! reason is worth stating before the code. hugg shouted three wrong causes over one
//! correct line, so there was something to notice. Here the message is *right* —
//! `pin::skip_notice` says outright that nothing was established — and it goes to stderr,
//! which cargo captures and discards for a **passing** test. There is no misleading text
//! and no failure to investigate. A green run looks identical whether the rig ran or not.
//!
//! # What this guard is, and what it is not
//!
//! It is a **join** check: it does not read a rig's output, and it makes no claim that any
//! row is false. Every one of the twelve may have been verified on a pin-bearing host by
//! the agent who closed it, and several bead bodies say exactly that. The defect is that
//! **the repository cannot tell**, and each CI run silently re-asserts the green. So the
//! guard binds the *population* of such rows to a declared allowance, in both directions,
//! and makes any change to it fail.
//!
//! It measures **reach**, not decline: whether a cited surface's code can consult the
//! pinned Reference, not whether it skips or hard-fails without it. That is deliberate —
//! both mean the row's evidence was not established by the CI run — but it is not the
//! bead's eventual mechanism, which is a structured execution record each rig emits and
//! the gate collects. Nothing here observes a run happening.
//!
//! # Why the scope is derived
//!
//! hugg is criticised in item 7's own table because its affected-surface list is
//! *hand-listed*, so a new lane that starts refusing goes unnamed and nothing notices.
//! Everything here is resolved from the artefacts themselves: workspace members from the
//! root manifest's `members` globs, CI jobs from the workflow files, the workspace suite
//! from `scripts/check.sh`, the e2e registry from `E2E_STEP_ORDERS`, the terminal state
//! from the tracker. A surface added tomorrow is in scope the day it lands.
//!
//! Two things *are* declared, both bounded and both checked in both directions so each can
//! only shrink: the population allowance, and a short exclusion list for files whose text
//! carries a pin coordinate for some reason other than reaching the pin. See
//! [`PIN_REACH_SCAN_EXCLUSIONS`] for why that is not the same defect as hugg's hand-list.
//!
//! Measured at `7b1af002`. The derivation found **three rows a careful hand-list missed** —
//! `fln-ffam`, `franken_lean-2jht`, `franken_lean-c24a` — each citing a pin-reaching
//! surface outside `fln-conformance`. `crates/fln-kernel/tests/reference_differential.rs`
//! is the sharpest: it carries its own `PIN_TAG` and its own locator, imports nothing from
//! [`fln_conformance::pin`], and *cannot* — `fln-kernel` sits below `fln-conformance` in
//! the §21 crate map, so any design premised on one sanctioned skip type that every rig
//! constructs is structurally impossible for it.
//!
//! # What could not be derived — the residue, where the next instance will hide
//!
//! Stated here rather than discovered again, because item 7's whole complaint is claims
//! whose limits live somewhere other than the claim.
//!
//! 1. ~~**The `E2E_STEP_ORDERS` key → shell script binding is nowhere declared.**~~ Still
//!    undeclared, now **derived** — see [`judge_lane_binding`]. The sentence this residue
//!    item used to carry was measured false at `ad2b9207`: it said keys match
//!    `scripts/e2e/<key>.sh` "by shared filename", which holds for eight of thirteen and
//!    for none of the interesting ones. `env_snapshots.sh` alone hosts **six** registered
//!    scenarios, five of them named nothing like it, so renaming that one file orphans five
//!    registrations at once. Of 21 lane scripts only **8** carry the `fln.e2e/2` schema, and
//!    one of those eight — `kernel_replay.sh` — is dispatched by **no workflow at all**,
//!    while sitting in `E2E_STEP_ORDERS` and `check.sh`'s shellcheck stage looking exactly
//!    as authoritative as the twelve that run. That is this bead's own thesis one floor up:
//!    the guard was written because *rows* rest on suites CI never runs, and a *lane* CI
//!    never runs was sitting inside the registry the guard was reading from.
//!
//!    What remains underived is **dispatch at runtime**: a workflow naming a script is not
//!    a run of it, exactly as `uagk` records for its cron.
//! 2. **Cargo's real target set.** Text cannot yield it; `bkw6` already paid for the
//!    text-only version by counting `[[bench]]` sections while cargo auto-discovered the
//!    rest. Member globs and directory layout are resolved here; `[[test]]` sections,
//!    `required-features` and auto-discovery beyond `tests/*.rs` are not modelled.
//! 3. **`check.sh` sub-modes.** `--self-test` and `--tribunal-manifest-inventory` are read
//!    as reaching the workspace suite because they invoke the same script. Today the same
//!    job also runs the plain gate, so the answer is unchanged; a job that ran *only* a
//!    sub-mode would be over-credited.
//! 4. ~~**The five `#[ignore]`d tests.**~~ **This item's stated reason for being residue was
//!    retired by this guard's own repair, and nobody re-read it.** It said: "Artifact
//!    citations are file-granular, so the manifest cannot express which test a row rests on
//!    and this guard cannot check it." True when written, false from `f24b6670`, which added
//!    the `test:<pkg>::<target>::<path>` kind — the manifest can now name one function, and
//!    the first thing it can name is a function CI never runs. Measured green at `5f7e44ad`:
//!    a row citing an `#[ignore]`d function left `FILE_GRANULAR_EVIDENCE_ALLOWANCE` as a
//!    **repair** and lowered the ceiling with it. Ten terminal rows cite one of the four
//!    ignored-producer surfaces and all ten are declared in that allowance, so every one is
//!    queued for the migration that opens it; for `fln-7odd` and `93te` the ignored function
//!    is the only honest answer, because its `#[ignore]` reason names their bead. Now joined
//!    in [`judge_granularity`] — `granularity-ignored` for either citation shape,
//!    `granularity-hollow-surface` for a cited file whose every test is ignored, and
//!    `granularity-ignored-scan` when the producing scan collapses. Four mutants, each
//!    gutted independently at `5f7e44ad` and each killing exactly the one that names it.
//!
//!    **What is still residue.** A file-granular row citing a surface where *some* tests are
//!    ignored still cannot say which test it rests on — that is the 67-row debt, not this
//!    join. And `#[ignore]` is only one way a compiled test does not run: `#[cfg]` gating and
//!    an early `return` are not modelled, and `--skip` is item 5. Measured at `974fcc5a`, all
//!    five instances are compensated — `fln-8zsq` went source-level *because* its producer is
//!    ignored, `93te` carries a mechanically-expiring PG-5 waiver, `uagk` a retention receipt,
//!    `4o3n` the private `Calibration` field — and `golden_vellum.rs`'s only prints for a
//!    human. **What was unguarded is the class, not the instances**
//!    (bead `franken_lean-ignored-producer-class-unguarded-t4u1`). Count the ATTRIBUTE, never
//!    the token: this paragraph said "fifteen" until `974fcc5a` because `rg -c '#\[ignore'`
//!    returns 22 *mentions*, `kernel_replay.rs` being full of guards that discuss it —
//!    the same mentions-vs-construct error `bkw6` paid for by counting `[[bench]]`
//!    sections, committed here inside the guard written about that defect.
//! 5. **`--skip` at `scripts/check.sh:1586-1590`.** Treated as workspace-wide because
//!    `--skip` filters test *names*, not targets — true today, and a libtest filter that
//!    matches nothing exits 0 (`uagk`).

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use fln_conformance::execution::{
    CiJob, Field, GOVERNED_E2E_SCHEMA, PIN_COORDINATES, autodiscovery_overrides,
    check_sh_reaches_workspace, ci_jobs, e2e_scenario_keys, ignored_tests, installs_reference_pin,
    is_terminal, module_path_prefix, names_scenario_in_code, reach_covers,
    reaches_the_pinned_reference, record_field, scenario_assignments, shell_code_only,
    test_function_citation, test_functions, test_reach, workspace_member_patterns,
};

// ---------------------------------------------------------------------------
// The two declarations
// ---------------------------------------------------------------------------

/// Terminal rows whose cited evidence CI runs **without** the pinned Reference, so the
/// repository cannot show that the pin-dependent half of that evidence ever executed.
///
/// **This is not a budget and not a judgement.** It is the count of rows whose evidence
/// cannot be *shown* to have run, not a count anyone has decided is acceptable. Declaring
/// a population converts unmeasured into accepted if nobody says otherwise
/// (`fln-bench-apparatus-empty-referent-bkw6`), and freezing one repeats `3s8w`'s complaint
/// about the 105 exempt rows. Every entry here is a debt.
///
/// It exists at all because a guard that reddened on day one for twelve pre-existing rows
/// is a gate people bypass with `--no-verify`, which AGENTS.md already records as a real
/// limit on the projection guard.
///
/// **The only legitimate edit is a deletion**, and the equality check below forces one the
/// moment a row leaves the population — see [`judge`].
const UNEXECUTED_EVIDENCE_ALLOWANCE: &[&str] = &[
    "fln-7odd",
    "fln-8zsq",
    "fln-c78c",
    "fln-corpus-thread-matrix-93te",
    "fln-ffam",
    "franken_lean-2jht",
    "franken_lean-2ki4",
    "franken_lean-c24a",
    "franken_lean-eh0c",
    "franken_lean-ext-observable-fixture-drift-gap-vqnu",
    "franken_lean-kxbj",
    "franken_lean-sxsk",
];

/// The high-water mark of [`UNEXECUTED_EVIDENCE_ALLOWANCE`], asserted by **equality**.
///
/// `<=` would leave headroom: a shrink to eleven would let the next hollow row be silenced
/// by growing back to twelve with no visible change to a literal. Equality makes the
/// ceiling a ratchet whose only legitimate edit is downward, and makes any upward edit a
/// deliberate, reviewable change to a constant that says what it is.
const UNEXECUTED_EVIDENCE_CEILING: usize = 12;

/// Files whose text carries a pin coordinate for a reason other than reaching the pin.
///
/// **Why this is not hugg's defect.** hugg hand-lists its *scope*, so a surface that starts
/// refusing tomorrow is never named and nothing notices. Here the scope is derived from the
/// workspace's own member globs, and a new pin-reaching file enters it automatically; what
/// is declared is a bounded *exclusion*, checked in both directions — an entry that stops
/// matching a coordinate is stale and fails, and an entry whose exclusion changes nothing
/// is vacuous and fails. The failure mode hugg has cannot occur here.
///
/// `execution.rs` declares the coordinates this scan searches for.
/// `contract_handoff.rs` is a generated-code leak scanner whose needle *is* the coordinate;
/// it belongs to another domain and is declared rather than edited.
const PIN_REACH_SCAN_EXCLUSIONS: &[(&str, &str)] = &[
    (
        "crates/fln-conformance/src/execution.rs",
        "declares the pin coordinates this scan searches for",
    ),
    (
        "tools/structure-guard/src/contract_handoff.rs",
        "a generated-code leak scanner whose needle is the coordinate itself",
    ),
];

const PIN_REACH_SCAN_EXCLUSION_CEILING: usize = 2;

/// Every `#[ignore]`d test in the workspace, each with the mechanism that compensates for
/// CI compiling it and never running it (bead `franken_lean-ignored-producer-class-unguarded-t4u1`).
///
/// **The instances are fine; the class is what is unguarded.** Measured at `974fcc5a`, all
/// five ignored tests are already compensated — but by five bespoke mechanisms, written by
/// four different people, each invisible from the ignore site. Nothing binds an ignored
/// producer to a compensating mechanism, so a sixth `#[ignore]` added tomorrow gets no
/// scrutiny at all. That is AGENTS.md's own sentence about item 7: instances found by
/// attentive reading are not a mechanism, they are luck with good people, and luck does not
/// survive a context restart.
///
/// This is the same defect as the population above, one granularity finer. A coverage row
/// cites a **file**; cargo runs a **function**. Ten terminal rows cite one of these four
/// surfaces and a file-granular one cannot say which test it rests on — so this guard does
/// not claim those rows are hollow, and measurement said they are not: the ignored fraction
/// was 2/14, 1/15, 1/10 and 1/9 at `974fcc5a`, and no surface has every test ignored.
///
/// **That last clause is the load-bearing one, and it was a measurement transcribed into a
/// doc comment with nothing rechecking it.** It is derived now — `granularity-hollow-surface`
/// in [`judge_granularity`] fails the day a cited surface's last running test is `#[ignore]`d.
/// The four fractions are deliberately *not* pinned: they move whenever a test is added, so
/// pinning them buys churn, and the property that matters is the clause, not the arithmetic.
///
/// **And the sentence above no longer bounds the exposure**, because a row is no longer
/// obliged to be file-granular. From `f24b6670` a row may cite one function, and all ten of
/// these rows are declared debts in [`FILE_GRANULAR_EVIDENCE_ALLOWANCE`] whose sanctioned
/// repair is exactly that migration. See residue item 4 in the module header.
const IGNORED_PRODUCER_ALLOWANCE: &[(&str, &str, &str)] = &[
    (
        "crates/fln-conformance/tests/kernel_replay.rs",
        "pinned_present_olean_kernel_differential",
        "fln-8zsq made its census guard SOURCE-level precisely because this producer is \
         ignored: a lane grepping stdout observes silence rather than a missing disclosure",
    ),
    (
        "crates/fln-conformance/tests/kernel_replay.rs",
        "present_olean_corpus_thread_matrix_compares_stream_digests",
        "AGENTS.md's public PG-5 waiver, which expires MECHANICALLY — the receipt path is \
         keyed by pin, so advancing SUITE.lock fails the retention check (fln-corpus-thread-matrix-93te)",
    ),
    (
        "crates/fln-conformance/tests/mandated_mutants.rs",
        "the_mandated_mutants_are_planted_and_their_killers_die",
        "fln-mandated-mutant-join-unwatched-uagk's per-commit retention receipt, weekly \
         dispatcher, and a class token DERIVED from what dispatches it",
    ),
    (
        "crates/fln-kernel/tests/depth_stack_calibration.rs",
        "calibrate_stack_bytes_per_depth",
        "franken_lean-4o3n's private Calibration field: no bound can exist without the \
         provenance of the configuration it was measured in",
    ),
    (
        "crates/fln-syntax/tests/golden_vellum.rs",
        "emit_corpus_for_review",
        "not evidence for any claim — a regeneration ceremony that only PRINTS rows for a \
         human to review, and never writes the corpus",
    ),
];

/// The ratchet for [`IGNORED_PRODUCER_ALLOWANCE`], by equality, for the reason
/// [`UNEXECUTED_EVIDENCE_CEILING`] gives.
const IGNORED_PRODUCER_CEILING: usize = 5;

/// Scenario tokens that name a gate stage rather than an `fln.e2e/2` lane.
const NON_E2E_SCENARIOS: &[&str] = &["quality_gate", "gate_self_test"];

/// Registered scenarios bound to their lane only by a **bare word in code**, because they
/// reach it as a dispatch helper's argument rather than through a `…SCENARIO=` assignment.
///
/// **Declared as a set, never as a count, and that is `k60n`'s finding applied here.** A
/// count over a population is a budget its own repairs refill: convert one of these to an
/// assignment and the number frees a slot the next weakly-bound scenario spends silently.
/// Set equality in both directions means a repair must name what it repaired and an
/// addition must name what it added.
///
/// All three are `env_snapshots.sh`'s children, dispatched by `run_identity_child <key> …`.
/// The alternative to the word scan is matching that helper by name, which is a hand-list —
/// see [`names_scenario_in_code`] for why this codebase does not get to make that trade
/// again.
const WEAKLY_BOUND_SCENARIOS: &[&str] = &[
    "declaration_membership",
    "declaration_tag_matrix",
    "extension_descriptor_matrix",
];

/// Governed `fln.e2e/2` lanes that **no workflow dispatches**, each with the reason —
/// and the reason is re-derived, not read.
///
/// `kernel_replay.sh` reaches the pinned Reference (`FLN_REFERENCE_LIB`, its own elan path
/// at line 94) and CI installs no Reference toolchain, so it could not run there if it were
/// dispatched. That is the honest state, and it is this bead's subject rather than an
/// exception to it: a lane nothing runs is the same hollow green as a row whose suite
/// nothing runs, one level up.
///
/// **Both halves are live bindings.** Adding a dispatch makes the entry stale and fails;
/// the lane ceasing to reach the pin falsifies the recorded reason and fails. Neither can
/// rot into a bare exemption, which is what `qydn`'s thirteen declared violations earn by
/// being checked in both directions.
const UNDISPATCHED_GOVERNED_LANES: &[(&str, &str)] = &[(
    "scripts/e2e/kernel_replay.sh",
    "reaches the pinned Reference, which CI does not install",
)];

/// Terminal rows whose evidence is stated at a granularity **coarser than the unit that runs**.
///
/// A coverage row cites a *file*; cargo compiles a *target*; libtest runs a *function*. Two
/// shapes, and the second is the worse one:
///
/// - **A** — the row cites an integration target (`tests/*.rs`, or `cargo-test:<stem>`). That
///   names one real cargo target, but the target holds many functions and the row names none.
/// - **B** — the row cites a `src/*.rs` carrying `#[cfg(test)]` tests. There is **no cargo
///   invocation at all** that runs that file's tests: the narrowest selectable unit is
///   `-p <pkg> --lib`, which is every sibling source file's tests too.
///
/// Measured at `29852ec1` over the 166 coverage rows: A is 53 rows (47 terminal), B is 45 (37),
/// and the union is **80 rows, 70 of them terminal**, with **1733 test functions** behind the
/// terminal citations. `crates/fln-env/src/extensions.rs` alone carries 87 functions in a lib
/// target shared with 11 sibling files, and three rows cite it.
///
/// **A and B are one mechanism, and the check that says so is the one that says povo and ywmq
/// are not.** Same producer (the test binary), same repair (name a runnable libtest unit), same
/// change site, one law preventing both recurrences. The first draft of this guard scoped the
/// population to A and would have left 27 terminal B rows outside a guard written to catch
/// them — `franken_lean-worktree-gitdir-refusal-hugg`'s criticism, committed here, caught by
/// re-reading the question rather than by the derivation.
///
/// **What this is not.** No row here is claimed false; several are separately compensated, as
/// [`IGNORED_PRODUCER_ALLOWANCE`] records. This is
/// `fln-bench-apparatus-empty-referent-bkw6`'s move applied to *granularity* — bind the claim
/// to the **cardinality** of what it asserts and let the number fail in both directions — and
/// the fact it binds is exact: **the manifest cannot say which test 70 terminal rows rest on.**
///
/// **The shrink direction is reachable, which is what makes equality honest rather than a
/// wall.** `fln-shrinking-allowance-guard-direction` is this lineage's own finding that an
/// equality check is a wall when a correct repair cannot satisfy it. Not so here: the migration
/// ships with the ratchet — replace the citation with `test:<pkg>::<target>::<path>`, which
/// [`test_function_citation`] parses and [`judge_granularity`] resolves against the target's
/// real function list. Every entry is a debt, not a budget.
const FILE_GRANULAR_EVIDENCE_ALLOWANCE: &[&str] = &[
    "fln-22i1",
    "fln-23cz",
    "fln-2bn5",
    "fln-46mw",
    "fln-49c",
    "fln-4yos",
    "fln-7odd",
    "fln-8138",
    "fln-8gz3",
    "fln-8zsq",
    "fln-9wya",
    "fln-amv.14",
    "fln-bench-apparatus-empty-referent-bkw6",
    "fln-c78c",
    "fln-corpus-thread-matrix-93te",
    "fln-env-merge-resource-envelope-9m74",
    "fln-ffam",
    "fln-glml",
    "fln-judgement-row-not-bound-to-its-closure-iumd",
    "fln-kernel-loc-disclosure-foreign-counter-c118",
    "fln-kx3y",
    "fln-laxj",
    "fln-mandated-mutant-join-unwatched-uagk",
    "fln-okfb",
    "fln-pu6i",
    "fln-q8qt",
    "fln-rwz",
    "fln-sn0w",
    "fln-sr2z",
    "fln-stc1",
    "fln-sv7x",
    "fln-uc44",
    "fln-um4a",
    "fln-uuuz",
    "fln-yswb",
    "fln-zti3",
    "franken_lean-0sv9",
    "franken_lean-2ki4",
    "franken_lean-4o3n",
    "franken_lean-81oq",
    "franken_lean-admission-tripwire-needles-unbound-en9q",
    "franken_lean-c24a",
    "franken_lean-checker-charter-line-citations-unbound-68ob",
    "franken_lean-claim-matrix-doc-ci-mhew",
    "franken_lean-dgxa",
    "franken_lean-e5k7",
    "franken_lean-eh0c",
    "franken_lean-ex54",
    "franken_lean-ext-observable-fixture-drift-gap-vqnu",
    "franken_lean-h5z1",
    "franken_lean-hv9m",
    "franken_lean-kxbj",
    "franken_lean-l84f",
    "franken_lean-lu5",
    "franken_lean-mrlo",
    "franken_lean-mvak",
    "franken_lean-oh1j",
    "franken_lean-ome7",
    "franken_lean-oof9",
    "franken_lean-pmap-refusal-outcome-taxonomy-i1z9",
    "franken_lean-pnav",
    "franken_lean-r0xu",
    "franken_lean-r2st",
    "franken_lean-r4m8",
    "franken_lean-sxsk",
    "franken_lean-tkr2",
    "franken_lean-vui8",
];

/// The ratchet for [`FILE_GRANULAR_EVIDENCE_ALLOWANCE`], by equality, for the reason
/// [`UNEXECUTED_EVIDENCE_CEILING`] gives.
const FILE_GRANULAR_EVIDENCE_CEILING: usize = 67;

/// The floor beneath [`judge_granularity`]'s vacuity check.
///
/// A population whose cited surfaces each held **one** test function would be a distinction
/// without a difference — file granularity and function granularity would name the same thing,
/// and the finding would be measuring nothing. 1733 at `29852ec1`; the floor sits an order of
/// magnitude below so ordinary churn never trips it and a collapsed scan always does.
const FILE_GRANULAR_FANOUT_FLOOR: usize = 150;

// ---------------------------------------------------------------------------
// The derivation, gathered from disk
// ---------------------------------------------------------------------------

/// One terminal coverage row, reduced to what the join needs.
#[derive(Debug, Clone)]
struct TerminalRow {
    bead: String,
    surfaces: BTreeSet<String>,
    scenarios: Vec<String>,
    /// Surfaces this row names at a granularity coarser than the unit that runs: an
    /// integration target (shape A) or a `src/*.rs` with unit tests (shape B).
    coarse: BTreeSet<String>,
    /// Raw `test:`-prefixed artifacts, resolved by [`judge_granularity`] rather than here, so
    /// an unresolvable one is a **finding** and not a silently dropped artifact.
    fine: Vec<String>,
}

/// Everything the guard measures, in one value, so [`judge`] is a pure function of it and
/// the mutation campaign can perturb any field without touching the repository.
#[derive(Debug, Clone)]
struct Derivation {
    members: Vec<String>,
    /// Every workspace member source file, workspace-relative, mapped to its raw text.
    surfaces: BTreeMap<String, String>,
    excluded: BTreeSet<String>,
    pin_reaching: BTreeSet<String>,
    jobs: Vec<CiJob>,
    check_sh_workspace: bool,
    rows: Vec<TerminalRow>,
    e2e_keys: BTreeSet<String>,
    /// Every `scripts/e2e/*.sh`, workspace-relative, mapped to its raw text. All of them,
    /// governed or not: which are governed is derived from the text, never from the name.
    lanes: BTreeMap<String, String>,
    /// The concatenated `.github/workflows/*.yml` text, for the dispatch scan. A workflow
    /// naming a script is not a run of it — see [`judge_lane_binding`] for what that costs.
    workflow_text: String,
    /// `crates/fln-conformance/src/pin.rs`, raw — the coordinate set's positive control.
    pin_module: String,
    /// `(surface, function)` for every `#[ignore]`d test cargo compiles and never runs.
    ignored: BTreeSet<(String, String)>,
    /// `<stem>` → path, for every integration target cargo auto-discovers. Replaces the old
    /// stem map, which was **not injective**: it ingested every `.rs` under a `tests/` tree, so
    /// the three `tests/common/mod.rs` modules all claimed the stem `mod` and two vanished
    /// silently — a key used as an identity with nobody checking, live at `29852ec1`.
    targets: BTreeMap<String, String>,
    /// `<stem>` → the `#[test]` functions inside that integration target.
    target_tests: BTreeMap<String, BTreeSet<String>>,
    /// `<package>` → `(module path prefix, function)` for every lib unit test.
    lib_tests: BTreeMap<String, BTreeSet<(String, String)>>,
    /// member directory → the package name its manifest **declares**. Read, never inferred
    /// from the directory name, which merely happens to match for all 33 members today.
    packages: BTreeMap<String, String>,
    /// `(where, reason)` for everything that makes the layout-derived target set incomplete:
    /// a manifest override, a directory-style target, a stem collision, a `#[path]` attribute.
    granularity_preconditions: Vec<(String, String)>,
}

fn read(root: &Path, relative: &str) -> String {
    fs::read_to_string(root.join(relative))
        .unwrap_or_else(|error| panic!("{relative} must be readable: {error}"))
}

/// Resolve the root manifest's `members` globs against the tree.
fn member_dirs(root: &Path) -> Vec<String> {
    let manifest = read(root, "Cargo.toml");
    let patterns = workspace_member_patterns(&manifest)
        .expect("the root Cargo.toml must declare a non-empty [workspace] members array");
    let mut dirs = BTreeSet::new();
    for pattern in patterns {
        match pattern.strip_suffix("/*") {
            Some(prefix) => {
                let Ok(entries) = fs::read_dir(root.join(prefix)) else {
                    continue;
                };
                for entry in entries.flatten() {
                    if entry.path().is_dir() {
                        let name = entry.file_name().to_string_lossy().into_owned();
                        dirs.insert(format!("{prefix}/{name}"));
                    }
                }
            }
            None => {
                if root.join(&pattern).is_dir() {
                    dirs.insert(pattern);
                }
            }
        }
    }
    dirs.into_iter().collect()
}

/// Walk a member's source tree.
///
/// **A node this cannot read is a refusal, never a skip.** A guard that quietly drops a file
/// it could not parse has a hole in the shape of the next instance: the dropped file is
/// exactly the one nobody is looking at. The only silent case left is a directory that does
/// not exist, which is not a member without `tests/` failing to be read — it is a member
/// without `tests/`.
///
/// **Symlinks are not followed.** `path.is_dir()` resolves them, so a symlinked cycle inside
/// a member would recurse until the stack ran out. Cargo does not compile through a
/// directory symlink either, so refusing to descend one costs nothing and removes the only
/// way this walk can fail to terminate.
fn collect_rs(dir: &Path, root: &Path, out: &mut BTreeMap<String, String>) {
    let entries = match fs::read_dir(dir) {
        Ok(entries) => entries,
        // A member with no `src/` or no `tests/` is ordinary; anything else is not.
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return,
        Err(error) => panic!("scan: {} could not be walked: {error}", dir.display()),
    };
    for entry in entries {
        let entry = entry.unwrap_or_else(|error| {
            panic!(
                "scan: an entry of {} could not be read: {error}",
                dir.display()
            )
        });
        let kind = entry.file_type().unwrap_or_else(|error| {
            panic!(
                "scan: {:?} has no readable file type: {error}",
                entry.path()
            )
        });
        if kind.is_symlink() {
            continue;
        }
        let path = entry.path();
        if kind.is_dir() {
            collect_rs(&path, root, out);
            continue;
        }
        if !path.extension().is_some_and(|ext| ext == "rs") {
            continue;
        }
        let text = fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!(
                "scan: {} is a Rust source file this scan could not read ({error}). A file \
                 dropped here is a file the pin-reach scan never judges — refuse rather than \
                 narrow the scope silently.",
                path.display()
            )
        });
        let relative = path
            .strip_prefix(root)
            .expect("a scanned path lies under the repository")
            .to_string_lossy()
            .replace('\\', "/");
        out.insert(relative, text);
    }
}

fn derive(root: &Path) -> Derivation {
    let members = member_dirs(root);

    let mut surfaces = BTreeMap::new();
    for member in &members {
        for sub in ["src", "tests"] {
            collect_rs(&root.join(member).join(sub), root, &mut surfaces);
        }
    }

    let excluded: BTreeSet<String> = PIN_REACH_SCAN_EXCLUSIONS
        .iter()
        .map(|(path, _)| (*path).to_string())
        .collect();
    let pin_reaching: BTreeSet<String> = surfaces
        .iter()
        .filter(|(path, text)| !excluded.contains(*path) && reaches_the_pinned_reference(text))
        .map(|(path, _)| path.clone())
        .collect();

    // Every lane script, read by directory listing rather than by any list of names. A file
    // this cannot read is a refusal: a dropped lane is exactly the lane nobody is looking at.
    let mut lanes = BTreeMap::new();
    let lane_dir = root.join("scripts/e2e");
    let mut lane_paths: Vec<PathBuf> = fs::read_dir(&lane_dir)
        .expect("scripts/e2e must be readable")
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "sh"))
        .collect();
    lane_paths.sort();
    for path in lane_paths {
        let text = fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!("scan: lane {} could not be read: {error}", path.display())
        });
        let relative = path
            .strip_prefix(root)
            .expect("a lane script lies under the repository")
            .to_string_lossy()
            .replace('\\', "/");
        lanes.insert(relative, text);
    }

    let mut jobs = Vec::new();
    let mut workflow_text = String::new();
    let workflows = root.join(".github/workflows");
    let mut names: Vec<PathBuf> = fs::read_dir(&workflows)
        .expect(".github/workflows must be readable")
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.extension()
                .is_some_and(|ext| ext == "yml" || ext == "yaml")
        })
        .collect();
    names.sort();
    for path in names {
        let name = path
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default();
        // NOT `unwrap_or_default()`. A workflow read as the empty string contributes no
        // jobs, so an unreadable `ci.yml` would look exactly like a CI that runs nothing —
        // and "runs nothing" is a state this guard reports rather than a state it may
        // silently assume.
        let text = fs::read_to_string(&path).unwrap_or_else(|error| {
            panic!(
                "scan: workflow {} could not be read: {error}",
                path.display()
            )
        });
        workflow_text.push_str(&text);
        workflow_text.push('\n');
        jobs.extend(ci_jobs(&name, &text));
    }

    let check_sh_workspace = check_sh_reaches_workspace(&read(root, "scripts/check.sh"));
    let e2e_keys = e2e_scenario_keys(&read(root, "scripts/evidence.py"));

    // The tracker decides terminal state; coverage rows never declare it.
    //
    // A line this reader cannot resolve is TYPED INCONCLUSIVE, not skipped. The distinction
    // is not hypothetical: the first version of `record_field` decoded while *skipping*, so
    // it refused on the `§` and `—` in a bead's prose, recovered by advancing one byte, and
    // walked into the string — silently dropping 292 records. Every coverage row naming one
    // of those beads then read as an orphan. Skipping made a reader defect look like a
    // tracker defect; refusing makes it look like what it is.
    let mut status = BTreeMap::new();
    let mut unreadable: Vec<usize> = Vec::new();
    for (number, line) in read(root, ".beads/issues.jsonl").lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        match (record_field(line, "id"), record_field(line, "status")) {
            (Some(Field::Text(id)), Some(Field::Text(state))) => {
                status.insert(id, state);
            }
            _ => unreadable.push(number + 1),
        }
    }
    assert!(
        unreadable.is_empty(),
        "scan: .beads/issues.jsonl lines {unreadable:?} yielded no id/status pair. A tracker \
         record this reader cannot read is a refusal, never a bead that does not exist — \
         dropping it silently would report every coverage row naming it as an orphan."
    );
    assert!(
        !status.is_empty(),
        "scan: the tracker reader resolved no issues at all — a broken reader, not an empty tracker"
    );

    // Every test cargo compiles and never runs, keyed by the attribute rather than the token.
    let ignored: BTreeSet<(String, String)> = surfaces
        .iter()
        .flat_map(|(path, text)| {
            ignored_tests(text)
                .into_iter()
                .map(|(name, _reason)| (path.clone(), name))
        })
        .collect();

    // `cargo-test:<stem>` names an integration target; cargo binds a target's name to its
    // file stem under `tests/`, so unlike the e2e scenario convention this binding is the
    // build system's, not a local habit.
    //
    // **Only what cargo auto-discovers.** The previous version of this map took every `.rs`
    // whose path contained `/tests/`, which ingested the three `tests/common/mod.rs` modules
    // as well — all three claiming the stem `mod`, last insert winning, the other two gone in
    // silence. That key denoted no cargo target at all and collided three ways, at
    // `29852ec1`; no row cited it, so it produced no wrong answer *yet*. Restricting to
    // top-level `tests/*.rs` under a declared member drops exactly that key and moves no
    // terminal row's resolved surface set — measured before the change, not assumed.
    let mut targets: BTreeMap<String, String> = BTreeMap::new();
    let mut preconditions: Vec<(String, String)> = Vec::new();
    for path in surfaces.keys() {
        let Some((member, file)) = path.rsplit_once("/tests/") else {
            continue;
        };
        if file.contains('/') || !members.iter().any(|m| m == member) {
            continue;
        }
        let Some(stem) = file.strip_suffix(".rs") else {
            continue;
        };
        if let Some(previous) = targets.insert(stem.to_string(), path.clone()) {
            preconditions.push((
                path.clone(),
                format!(
                    "shares its file stem with {previous}, so `cargo-test:<stem>` has stopped \
                     denoting one target — a key used as an identity without injectivity"
                ),
            ));
        }
    }
    let target_tests: BTreeMap<String, BTreeSet<String>> = targets
        .iter()
        .map(|(stem, path)| {
            (
                stem.clone(),
                test_functions(&surfaces[path]).into_iter().collect(),
            )
        })
        .collect();
    let by_stem = targets.clone();

    // The lib half: a `src/*.rs`'s unit tests compile into the crate's ONE lib target, so the
    // file is not a selectable unit at all. Keyed by package because that is what `-p` takes.
    let mut packages: BTreeMap<String, String> = BTreeMap::new();
    let mut lib_tests: BTreeMap<String, BTreeSet<(String, String)>> = BTreeMap::new();
    for member in &members {
        let manifest = read(root, &format!("{member}/Cargo.toml"));
        let name = manifest
            .lines()
            .find_map(|line| {
                let rest = line.trim().strip_prefix("name")?.trim_start();
                let value = rest.strip_prefix('=')?.trim();
                value
                    .strip_prefix('"')
                    .and_then(|v| v.strip_suffix('"'))
                    .map(str::to_string)
            })
            .unwrap_or_else(|| {
                panic!("scan: {member}/Cargo.toml declares no package name this reader can find")
            });
        for reason in autodiscovery_overrides(&manifest) {
            preconditions.push((format!("{member}/Cargo.toml"), reason.to_string()));
        }
        if let Ok(entries) = fs::read_dir(root.join(member).join("tests")) {
            for entry in entries.flatten() {
                if entry.path().is_dir() && entry.path().join("main.rs").is_file() {
                    preconditions.push((
                        format!(
                            "{member}/tests/{}/main.rs",
                            entry.file_name().to_string_lossy()
                        ),
                        "is a directory-style integration target this layout rule does not model"
                            .to_string(),
                    ));
                }
            }
        }
        packages.insert(member.clone(), name.clone());
        for (path, text) in &surfaces {
            if !path.starts_with(&format!("{member}/src/")) {
                continue;
            }
            // A `#[path]` attribute decouples a module's name from its file, which is the one
            // thing that makes `module_path_prefix` wrong rather than merely partial.
            if text
                .lines()
                .any(|line| line.trim_start().starts_with("#[path"))
            {
                preconditions.push((
                    path.clone(),
                    "carries a #[path] attribute, so a module path can no longer be derived \
                     from the file layout"
                        .to_string(),
                ));
            }
            let Some(prefix) = module_path_prefix(path) else {
                continue;
            };
            for function in test_functions(text) {
                lib_tests
                    .entry(name.clone())
                    .or_default()
                    .insert((prefix.clone(), function));
            }
        }
    }
    preconditions.sort();
    preconditions.dedup();

    let mut rows = Vec::new();
    for (number, line) in read(root, "ci/VERIFICATION_MANIFEST.jsonl")
        .lines()
        .enumerate()
    {
        if line.trim().is_empty() {
            continue;
        }
        let Some(Field::Text(bead)) = record_field(line, "bead") else {
            continue; // the adoption header and the scenario rows carry no bead
        };
        let (Some(Field::Text(skip)), Some(Field::List(artifacts)), Some(Field::List(scenarios))) = (
            record_field(line, "skip"),
            record_field(line, "artifacts"),
            record_field(line, "scenarios"),
        ) else {
            panic!(
                "scan: coverage row {} for {bead:?} did not yield skip/artifacts/scenarios — a \
                 record this reader cannot read is a refusal, never a row with no evidence",
                number + 1
            );
        };
        let state = status.get(&bead).unwrap_or_else(|| {
            panic!("scan: coverage row for {bead:?} names an issue the tracker does not carry")
        });
        if !is_terminal(state, &skip) {
            continue;
        }
        let mut cited = BTreeSet::new();
        let mut coarse = BTreeSet::new();
        let mut fine = Vec::new();
        for artifact in &artifacts {
            if artifact.starts_with("test:") {
                fine.push(artifact.clone());
                // **A function-granular citation still names a surface, and every OTHER
                // population resolves surfaces.** Migrating a row off a file citation must not
                // make it vanish from a neighbouring guard: `franken_lean-2jht` rests on a
                // pin-dependent rig, and when its `reference_differential.rs` citation was
                // replaced by a `test:` one the CI-execution join reported the row as REPAIRED
                // — a granularity fix silently shrinking the pin-dependence population by
                // making its referent unresolvable. Measured, by that guard, on this change.
                // So resolve the citation back to the file it names and feed `cited` too.
                if let Some((package, target, path)) = test_function_citation(artifact) {
                    if target == "lib" {
                        // The lib flavour names a module path; map it back to the source file
                        // whose layout prefix it begins with, longest prefix winning so
                        // `foo::bar` prefers `foo/bar.rs` over `foo.rs`.
                        let mut best: Option<(usize, String)> = None;
                        for candidate in surfaces.keys() {
                            let Some(member) = candidate.split("/src/").next() else {
                                continue;
                            };
                            if packages.get(member).map(String::as_str) != Some(package) {
                                continue;
                            }
                            let Some(prefix) = module_path_prefix(candidate) else {
                                continue;
                            };
                            if prefix.is_empty() || path.starts_with(prefix.as_str()) {
                                let score = prefix.len();
                                if best.as_ref().is_none_or(|(best, _)| *best < score) {
                                    best = Some((score, candidate.clone()));
                                }
                            }
                        }
                        if let Some((_, path)) = best {
                            cited.insert(path);
                        }
                    } else if let Some(path) = targets.get(target) {
                        cited.insert(path.clone());
                    }
                }
                continue;
            }
            if surfaces.contains_key(artifact) {
                cited.insert(artifact.clone());
                // Shape A: the cited file IS an integration target. Shape B: it is a
                // `src/*.rs` whose unit tests are a fraction of a shared lib target. Shape C —
                // a source file with no tests at all — is an implementation reference, a
                // different claim, and is deliberately NOT folded in.
                let is_target = targets.values().any(|path| path == artifact);
                let has_unit_tests =
                    artifact.contains("/src/") && !test_functions(&surfaces[artifact]).is_empty();
                if is_target || has_unit_tests {
                    coarse.insert(artifact.clone());
                }
            } else if let Some(stem) = artifact.strip_prefix("cargo-test:")
                && let Some(path) = by_stem.get(stem)
            {
                cited.insert(path.clone());
                coarse.insert(path.clone());
            }
        }
        rows.push(TerminalRow {
            bead,
            surfaces: cited,
            scenarios,
            coarse,
            fine,
        });
    }

    Derivation {
        members,
        surfaces,
        excluded,
        pin_reaching,
        jobs,
        check_sh_workspace,
        rows,
        e2e_keys,
        lanes,
        workflow_text,
        pin_module: read(root, "crates/fln-conformance/src/pin.rs"),
        ignored,
        targets,
        target_tests,
        lib_tests,
        packages,
        granularity_preconditions: preconditions,
    }
}

/// Every `#[ignore]`d test is declared with the mechanism that compensates for it, and the
/// declaration can only shrink. Findings are prefixed so a mutant can assert *which* fired.
fn judge_ignored(d: &Derivation, allowance: &[(&str, &str, &str)], ceiling: usize) -> Vec<String> {
    let mut findings = Vec::new();

    // Zero is a broken scan, not a repaired tree: the attribute cannot stop existing while
    // the corpus lane, the mutant campaign and the calibration runs all still carry it.
    if d.ignored.is_empty() {
        findings.push(
            "ignored-scan: no `#[ignore]`d test was found anywhere in the workspace. That is \
             the attribute scan breaking, not a tree in which every lane now runs per commit."
                .to_string(),
        );
    }

    let declared: BTreeSet<(String, String)> = allowance
        .iter()
        .map(|(surface, name, _)| ((*surface).to_string(), (*name).to_string()))
        .collect();

    let undeclared: Vec<&(String, String)> = d.ignored.difference(&declared).collect();
    if !undeclared.is_empty() {
        findings.push(format!(
            "ignored-undeclared: {undeclared:?} are `#[ignore]`d, so CI compiles them and \
             never runs them. Declare each in IGNORED_PRODUCER_ALLOWANCE with the mechanism \
             that compensates — what still fails if the thing this test would have proved \
             stops being true. If the honest answer is `nothing`, the test is not evidence \
             and no coverage row may cite its surface for that claim."
        ));
    }

    let stale: Vec<&(String, String)> = declared.difference(&d.ignored).collect();
    if !stale.is_empty() {
        findings.push(format!(
            "ignored-stale: {stale:?} are declared in IGNORED_PRODUCER_ALLOWANCE but are no \
             longer `#[ignore]`d (or were renamed). This is the good direction: delete those \
             entries and lower IGNORED_PRODUCER_CEILING to {} in the same commit.",
            d.ignored.len()
        ));
    }

    if allowance.len() != ceiling {
        findings.push(format!(
            "ignored-ceiling: IGNORED_PRODUCER_ALLOWANCE holds {} entries against a ceiling \
             of {ceiling}. Equality, so a shrink must lower it and the headroom a repair \
             earns cannot be spent admitting the next unexamined `#[ignore]`.",
            allowance.len()
        ));
    }

    for (surface, name, mechanism) in allowance {
        if mechanism.trim().is_empty() {
            findings.push(format!(
                "ignored-vacuous: {surface}::{name} is declared with an empty compensating \
                 mechanism, which is a declaration that says nothing."
            ));
        }
    }

    findings
}

/// Every terminal row states its evidence at the granularity that runs, or is declared — and
/// the declaration can only shrink.
///
/// Findings are prefixed `granularity-…` so the campaign asserts *which* one fired. A campaign
/// scoring "something went red" credits a mutant to an assertion that had stopped testing what
/// it names (`fln-mandated-mutant-join-unwatched-uagk`).
fn judge_granularity(d: &Derivation, allowance: &[&str], ceiling: usize) -> Vec<String> {
    let mut findings = Vec::new();

    // --- the scan must refuse rather than report a clean tree ---------------
    if d.targets.is_empty() {
        findings.push(
            "granularity-scan: no integration-test target was found in any member. Cargo \
             auto-discovers one per top-level `tests/*.rs` and this workspace has 75 — zero is \
             the layout rule breaking, not a workspace that stopped testing."
                .to_string(),
        );
    }
    if d.lib_tests.is_empty() {
        findings.push(
            "granularity-scan: no package declares a single lib unit test. That is the \
             `#[test]` attribute scan breaking, not a workspace whose crates test nothing."
                .to_string(),
        );
    }

    // --- the derivation's own preconditions, in the loud direction ----------
    //
    // The mirror of `bkw6`. It counted `[[bench]]` sections and reported a false clean because
    // cargo auto-discovered the rest; here auto-discovery IS the whole rule, so what silently
    // breaks this scan is an override APPEARING. Refuse rather than under-count.
    for (where_, reason) in &d.granularity_preconditions {
        findings.push(format!(
            "granularity-derivation: {where_} {reason}. The population below is derived from \
             the LAYOUT, which is exact only while nothing overrides it. Model the override or \
             the count is low — and a low count reads as a repair."
        ));
    }

    // --- the finding must not be vacuous ------------------------------------
    let fanout: usize = d
        .rows
        .iter()
        .flat_map(|row| row.coarse.iter())
        .map(|surface| match surface.rsplit_once("/tests/") {
            Some((_, file)) => file
                .strip_suffix(".rs")
                .and_then(|stem| d.target_tests.get(stem))
                .map_or(0, BTreeSet::len),
            None => d
                .packages
                .iter()
                .find(|(member, _)| surface.starts_with(&format!("{member}/src/")))
                .and_then(|(member, package)| {
                    let prefix = module_path_prefix(surface)?;
                    let _ = member;
                    Some(
                        d.lib_tests
                            .get(package)?
                            .iter()
                            .filter(|(p, _)| *p == prefix)
                            .count(),
                    )
                })
                .unwrap_or(0),
        })
        .sum();
    if fanout < FILE_GRANULAR_FANOUT_FLOOR {
        findings.push(format!(
            "granularity-fanout: {fanout} test functions live behind the cited surfaces, below \
             the floor of {FILE_GRANULAR_FANOUT_FLOOR}. Either the `#[test]` scan has broken, \
             or the population has become one where naming a file and naming a function mean \
             the same thing — in which case this check measures nothing and should be retired \
             deliberately, not passed silently."
        ));
    }

    // --- the population, bound by cardinality in both directions ------------
    //
    // A row stays in while it carries ANY coarse citation, even beside a precise one. Letting
    // one `test:` citation excuse a row that still cites a bare file is an exit that costs
    // nothing and proves nothing. Migration means REPLACING the coarse citation.
    let measured: BTreeSet<String> = d
        .rows
        .iter()
        .filter(|row| !row.coarse.is_empty())
        .map(|row| row.bead.clone())
        .collect();
    let declared: BTreeSet<String> = allowance.iter().map(|id| (*id).to_string()).collect();

    let grew: Vec<&String> = measured.difference(&declared).collect();
    if !grew.is_empty() {
        findings.push(format!(
            "granularity-grew: {grew:?} are terminal `complete` rows whose evidence names a \
             FILE. Cargo compiles a target; libtest runs a FUNCTION. So the row cannot say \
             which test carries its claim, and a run in which that test was `#[ignore]`d, \
             filtered out by `--skip`, or returned early is indistinguishable from one in which \
             it ran. A `src/*.rs` citation is worse still: no cargo invocation runs one source \
             file's tests, the narrowest unit being `-p <pkg> --lib`. Cite the function — \
             `test:<pkg>::<target>::<path>` or `test:<pkg>::lib::<module::path::fn>`, which is \
             exactly what a `cargo test … -- --exact` invocation runs. Declaring it here needs \
             FILE_GRANULAR_EVIDENCE_CEILING raised, which is a debt, not a fix."
        ));
    }

    let shrank: Vec<&String> = declared.difference(&measured).collect();
    if !shrank.is_empty() {
        findings.push(format!(
            "granularity-shrank: {shrank:?} are declared in FILE_GRANULAR_EVIDENCE_ALLOWANCE \
             but are no longer measured. This is the good direction and the edit is mechanical: \
             delete exactly those ids and lower FILE_GRANULAR_EVIDENCE_CEILING to {} in the \
             same commit.",
            measured.len()
        ));
    }

    if allowance.len() != ceiling {
        findings.push(format!(
            "granularity-ceiling: FILE_GRANULAR_EVIDENCE_ALLOWANCE holds {} ids against a \
             ceiling of {ceiling}. Equality, so the headroom a migration earns cannot be spent \
             admitting the next file-granular row.",
            allowance.len()
        ));
    }

    // --- the migration path must DENOTE -------------------------------------
    //
    // Without this the new kind is a free exit: write `test:a::b::c` naming a function that
    // does not exist and the row leaves the count while proving strictly LESS than the file
    // path it replaced. That is `fln-0rxm`'s shape — a citation that denotes nothing —
    // reproduced inside the repair for its neighbour.
    for row in &d.rows {
        for artifact in &row.fine {
            let Some((package, target, path)) = test_function_citation(artifact) else {
                findings.push(format!(
                    "granularity-unbound: terminal row {} cites {artifact:?}, which is not a \
                     well-formed `test:<pkg>::<target>::<path>` citation. A malformed one is a \
                     finding, never an artifact of another kind — or a typo is a way out.",
                    row.bead
                ));
                continue;
            };
            if !d.packages.values().any(|name| name == package) {
                findings.push(format!(
                    "granularity-unbound: terminal row {} cites {artifact:?}, but no workspace \
                     member declares the package name {package:?}.",
                    row.bead
                ));
                continue;
            }
            if target == "lib" {
                // The lib half of the ignore join. No lib unit test is `#[ignore]`d today, so
                // this branch has no live instance and is exercised by a planted one — an
                // unfalsifiable half is `bkw6`'s empty referent, and a population with no
                // members is exactly where the next instance lands.
                let ignored_here = d.ignored.iter().any(|(surface, function)| {
                    path.ends_with(function.as_str())
                        && d.packages.iter().any(|(member, name)| {
                            name == package && surface.starts_with(&format!("{member}/src/"))
                        })
                        && module_path_prefix(surface).is_some_and(|prefix| {
                            prefix.is_empty() || path.starts_with(prefix.as_str())
                        })
                });
                if ignored_here {
                    findings.push(format!(
                        "granularity-ignored: terminal row {} cites {artifact:?}, and that \
                         function carries `#[ignore]`. Cargo compiles it; libtest never runs \
                         it. The row now rests on ONE test, and that test is one CI does not \
                         execute — see IGNORED_PRODUCER_ALLOWANCE, which declares it.",
                        row.bead
                    ));
                }
                let known = d.lib_tests.get(package);
                // The module path prefix is a NECESSARY condition, not a sufficient one:
                // inner `mod tests { … }` nesting appends components the file layout cannot
                // give. Resolving by function name alone would be unsound — measured, two of
                // 33 packages have ambiguous unit-test names — so both halves are required.
                let resolves = known.is_some_and(|tests| {
                    tests.iter().any(|(prefix, function)| {
                        path.ends_with(function)
                            && (prefix.is_empty() || path.starts_with(prefix.as_str()))
                    })
                });
                if !resolves {
                    findings.push(format!(
                        "granularity-unbound: terminal row {} cites {artifact:?}, but package \
                         {package:?} declares no `#[test]` function whose name ends {path:?} at \
                         a module path the file layout can produce. The citation names a \
                         `--exact` filter that would match nothing, and a libtest filter \
                         matching nothing exits 0 (`fln-mandated-mutant-join-unwatched-uagk`).",
                        row.bead
                    ));
                }
                continue;
            }
            let Some(target_path) = d.targets.get(target) else {
                findings.push(format!(
                    "granularity-unbound: terminal row {} cites {artifact:?}, but no \
                     integration-test target named {target:?} exists in this workspace.",
                    row.bead
                ));
                continue;
            };
            let owner = target_path
                .rsplit_once("/tests/")
                .map(|(member, _)| member)
                .unwrap_or_default();
            if d.packages.get(owner).map(String::as_str) != Some(package) {
                findings.push(format!(
                    "granularity-unbound: terminal row {} cites {artifact:?}, but target \
                     {target:?} lives in {target_path}, whose package is {:?}. The package \
                     qualifier is what makes this kind survive two members sharing a stem — it \
                     may not be wrong.",
                    row.bead,
                    d.packages.get(owner)
                ));
                continue;
            }
            if !d.target_tests[target].contains(path) {
                findings.push(format!(
                    "granularity-unbound: terminal row {} cites {artifact:?}, but {target:?} \
                     declares no `#[test] fn {path}`.",
                    row.bead
                ));
            } else if d.ignored.contains(&(target_path.clone(), path.to_string())) {
                findings.push(format!(
                    "granularity-ignored: terminal row {} cites {artifact:?}, and that function \
                     carries `#[ignore]`. Cargo compiles it; libtest never runs it. The row now \
                     rests on ONE test, and that test is one CI does not execute — see \
                     IGNORED_PRODUCER_ALLOWANCE, which declares it. Migrating a row to this \
                     citation would delete it from FILE_GRANULAR_EVIDENCE_ALLOWANCE and lower \
                     the ceiling, recording a REPAIR for a row that now rests on nothing that \
                     runs. Cite a test CI executes, or leave the row file-granular and say why.",
                    row.bead
                ));
            }
        }
    }

    // --- the join to the ignored-producer set, in both citation shapes ------
    //
    // **The premise this guard's own residue item 4 rested on was retired by its own repair.**
    // That item read: "Artifact citations are file-granular, so the manifest cannot express
    // which test a row rests on and this guard cannot check it." True when written, and false
    // from `f24b6670`, which added `test:<pkg>::<target>::<path>` — the manifest can now name
    // one function, and the first thing it can name is an `#[ignore]`d one. The two facts sat
    // in THIS FILE, forty lines apart: `IGNORED_PRODUCER_ALLOWANCE` names five tests CI
    // compiles and never runs, `judge_granularity` resolved a citation against the function
    // list without consulting it. That is item 7's join, inside one artifact, in the guard
    // written about item 7 — `fln-history-rewrite-evidence-anchor-reachability-vdi4`'s row was
    // caught by this same guard for the same shape.
    //
    // Measured green at `5f7e44ad`: all four mutants below failed and the other 44 tests
    // passed, so a row citing an ignored function left the population as a REPAIR and lowered
    // the ceiling. Ten terminal rows cite one of the four ignored-producer surfaces and **all
    // ten** are declared in `FILE_GRANULAR_EVIDENCE_ALLOWANCE`, so every one is queued for the
    // migration that opens this. For two the ignored function is the *only* honest answer:
    // `pinned_present_olean_kernel_differential`'s `#[ignore]` reason names `fln-7odd`, and
    // `present_olean_corpus_thread_matrix_compares_stream_digests`' names `93te` — both beads
    // whose coverage rows cite the file.
    if d.ignored.is_empty() {
        findings.push(
            "granularity-ignored-scan: the `#[ignore]` scan found nothing, so both checks below \
             are vacuous and every citation resolves clean regardless of whether CI runs it. \
             That is the attribute scan breaking, not a tree in which every test now runs."
                .to_string(),
        );
    }

    // The coarse half, and the reason it is not redundant with the population above. A row
    // citing a FILE has always rested on that file's tests collectively, and
    // `IGNORED_PRODUCER_ALLOWANCE`'s own defence is a fraction — "2/14, 1/15, 1/10 and 1/9,
    // and no surface has every test ignored". That last clause is the load-bearing one and it
    // was a measurement transcribed into a doc comment, checked by nobody. Derived here, so
    // the day a surface's last running test is `#[ignore]`d the rows citing it say so.
    for row in &d.rows {
        for surface in &row.coarse {
            let Some(text) = d.surfaces.get(surface) else {
                continue;
            };
            let total = test_functions(text).len();
            let ignored_here = d
                .ignored
                .iter()
                .filter(|(where_, _)| where_ == surface)
                .count();
            if total > 0 && ignored_here >= total {
                findings.push(format!(
                    "granularity-hollow-surface: terminal row {} cites {surface}, whose \
                     {total} `#[test]` functions are ALL `#[ignore]`d. A file-granular citation \
                     rests on the surface's tests collectively; this surface has none that run, \
                     so the row's evidence is compiled and never executed. The fraction defence \
                     in IGNORED_PRODUCER_ALLOWANCE — no surface has every test ignored — has \
                     stopped holding here.",
                    row.bead
                ));
            }
        }
    }

    findings
}

/// Every registered `fln.e2e/2` scenario is bound to a lane script that exists, every lane
/// script's scenario is registered, and every governed lane is dispatched by a workflow —
/// or declared, by set equality in both directions.
///
/// **Residue item 1 of this module's own list, closed as far as text can close it.** The
/// binding this derives was previously asserted in prose as "keys match `scripts/e2e/<key>.sh`
/// by shared filename", which is false for five of thirteen keys — `env_snapshots.sh` hosts
/// six scenarios and is named after one. A rename of that file would have orphaned five
/// registrations with nothing to say so.
///
/// Findings are prefixed `lane-…` so the campaign asserts *which* one fired. A campaign
/// scoring "something went red" credits a mutant to an assertion that had stopped testing
/// what it names (`fln-mandated-mutant-join-unwatched-uagk`).
///
/// **What it does not earn.** A workflow *naming* a script is not a run of it — the same
/// limit `uagk`'s cron token carries, stated here so nobody re-derives it as observation.
/// And a lane dispatched only from `scripts/check.sh` would read as undispatched: measured
/// at `ad2b9207` no lane is, `check.sh` names two only to shellcheck them, and the loud
/// direction is the correct one for a check that cannot decide.
fn judge_lane_binding(
    d: &Derivation,
    weak_allowance: &[&str],
    undispatched_allowance: &[(&str, &str)],
) -> Vec<String> {
    let mut findings = Vec::new();

    // Which lanes are governed is read off their text, never their name or a list.
    let governed: BTreeMap<&str, &str> = d
        .lanes
        .iter()
        .filter(|(_, text)| text.contains(GOVERNED_E2E_SCHEMA))
        .map(|(path, text)| (path.as_str(), text.as_str()))
        .collect();

    // --- A collapsed scan is a broken scan, never a clean tree ---------------
    if d.lanes.is_empty() {
        findings.push(
            "lane-scan: scripts/e2e yielded no lane scripts at all. That is a broken walk, \
             not a repository without lanes."
                .to_string(),
        );
    }
    if governed.is_empty() {
        findings.push(format!(
            "lane-scan: none of the {} lane scripts carries the {GOVERNED_E2E_SCHEMA} schema \
             token. Either the schema was renamed — in which case this guard, \
             scripts/evidence.py and every lane moved apart — or the read returned nothing.",
            d.lanes.len()
        ));
    }
    if d.e2e_keys.is_empty() {
        findings.push(
            "lane-scan: E2E_STEP_ORDERS yielded no registered scenarios. The registry moved \
             or the reader broke; an empty registry is not a state this guard may assume."
                .to_string(),
        );
    }
    if !findings.is_empty() {
        return findings;
    }

    // --- How each registered scenario reaches a lane ------------------------
    let mut assigned_by: BTreeMap<&str, BTreeSet<&str>> = BTreeMap::new();
    for (path, text) in &governed {
        for literal in scenario_assignments(text) {
            if !d.e2e_keys.contains(&literal) {
                findings.push(format!(
                    "lane-unregistered: {path} assigns scenario {literal:?}, which is absent \
                     from E2E_STEP_ORDERS. scripts/evidence.py refuses to validate a run \
                     under an unregistered scenario, so this lane cannot produce evidence \
                     until the step order is registered."
                ));
                continue;
            }
            assigned_by
                .entry(
                    d.e2e_keys
                        .get(&literal)
                        .expect("membership was just checked")
                        .as_str(),
                )
                .or_default()
                .insert(path);
        }
    }

    let mut weakly_bound: BTreeSet<&str> = BTreeSet::new();
    for key in &d.e2e_keys {
        if assigned_by.contains_key(key.as_str()) {
            continue;
        }
        let worded: Vec<&str> = governed
            .iter()
            .filter(|(_, text)| names_scenario_in_code(text, key))
            .map(|(path, _)| *path)
            .collect();
        if worded.is_empty() {
            findings.push(format!(
                "lane-orphan: scenario {key:?} is registered in E2E_STEP_ORDERS and no \
                 governed lane script assigns or names it. A registered scenario no lane \
                 runs is a step order nothing can ever satisfy, and a coverage row citing \
                 it passes the registration check in this same file as though a lane existed."
            ));
        } else {
            weakly_bound.insert(key.as_str());
        }
    }

    // --- The weakly-bound population, by set equality in both directions ----
    let declared_weak: BTreeSet<&str> = weak_allowance.iter().copied().collect();
    let grew: Vec<&&str> = weakly_bound.difference(&declared_weak).collect();
    if !grew.is_empty() {
        findings.push(format!(
            "lane-weak-grew: {grew:?} reach their lane only as a bare word in code, and are \
             not in WEAKLY_BOUND_SCENARIOS. Either bind the scenario with a `…SCENARIO=` \
             assignment in its lane — the repair — or add it here, which is a deliberate \
             edit naming exactly what is now resting on the weaker binding."
        ));
    }
    let shrank: Vec<&&str> = declared_weak.difference(&weakly_bound).collect();
    if !shrank.is_empty() {
        findings.push(format!(
            "lane-weak-shrank: {shrank:?} are declared in WEAKLY_BOUND_SCENARIOS but now \
             carry a real assignment. This is the good direction: delete exactly those \
             entries. A set, not a count, so the slot a repair frees cannot be spent on the \
             next weakly-bound scenario without naming it (fln-cross-tree-baked-root-k60n)."
        ));
    }

    // --- Governed lanes no workflow dispatches ------------------------------
    let measured_undispatched: BTreeSet<&str> = governed
        .keys()
        .copied()
        .filter(|path| !d.workflow_text.contains(*path))
        .collect();
    let declared_undispatched: BTreeSet<&str> = undispatched_allowance
        .iter()
        .map(|(path, _)| *path)
        .collect();

    let newly: Vec<&&str> = measured_undispatched
        .difference(&declared_undispatched)
        .collect();
    if !newly.is_empty() {
        findings.push(format!(
            "lane-undispatched: {newly:?} carry the {GOVERNED_E2E_SCHEMA} schema and are \
             named by no workflow. A governed lane nothing dispatches is this bead's own \
             defect one level up from the rows it judges: registered, linted, and never run."
        ));
    }
    let now_dispatched: Vec<&&str> = declared_undispatched
        .difference(&measured_undispatched)
        .collect();
    if !now_dispatched.is_empty() {
        findings.push(format!(
            "lane-dispatch-stale: {now_dispatched:?} are declared undispatched and a \
             workflow now names them. Delete those entries from \
             UNDISPATCHED_GOVERNED_LANES."
        ));
    }

    // Each declared entry's stated reason is re-derived, so it cannot rot into a bare
    // exemption whose argument nobody reads — AGENTS.md's own complaint about the
    // BOUNDARY_API rows whose fields 5 and 6 are checked non-empty and discarded.
    for (path, reason) in undispatched_allowance {
        let Some(text) = d.lanes.get(*path) else {
            findings.push(format!(
                "lane-dispatch-stale: UNDISPATCHED_GOVERNED_LANES names {path}, which is not \
                 a lane script in scripts/e2e. A declaration outliving its subject is the \
                 shape this guard exists to refuse."
            ));
            continue;
        };
        if !governed.contains_key(path) {
            findings.push(format!(
                "lane-dispatch-stale: {path} is declared undispatched but no longer carries \
                 the {GOVERNED_E2E_SCHEMA} schema, so this guard does not govern it."
            ));
            continue;
        }
        if !reaches_the_pinned_reference(&shell_code_only(text)) {
            findings.push(format!(
                "lane-reason-falsified: {path} is exempted because it {reason}, and its code \
                 no longer names any pin coordinate. The exemption's stated reason is the \
                 thing that earns it; when the reason stops holding the exemption goes, \
                 rather than surviving as a path in a list."
            ));
        }
    }

    findings
}

// ---------------------------------------------------------------------------
// The judgement
// ---------------------------------------------------------------------------

/// Does any CI job run `surface` at all?
fn run_by_ci(d: &Derivation, surface: &str) -> bool {
    d.jobs
        .iter()
        .any(|job| reach_covers(&test_reach(job, d.check_sh_workspace), surface, &d.members))
}

/// Does any CI job that has installed the pinned Reference run `surface`?
fn run_by_ci_with_the_pin(d: &Derivation, surface: &str) -> bool {
    d.jobs.iter().any(|job| {
        installs_reference_pin(job)
            && reach_covers(&test_reach(job, d.check_sh_workspace), surface, &d.members)
    })
}

/// The measured population: terminal rows citing a pin-reaching surface that CI runs
/// pinless, and terminal rows citing a surface CI does not run at all.
fn measure(d: &Derivation) -> (BTreeSet<String>, BTreeMap<String, BTreeSet<String>>) {
    let mut unexecuted = BTreeSet::new();
    let mut unrun: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    for row in &d.rows {
        for surface in &row.surfaces {
            if !run_by_ci(d, surface) {
                unrun
                    .entry(row.bead.clone())
                    .or_default()
                    .insert(surface.clone());
            } else if d.pin_reaching.contains(surface) && !run_by_ci_with_the_pin(d, surface) {
                unexecuted.insert(row.bead.clone());
            }
        }
    }
    (unexecuted, unrun)
}

/// Every finding, as a list of sentences. Empty is clean.
///
/// Factored out of the test so the mutation campaign can perturb one derived fact at a time
/// and assert *which* finding appears. A campaign that accepted "something went red" would
/// score a mutant killed by an assertion that had stopped testing what it names
/// (`fln-mandated-mutant-join-unwatched-uagk`).
fn judge(d: &Derivation, allowance: &[&str], ceiling: usize) -> Vec<String> {
    let mut findings = Vec::new();

    // --- R1: the scan must refuse rather than report a clean tree ------------
    //
    // A tally of zero is a broken collector, never a clean tree. Each of these is the
    // question "did the thing that produces this answer actually run?" asked of the guard
    // itself — which is the bead's own subject, one level in.
    if d.jobs.is_empty() {
        findings.push(
            "scan: the workflow reader found no jobs. It reads block-mapping YAML \
             (`jobs:` at column zero, ids at two spaces); a flow-style or restructured \
             workflow defeats it. Zero jobs is a broken reader, not a CI with no jobs."
                .to_string(),
        );
    }
    if d.surfaces.is_empty() {
        findings.push(
            "scan: no workspace member source files were found. The member globs resolved \
             to nothing, or the layout moved."
                .to_string(),
        );
    }
    if d.pin_reaching.is_empty() {
        findings.push(format!(
            "scan: no source file in the workspace reaches the pinned Reference. That is \
             not a repaired tree — the coordinates {PIN_COORDINATES:?} no longer match how \
             this workspace locates the toolchain, so the scan is measuring nothing."
        ));
    }
    if !reaches_the_pinned_reference(&d.pin_module) {
        findings.push(format!(
            "scan: crates/fln-conformance/src/pin.rs — the sanctioned locator, and this \
             scan's positive control — matches none of {PIN_COORDINATES:?}. The coordinate \
             set is stale; every negative result below is vacuous until it is repaired."
        ));
    }
    if d.rows.is_empty() {
        findings.push(
            "scan: no terminal coverage rows were derived. Either every bead is open, or \
             the manifest reader stopped resolving rows."
                .to_string(),
        );
    }
    if d.e2e_keys.is_empty() {
        findings.push(
            "scan: E2E_STEP_ORDERS yielded no scenarios. The registry moved or was \
             restructured; the e2e citation check below cannot decide."
                .to_string(),
        );
    }
    if !d
        .jobs
        .iter()
        .any(|job| !test_reach(job, d.check_sh_workspace).is_empty())
    {
        findings.push(
            "scan: no CI job runs any cargo test. Either CI has stopped testing this \
             workspace — in which case every row below rests on nothing — or the link from \
             .github/workflows through scripts/check.sh to the workspace suite has broken. \
             ci.yml never invokes `cargo test` for the workspace itself; its gate step runs \
             scripts/check.sh, whose `test` stage does."
                .to_string(),
        );
    }

    // --- The exclusion allowance, both directions ---------------------------
    for (path, reason) in PIN_REACH_SCAN_EXCLUSIONS {
        match d.surfaces.get(*path) {
            None => findings.push(format!(
                "exclusion: {path} is declared excluded ({reason}) but is not in the scan \
                 scope. A dangling exclusion is itself a defect — delete the entry."
            )),
            Some(text) if !reaches_the_pinned_reference(text) => findings.push(format!(
                "exclusion: {path} is declared excluded ({reason}) but no longer matches any \
                 pin coordinate, so excluding it changes nothing. A vacuous exclusion hides \
                 the next real one — delete the entry."
            )),
            Some(_) => {}
        }
    }
    if PIN_REACH_SCAN_EXCLUSIONS.len() != PIN_REACH_SCAN_EXCLUSION_CEILING {
        findings.push(format!(
            "exclusion: the exclusion allowance holds {} entries against a ceiling of {}. \
             Growing it is how a derived scope quietly becomes a hand-list; shrinking it \
             requires lowering the ceiling in the same edit.",
            PIN_REACH_SCAN_EXCLUSIONS.len(),
            PIN_REACH_SCAN_EXCLUSION_CEILING
        ));
    }

    // --- R2/R3: the population, bound by cardinality in both directions -----
    let (unexecuted, unrun) = measure(d);
    let declared: BTreeSet<String> = allowance.iter().map(|id| (*id).to_string()).collect();

    let grew: Vec<&String> = unexecuted.difference(&declared).collect();
    if !grew.is_empty() {
        findings.push(format!(
            "population-grew: {grew:?} are terminal `complete` rows whose cited evidence CI \
             runs WITHOUT the pinned Reference installed, so the pin-dependent rigs inside \
             it take a typed skip and the run reports ok. This does not say the rows are \
             false — it says the repository cannot tell, and every CI run re-asserts the \
             green. Either make the job that runs them install the pin, or stop citing a \
             pin-dependent surface as the evidence. Declaring them here is the last resort \
             and requires raising UNEXECUTED_EVIDENCE_CEILING, which is a debt, not a fix."
        ));
    }

    let shrank: Vec<&String> = declared.difference(&unexecuted).collect();
    if !shrank.is_empty() {
        findings.push(format!(
            "population-shrank: {shrank:?} are declared in UNEXECUTED_EVIDENCE_ALLOWANCE but \
             are no longer measured. This is the good direction and the edit is mechanical: \
             delete exactly those ids from UNEXECUTED_EVIDENCE_ALLOWANCE and lower \
             UNEXECUTED_EVIDENCE_CEILING to {} in the same commit. The equality is checked \
             so a repair cannot land without shrinking the declaration with it — an \
             allowance that only ever grows is the shape this guard exists to prevent.",
            unexecuted.len()
        ));
    }

    if allowance.len() != ceiling {
        findings.push(format!(
            "ceiling: UNEXECUTED_EVIDENCE_ALLOWANCE holds {} ids against a ceiling of {}. \
             The ceiling is a ratchet, not a budget: equality means a shrink must lower it \
             in the same edit, so the headroom a repair earns cannot be spent silencing the \
             next hollow row.",
            allowance.len(),
            ceiling
        ));
    }

    // --- The empty allowance, asserted rather than passed silently ----------
    if !unrun.is_empty() {
        findings.push(format!(
            "unrun: {unrun:?} — terminal rows citing a test surface that NO CI job compiles \
             or runs at all. There is no allowance for this and there has never been one \
             (measured empty at 7b1af002). Asking whether the thing a citation names is run \
             at all is the check `fln-bench-apparatus-empty-referent-bkw6` had to invent \
             because there was no evidence object to compare against."
        ));
    }

    // --- R4: cited e2e scenarios must be registered -------------------------
    for row in &d.rows {
        for scenario in &row.scenarios {
            if NON_E2E_SCENARIOS.contains(&scenario.as_str()) || d.e2e_keys.contains(scenario) {
                continue;
            }
            findings.push(format!(
                "e2e: terminal row {} cites scenario {scenario:?}, which is not registered in \
                 E2E_STEP_ORDERS. scripts/evidence.py refuses to validate an unregistered \
                 scenario, so nothing checks that lane's step order.",
                row.bead
            ));
        }
    }

    findings
}

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
}

// ---------------------------------------------------------------------------
// The guard
// ---------------------------------------------------------------------------

/// Every terminal coverage row's cited evidence is either run by CI with the pinned
/// Reference installed, or declared — and the declaration can only shrink.
#[test]
fn terminal_rows_do_not_rest_on_evidence_ci_never_executed() {
    let d = derive(&root());
    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        findings.is_empty(),
        "the CI-execution join (bead fln-rgha):\n  - {}",
        findings.join("\n  - ")
    );
}

/// Every registered scenario reaches a lane that exists, and every governed lane is
/// dispatched — or declared, by set equality in both directions.
#[test]
fn every_registered_e2e_scenario_is_bound_to_a_lane_and_every_governed_lane_is_dispatched() {
    let d = derive(&root());
    let findings = judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES);
    assert!(
        findings.is_empty(),
        "the registered-scenario/lane join (bead fln-rgha, residue item 1):\n  - {}",
        findings.join("\n  - ")
    );
}

/// The derivation's own shape, reported so a silent collapse cannot read as a clean tree.
///
/// `bkw6`'s lesson in one assertion: when the far end can be empty, bind the claim to the
/// cardinality of what it asserts and let the number fail in both directions. Every count
/// here is a *floor of one*, deliberately — freezing today's numbers would redden a correct
/// repair, and the population equality above already binds the number that matters.
#[test]
fn the_derivation_reports_what_it_measured_and_refuses_an_empty_scan() {
    let d = derive(&root());
    eprintln!(
        "ci-execution-join: members={} surfaces={} pin_reaching={} excluded={} jobs={} \
         check_sh_workspace={} terminal_rows={} e2e_keys={}",
        d.members.len(),
        d.surfaces.len(),
        d.pin_reaching.len(),
        d.excluded.len(),
        d.jobs.len(),
        d.check_sh_workspace,
        d.rows.len(),
        d.e2e_keys.len(),
    );
    assert!(!d.members.is_empty(), "member globs resolved to nothing");
    assert!(!d.surfaces.is_empty(), "no member source files found");
    assert!(!d.jobs.is_empty(), "no CI jobs parsed");
    assert!(!d.rows.is_empty(), "no terminal coverage rows derived");
    assert!(
        d.check_sh_workspace,
        "scripts/check.sh no longer runs an unrestricted workspace `cargo test`. That is \
         either a real change to what CI covers — in which case every conformance row's \
         evidence stopped running — or this reader has broken. It is the single link \
         between .github/workflows and the workspace suite."
    );
}

/// The self-exclusion is exercised, not asserted.
///
/// `fln-8zsq`'s repair taught that a source-reading guard's own text is inside its search
/// space, and `franken_lean-2ki4` cost a third instance by excluding only *itself* rather
/// than every guard body. The trap one level in is that such a control is usually
/// **vacuous**: if the guard spells its needles in a form the scan cannot match, excluding
/// itself changes nothing and the check passes for the wrong reason. So both halves are
/// asserted — the file is excluded, *and* it would be caught without the exclusion.
#[test]
fn the_scan_excludes_its_own_declarations_and_that_exclusion_is_not_vacuous() {
    let d = derive(&root());
    for (path, reason) in PIN_REACH_SCAN_EXCLUSIONS {
        let text = d
            .surfaces
            .get(*path)
            .unwrap_or_else(|| panic!("declared exclusion {path} ({reason}) is not in scope"));
        assert!(
            reaches_the_pinned_reference(text),
            "{path} is excluded ({reason}) but matches no pin coordinate, so the exclusion \
             is vacuous — it is not doing the job it is declared to do"
        );
        assert!(
            !d.pin_reaching.contains(*path),
            "{path} is declared excluded but is in the pin-reaching set anyway"
        );
    }
}

// ---------------------------------------------------------------------------
// The mutation campaign
// ---------------------------------------------------------------------------
//
// Each mutant perturbs ONE derived fact and asserts the finding that names it. Asserting
// only that something went red would score a mutant killed by an assertion that had
// stopped testing what it claims to (`fln-mandated-mutant-join-unwatched-uagk`, measured:
// skipping the positivity check still left the bad block rejected, for a different reason).

fn has(findings: &[String], prefix: &str) -> bool {
    findings.iter().any(|finding| finding.starts_with(prefix))
}

fn baseline() -> Derivation {
    let d = derive(&root());
    assert!(
        judge(
            &d,
            UNEXECUTED_EVIDENCE_ALLOWANCE,
            UNEXECUTED_EVIDENCE_CEILING
        )
        .is_empty(),
        "the campaign's control must start clean, or every kill below is unattributable"
    );
    d
}

/// A CI job that installs the pin repairs the defect — and the declaration must shrink
/// with it, in the same commit, or the guard reddens.
#[test]
fn mutant_ci_installs_the_pin_forces_the_declaration_to_shrink() {
    let mut d = baseline();
    let workspace = d.check_sh_workspace;
    for job in &mut d.jobs {
        if !test_reach(job, workspace).is_empty() {
            job.body
                .push_str("      - run: elan toolchain install leanprover/lean4:v4.32.0\n");
        }
    }
    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        has(&findings, "population-shrank:"),
        "installing the pin in the job that runs the suite must empty the population and \
         demand the declaration shrink; got {findings:?}"
    );
    assert!(
        !has(&findings, "population-grew:"),
        "a repair must not read as a new instance: {findings:?}"
    );
}

/// A new terminal row resting on an unrun suite reddens, and cannot be silenced by
/// declaring it without also raising the ceiling.
#[test]
fn mutant_a_new_row_on_a_pin_reaching_surface_reddens_and_resists_silencing() {
    let mut d = baseline();
    let surface = d
        .pin_reaching
        .iter()
        .find(|path| path.contains("/tests/"))
        .expect("at least one pin-reaching test surface")
        .clone();
    d.rows.push(TerminalRow {
        bead: "fln-planted-mutant".to_string(),
        surfaces: [surface].into(),
        scenarios: vec!["quality_gate".to_string()],
        coarse: BTreeSet::new(),
        fine: Vec::new(),
    });

    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        has(&findings, "population-grew:"),
        "a thirteenth row must redden; got {findings:?}"
    );

    // The silencing move: declare it. The ceiling must refuse.
    let mut grown: Vec<&str> = UNEXECUTED_EVIDENCE_ALLOWANCE.to_vec();
    grown.push("fln-planted-mutant");
    let findings = judge(&d, &grown, UNEXECUTED_EVIDENCE_CEILING);
    assert!(
        !has(&findings, "population-grew:"),
        "declaring it must satisfy the membership check, or the ceiling is not what refuses"
    );
    assert!(
        has(&findings, "ceiling:"),
        "growing the declaration must trip the ceiling — that is the whole reason it is an \
         equality; got {findings:?}"
    );
}

/// A repair that is not accompanied by a shrink reddens: this is the direction a one-way
/// membership check would miss entirely.
#[test]
fn mutant_a_row_leaving_the_population_without_a_shrink_reddens() {
    let mut d = baseline();
    // It must be a row that is IN the population. The first draft removed `rows[0]`, which
    // is not, so nothing changed and the mutant survived a guard that was working correctly
    // — a control that perturbs the wrong thing scores a kill it did not earn.
    let declared: BTreeSet<&str> = UNEXECUTED_EVIDENCE_ALLOWANCE.iter().copied().collect();
    let index = d
        .rows
        .iter()
        .position(|row| declared.contains(row.bead.as_str()))
        .expect("the population is non-empty, so some row carries a declared bead");
    let dropped = d.rows.remove(index).bead;
    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        has(&findings, "population-shrank:"),
        "removing {dropped} must demand the declaration shrink; got {findings:?}"
    );
    assert!(
        findings.iter().any(|finding| finding.contains(&dropped)),
        "the finding must NAME the id to delete — a wall you cannot act on is a gate people \
         bypass; got {findings:?}"
    );
}

/// A suite removed from CI must redden as loudly as a row added to the population — the
/// second of the two directions this guard exists to bind.
///
/// `scripts/check.sh` is the only link between the workflow files and the workspace suite,
/// so severing it takes every cited surface out of CI's reach at once. Note which finding
/// fires: **not** the `scan:` refusal, because `mandated-mutants.yml` still runs one
/// `--test` target so *some* job still runs *some* cargo test. The first version of this
/// mutant asserted `scan:` and failed against a guard that was behaving correctly. What
/// actually catches it is `unrun:`, the empty allowance — which is the assertion that has
/// no headroom at all and therefore the one that should catch it.
#[test]
fn mutant_check_sh_stops_running_the_workspace_suite() {
    let mut d = baseline();
    d.check_sh_workspace = false;
    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        has(&findings, "unrun:"),
        "severing check.sh must report every cited surface as one no CI job runs, against an \
         allowance that is empty and has never been anything else; got {findings:?}"
    );
    // And the population must EMPTY rather than persist: those rows are no longer merely
    // pinless, they are unrun, which is the stronger finding and must not be double-counted.
    assert!(
        has(&findings, "population-shrank:"),
        "the pinless population must give way to the unrun one rather than both standing; \
         got {findings:?}"
    );
}

/// The coordinates going stale must refuse, not report a repaired tree. This is the
/// broken-collector direction: `uagk` scored a campaign green while running nothing
/// because a libtest filter matched nothing and exited 0.
#[test]
fn mutant_an_empty_pin_reaching_scope_refuses_instead_of_reporting_clean() {
    let mut d = baseline();
    d.pin_reaching.clear();
    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        has(&findings, "scan:"),
        "an empty pin-reaching set is a broken scan and must refuse; got {findings:?}"
    );
    assert!(
        has(&findings, "population-shrank:"),
        "it must ALSO fail the population equality rather than silently emptying it: a scan \
         that measures nothing agrees with every declaration; got {findings:?}"
    );
}

/// The positive control on the coordinate set itself. If the sanctioned locator stops
/// matching, every negative result is vacuous and the guard must say so.
#[test]
fn mutant_a_stale_coordinate_set_is_caught_by_its_own_positive_control() {
    let mut d = baseline();
    d.pin_module = "// the locator was rewritten and names no coordinate\n".to_string();
    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        has(&findings, "scan:"),
        "a locator that matches no coordinate must refuse; got {findings:?}"
    );
}

/// Removing the exclusion must fail LOUD rather than pass. When self-exclusion is removed
/// entirely the correct direction is a refusal on a clean tree (`fln-8zsq`).
#[test]
fn mutant_a_stale_or_vacuous_exclusion_is_refused() {
    let mut d = baseline();
    // A declared exclusion whose file no longer carries a coordinate.
    d.surfaces.insert(
        PIN_REACH_SCAN_EXCLUSIONS[0].0.to_string(),
        "// nothing here\n".to_string(),
    );
    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        has(&findings, "exclusion:"),
        "an exclusion that no longer excludes anything must be refused as vacuous; got \
         {findings:?}"
    );
}

/// Workspace membership must come from the manifest. Equating the workspace with `crates/`
/// reports six terminal rows citing `tools/structure-guard` tests as evidence CI never
/// runs — measured, and the false positive this test exists to keep dead.
#[test]
fn mutant_members_hardcoded_to_crates_resurrects_the_tools_false_positive() {
    let mut d = baseline();
    d.members.retain(|member| member.starts_with("crates/"));
    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        has(&findings, "unrun:"),
        "dropping tools/* from the member set must report its tests as unrun — if it does \
         not, the manifest-derived membership is not load-bearing and this guard would have \
         shipped six false positives; got {findings:?}"
    );
    assert!(
        findings
            .iter()
            .any(|finding| finding.contains("tools/structure-guard")),
        "the finding must name the surfaces that dropped out; got {findings:?}"
    );
}

/// Every test CI compiles and never runs is declared with what compensates for it.
#[test]
fn every_ignored_producer_is_declared_with_its_compensating_mechanism() {
    let d = derive(&root());
    eprintln!(
        "ci-execution-join: ignored_tests={} (attribute-counted, not token-counted)",
        d.ignored.len()
    );
    let findings = judge_ignored(&d, IGNORED_PRODUCER_ALLOWANCE, IGNORED_PRODUCER_CEILING);
    assert!(
        findings.is_empty(),
        "the ignored-producer class (bead franken_lean-ignored-producer-class-unguarded-t4u1):\n  - {}",
        findings.join("\n  - ")
    );
}

/// **The mutant that would have caught this guard's own wrong number.**
///
/// Until `974fcc5a` the module doc above said "fifteen `#[ignore]`d tests". There are five.
/// The number came from counting the token, which `kernel_replay.rs` alone mentions many
/// times in module docs, doc comments, an assertion message, and one guard's own *needle*.
/// So the control is not "does the count look right" — it is: **inject every shape of
/// mention and require the count not to move.**
#[test]
fn mutant_discussing_the_attribute_must_not_change_the_count() {
    let mut d = baseline_ignored();
    let before = d.ignored.len();

    let discussion = "\
//! The corpus lane is `#[ignore]`d for cost.\n\
/// `#[ignore]`d because it edits tracked source.\n\
fn talks_about_it() {\n\
    let gated = body.contains(\"#[ignore\");\n\
    assert!(gated, \"the campaign is #[ignore]d, so the filter matches nothing\");\n\
}\n";
    d.surfaces.insert(
        "crates/fln-planted/tests/discussion.rs".to_string(),
        discussion.to_string(),
    );
    let recounted: BTreeSet<(String, String)> = d
        .surfaces
        .iter()
        .flat_map(|(path, text)| {
            ignored_tests(text)
                .into_iter()
                .map(|(name, _)| (path.clone(), name))
        })
        .collect();
    assert_eq!(
        recounted.len(),
        before,
        "five shapes of MENTION were injected and the count moved. Counting the token \
         rather than the attribute is exactly how this guard's own documentation came to \
         claim fifteen; recounted {recounted:?}"
    );

    // And the positive half: one real attribute must move it by exactly one.
    d.surfaces.insert(
        "crates/fln-planted/tests/real.rs".to_string(),
        format!("{discussion}#[ignore = \"cost\"]\nfn real_lane() {{}}\n"),
    );
    let recounted: BTreeSet<(String, String)> = d
        .surfaces
        .iter()
        .flat_map(|(path, text)| {
            ignored_tests(text)
                .into_iter()
                .map(|(name, _)| (path.clone(), name))
        })
        .collect();
    assert_eq!(
        recounted.len(),
        before + 1,
        "a real attribute must be counted, or the scan is blind rather than precise"
    );
}

fn baseline_ignored() -> Derivation {
    let d = derive(&root());
    assert!(
        judge_ignored(&d, IGNORED_PRODUCER_ALLOWANCE, IGNORED_PRODUCER_CEILING).is_empty(),
        "the campaign's control must start clean, or every kill below is unattributable"
    );
    d
}

/// A sixth `#[ignore]` reddens until its author says what compensates it, and declaring it
/// costs a visible edit to the ceiling.
#[test]
fn mutant_a_new_ignore_reddens_and_resists_silent_declaration() {
    let mut d = baseline_ignored();
    d.ignored.insert((
        "crates/fln-planted/tests/new_lane.rs".to_string(),
        "an_expensive_new_lane".to_string(),
    ));
    let findings = judge_ignored(&d, IGNORED_PRODUCER_ALLOWANCE, IGNORED_PRODUCER_CEILING);
    assert!(
        has(&findings, "ignored-undeclared:"),
        "a sixth ignored test must redden; got {findings:?}"
    );

    let mut grown: Vec<(&str, &str, &str)> = IGNORED_PRODUCER_ALLOWANCE.to_vec();
    grown.push((
        "crates/fln-planted/tests/new_lane.rs",
        "an_expensive_new_lane",
        "nothing yet",
    ));
    let findings = judge_ignored(&d, &grown, IGNORED_PRODUCER_CEILING);
    assert!(
        !has(&findings, "ignored-undeclared:"),
        "declaring it must satisfy membership, or the ceiling is not what refuses"
    );
    assert!(
        has(&findings, "ignored-ceiling:"),
        "growing the declaration must trip the ceiling; got {findings:?}"
    );
}

/// Un-ignoring a test forces the declaration to shrink with it.
#[test]
fn mutant_un_ignoring_a_test_forces_the_declaration_to_shrink() {
    let mut d = baseline_ignored();
    let removed = d
        .ignored
        .iter()
        .next()
        .cloned()
        .expect("the ignored set is non-empty");
    d.ignored.remove(&removed);
    let findings = judge_ignored(&d, IGNORED_PRODUCER_ALLOWANCE, IGNORED_PRODUCER_CEILING);
    assert!(
        has(&findings, "ignored-stale:"),
        "a declaration that outlived its ignore must redden; got {findings:?}"
    );
    assert!(
        findings.iter().any(|f| f.contains(&removed.1)),
        "the finding must NAME the entry to delete; got {findings:?}"
    );
}

/// An empty scan refuses rather than agreeing with every declaration.
#[test]
fn mutant_an_empty_ignore_scan_refuses_instead_of_reporting_clean() {
    let mut d = baseline_ignored();
    d.ignored.clear();
    let findings = judge_ignored(&d, IGNORED_PRODUCER_ALLOWANCE, IGNORED_PRODUCER_CEILING);
    assert!(
        has(&findings, "ignored-scan:"),
        "a scan finding nothing is broken, not clean; got {findings:?}"
    );
}

/// A declaration whose mechanism is blank declares nothing.
#[test]
fn mutant_a_blank_compensating_mechanism_is_refused() {
    let d = baseline_ignored();
    let mut blank: Vec<(&str, &str, &str)> = IGNORED_PRODUCER_ALLOWANCE.to_vec();
    blank[0].2 = "   ";
    let findings = judge_ignored(&d, &blank, IGNORED_PRODUCER_CEILING);
    assert!(
        has(&findings, "ignored-vacuous:"),
        "an empty mechanism must be refused; got {findings:?}"
    );
}

/// A cited scenario that is not registered has nothing checking its step order.
#[test]
fn mutant_an_unregistered_e2e_scenario_reddens() {
    let mut d = baseline();
    d.rows.push(TerminalRow {
        bead: "fln-planted-scenario".to_string(),
        surfaces: BTreeSet::new(),
        scenarios: vec!["a_lane_nobody_registered".to_string()],
        coarse: BTreeSet::new(),
        fine: Vec::new(),
    });
    let findings = judge(
        &d,
        UNEXECUTED_EVIDENCE_ALLOWANCE,
        UNEXECUTED_EVIDENCE_CEILING,
    );
    assert!(
        has(&findings, "e2e:"),
        "citing an unregistered scenario must redden; got {findings:?}"
    );
}

// ---------------------------------------------------------------------------
// Granularity: the guard, and the campaign against it
// ---------------------------------------------------------------------------

/// Terminal rows state their evidence at the granularity that runs, or are declared.
#[test]
fn terminal_rows_do_not_state_evidence_coarser_than_the_unit_that_runs() {
    let d = derive(&root());
    let findings = judge_granularity(
        &d,
        FILE_GRANULAR_EVIDENCE_ALLOWANCE,
        FILE_GRANULAR_EVIDENCE_CEILING,
    );
    assert!(findings.is_empty(), "{}", findings.join("\n\n"));
}

/// The stem the legacy `cargo-test:<stem>` kind is keyed by is still an identity.
///
/// The map this asserts over is the *repaired* one. Its predecessor took every `.rs` beneath a
/// `tests/` tree and so carried the stem `mod` three times over, last insert winning — a key
/// denoting no cargo target and colliding three ways, live and unnoticed at `29852ec1`.
#[test]
fn the_cargo_test_stem_is_still_an_identity() {
    let d = derive(&root());
    let collisions: Vec<&(String, String)> = d
        .granularity_preconditions
        .iter()
        .filter(|(_, reason)| reason.contains("shares its file stem"))
        .collect();
    assert!(
        collisions.is_empty(),
        "`cargo-test:<stem>` is keyed by file stem and these targets now share one, so the key \
         has stopped being an identity: {collisions:?}"
    );
    assert!(
        d.targets.len() >= 70,
        "the target scan resolved only {} targets against 75 at 29852ec1 — a collapsed map \
         makes the assertion above vacuous",
        d.targets.len()
    );
    assert!(
        !d.targets.contains_key("mod"),
        "`mod` is back in the target map, so the scan is ingesting `tests/common/mod.rs` \
         modules again — that key denotes no cargo target and collides three ways"
    );
}

fn granularity_findings(d: &Derivation) -> Vec<String> {
    judge_granularity(
        d,
        FILE_GRANULAR_EVIDENCE_ALLOWANCE,
        FILE_GRANULAR_EVIDENCE_CEILING,
    )
}

fn fires(findings: &[String], prefix: &str) -> bool {
    findings.iter().any(|finding| finding.starts_with(prefix))
}

fn a_coarse_row(d: &mut Derivation) -> &mut TerminalRow {
    d.rows
        .iter_mut()
        .find(|row| !row.coarse.is_empty())
        .expect("at least one terminal row cites a surface coarsely")
}

#[test]
fn granularity_mutant_a_new_file_granular_row_is_caught() {
    let mut d = derive(&root());
    let stem = d.targets.values().next().expect("targets").clone();
    d.rows.push(TerminalRow {
        bead: "planted-row-citing-a-file".to_string(),
        surfaces: BTreeSet::new(),
        scenarios: Vec::new(),
        coarse: BTreeSet::from([stem]),
        fine: Vec::new(),
    });
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-grew"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_migration_that_did_not_shrink_the_declaration_is_caught() {
    let mut d = derive(&root());
    a_coarse_row(&mut d).coarse.clear();
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-shrank"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_grown_declaration_is_caught_by_the_ceiling() {
    let d = derive(&root());
    let mut grown: Vec<&str> = FILE_GRANULAR_EVIDENCE_ALLOWANCE.to_vec();
    grown.push("planted-extra-id");
    let findings = judge_granularity(&d, &grown, FILE_GRANULAR_EVIDENCE_CEILING);
    assert!(fires(&findings, "granularity-ceiling"), "{findings:?}");
}

#[test]
fn granularity_mutant_an_empty_target_scan_refuses_instead_of_passing() {
    let mut d = derive(&root());
    d.targets.clear();
    d.target_tests.clear();
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-scan"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_manifest_that_defeats_autodiscovery_is_caught() {
    let mut d = derive(&root());
    d.granularity_preconditions.push((
        "crates/fln-planted/Cargo.toml".to_string(),
        "declares an explicit [[test]] target section".to_string(),
    ));
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-derivation"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_collapsed_fanout_refuses_instead_of_reporting_a_repair() {
    let mut d = derive(&root());
    for names in d.target_tests.values_mut() {
        names.clear();
    }
    d.lib_tests.clear();
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-fanout"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_citation_naming_no_such_function_cannot_leave_the_population() {
    let mut d = derive(&root());
    let row = a_coarse_row(&mut d);
    row.coarse.clear();
    row.fine
        .push("test:fln-conformance::kernel_replay::no_such_function".to_string());
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-unbound"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_lib_citation_naming_no_such_function_is_caught() {
    let mut d = derive(&root());
    let row = a_coarse_row(&mut d);
    row.coarse.clear();
    row.fine
        .push("test:fln-env::lib::extensions::tests::no_such_unit_test".to_string());
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-unbound"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_lib_citation_at_the_wrong_module_path_is_caught() {
    let d0 = derive(&root());
    // A real function, deliberately cited under a module prefix that is not its file's.
    let (prefix, function) = d0
        .lib_tests
        .get("fln-env")
        .expect("fln-env declares lib unit tests")
        .iter()
        .find(|(prefix, _)| !prefix.is_empty())
        .expect("a non-root module carries a unit test")
        .clone();
    let mut d = derive(&root());
    let row = a_coarse_row(&mut d);
    row.coarse.clear();
    row.fine.push(format!(
        "test:fln-env::lib::not_{prefix}::tests::{function}"
    ));
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-unbound"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_citation_naming_no_such_target_is_caught() {
    let mut d = derive(&root());
    d.rows[0]
        .fine
        .push("test:fln-conformance::no_such_target::f".to_string());
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-unbound"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_citation_with_the_wrong_package_is_caught() {
    let mut d = derive(&root());
    d.rows[0]
        .fine
        .push("test:fln-kernel::kernel_replay::prelude_replays_through_the_kernel".to_string());
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-unbound"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_malformed_citation_is_a_finding_not_a_shrug() {
    let mut d = derive(&root());
    d.rows[0].fine.push("test:kernel_replay".to_string());
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-unbound"), "{findings:?}");
}

/// The name of an `#[ignore]`d test in `kernel_replay`, taken from the derivation rather than
/// written down, so a rename moves this with it.
fn an_ignored_function(d: &Derivation, surface: &str) -> String {
    d.ignored
        .iter()
        .find(|(where_, _)| where_ == surface)
        .map(|(_, function)| function.clone())
        .unwrap_or_else(|| panic!("{surface} declares no `#[ignore]`d test"))
}

#[test]
fn granularity_mutant_a_citation_naming_an_ignored_function_cannot_leave_the_population() {
    let mut d = derive(&root());
    let function = an_ignored_function(&d, "crates/fln-conformance/tests/kernel_replay.rs");
    let row = a_coarse_row(&mut d);
    row.coarse.clear();
    row.fine
        .push(format!("test:fln-conformance::kernel_replay::{function}"));
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-ignored"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_lib_citation_naming_an_ignored_unit_test_is_caught() {
    let mut d = derive(&root());
    // No lib unit test is `#[ignore]`d today, so the lib half of the join has no live
    // instance. Plant one: an unfalsifiable half is `bkw6`'s empty referent, and the whole
    // point of this bead is that a population with no members is where the next one lands.
    let surface = "crates/fln-env/src/extensions.rs".to_string();
    assert!(
        d.surfaces.contains_key(&surface),
        "the planted surface must be real, or this mutant proves nothing"
    );
    let prefix = module_path_prefix(&surface).expect("a lib source file has a module path");
    d.ignored
        .insert((surface, "planted_ignored_unit_test".to_string()));
    d.lib_tests
        .entry("fln-env".to_string())
        .or_default()
        .insert((prefix.clone(), "planted_ignored_unit_test".to_string()));
    let row = a_coarse_row(&mut d);
    row.coarse.clear();
    row.fine.push(format!(
        "test:fln-env::lib::{prefix}::planted_ignored_unit_test"
    ));
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-ignored"), "{findings:?}");
}

#[test]
fn granularity_mutant_a_surface_whose_every_test_is_ignored_is_not_evidence() {
    let mut d = derive(&root());
    let surface = "crates/fln-conformance/tests/kernel_replay.rs".to_string();
    // Every `#[test]` in the file ignored: the file-granular defence — a row rests on the
    // surface's *other* tests — has nothing left to rest on.
    for function in test_functions(&d.surfaces[&surface]) {
        d.ignored.insert((surface.clone(), function));
    }
    let row = a_coarse_row(&mut d);
    row.coarse.clear();
    row.coarse.insert(surface);
    let findings = granularity_findings(&d);
    assert!(
        fires(&findings, "granularity-hollow-surface"),
        "{findings:?}"
    );
}

#[test]
fn granularity_mutant_an_empty_ignore_scan_makes_the_join_refuse() {
    let mut d = derive(&root());
    d.ignored.clear();
    let findings = granularity_findings(&d);
    assert!(fires(&findings, "granularity-ignored-scan"), "{findings:?}");
}

/// The positive control, and what stops every mutant above being vacuous: a **real** citation
/// of each flavour resolves, produces no finding, and forces its own declaration edit.
#[test]
fn granularity_control_real_citations_resolve_and_force_their_own_shrink() {
    for (package, target, path_of) in [
        ("fln-conformance", "kernel_replay", true),
        ("fln-env", "lib", false),
    ] {
        let mut d = derive(&root());
        let citation = if path_of {
            let function = d.target_tests[target]
                .iter()
                .next()
                .expect("the target declares tests")
                .clone();
            format!("test:{package}::{target}::{function}")
        } else {
            let (prefix, function) = d.lib_tests[package]
                .iter()
                .find(|(prefix, _)| !prefix.is_empty())
                .expect("a non-root module carries a unit test")
                .clone();
            format!("test:{package}::lib::{prefix}::tests::{function}")
        };
        let row = a_coarse_row(&mut d);
        let bead = row.bead.clone();
        row.coarse.clear();
        row.fine.push(citation.clone());
        let findings = granularity_findings(&d);
        assert!(
            !fires(&findings, "granularity-unbound"),
            "{citation} must resolve: {findings:?}"
        );
        assert!(
            findings
                .iter()
                .any(|f| f.starts_with("granularity-shrank") && f.contains(&bead)),
            "a migration must force its own declaration edit: {findings:?}"
        );
    }
}

/// A function-granular citation still resolves to the surface it names.
///
/// **This test exists because the migration that introduced the kind broke this, and the other
/// guard caught it.** `franken_lean-2jht` rests on a pin-dependent rig. When its
/// `crates/fln-kernel/tests/reference_differential.rs` citation was replaced by
/// `test:fln-kernel::reference_differential::kernel_verdicts_agree_with_the_pinned_reference`,
/// the row stopped resolving to any surface — so
/// `terminal_rows_do_not_rest_on_evidence_ci_never_executed` reported it as **repaired** and
/// demanded the pin-dependence allowance shrink. A granularity fix had silently shrunk a
/// neighbouring population by making its referent unresolvable.
///
/// The shape generalises past this instance: every population here is computed over resolved
/// surfaces, so a new citation kind that does not resolve does not merely fail to help — it
/// *removes* rows from every other guard at once, in the direction that reads as progress.
#[test]
fn a_function_granular_citation_still_resolves_to_its_surface() {
    let d = derive(&root());

    let migrated = d
        .rows
        .iter()
        .find(|row| row.bead == "franken_lean-2jht")
        .expect("franken_lean-2jht is terminal and carries a function-granular citation");
    assert!(
        !migrated.fine.is_empty(),
        "2jht is the live example this test is written from; if its citation stopped being \
         function-granular, point this test at another migrated row rather than deleting it"
    );
    assert!(
        migrated
            .surfaces
            .contains("crates/fln-kernel/tests/reference_differential.rs"),
        "a `test:` citation must resolve back to the surface it names, or every population \
         computed over surfaces silently loses this row. Resolved: {:?}",
        migrated.surfaces
    );

    // The lib flavour resolves too, and by LONGEST module prefix — `execution::tests::f` must
    // pick `src/execution.rs`, never `src/lib.rs`, whose empty prefix also matches.
    let lib_cited = d
        .rows
        .iter()
        .find(|row| row.bead == "franken_lean-ignored-producer-class-unguarded-t4u1")
        .expect("t4u1 is terminal and carries a lib-flavour citation");
    assert!(
        lib_cited
            .surfaces
            .contains("crates/fln-conformance/src/execution.rs"),
        "a `test:<pkg>::lib::<module::path::fn>` citation must resolve to the source file whose \
         layout prefix it begins with, longest prefix winning. Resolved: {:?}",
        lib_cited.surfaces
    );
}

// ---------------------------------------------------------------------------
// The lane-binding campaign (residue item 1)
// ---------------------------------------------------------------------------
//
// Each mutant perturbs ONE derived fact and asserts the `lane-…` finding that names it.
// The last one is a NEGATIVE control in the good direction: it renames the dispatch helper
// three scenarios reach their lane through, and requires the guard to stay GREEN. A
// helper-keyed scan — the hand-list this derivation exists to avoid — dies there, and a
// campaign made only of kills would never notice.

fn baseline_lane() -> Derivation {
    let d = derive(&root());
    assert!(
        judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES).is_empty(),
        "the campaign's control must start clean, or every kill below is unattributable"
    );
    d
}

fn lane_mut<'a>(d: &'a mut Derivation, path: &str) -> &'a mut String {
    d.lanes
        .get_mut(path)
        .unwrap_or_else(|| panic!("{path} must be a lane script this scan read"))
}

/// A step order registered for a scenario no lane runs.
#[test]
fn lane_mutant_a_registered_scenario_with_no_lane_is_an_orphan() {
    let mut d = baseline_lane();
    d.e2e_keys
        .insert("a_lane_that_was_renamed_away".to_string());
    let findings = judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES);
    assert!(
        has(&findings, "lane-orphan:"),
        "a registered scenario no lane assigns or names must redden as an orphan; got {findings:?}"
    );
}

/// A lane whose scenario `scripts/evidence.py` would refuse to validate.
#[test]
fn lane_mutant_a_lane_assigning_an_unregistered_scenario_reddens() {
    let mut d = baseline_lane();
    lane_mut(&mut d, "scripts/e2e/verdict_schema.sh").push_str("\nSCENARIO=\"never_registered\"\n");
    let findings = judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES);
    assert!(
        has(&findings, "lane-unregistered:"),
        "a governed lane assigning a scenario absent from E2E_STEP_ORDERS must redden; got {findings:?}"
    );
}

/// A fourth scenario dropping to the weaker binding cannot arrive silently.
#[test]
fn lane_mutant_a_fourth_weakly_bound_scenario_cannot_arrive_silently() {
    let mut d = baseline_lane();
    let lane = lane_mut(&mut d, "scripts/e2e/verdict_schema.sh");
    *lane = lane.replace(
        "SCENARIO=\"verdict_schema\"",
        "SCENARIO=\"$held_elsewhere\"",
    );
    lane.push_str("\nrun_identity_child verdict_schema fln-planted\n");
    let findings = judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES);
    assert!(
        has(&findings, "lane-weak-grew:"),
        "a scenario losing its assignment and resting on a bare word must redden; got {findings:?}"
    );
    assert!(
        !has(&findings, "lane-orphan:"),
        "it is still bound, just weakly — reporting it as an orphan would name the wrong \
         repair: {findings:?}"
    );
}

/// Binding a weakly-bound scenario properly is the repair, and the declaration must shrink
/// with it in the same commit.
#[test]
fn lane_mutant_repairing_a_weak_binding_forces_the_declaration_to_shrink() {
    let mut d = baseline_lane();
    lane_mut(&mut d, "scripts/e2e/env_snapshots.sh")
        .push_str("\nSCENARIO=\"declaration_tag_matrix\"\n");
    let findings = judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES);
    assert!(
        has(&findings, "lane-weak-shrank:"),
        "a repaired binding must demand its entry be deleted, so the freed slot cannot be \
         spent on the next one; got {findings:?}"
    );
    assert!(
        !has(&findings, "lane-weak-grew:"),
        "a repair must not read as a new instance: {findings:?}"
    );
}

/// A governed lane that no workflow dispatches — the defect this residue item found live.
#[test]
fn lane_mutant_a_governed_lane_no_workflow_dispatches_reddens() {
    let mut d = baseline_lane();
    d.workflow_text = d.workflow_text.replace(
        "scripts/e2e/verdict_schema.sh",
        "scripts/e2e/renamed_away.sh",
    );
    let findings = judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES);
    assert!(
        has(&findings, "lane-undispatched:"),
        "a governed lane dropping out of every workflow must redden; got {findings:?}"
    );
}

/// Dispatching the exempt lane is the repair, and its entry must go in the same commit.
#[test]
fn lane_mutant_dispatching_the_exempt_lane_forces_the_declaration_to_shrink() {
    let mut d = baseline_lane();
    d.workflow_text
        .push_str("\n            ./scripts/e2e/kernel_replay.sh\n");
    let findings = judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES);
    assert!(
        has(&findings, "lane-dispatch-stale:"),
        "an exemption whose lane is now dispatched must demand deletion; got {findings:?}"
    );
}

/// The exemption's stated reason is re-derived, never read.
///
/// The sharpest mutant here, and the one that separates this from AGENTS.md's own complaint
/// about `ci/BOUNDARY_API.txt`: 24 of its 66 rows argue nothing at all, because the field
/// carrying the argument is checked non-empty and then discarded. A reason that is only
/// prose survives its own falsification.
#[test]
fn lane_mutant_the_exempt_lanes_reason_is_re_derived_not_read() {
    let mut d = baseline_lane();
    let lane = lane_mut(&mut d, "scripts/e2e/kernel_replay.sh");
    for coordinate in PIN_COORDINATES {
        *lane = lane.replace(coordinate, "A_LOCAL_FIXTURE");
    }
    let findings = judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES);
    assert!(
        has(&findings, "lane-reason-falsified:"),
        "a lane exempted for reaching the pin, that no longer reaches it, must lose the \
         exemption rather than keep it as a path in a list; got {findings:?}"
    );
}

/// A scan that returns nothing is a broken scan, never a repository without lanes.
#[test]
fn lane_mutant_an_empty_scan_refuses_instead_of_reporting_clean() {
    let mut d = baseline_lane();
    d.lanes.clear();
    assert!(
        has(
            &judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES),
            "lane-scan:"
        ),
        "an empty lane walk must refuse"
    );

    let mut d = baseline_lane();
    for text in d.lanes.values_mut() {
        *text = text.replace(GOVERNED_E2E_SCHEMA, "fln.e2e/superseded");
    }
    assert!(
        has(
            &judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES),
            "lane-scan:"
        ),
        "every lane losing the governed schema token must refuse, not report a clean tree"
    );
}

/// **The negative control.** Renaming the dispatch helper must change nothing.
///
/// Three scenarios reach their lane as `run_identity_child <key> …`. The obvious derivation
/// matches that helper by name — and is a hand-list, the defect
/// `franken_lean-worktree-gitdir-refusal-hugg` is criticised for and the one
/// `franken_lean-build-gate-lane-governed-set-98np` measured itself committing: a scan keyed
/// to one spelling is a hand-list wearing a derived scan's clothes. This mutant is what tells
/// the two apart, and it is the only test here that requires GREEN.
#[test]
fn lane_control_renaming_the_dispatch_helper_does_not_break_the_binding() {
    let mut d = baseline_lane();
    let lane = lane_mut(&mut d, "scripts/e2e/env_snapshots.sh");
    *lane = lane.replace("run_identity_child", "dispatch_child_scenario");
    let findings = judge_lane_binding(&d, WEAKLY_BOUND_SCENARIOS, UNDISPATCHED_GOVERNED_LANES);
    assert!(
        findings.is_empty(),
        "the binding must survive renaming the helper it travels through — a scan that dies \
         here is keyed to a spelling, not derived from the artefacts; got {findings:?}"
    );
}
