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
//! 1. **The `E2E_STEP_ORDERS` key → shell script binding is nowhere declared.** Keys match
//!    `scripts/e2e/<key>.sh` by shared filename and nothing ties them; diverge them and any
//!    dispatch derivation silently misses the lane. That is hugg's criticism reproduced
//!    inside the method built to answer it, so this guard checks only *registration* —
//!    which `scripts/evidence.py` does enforce — and makes no dispatch claim at all.
//! 2. **Cargo's real target set.** Text cannot yield it; `bkw6` already paid for the
//!    text-only version by counting `[[bench]]` sections while cargo auto-discovered the
//!    rest. Member globs and directory layout are resolved here; `[[test]]` sections,
//!    `required-features` and auto-discovery beyond `tests/*.rs` are not modelled.
//! 3. **`check.sh` sub-modes.** `--self-test` and `--tribunal-manifest-inventory` are read
//!    as reaching the workspace suite because they invoke the same script. Today the same
//!    job also runs the plain gate, so the answer is unchanged; a job that ran *only* a
//!    sub-mode would be over-credited.
//! 4. **The fifteen `#[ignore]`d tests.** A cited surface can be run by CI while the test
//!    inside it that actually produces the evidence never executes. Artifact citations are
//!    file-granular, so the manifest cannot express which test a row rests on and this
//!    guard cannot check it. **This is the next instance of item 7 in this area.**
//! 5. **`--skip` at `scripts/check.sh:1586-1590`.** Treated as workspace-wide because
//!    `--skip` filters test *names*, not targets — true today, and a libtest filter that
//!    matches nothing exits 0 (`uagk`).

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use fln_conformance::execution::{
    CiJob, Field, PIN_COORDINATES, check_sh_reaches_workspace, ci_jobs, e2e_scenario_keys,
    installs_reference_pin, is_terminal, reach_covers, reaches_the_pinned_reference, record_field,
    test_reach, workspace_member_patterns,
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

/// Scenario tokens that name a gate stage rather than an `fln.e2e/2` lane.
const NON_E2E_SCENARIOS: &[&str] = &["quality_gate", "gate_self_test"];

// ---------------------------------------------------------------------------
// The derivation, gathered from disk
// ---------------------------------------------------------------------------

/// One terminal coverage row, reduced to what the join needs.
#[derive(Debug, Clone)]
struct TerminalRow {
    bead: String,
    surfaces: BTreeSet<String>,
    scenarios: Vec<String>,
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
    /// `crates/fln-conformance/src/pin.rs`, raw — the coordinate set's positive control.
    pin_module: String,
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

    let mut jobs = Vec::new();
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

    // `cargo-test:<stem>` names an integration target; cargo binds a target's name to its
    // file stem under `tests/`, so unlike the e2e scenario convention this binding is the
    // build system's, not a local habit.
    let mut by_stem: BTreeMap<String, String> = BTreeMap::new();
    for path in surfaces.keys() {
        if !path.contains("/tests/") {
            continue;
        }
        if let Some(stem) = path.rsplit('/').next().and_then(|n| n.strip_suffix(".rs")) {
            by_stem.insert(stem.to_string(), path.clone());
        }
    }

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
        for artifact in &artifacts {
            if surfaces.contains_key(artifact) {
                cited.insert(artifact.clone());
            } else if let Some(stem) = artifact.strip_prefix("cargo-test:")
                && let Some(path) = by_stem.get(stem)
            {
                cited.insert(path.clone());
            }
        }
        rows.push(TerminalRow {
            bead,
            surfaces: cited,
            scenarios,
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
        pin_module: read(root, "crates/fln-conformance/src/pin.rs"),
    }
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

/// A cited scenario that is not registered has nothing checking its step order.
#[test]
fn mutant_an_unregistered_e2e_scenario_reddens() {
    let mut d = baseline();
    d.rows.push(TerminalRow {
        bead: "fln-planted-scenario".to_string(),
        surfaces: BTreeSet::new(),
        scenarios: vec!["a_lane_nobody_registered".to_string()],
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
