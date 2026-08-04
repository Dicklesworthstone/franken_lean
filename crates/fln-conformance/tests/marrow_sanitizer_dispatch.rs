//! The join back from the Marrow sanitizer guards to the thing that dispatches them
//! (bead `fln-nhf5`).
//!
//! **Why this file exists at all.** `fln-nhf5`'s own item 1 is that the Miri and TSAN
//! guards were a *documented command* rather than a lane: "a sanitizer nobody invokes is
//! not coverage — it is a README". Landing a workflow fixes that once. Nothing stops it
//! being deleted, renamed, or quietly stripped of its cron afterwards, at which point the
//! guard document and this repository's evidence would still describe a lane that no
//! longer runs, and no test would say so. That is item 7's shape — a claim and its
//! producer, unjoined — arriving on the repair for a hollow green.
//!
//! **Both directions, because one-way is how this rots.** A workflow that names no runner
//! is a dispatcher for nothing; a runner that no workflow names is the README state
//! returning. Each is refused separately and by name.
//!
//! **Scope is DERIVED, never hand-listed.** The workflow directory is read, so a
//! dispatcher cannot be added, renamed or deleted behind this guard's back —
//! `mandated_mutants.rs` records why: `scripts/check.sh`'s `INPUT_PATHS` names `ci.yml`
//! and `contract-drift.yml` individually, so a third workflow joined the tree outside it
//! silently.
//!
//! **The predicates are BORROWED, not re-implemented.**
//! `fln_conformance::execution::{trigger_reachability, classifiable_workflows}` already
//! answer "can this workflow fire" for `fln-rgha` and `uagk`. A second copy here would be
//! free to drift from the one those beads are judged by, which is the defect family this
//! whole area is about.
//!
//! **What this does NOT earn, and it is inherited deliberately.** It proves the cadence is
//! CONFIGURED. It never proves a run OCCURRED — a workflow GitHub silently disables is
//! invisible from inside this repository. That is the open half of
//! `fln-mandated-mutant-join-unwatched-uagk`, and this guard inherits it rather than
//! closing it. It also says nothing about whether the sanitizers *find* anything: the
//! evidence that they fail on the real defect is a bounded measurement recorded on
//! `fln-nhf5`, not something re-run here.

#![forbid(unsafe_code)]

use fln_conformance::execution::{
    TriggerReachability, classifiable_workflows, trigger_reachability,
};

/// The runner every sanitizer step must go through.
///
/// It is a real file rather than an inline `cargo` invocation because it answers two
/// questions the exit code alone cannot: a race fired (exit code, checked first) and the
/// test actually ran (pass count, checked second). Both failure modes were measured on
/// `fln-nhf5`; the second is a libtest filter matching nothing, which exits 0.
const RUNNER: &str = "scripts/ci/run_sanitizer_test.sh";

/// The four concurrency tests the guards cover.
///
/// Named here so that dropping one from the workflow is a build failure rather than a
/// quiet reduction in coverage. This is the guard's *subject*, and the guard document
/// (`crates/fln-unsafe-abi/MIRI_CONCURRENCY_GUARD.md`) must keep naming them too, so the
/// document and the lane cannot drift apart in either direction.
const COVERED_TESTS: [&str; 4] = [
    "mark_mt_negates_and_atomics_conserve",
    "mt_object_dies_on_last_dec",
    "rc_clone_and_drop_balance",
    "concurrent_publication",
];

const GUARD_DOC: &str = "crates/fln-unsafe-abi/MIRI_CONCURRENCY_GUARD.md";

fn workspace_root() -> &'static std::path::Path {
    static ROOT: std::sync::OnceLock<std::path::PathBuf> = std::sync::OnceLock::new();
    ROOT.get_or_init(|| fln_conformance::checked_workspace_root!())
        .as_path()
}

/// Every workflow file, read from the directory rather than from a list.
fn workflow_files(root: &std::path::Path) -> Vec<(String, String)> {
    let dir = root.join(".github/workflows");
    let mut out = Vec::new();
    let Ok(entries) = std::fs::read_dir(&dir) else {
        return out;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let is_yaml = path
            .extension()
            .and_then(|e| e.to_str())
            .is_some_and(|e| e == "yml" || e == "yaml");
        if !is_yaml {
            continue;
        }
        if let Ok(text) = std::fs::read_to_string(&path) {
            let name = path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or_default()
                .to_string();
            out.push((name, text));
        }
    }
    out.sort();
    out
}

#[test]
fn the_marrow_sanitizer_guards_are_dispatched_by_something_that_can_actually_fire() {
    let root = workspace_root();
    let workflows = workflow_files(root);

    // ANTI-VACUITY FLOOR. An empty or implausibly small scan is a BROKEN SCAN, not a clean
    // tree — the failure this repository has recorded repeatedly, most sharply when a
    // derived scope returned zero and read as "nothing to report". Without this, deleting
    // `.github/workflows/` entirely would make every assertion below pass vacuously.
    assert!(
        workflows.len() >= 2,
        "read {} workflow files from {}; a scan this small is broken, not clean. Every \
         assertion below would pass vacuously on an empty directory.",
        workflows.len(),
        root.join(".github/workflows").display()
    );

    // A workflow this guard cannot classify is refused BY NAME rather than silently scored
    // as "no dispatcher" — an inconclusive rendered as a verdict is FL-INV-07's exact
    // prohibition, and it would read as the true-looking finding "the cron was deleted".
    classifiable_workflows(&workflows).expect("every workflow must be classifiable");

    // ---- DIRECTION 1: some workflow dispatches the runner, and it can actually fire.
    let dispatchers: Vec<&(String, String)> = workflows
        .iter()
        .filter(|(_, text)| text.contains(RUNNER))
        .collect();
    assert!(
        !dispatchers.is_empty(),
        "no workflow in .github/workflows/ invokes `{RUNNER}`. The Marrow sanitizer guards \
         are back to being a documented command nobody runs, which is bead fln-nhf5's own \
         item 1: a sanitizer nobody invokes is not coverage, it is a README."
    );

    for (name, text) in &dispatchers {
        // Borrowed predicate: a workflow whose triggers cannot be reached is a file that
        // will never run, which is indistinguishable from an absent one at the moment it
        // matters.
        assert_eq!(
            trigger_reachability(text),
            TriggerReachability::Reachable,
            "{name} invokes {RUNNER} but its triggers are not reachable, so it can never \
             fire. A dispatcher that cannot run is not a dispatcher."
        );

        // The cadence claim itself. `fln-nhf5` asks for a nightly or pre-release cadence
        // rather than a per-commit gate; a workflow reduced to `workflow_dispatch` only
        // would still be "reachable" while nothing ever scheduled it.
        let scheduled = text
            .lines()
            .any(|l| l.trim_start().starts_with("schedule:"))
            && text.lines().any(|l| l.contains("cron:"));
        assert!(
            scheduled,
            "{name} invokes {RUNNER} but declares no `schedule:`/`cron:`. It would then run \
             only when a human remembers, which is the state fln-nhf5 was filed to end. If \
             the cadence is deliberately being withdrawn, say so here and in the bead \
             rather than deleting the cron quietly."
        );
    }

    // ---- DIRECTION 2: the runner exists. A workflow naming an absent script is a lane
    // that fails for the wrong reason, and the failure would read as a sanitizer finding.
    let runner = root.join(RUNNER);
    assert!(
        runner.is_file(),
        "{} names `{RUNNER}`, which does not exist at {}. The lane would fail for an \
         environment reason wearing the shape of a code defect.",
        dispatchers
            .iter()
            .map(|(n, _)| n.as_str())
            .collect::<Vec<_>>()
            .join(", "),
        runner.display()
    );

    // ---- DIRECTION 3: the covered tests are named in BOTH the lane and the guard
    // document, so neither can silently shed coverage the other still advertises.
    let dispatch_text: String = dispatchers
        .iter()
        .map(|(_, t)| t.as_str())
        .collect::<Vec<_>>()
        .join("\n");
    let doc = std::fs::read_to_string(root.join(GUARD_DOC))
        .unwrap_or_else(|e| panic!("{GUARD_DOC} must be readable: {e}"));
    for test in COVERED_TESTS {
        assert!(
            dispatch_text.contains(test),
            "the sanitizer workflow no longer names `{test}`. Coverage shrank without this \
             guard moving; if that is deliberate, remove it from COVERED_TESTS in the same \
             commit and say why."
        );
        assert!(
            doc.contains(test),
            "{GUARD_DOC} no longer names `{test}` while the workflow still runs it. The \
             runnable spec and the lane have drifted."
        );
    }
}

/// The runner must judge the exit code BEFORE it reads any output text.
///
/// This is the whole reason the runner is a file rather than a bare `cargo` line, and it
/// is the one property that cannot be recovered by reading the workflow: TSAN reports at
/// process teardown, *after* libtest prints `test result: ok`, and exits 66. A runner that
/// inspected the text first — or that greps for `ok` at all as its verdict — reports a
/// clean run over a detected data race. Measured on `fln-nhf5` against the real crate.
#[test]
fn the_sanitizer_runner_judges_the_exit_code_before_it_reads_any_output() {
    let root = workspace_root();
    let runner = std::fs::read_to_string(root.join(RUNNER))
        .unwrap_or_else(|e| panic!("{RUNNER} must be readable: {e}"));

    let code: Vec<&str> = runner
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .collect();
    assert!(
        code.len() >= 15,
        "read only {} executable lines from {RUNNER}; a scan this small is broken, not a \
         simple script, and every assertion below would pass vacuously.",
        code.len()
    );

    let exit_check = code
        .iter()
        .position(|l| l.contains("$rc") && l.contains("-ne 0"))
        .expect("the runner must test the captured exit code against zero");
    let text_read = code
        .iter()
        .position(|l| l.contains("test result"))
        .expect("the runner must read the libtest result line for its anti-vacuity floor");

    assert!(
        exit_check < text_read,
        "{RUNNER} inspects libtest's output text (line {text_read}) BEFORE it judges the \
         exit code (line {exit_check}). TSAN reports at teardown, after libtest has \
         printed `test result: ok`, so a race-failed run would be reported as a filter \
         problem instead of as the data race it is. Judge the exit code first."
    );

    // The anti-vacuity half must also be present: a zero pass count is a broken run, not a
    // clean one, because a libtest filter matching nothing exits 0.
    assert!(
        code.iter()
            .any(|l| l.contains("passed") && l.contains("-eq 0")),
        "{RUNNER} does not refuse a zero pass count. A libtest filter matching nothing \
         prints `0 passed` and exits 0, so without this the lane is green while running no \
         test — measured on fln-nhf5 by adding `--exact` to a short test name."
    );
}
