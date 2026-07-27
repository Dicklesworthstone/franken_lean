//! Cross-artifact linkage for the extracted contracts (bead franken_lean-53v,
//! plan Appendix B/C). Every rendered surface — Markdown contract, generated
//! Rust module, canonical inventory — must name the SAME inventory root, and
//! the extern census must be internally coherent. A hand edit to any one
//! artifact breaks the linkage here; drift against the pin itself is caught by
//! the extractors' `--check` lanes (scripts/e2e/contract_drift.sh).
//!
//! ## What this suite does NOT verify, and why (bead `franken_lean-pnav`)
//!
//! [`assert_linked`] compares the inventory digest *labels* the Markdown and the
//! generated Rust each carry, and checks the inventory file is non-empty. It does
//! **not** recompute a digest from content, so a reader should not take a green
//! run here as "the contracts match the pin".
//!
//! That is not laziness, and it is worth recording why rather than leaving it as
//! an apparent oversight: `INVENTORY_DIGEST` is **sha256** of the inventory text
//! (`gen_abi_contract.py:1348`), and the closed dependency universe (D1) contains
//! **no sha256** — `fln-hash` implements BLAKE3. So no Rust in this workspace can
//! recompute that digest, and the only thing that can verify it is the Python
//! extractor that produced it. Implementing sha256 to satisfy a test would be the
//! wrong trade; recording that the verification is single-sourced is the honest
//! one.
//!
//! What this suite *can* do is refuse to let the delegation go silently missing —
//! see [`the_lane_this_suite_delegates_to_is_present_and_invoked`]. The risk
//! `franken_lean-pnav` names is structural: if `contract_drift.sh` is ever removed
//! or unwired, this shape-only cluster becomes the only remaining check on
//! the ABI and olean contracts, and nothing in these tests would change colour.
//!
//! ## Where the delegate runs (bead `franken_lean-0kpa`)
//!
//! The pin-dependent lane runs weekly and on demand in
//! `.github/workflows/contract-drift.yml`. That workflow installs the exact Reference
//! tag parsed from `SUITE.lock`, exposes the toolchain/vendor identity joins, and runs
//! every extractor check plus the lane's seeded mutants. It deliberately does not run
//! in the per-commit workflow, whose runner has no Reference toolchain.

#![forbid(unsafe_code)]

use fln_conformance::execution::{TriggerReachability, trigger_reachability};
use std::fs;
use std::path::{Path, PathBuf};

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
        .canonicalize()
        .expect("repo root")
}

fn find_digest(text: &str, marker: &str) -> Option<String> {
    // The first 64-hex-char token on the first line naming the marker.
    let line = text.lines().find(|l| l.contains(marker))?;
    line.split(|c: char| !c.is_ascii_hexdigit())
        .find(|tk| tk.len() == 64)
        .map(str::to_string)
}

fn assert_linked(md_rel: &str, rs_rel: &str, inv_rel: &str) {
    let root = root();
    let md = fs::read_to_string(root.join(md_rel));
    assert!(md.is_ok(), "{md_rel}: {:?}", md.as_ref().err());
    let md = md.expect("asserted above");
    let rs = fs::read_to_string(root.join(rs_rel));
    assert!(rs.is_ok(), "{rs_rel}: {:?}", rs.as_ref().err());
    let rs = rs.expect("asserted above");
    let inv = fs::read(root.join(inv_rel));
    assert!(inv.is_ok(), "{inv_rel}: {:?}", inv.as_ref().err());
    assert!(
        !inv.expect("asserted above").is_empty(),
        "{inv_rel} is empty"
    );
    let md_digest = find_digest(&md, "inventory");
    assert!(md_digest.is_some(), "{md_rel}: no inventory digest line");
    let rs_digest = find_digest(&rs, "INVENTORY_DIGEST");
    assert!(rs_digest.is_some(), "{rs_rel}: no INVENTORY_DIGEST line");
    assert_eq!(
        md_digest, rs_digest,
        "{md_rel} and {rs_rel} name different inventory roots"
    );
    assert!(
        md.contains("@generated") && rs.contains("@generated"),
        "rendered artifacts must carry the @generated marker"
    );
}

/// Lanes that exist and are correct but are wired into no gate, each naming the bead
/// that tracks the wiring. The remainder is declared, never silent.
///
/// Checked in BOTH directions by
/// [`the_lane_this_suite_delegates_to_is_present_and_invoked`]: an undeclared unwired
/// lane fails, and a declared lane that has since been wired ALSO fails. So the
/// allowance shrinks as lanes land and cannot quietly outlive the defect it records.
const UNWIRED_LANE_ALLOWANCE: &[(&str, &str)] = &[];

/// Is `lane` EXECUTED by the gate, as opposed to merely NAMED in it?
///
/// This distinction is the whole of bead `franken_lean-0kpa`, and getting it wrong is
/// how the previous version of this test sat green over a dormant lane. `scripts/check.sh`
/// names `contract_drift.sh` twice — once in `INPUT_PATHS`, once as an **argument to the
/// shellcheck stage** — and a `contains` check reads both as registration. Neither runs it.
///
/// Backslash continuations are joined into one logical line first, and that is
/// load-bearing in both directions. Without it a lane invoked by a wrapped `run_stage`
/// would be missed; with it, the shellcheck stage's arguments — `contract_drift.sh`
/// among them — land on the same logical line as `run_stage`, so mere membership in that
/// line cannot be the test. What remains is COMMAND POSITION:
///
/// * in `scripts/check.sh`, the command of a `run_stage <name>` (optionally through
///   `bash`/`sh`), not any argument that follows it;
/// * in any `.github/workflows/*.yml` or `*.yaml`, an executed `./<path>` **in a workflow
///   that can actually fire**.
///
/// That last clause is bead `franken_lean-workflow-invocation-ignores-trigger-reachability-acm4`,
/// and it is this bead's own defect one rung up. `0kpa` moved the check from *named in
/// `check.sh`* to *appears as `./path` in a workflow*; appearing in a workflow is still not
/// *reachable by a trigger*. A file with no `on:` block can never be dispatched, and until
/// this conjunct it satisfied the check that exists to stop a dormant lane — restoring the
/// exact state `0kpa` was filed for while every guard here stayed green. Reachability is
/// decided by [`trigger_reachability`], which is shared with `mandated_mutants`' dispatch
/// scan rather than written twice.
fn lane_is_invoked(root: &Path, lane: &str) -> bool {
    if fs::read_to_string(root.join("scripts/check.sh"))
        .is_ok_and(|gate| invoked_by_check_sh(&gate, lane))
    {
        return true;
    }

    fs::read_dir(root.join(".github/workflows")).is_ok_and(|entries| {
        entries.filter_map(Result::ok).any(|entry| {
            let path = entry.path();
            matches!(
                path.extension().and_then(|extension| extension.to_str()),
                Some("yml" | "yaml")
            ) && fs::read_to_string(path)
                .is_ok_and(|workflow| workflow_invokes_lane(&workflow, lane))
        })
    })
}

/// Does one workflow both execute `lane` and stand a chance of running?
///
/// Lifted out of [`lane_is_invoked`] for the same reason [`allowance_verdict`] was, and the
/// reason is worth stating because the first version of this repair did not do it: with the
/// conjunction inlined above, **deleting the reachability half broke no test**. The controls
/// exercised [`invoked_by_ci_yml`] and [`trigger_reachability`] individually, both of which
/// kept passing, while the production decision quietly returned to what `acm4` reported. A
/// guard whose fixtures pass either way is the defect this module exists to catch, one floor
/// down — so the decision the real scan makes is the decision the control calls.
fn workflow_invokes_lane(workflow: &str, lane: &str) -> bool {
    invoked_by_ci_yml(workflow, lane)
        && trigger_reachability(workflow) == TriggerReachability::Reachable
}

/// Join backslash continuations, so a wrapped `run_stage` is one line to the scanner.
fn logical_lines(text: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut current = String::new();
    for line in text.lines() {
        let trimmed = line.trim_end();
        match trimmed.strip_suffix('\\') {
            Some(head) => {
                current.push_str(head);
                current.push(' ');
            }
            None => {
                current.push_str(trimmed);
                out.push(std::mem::take(&mut current));
            }
        }
    }
    if !current.is_empty() {
        out.push(current);
    }
    out
}

/// Does `gate` run `lane` as the COMMAND of a `run_stage`, rather than name it?
fn invoked_by_check_sh(gate: &str, lane: &str) -> bool {
    logical_lines(gate).iter().any(|line| {
        let mut tok = line.split_whitespace();
        if tok.next() != Some("run_stage") {
            return false;
        }
        // Skip the stage name, then any interpreter prefix; what remains is the
        // command itself. Arguments further along the line do not count.
        let _stage = tok.next();
        let command = tok.next().map(|first| match first {
            "bash" | "sh" => tok.next().unwrap_or(first),
            other => other,
        });
        command == Some(lane)
    })
}

/// Does `ci` execute `lane` as `./<path>`?
///
/// **Execution position only — this deliberately says nothing about whether the workflow can
/// fire.** Keeping the two questions apart is what lets [`the_scanner_distinguishes_command_position_from_mention`]
/// and [`a_workflow_that_can_never_fire_does_not_count_as_invoking_a_lane`] each vary one
/// axis; the caller conjoins them. Reading this as "the lane runs" is `acm4` exactly.
fn invoked_by_ci_yml(ci: &str, lane: &str) -> bool {
    let executed = format!("./{lane}");
    ci.lines()
        .any(|line| line.trim_start().starts_with(&executed))
}

/// The scanner tells invocation from mention, including across a wrapped `run_stage`.
///
/// These are the controls for the two code paths a filesystem-level mutant cannot
/// reach today: `scripts/check.sh` happens to invoke every lane on a single line, so
/// deleting the continuation handling breaks nothing observable — until someone wraps
/// one, at which point a real invocation would read as absent.
#[test]
fn the_scanner_distinguishes_command_position_from_mention() {
    // A wrapped invocation IS an invocation.
    let wrapped = "run_stage drift \\\n  bash scripts/e2e/contract_drift.sh\n";
    assert!(
        invoked_by_check_sh(wrapped, "scripts/e2e/contract_drift.sh"),
        "a lane invoked across a backslash continuation must be seen"
    );

    // The shellcheck shape: the lane is an ARGUMENT on the same logical line as
    // run_stage. This is the exact false-green the old `contains` check reported as
    // registration.
    let as_argument = "run_stage shellcheck shellcheck scripts/check.sh \\\n  \
                       scripts/e2e/contract_drift.sh scripts/e2e/other.sh\n";
    assert!(
        !invoked_by_check_sh(as_argument, "scripts/e2e/contract_drift.sh"),
        "a lane passed as an argument to another command is NOT invoked"
    );

    // A governed-input listing is not invocation either.
    let as_input_path = "INPUT_PATHS=(\n  scripts/e2e/contract_drift.sh\n)\n";
    assert!(!invoked_by_check_sh(
        as_input_path,
        "scripts/e2e/contract_drift.sh"
    ));

    // ci.yml executes lanes as ./path; a bare mention in a comment does not.
    assert!(invoked_by_ci_yml(
        "          ./scripts/e2e/x.sh\n",
        "scripts/e2e/x.sh"
    ));
    assert!(!invoked_by_ci_yml(
        "          # see scripts/e2e/x.sh for details\n",
        "scripts/e2e/x.sh"
    ));
}

/// A workflow that can never fire is not a gate, however plainly it names the lane.
///
/// The control varies **reachability** and holds everything else fixed, which is the axis
/// `0kpa`'s own negative control did not vary — it separated a never-written filename from a
/// written one, and so earned confidence along an axis the claim did not rest on. Both texts
/// below contain the executed command, so [`invoked_by_ci_yml`] cannot tell them apart; that
/// is precisely the defect, and it is why the assertion is written against the pair rather
/// than against either one.
#[test]
fn a_workflow_that_can_never_fire_does_not_count_as_invoking_a_lane() {
    const LANE: &str = "scripts/e2e/contract_drift.sh";
    let steps = "jobs:\n  c:\n    steps:\n      - run: |\n          ./scripts/e2e/contract_drift.sh --check\n";
    let with_trigger = format!("on:\n  workflow_dispatch:\n{steps}");
    let no_trigger = steps.to_string();

    // The command is in execution position in BOTH, so the older half of the check is blind
    // to the difference. Asserted, not assumed: if this stopped holding, the control below
    // would be varying nothing.
    assert!(
        invoked_by_ci_yml(&with_trigger, LANE) && invoked_by_ci_yml(&no_trigger, LANE),
        "both fixtures must execute the lane, or this control no longer isolates reachability"
    );

    assert_eq!(
        trigger_reachability(&with_trigger),
        TriggerReachability::Reachable
    );
    assert_eq!(
        trigger_reachability(&no_trigger),
        TriggerReachability::NeverFires,
        "a workflow with no `on:` block can never be dispatched by GitHub, so it must not be \
         allowed to satisfy the check that exists to stop a dormant lane (acm4)"
    );

    // The decision the real scan makes, not its ingredients. Asserting only the two lines
    // above leaves the conjunction in `workflow_invokes_lane` untested, and a mutant deleting
    // it passes every other assertion in this file — measured, not supposed.
    assert!(workflow_invokes_lane(&with_trigger, LANE));
    assert!(
        !workflow_invokes_lane(&no_trigger, LANE),
        "the lane is executed by this workflow and the workflow can never run, so the lane is \
         not invoked by it — this is the assertion acm4's repair actually rests on"
    );
}

/// Every workflow in the tree must be classifiable, or the reachability half is guessing.
///
/// [`lane_is_invoked`] admits only [`TriggerReachability::Reachable`], so an *unreadable*
/// workflow silently reads as "does not invoke" — and a lane that is genuinely wired would
/// then fail as dormant, with the message blaming the lane rather than the reader. FL-INV-07
/// says an inconclusive outcome is neither verdict, so it is surfaced here as itself, named,
/// before it can be mistaken for either.
///
/// The floor is the other half: a scan that walked no workflows is a broken scan, not a
/// repository with no CI, and it would otherwise report this check as satisfied by nothing.
#[test]
fn every_workflow_can_be_classified_for_reachability() {
    let root = root();
    let dir = root.join(".github/workflows");
    let mut seen = 0usize;
    let mut reachable = 0usize;

    let entries = fs::read_dir(&dir).unwrap_or_else(|error| {
        panic!("{}: {error}", dir.display());
    });
    let mut files: Vec<(String, String)> = Vec::new();
    for entry in entries.flatten() {
        let path = entry.path();
        if !matches!(
            path.extension().and_then(|extension| extension.to_str()),
            Some("yml" | "yaml")
        ) {
            continue;
        }
        let text =
            fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        seen += 1;
        if trigger_reachability(&text) == TriggerReachability::Reachable {
            reachable += 1;
        }
        files.push((path.display().to_string(), text));
    }

    assert!(
        seen > 0,
        "no workflow files were read from {}. An empty scan is a broken scan, not a \
         repository with no CI: the reachability half of lane_is_invoked derives its whole \
         answer from this directory, so it refuses rather than passing on no evidence",
        dir.display()
    );

    // The real population plus ONE planted unclassifiable member, judged together. Asserting
    // only that the real population is clean leaves the refusal unexecuted — a healthy tree
    // has no unclassifiable workflow, so that assertion is decorative and a mutant gutting it
    // survives, measured. Judging the union instead exercises the refusal per commit *and*
    // pins the real tree: the verdict must name the plant and nothing else.
    const PLANT: &str = "planted-unclassifiable.yml";
    files.push((PLANT.to_string(), "{on: push, jobs: {}}\n".to_string()));
    let refusal = fln_conformance::execution::classifiable_workflows(&files)
        .expect_err("a planted unclassifiable workflow must be refused, or this guard is inert");
    assert!(
        refusal.contains(PLANT),
        "the refusal must name the offending workflow: {refusal}"
    );
    let real_offenders: Vec<&(String, String)> = files
        .iter()
        .filter(|(name, _)| name != PLANT && refusal.contains(name.as_str()))
        .collect();
    assert!(
        real_offenders.is_empty(),
        "{refusal}\n\nthe plant is expected; these are not: {:?}",
        real_offenders
            .iter()
            .map(|(name, _)| name)
            .collect::<Vec<_>>()
    );

    assert!(
        reachable > 0,
        "{seen} workflow(s) read and none declares a trigger. Either every workflow in this \
         repository is dormant, or the reader has stopped recognising a live one — and the \
         second would make lane_is_invoked's workflow branch answer `false` for everything, \
         which is a wall rather than a finding"
    );
}

/// Decide the allowance verdict for one lane: invoked-or-declared, in both directions.
///
/// Pure, and separated from the filesystem deliberately. Seeding a mutant that reaches
/// the stale-declaration branch through the real test requires a lane that is invoked,
/// declared, AND contains `--check`; every simpler mutation trips an earlier assertion
/// instead, so that branch reported as "killed" while never executing. An untested
/// branch inside a guard is the defect this module exists to catch, so the decision is
/// lifted out where [`allowance_verdict_fails_in_both_directions`] can exercise all
/// four combinations directly.
fn allowance_verdict(lane: &str, invoked: bool, declared: Option<&str>) -> Result<(), String> {
    match (invoked, declared) {
        (true, Some(reason)) => Err(format!(
            "{lane} IS now invoked by a gate, but it is still declared unwired in \
             UNWIRED_LANE_ALLOWANCE ({reason}). Remove the declaration: an allowance \
             that outlives its defect is how a repaired gap keeps reading as broken, \
             and it is what stops this list from shrinking."
        )),
        (false, None) => Err(format!(
            "{lane} exists but NO gate invokes it — it is not the command of any \
             run_stage in scripts/check.sh and is not executed in ci.yml. Being named \
             in INPUT_PATHS or passed to shellcheck is not invocation. Three suites \
             delegate their digest verification here, so the shape-only assertions \
             have silently become the only remaining check. Either wire it, or declare \
             it in UNWIRED_LANE_ALLOWANCE with the bead that tracks the wiring."
        )),
        (true, None) | (false, Some(_)) => Ok(()),
    }
}

/// Both failure directions fire, and both passing directions stay quiet.
#[test]
fn allowance_verdict_fails_in_both_directions() {
    // Wired and undeclared: the healthy end state.
    assert!(allowance_verdict("lane.sh", true, None).is_ok());
    // Unwired and declared: an explicitly tracked temporary state.
    assert!(allowance_verdict("lane.sh", false, Some("bead-x")).is_ok());

    // Unwired and undeclared — a lane silently doing nothing.
    let unwired = allowance_verdict("lane.sh", false, None)
        .expect_err("an unwired, undeclared lane must fail");
    assert!(
        unwired.contains("NO gate invokes it"),
        "wrong complaint: {unwired}"
    );

    // Wired but still declared — the allowance outliving its defect. This is the
    // branch a filesystem-level mutant could not reach.
    let stale = allowance_verdict("lane.sh", true, Some("bead-x"))
        .expect_err("a declared lane that is now invoked must fail");
    assert!(
        stale.contains("IS now invoked") && stale.contains("bead-x"),
        "wrong complaint: {stale}"
    );
}

/// The delegation in this module's header must stay true.
///
/// Every shape-only assertion in this cluster — here, `fln-rt`'s
/// `pin_binding_is_present`, and `fln-olean`'s — points at one lane for the real
/// verification. A pointer to a lane that no longer exists, or exists but is wired
/// into no gate, is worse than no pointer: it reads as coverage.
///
/// The earlier version of this test asserted that `scripts/check.sh` CONTAINS the lane
/// path and reported that as "it is run by the gate". Naming is not invoking, and the
/// lane has never been invoked anywhere. Its negative control varied the wrong axis —
/// it proved `contains` could distinguish a *never-written filename*, which was never
/// the risk. A negative control only earns confidence along the axis it actually
/// varies, so the controls below vary mention-versus-invocation, the axis the claim
/// rests on.
#[test]
fn the_lane_this_suite_delegates_to_is_present_and_invoked() {
    let root = root();
    const LANE: &str = "scripts/e2e/contract_drift.sh";

    let lane = fs::read_to_string(root.join(LANE));
    assert!(
        lane.is_ok(),
        "{LANE} is missing, and three test suites delegate their digest \
         verification to it. Either restore it or stop claiming the delegation in \
         those headers — a dangling pointer reads as coverage."
    );
    let lane = lane.expect("asserted above");
    assert!(
        lane.contains("--check"),
        "{LANE} no longer invokes an extractor --check lane, so the delegation it \
         receives is no longer honoured"
    );

    let declared = UNWIRED_LANE_ALLOWANCE
        .iter()
        .find(|(path, _)| *path == LANE)
        .map(|(_, reason)| *reason);
    let verdict = allowance_verdict(LANE, lane_is_invoked(&root, LANE), declared);
    assert!(verdict.is_ok(), "{}", verdict.err().unwrap_or_default());

    // Negative controls, varying the axis this assertion actually depends on:
    // mention versus invocation. The first is the live defect itself — the lane is
    // named in the gate and still not invoked — which is exactly the state the old
    // `contains` check reported as registered.
    let gate = fs::read_to_string(root.join("scripts/check.sh")).expect("scripts/check.sh");
    assert!(
        gate.contains(LANE) && !invoked_by_check_sh(&gate, LANE),
        "the mention-versus-invocation control no longer holds: {LANE} must still be \
         NAMED in scripts/check.sh while not being invoked by it, or this test can no \
         longer demonstrate that it tells the two apart"
    );
    // The converse: a lane that really is invoked must be recognised as such, so the
    // check is not merely returning false for everything.
    assert!(
        lane_is_invoked(&root, "scripts/verify_vendor_tree.sh"),
        "scripts/verify_vendor_tree.sh is the command of a run_stage in \
         scripts/check.sh, so an invocation check that cannot see it is broken"
    );
    assert!(
        !lane_is_invoked(&root, "scripts/e2e/contract_drift_that_does_not_exist.sh"),
        "a lane that was never written must not read as invoked"
    );
}

#[test]
fn abi_artifacts_share_one_inventory_root() {
    assert_linked(
        "ABI_CONTRACT.md",
        "crates/fln-rt/src/abi.rs",
        "contracts/abi_inventory.json",
    );
}

#[test]
fn olean_artifacts_share_one_inventory_root() {
    assert_linked(
        "OLEAN_CONTRACT.md",
        "crates/fln-olean/src/format.rs",
        "contracts/olean_inventory.json",
    );
}

#[test]
fn extern_census_is_coherent() {
    let root = root();
    let text = fs::read_to_string(root.join("contracts/extern_census.tsv"))
        .expect("contracts/extern_census.tsv");
    let mut declared_extern: Option<usize> = None;
    let mut declared_constants: Option<usize> = None;
    let mut extern_rows: Vec<Vec<&str>> = Vec::new();
    let mut summary_total: usize = 0;
    let mut schema_seen = false;
    let mut unknown_rows: Vec<String> = Vec::new();
    for line in text.lines() {
        if line.starts_with('#') || line.is_empty() {
            continue;
        }
        let cols: Vec<&str> = line.split('\t').collect();
        match cols[0] {
            _ if line == "schema fln-extern-census/1" => schema_seen = true,
            "extern_count" => declared_extern = Some(cols[1].parse().expect("extern_count")),
            "constant_count" => declared_constants = Some(cols[1].parse().expect("constant_count")),
            "columns" | "columns_summary" => {}
            "extern" => extern_rows.push(cols),
            "summary" => {
                assert_eq!(cols.len(), 4, "summary row arity: {line:?}");
                summary_total += cols[3].parse::<usize>().expect("summary count");
            }
            other => unknown_rows.push(other.to_string()),
        }
    }
    assert!(
        unknown_rows.is_empty(),
        "unknown row kinds in extern census: {unknown_rows:?}"
    );
    assert!(schema_seen, "missing schema row");
    let declared_extern = declared_extern.expect("missing extern_count row");
    let declared_constants = declared_constants.expect("missing constant_count row");
    assert_eq!(
        extern_rows.len(),
        declared_extern,
        "extern row count differs from declared extern_count"
    );
    assert_eq!(
        summary_total, declared_constants,
        "totality summary must partition the entire constant surface (Appendix C)"
    );
    assert!(
        declared_extern > 500,
        "extern census implausibly small: {declared_extern}"
    );
    let mut prev = "";
    for row in &extern_rows {
        assert_eq!(row.len(), 7, "extern row arity: {row:?}");
        assert!(prev < row[1], "extern rows must be strictly sorted by name");
        prev = row[1];
        assert!(
            row[4].parse::<u32>().is_ok() && row[5].parse::<u32>().is_ok(),
            "arity/level_params must be numeric: {row:?}"
        );
        assert!(
            !row[6].is_empty(),
            "extern entries must be nonempty: {row:?}"
        );
    }
}
