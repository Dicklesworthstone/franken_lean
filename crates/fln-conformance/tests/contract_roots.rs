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
//! The pin-dependent lane is configured to run weekly and on demand in
//! `.github/workflows/contract-drift.yml`. That workflow installs the exact Reference
//! tag parsed from `SUITE.lock`, exposes the toolchain/vendor identity joins, and runs
//! every extractor check plus the lane's seeded mutants. It deliberately does not run
//! in the per-commit workflow, whose runner has no Reference toolchain.

#![forbid(unsafe_code)]

use fln_conformance::execution::{TriggerReachability, trigger_reachability};
use std::fs;
use std::path::{Path, PathBuf};

const CONTRACT_DRIFT_LANE: &str = "scripts/e2e/contract_drift.sh";
const CONTRACT_DRIFT_WORKFLOW: &str = ".github/workflows/contract-drift.yml";
const CONFIGURED_CADENCE_CLAIM: &str =
    "configured to run weekly and on demand in `.github/workflows/contract-drift.yml`";
const CADENCE_CLAIM_SITES: [&str; 3] = [
    "crates/fln-conformance/tests/contract_roots.rs",
    "crates/fln-rt/tests/abi_contract.rs",
    "crates/fln-olean/tests/olean_contract.rs",
];

fn root() -> PathBuf {
    fln_conformance::checked_workspace_root!()
        .canonicalize()
        .expect("repo root")
}

#[derive(Debug, PartialEq, Eq)]
struct DeclaredCadence {
    workflow_dispatch: bool,
    crons: Vec<String>,
}

/// Read only the trigger block that can schedule a workflow.
///
/// This is an indentation reader, not a YAML parser. It deliberately refuses flow-style
/// `on: {schedule: ...}` rather than scanning the whole file: a file-wide search can count
/// `schedule:` or `cron:` inside a job's shell script and recreate `acm4` as a false clean.
/// [`trigger_reachability`] remains the shared authority for whether a workflow can fire at
/// all; this narrower reader answers which configured triggers back the cadence claim.
fn declared_cadence(workflow: &str) -> Result<DeclaredCadence, String> {
    if trigger_reachability(workflow) != TriggerReachability::Reachable {
        return Err("the workflow has no classifiable, reachable top-level `on` key".to_string());
    }

    let lines: Vec<&str> = workflow.lines().collect();
    let on_start = lines
        .iter()
        .position(|line| !line.starts_with([' ', '\t']) && mapping_key(line) == Some("on"))
        .ok_or_else(|| "the reachable `on` key could not be located".to_string())?;
    let (_, inline_value) = lines[on_start]
        .split_once(':')
        .ok_or_else(|| "the `on` key has no colon".to_string())?;
    let inline_value = inline_value.trim();
    if !inline_value.is_empty() && !inline_value.starts_with('#') {
        return Err(
            "the cadence reader refuses an inline `on` value; use a block mapping".to_string(),
        );
    }

    let on_end = lines
        .iter()
        .enumerate()
        .skip(on_start + 1)
        .find(|(_, line)| {
            !line.trim().is_empty()
                && !line.trim_start().starts_with('#')
                && !line.starts_with([' ', '\t'])
        })
        .map_or(lines.len(), |(index, _)| index);
    let block = &lines[on_start + 1..on_end];
    if block.iter().any(|line| line.starts_with('\t')) {
        return Err("the cadence reader refuses tab-indented trigger keys".to_string());
    }

    let trigger_indent = block
        .iter()
        .filter(|line| !line.trim().is_empty() && !line.trim_start().starts_with('#'))
        .map(|line| line.len() - line.trim_start_matches(' ').len())
        .filter(|indent| *indent > 0)
        .min()
        .ok_or_else(|| "the `on` block declares no triggers".to_string())?;

    let mut current_trigger: Option<&str> = None;
    let mut workflow_dispatch = false;
    let mut crons = Vec::new();
    for line in block {
        let trimmed = line.trim_start_matches(' ');
        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }
        let indent = line.len() - trimmed.len();
        if indent == trigger_indent {
            current_trigger = mapping_key(trimmed);
            if current_trigger == Some("workflow_dispatch") {
                workflow_dispatch = true;
            }
            continue;
        }
        if indent <= trigger_indent || current_trigger != Some("schedule") {
            continue;
        }
        let cron_row = trimmed.strip_prefix("- ").unwrap_or(trimmed);
        if mapping_key(cron_row) != Some("cron") {
            continue;
        }
        let (_, value) = cron_row
            .split_once(':')
            .ok_or_else(|| format!("unparseable cron row: {line:?}"))?;
        let value = value.trim().trim_matches(['"', '\'']);
        if value.is_empty() {
            return Err(format!("empty cron row: {line:?}"));
        }
        crons.push(value.to_string());
    }

    Ok(DeclaredCadence {
        workflow_dispatch,
        crons,
    })
}

/// Return the block-mapping key on one line, accepting YAML's quoted and spaced forms.
fn mapping_key(line: &str) -> Option<&str> {
    let (head, _) = line.split_once(':')?;
    let key = head.trim().trim_matches(['"', '\'']).trim();
    let valid = !key.is_empty()
        && key
            .chars()
            .all(|character| character.is_ascii_alphanumeric() || character == '_');
    valid.then_some(key)
}

/// The GitHub cron names exactly one minute on exactly one day of each week.
fn is_once_weekly_cron(cron: &str) -> bool {
    let fields: Vec<&str> = cron.split_whitespace().collect();
    if fields.len() != 5 || fields[2] != "*" || fields[3] != "*" {
        return false;
    }
    let minute = fields[0].parse::<u8>();
    let hour = fields[1].parse::<u8>();
    let weekday = fields[4].parse::<u8>();
    matches!((minute, hour, weekday), (Ok(0..=59), Ok(0..=23), Ok(0..=7)))
}

fn configured_weekly_and_on_demand(workflow: &str) -> Result<(), String> {
    if !workflow_invokes_lane(workflow, CONTRACT_DRIFT_LANE) {
        return Err(format!(
            "{CONTRACT_DRIFT_WORKFLOW} does not execute {CONTRACT_DRIFT_LANE} from a reachable \
             workflow"
        ));
    }
    let cadence = declared_cadence(workflow)?;
    if !cadence.workflow_dispatch {
        return Err(format!(
            "{CONTRACT_DRIFT_WORKFLOW} has no workflow_dispatch trigger"
        ));
    }
    if cadence.crons.len() != 1 || !is_once_weekly_cron(&cadence.crons[0]) {
        return Err(format!(
            "{CONTRACT_DRIFT_WORKFLOW} must declare exactly one once-weekly cron; found {:?}",
            cadence.crons
        ));
    }
    Ok(())
}

/// Bind the configured producer to every prose claim in both directions.
fn cadence_binding_verdict(configured: bool, claims: &[(&str, bool)]) -> Result<(), String> {
    if !configured {
        return Err(format!(
            "{CONTRACT_DRIFT_WORKFLOW} no longer configures {CONTRACT_DRIFT_LANE} weekly and on \
             demand; the three delegating suites may not keep claiming that cadence"
        ));
    }
    let missing: Vec<&str> = claims
        .iter()
        .filter_map(|(path, present)| (!present).then_some(*path))
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "{CONTRACT_DRIFT_WORKFLOW} still configures the cadence, but these delegating suites \
             stopped disclosing it: {missing:?}"
        ));
    }
    Ok(())
}

/// Collapse only the leading module-documentation block.
///
/// The claim needle also exists below that block as [`CONFIGURED_CADENCE_CLAIM`]. Scanning
/// the whole source would therefore let the guard satisfy itself after every human-facing
/// claim was deleted — the exact false clean this join exists to prevent.
fn module_documentation(source: &str) -> String {
    source
        .lines()
        .take_while(|line| line.starts_with("//!") || line.trim().is_empty())
        .filter_map(|line| line.strip_prefix("//!"))
        .flat_map(str::split_whitespace)
        .collect::<Vec<_>>()
        .join(" ")
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
    let steps = "jobs:\n  c:\n    steps:\n      - run: |\n          ./scripts/e2e/contract_drift.sh --check\n";
    let with_trigger = format!("on:\n  workflow_dispatch:\n{steps}");
    let no_trigger = steps.to_string();

    // The command is in execution position in BOTH, so the older half of the check is blind
    // to the difference. Asserted, not assumed: if this stopped holding, the control below
    // would be varying nothing.
    assert!(
        invoked_by_ci_yml(&with_trigger, CONTRACT_DRIFT_LANE)
            && invoked_by_ci_yml(&no_trigger, CONTRACT_DRIFT_LANE),
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
    assert!(workflow_invokes_lane(&with_trigger, CONTRACT_DRIFT_LANE));
    assert!(
        !workflow_invokes_lane(&no_trigger, CONTRACT_DRIFT_LANE),
        "the lane is executed by this workflow and the workflow can never run, so the lane is \
         not invoked by it — this is the assertion acm4's repair actually rests on"
    );
}

/// The configured cadence and all three claims about it are one closed contract.
///
/// This binds **configuration**, not an observed run. A cron GitHub silently disables remains
/// invisible from inside the repository, so the guarded wording says "configured to run".
/// Both directions are load-bearing: removing the cron while retaining the prose is an
/// overclaim, while retaining the cron and dropping any claim hides where the delegated
/// verification actually runs. Removing both also fails because this lane is required to
/// remain scheduled; a deliberate withdrawal must change this contract explicitly.
#[test]
fn the_contract_drift_cadence_claim_is_bound_to_its_dispatcher() {
    let root = root();
    let workflow = fs::read_to_string(root.join(CONTRACT_DRIFT_WORKFLOW))
        .unwrap_or_else(|error| panic!("{CONTRACT_DRIFT_WORKFLOW}: {error}"));
    configured_weekly_and_on_demand(&workflow)
        .unwrap_or_else(|error| panic!("configured contract-drift cadence: {error}"));

    let claims: Vec<(&str, bool)> = CADENCE_CLAIM_SITES
        .iter()
        .map(|path| {
            let text = fs::read_to_string(root.join(path))
                .unwrap_or_else(|error| panic!("{path}: {error}"));
            (
                *path,
                module_documentation(&text).contains(CONFIGURED_CADENCE_CLAIM),
            )
        })
        .collect();
    cadence_binding_verdict(true, &claims)
        .unwrap_or_else(|error| panic!("contract-drift cadence binding: {error}"));
}

/// Controls for each direction of the cadence join, including the cron-frequency axis.
#[test]
fn the_cadence_reader_and_binding_refuse_each_unbacked_direction() {
    let job = "jobs:\n  c:\n    steps:\n      - run: |\n          ./scripts/e2e/contract_drift.sh --check\n";
    let weekly =
        format!("on:\n  schedule:\n    - cron: \"17 5 * * 1\"\n  workflow_dispatch:\n{job}");
    let on_demand_only = format!("on:\n  workflow_dispatch:\n{job}");
    let daily =
        format!("on:\n  schedule:\n    - cron: \"17 5 * * *\"\n  workflow_dispatch:\n{job}");

    assert!(
        configured_weekly_and_on_demand(&weekly).is_ok(),
        "the positive control must configure the lane weekly and on demand"
    );
    assert!(
        configured_weekly_and_on_demand(&on_demand_only).is_err(),
        "removing only schedule/cron while retaining workflow_dispatch and the lane command \
         must fail the cadence claim"
    );
    assert!(
        configured_weekly_and_on_demand(&daily).is_err(),
        "a daily cron is scheduled but does not back a weekly claim"
    );

    let complete_claims = [("a.rs", true), ("b.rs", true), ("c.rs", true)];
    assert!(cadence_binding_verdict(true, &complete_claims).is_ok());
    let no_producer = cadence_binding_verdict(false, &complete_claims)
        .expect_err("claims without a configured producer must fail");
    assert!(
        no_producer.contains("no longer configures"),
        "wrong no-producer complaint: {no_producer}"
    );
    let missing_claim =
        cadence_binding_verdict(true, &[("a.rs", true), ("b.rs", false), ("c.rs", true)])
            .expect_err("a configured producer with a missing claim must fail");
    assert!(
        missing_claim.contains("b.rs") && missing_claim.contains("stopped disclosing"),
        "wrong missing-claim complaint: {missing_claim}"
    );

    let decoy = format!(
        "//! This module no longer states the cadence.\n\n\
         const DECOY: &str = {CONFIGURED_CADENCE_CLAIM:?};\n"
    );
    assert!(
        !module_documentation(&decoy).contains(CONFIGURED_CADENCE_CLAIM),
        "the code-side claim needle must not satisfy a check over the human-facing module docs"
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

    let lane = fs::read_to_string(root.join(CONTRACT_DRIFT_LANE));
    assert!(
        lane.is_ok(),
        "{CONTRACT_DRIFT_LANE} is missing, and three test suites delegate their digest \
         verification to it. Either restore it or stop claiming the delegation in \
         those headers — a dangling pointer reads as coverage."
    );
    let lane = lane.expect("asserted above");
    assert!(
        lane.contains("--check"),
        "{CONTRACT_DRIFT_LANE} no longer invokes an extractor --check lane, so the delegation it \
         receives is no longer honoured"
    );

    let declared = UNWIRED_LANE_ALLOWANCE
        .iter()
        .find(|(path, _)| *path == CONTRACT_DRIFT_LANE)
        .map(|(_, reason)| *reason);
    let verdict = allowance_verdict(
        CONTRACT_DRIFT_LANE,
        lane_is_invoked(&root, CONTRACT_DRIFT_LANE),
        declared,
    );
    assert!(verdict.is_ok(), "{}", verdict.err().unwrap_or_default());

    // Negative controls, varying the axis this assertion actually depends on:
    // mention versus invocation. The first is the live defect itself — the lane is
    // named in the gate and still not invoked — which is exactly the state the old
    // `contains` check reported as registered.
    let gate = fs::read_to_string(root.join("scripts/check.sh")).expect("scripts/check.sh");
    assert!(
        gate.contains(CONTRACT_DRIFT_LANE) && !invoked_by_check_sh(&gate, CONTRACT_DRIFT_LANE),
        "the mention-versus-invocation control no longer holds: {CONTRACT_DRIFT_LANE} must still be \
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

/// Every vendored source the `.olean` extractor READS must be recorded in the contract it
/// renders (bead `franken_lean-contract-pin-tree-unestablished-monc`).
///
/// This exists because the extractor carried **two** hand-written lists of that population and
/// they disagreed: `build_inventory` named six, `render_exact_format` named nine, and the
/// contract's own sentence — "a sha256 is recorded below for each source read" — was therefore
/// false for `CompactedRegion.lean`, `Elab/Frontend.lean` and `Data/Lsp/Internal.lean`, all
/// three genuinely read.
///
/// **Why `--check` cannot replace this.** `--check` compares the artifact against what the
/// producer renders *today*, so it is green whenever the two agree — including when the producer
/// has silently gone back to naming a subset. This test derives the population from the
/// extractor's own path constants and requires the artifact to match it, so replacing the
/// derivation with a hand list fails here even though every artifact regenerates cleanly. That
/// is precisely the state this repository was in before the repair.
#[test]
fn every_vendored_source_the_olean_extractor_reads_is_recorded_in_its_contract() {
    let root = root();
    let producer = fs::read_to_string(root.join("scripts/extract/gen_olean_contract.py"))
        .expect("olean extractor");
    let contract = fs::read_to_string(root.join("OLEAN_CONTRACT.md")).expect("olean contract");

    // Derived from the producer's own constants. A line that looks like a vendored constant and
    // does not parse is a REFUSAL, never a skip: a scan that quietly drops what it cannot read
    // redefines its own denominator, which is the defect family this guard belongs to.
    let mut declared: Vec<String> = Vec::new();
    for line in producer.lines() {
        let Some((name, rest)) = line.split_once(" = VENDOR / ") else {
            continue;
        };
        if name.is_empty() || !name.chars().all(|c| c.is_ascii_uppercase() || c == '_') {
            continue;
        }
        let mut parts = vec!["vendor/lean4-src".to_string()];
        for segment in rest.trim().split(" / ") {
            let literal = segment
                .trim()
                .strip_prefix('"')
                .and_then(|s| s.strip_suffix('"'))
                .unwrap_or_else(|| {
                    panic!("vendored constant {name} has an unparsable segment {segment:?}")
                });
            parts.push(literal.to_string());
        }
        declared.push(parts.join("/"));
    }
    declared.sort();
    declared.dedup();

    let mut recorded: Vec<String> = Vec::new();
    for line in contract.lines() {
        if let Some(rest) = line.strip_prefix("> - `vendor/lean4-src/") {
            let (path, _) = rest
                .split_once('`')
                .unwrap_or_else(|| panic!("unterminated source row: {line:?}"));
            recorded.push(format!("vendor/lean4-src/{path}"));
        }
    }
    recorded.sort();
    recorded.dedup();

    // Anti-vacuity floors on BOTH sides. Two empty sets compare equal, so without these a broken
    // scan on either side is indistinguishable from a clean tree. Six is the number of sources
    // this contract cannot be rendered without; it is deliberately not the current population,
    // because a floor pinned at today's count is a wall that reddens a correct removal.
    assert!(
        declared.len() >= 6,
        "derived only {} vendored constants from the extractor — refusing a broken scan",
        declared.len()
    );
    assert!(
        recorded.len() >= 6,
        "found only {} source rows in OLEAN_CONTRACT.md — refusing a broken scan",
        recorded.len()
    );

    // Equality in BOTH directions. This is a measured population that must match exactly, not a
    // declared remainder that shrinks with repair, so equality is correct here and one-way
    // membership would let the artifact fall behind the reads again.
    assert_eq!(
        declared, recorded,
        "the sources OLEAN_CONTRACT.md records and the sources the extractor reads disagree; \
         the contract states a sha256 is recorded for every source read, so this makes that \
         sentence false (bead franken_lean-contract-pin-tree-unestablished-monc)"
    );
}

/// Both contracts must disclose that the D5/D9 producer-side tree obligation is now **met at the
/// producer**, and must keep disclosing the one thing that is still not
/// (bead `franken_lean-contract-pin-tree-producer-side-f8zo`).
///
/// This test previously required the word **UNMET**. That was correct while `rev-parse`, `ls-tree`
/// and `hash_object` occurred zero times in either extractor. They still do — the repair does not
/// reimplement tree hashing, it *calls* the predicate that already does it — so the needle had to
/// move with the claim rather than be deleted. Without this, softening the disclosure back toward
/// a single-voice pin line is caught only by the byte-compare and goes green on the next
/// regeneration, which is the unwatched join this bead was split off for.
///
/// The residual disclosure is load-bearing and is asserted separately: the rendered bytes do NOT
/// vary with the per-run outcome. They cannot — `scripts/e2e/contract_handoff.sh` builds its cold
/// root with `git archive`, which yields a tree with no `.git`, and requires `--check` to exit 0
/// there. An artifact that varied would report DRIFT for the ENVIRONMENT, which is the
/// `franken_lean-worktree-gitdir-refusal-hugg` class one layer up. So a run whose establishment
/// came back `inconclusive` renders these same bytes and only its stderr says so, and the contract
/// must keep admitting that.
#[test]
fn both_contracts_disclose_producer_side_tree_establishment_and_its_residual() {
    let root = root();
    for name in ["OLEAN_CONTRACT.md", "ABI_CONTRACT.md"] {
        let raw = fs::read_to_string(root.join(name)).unwrap_or_else(|e| panic!("{name}: {e}"));
        // Strip blockquote prefixes and collapse whitespace before matching. These blocks are
        // hard-wrapped by the renderer, so a needle that spans a wrap point tests the wrapping
        // rather than the claim: `is **UNMET**` once matched the `.olean` contract and missed the
        // ABI one purely because the line broke between the two words.
        let text = raw
            .lines()
            .map(|l| l.trim_start().trim_start_matches('>').trim())
            .collect::<Vec<_>>()
            .join(" ");
        assert!(
            text.contains("established at the producer"),
            "{name} must state the tree is established AT THE PRODUCER — that is the D5/D9 \
             obligation this bead exists to meet"
        );
        assert!(
            text.contains("scripts/evidence.py vendor-binding"),
            "{name} must NAME the predicate it calls. A disclosure that says `established` without \
             naming what establishes it is a claim with no producer, which is item 7's defect \
             family arriving inside the repair for it"
        );
        assert!(
            text.contains("inconclusive"),
            "{name} must disclose the FL-INV-07 inconclusive state; an environment fault is never \
             a verdict about the tree and never a silent pass"
        );
        assert!(
            text.contains("NOT rendered here") || text.contains("NOT rendered"),
            "{name} must disclose that the per-run outcome is NOT rendered into these bytes — the \
             residual, and the reason `--check` does not drift for the environment"
        );
        assert!(
            text.contains("franken_lean-contract-pin-tree-producer-side-f8zo"),
            "{name} must cite the bead, so the disclosure has a producer and cannot outlive the work"
        );
    }
}

/// The establishment block is duplicated in both extractors and must stay BYTE-IDENTICAL
/// (bead `franken_lean-contract-pin-tree-producer-side-f8zo`).
///
/// The duplication is forced, not chosen. Both extractors are invoked `python3 -I -S`, and `-I`
/// drops the script's own directory from `sys.path`, so a sibling import raises
/// `ModuleNotFoundError` — measured, rc=1 under `-I -S` against rc=0 plain. The other candidate
/// home, `scripts/evidence.py`, is the file the predicate is called *into*, not a producer.
///
/// So the choice was never "share or duplicate"; it was "duplicate watched or duplicate unwatched".
/// This is the watch. Without it the two copies drift and one extractor silently stops establishing
/// anything while its contract still says it does — a second copy of a predicate free to diverge,
/// which is the defect this repository names most often.
#[test]
fn the_vendor_tree_establishment_block_is_byte_identical_in_both_extractors() {
    const START: &str = "# --- producer-side vendor tree establishment (bead f8zo)";
    const END: &str = "die(f\"vendor tree binding failed: {detail}\")";

    let root = root();
    let mut blocks = Vec::new();
    for name in [
        "scripts/extract/gen_abi_contract.py",
        "scripts/extract/gen_olean_contract.py",
    ] {
        let text = fs::read_to_string(root.join(name)).unwrap_or_else(|e| panic!("{name}: {e}"));
        let start = text
            .find(START)
            .unwrap_or_else(|| panic!("{name} has no producer-side establishment block"));
        let end = text
            .rfind(END)
            .unwrap_or_else(|| panic!("{name} has no establishment block terminator"))
            + END.len();
        assert!(
            end > start,
            "{name}: establishment block terminator precedes its start — refusing a broken scan"
        );
        let block = text[start..end].to_string();
        // Anti-vacuity: two empty or trivially short slices compare equal, so a scan that located
        // nothing would pass. The block is ~4.5 KB; this floor is far below that and far above a
        // degenerate match.
        assert!(
            block.len() > 1000,
            "{name}: establishment block is only {} bytes — refusing a broken scan rather than \
             reporting two equal fragments as agreement",
            block.len()
        );
        // The block must actually contain the call, not merely the banner comment.
        assert!(
            block.contains("vendor-binding")
                && block.contains("VENDOR_BINDING_ENVIRONMENT_REFUSALS"),
            "{name}: establishment block does not contain the predicate call it exists to make"
        );
        blocks.push((name, block));
    }

    let (first_name, first) = &blocks[0];
    let (second_name, second) = &blocks[1];
    assert_eq!(
        first, second,
        "the producer-side establishment block has DRIFTED between {first_name} and {second_name}. \
         It is duplicated because `python3 -I -S` forbids a sibling import, so the copies are held \
         equal here instead. Re-sync them rather than relaxing this test"
    );

    // Both extractors must actually CALL it. A byte-identical block that nobody invokes is a
    // producer that does not produce, and the contracts assert establishment happens every run.
    for name in [
        "scripts/extract/gen_abi_contract.py",
        "scripts/extract/gen_olean_contract.py",
    ] {
        let text = fs::read_to_string(root.join(name)).unwrap_or_else(|e| panic!("{name}: {e}"));
        let calls = text.matches("report_vendor_tree_binding(").count();
        assert!(
            calls >= 2,
            "{name} defines report_vendor_tree_binding but calls it {} time(s); the contract it \
             renders says establishment runs on every run, so the definition and one call site are \
             both required",
            calls.saturating_sub(1)
        );
    }
}
