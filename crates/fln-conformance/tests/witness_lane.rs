//! The leanchecker witness lane (`scripts/tribunal/leanchecker_witness.sh`): what executes
//! it, what the prose says about that, and the retained receipt of a real run (bead
//! `franken_lean-z8j.1.17`).
//!
//! The lane re-checks the C3 fixture modules with the pinned Reference's `leanchecker`. For
//! weeks the code said it "runs in check.sh" while `scripts/check.sh` only hashed and
//! shellchecked it. Those sentences were corrected by hand at `46636ca3`. These cells make
//! the next drift fail instead of waiting for a reader:
//!
//! * [`the_witness_lane_claims_agree_with_what_executes_it`] derives where the lane is
//!   *executed* (`scripts/check.sh` and `.github/workflows/*.yml`, every mention classified
//!   as hashed input, shellcheck argument, path filter, or execution). It also derives what
//!   the tree *claims* about that from every file naming the lane. A claim that check.sh or a
//!   workflow runs the lane needs an execution there, and "no CI step executes it" needs
//!   there to be none.
//! * [`the_witness_lane_receipt_is_a_real_run_on_these_inputs`] holds the retained receipt of
//!   an actual execution to the lane script, the fixtures, and the pin it ran against. When
//!   any of them moves, the receipt expires and the cell names the re-run.
//!
//! What this does not establish: the claim scan reads fixed phrases, so a paraphrase of a
//! false claim passes it. Configured execution in a workflow proves a run *can* happen,
//! never that one did. And the lane re-executes the Reference kernel, so a receipt is
//! `ReferenceKernelOracle` evidence, not an independent opinion.
#![forbid(unsafe_code)]

use fln_hash::domain::{Domain, hash};
use std::path::Path;

const LANE: &str = "scripts/tribunal/leanchecker_witness.sh";
const LANE_TAIL: &str = "tribunal/leanchecker_witness.sh";
const LANE_NAME: &str = "leanchecker_witness";
const SELF: &str = "crates/fln-conformance/tests/witness_lane.rs";
const RECEIPTS: &str = "crates/fln-conformance/evidence/leanchecker_witness";
const C3: &str = "tribunal/fixtures/c3";

// ---- the execution side ---------------------------------------------------------------

/// How one mention of the lane is used.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Mention {
    /// An element of an `INPUT_PATHS` array: hashed for the governed root, not run.
    HashedInput,
    /// An argument of a `shellcheck` command: linted, not run.
    Shellchecked,
    /// A workflow `paths:` filter entry: a trigger, not a run.
    PathFilter,
    /// Run as (part of) a command.
    Executed,
    /// A shape this guard cannot classify. Refused rather than guessed.
    Unclassified,
}

/// Classify every mention of the lane in a shell script. Backslash-continued lines are
/// joined into one command; a mention inside an array literal takes the array's role.
fn classify_shell(text: &str) -> Vec<(usize, Mention)> {
    let mut mentions = Vec::new();
    let mut array: Option<String> = None;
    let mut command = String::new();
    let mut command_start = 0;
    for (index, raw) in text.lines().enumerate() {
        let line = raw.trim();
        if line.starts_with('#') {
            continue;
        }
        if let Some(name) = &array {
            if line.contains(LANE_TAIL) {
                let role = if name.contains("INPUT_PATHS") {
                    Mention::HashedInput
                } else {
                    Mention::Unclassified
                };
                mentions.push((index + 1, role));
            }
            if line == ")" || line.ends_with(')') {
                array = None;
            }
            continue;
        }
        if let Some((name, rest)) = line.split_once("=(")
            && !name.is_empty()
            && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
            && !rest.contains(')')
        {
            if rest.contains(LANE_TAIL) {
                let role = if name.contains("INPUT_PATHS") {
                    Mention::HashedInput
                } else {
                    Mention::Unclassified
                };
                mentions.push((index + 1, role));
            }
            array = Some(name.to_owned());
            continue;
        }
        if command.is_empty() {
            command_start = index + 1;
        }
        command.push_str(line.trim_end_matches('\\'));
        command.push(' ');
        if line.ends_with('\\') {
            continue;
        }
        if command.contains(LANE_TAIL) {
            let words: Vec<&str> = command.split_whitespace().collect();
            let linted = words.first() == Some(&"shellcheck")
                || (words.first() == Some(&"run_stage") && words.get(2) == Some(&"shellcheck"));
            let role = if linted {
                Mention::Shellchecked
            } else {
                Mention::Executed
            };
            for _ in 0..command.matches(LANE_TAIL).count() {
                mentions.push((command_start, role));
            }
        }
        command.clear();
    }
    mentions
}

/// Classify every mention of the lane in a workflow file.
fn classify_workflow(text: &str) -> Vec<(usize, Mention)> {
    text.lines()
        .enumerate()
        .filter(|(_, line)| line.contains(LANE_TAIL) && !line.trim().starts_with('#'))
        .map(|(index, line)| {
            let entry = line.trim().strip_prefix("- ").unwrap_or("");
            // A bare list entry that is nothing but a path is a trigger filter; a `- run:`
            // step or any command line runs the lane.
            let role = if !entry.is_empty() && !entry.contains(' ') && !entry.contains(':') {
                Mention::PathFilter
            } else {
                Mention::Executed
            };
            (index + 1, role)
        })
        .collect()
}

// ---- the claim side -------------------------------------------------------------------

/// What a sentence near a mention of the lane asserts about its execution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Claim {
    RunsInCheckSh,
    RunsInWorkflow,
    NoCiStepRunsIt,
}

const RUNS_IN_CHECK_SH: [&str; 11] = [
    "runs in check.sh",
    "runs in scripts/check.sh",
    "already runs in",
    "wired into check.sh",
    "wired into scripts/check.sh",
    "called from check.sh",
    "called from scripts/check.sh",
    "executed by check.sh",
    "executed by scripts/check.sh",
    "check.sh runs it",
    "check.sh executes it",
];
const RUNS_IN_WORKFLOW: [&str; 4] = [
    "executed weekly by",
    "runs weekly in",
    "executed by the weekly",
    "run by the weekly",
];
const NO_CI_STEP: [&str; 5] = [
    "executed by no ci step",
    "no ci step executes it",
    "executed by nothing",
    "only shellchecks and hashes it",
    "invoked nowhere",
];

/// Flatten prose across line breaks, comment markers, string continuations and quoting, so
/// a sentence wrapped over several source lines reads as one.
fn flatten(text: &str) -> String {
    let mut flat = String::with_capacity(text.len());
    for line in text.lines() {
        let line = line.trim_start();
        let line = line
            .strip_prefix("//!")
            .or_else(|| line.strip_prefix("///"))
            .or_else(|| line.strip_prefix("//"))
            .or_else(|| line.strip_prefix('#'))
            .unwrap_or(line);
        flat.push_str(line.trim_end().trim_end_matches('\\'));
        flat.push(' ');
    }
    let cleaned: String = flat
        .to_lowercase()
        .chars()
        .map(|c| {
            if matches!(c, '`' | '"' | '\'') {
                ' '
            } else {
                c
            }
        })
        .collect();
    cleaned.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The execution claims within `WINDOW` characters of a mention of the lane.
fn claims(text: &str) -> Vec<(Claim, String)> {
    const WINDOW: usize = 400;
    let flat = flatten(text);
    let mut found = Vec::new();
    for (at, _) in flat.match_indices(LANE_NAME) {
        let start = flat.floor_char_boundary(at.saturating_sub(WINDOW));
        let end = flat.ceil_char_boundary((at + LANE_NAME.len() + WINDOW).min(flat.len()));
        let window = &flat[start..end];
        for (claim, phrases) in [
            (Claim::RunsInCheckSh, RUNS_IN_CHECK_SH.as_slice()),
            (Claim::RunsInWorkflow, RUNS_IN_WORKFLOW.as_slice()),
            (Claim::NoCiStepRunsIt, NO_CI_STEP.as_slice()),
        ] {
            for phrase in phrases {
                if window.contains(phrase) {
                    found.push((claim, (*phrase).to_owned()));
                }
            }
        }
    }
    found.sort_by(|a, b| a.1.cmp(&b.1));
    found.dedup();
    found
}

/// Every disagreement between what the tree claims and what executes the lane.
fn disagreements(
    claims: &[(String, Claim, String)],
    check_sh: &[(usize, Mention)],
    workflows: &[(String, usize, Mention)],
) -> Vec<String> {
    let check_sh_runs = check_sh.iter().any(|(_, m)| *m == Mention::Executed);
    let workflow_runs = workflows.iter().any(|(_, _, m)| *m == Mention::Executed);
    let mut problems = Vec::new();
    for (file, claim, phrase) in claims {
        let holds = match claim {
            Claim::RunsInCheckSh => check_sh_runs,
            Claim::RunsInWorkflow => workflow_runs,
            Claim::NoCiStepRunsIt => !check_sh_runs && !workflow_runs,
        };
        if !holds {
            problems.push(format!(
                "{file} says \"{phrase}\" about {LANE}, but check.sh executes it: {check_sh_runs}, \
                 a workflow executes it: {workflow_runs}"
            ));
        }
    }
    for (line, mention) in check_sh {
        if *mention == Mention::Unclassified {
            problems.push(format!(
                "scripts/check.sh:{line} mentions the lane in a shape this guard cannot classify"
            ));
        }
    }
    problems
}

fn walk(root: &Path, dir: &Path, out: &mut Vec<String>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let name = entry.file_name().to_string_lossy().into_owned();
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        if kind.is_dir() {
            if name.starts_with('.')
                || matches!(name.as_str(), "target" | "vendor" | "node_modules")
            {
                continue;
            }
            walk(root, &path, out);
        } else if kind.is_file()
            && let Ok(relative) = path.strip_prefix(root)
        {
            out.push(relative.to_string_lossy().into_owned());
        }
    }
}

#[test]
fn the_witness_lane_claims_agree_with_what_executes_it() {
    let root = fln_conformance::checked_workspace_root!();
    let check_sh_text = std::fs::read_to_string(root.join("scripts/check.sh"))
        .expect("scripts/check.sh is readable");
    let check_sh = classify_shell(&check_sh_text);
    // Anti-vacuity: check.sh does name the lane today (hashed and linted). A parse that
    // finds no mention at all is a broken scan, not proof that nothing runs it.
    assert!(
        !check_sh.is_empty(),
        "no mention of {LANE} found in scripts/check.sh: a broken scan"
    );

    let mut workflows = Vec::new();
    let workflow_dir = root.join(".github/workflows");
    let entries = std::fs::read_dir(&workflow_dir).expect(".github/workflows is readable");
    let mut workflow_files = 0;
    for entry in entries.flatten() {
        let path = entry.path();
        if path
            .extension()
            .is_some_and(|ext| ext == "yml" || ext == "yaml")
        {
            workflow_files += 1;
            let text = std::fs::read_to_string(&path).unwrap_or_default();
            let name = entry.file_name().to_string_lossy().into_owned();
            for (line, mention) in classify_workflow(&text) {
                workflows.push((name.clone(), line, mention));
            }
        }
    }
    assert!(workflow_files > 0, "no workflow files found: a broken scan");

    // The claim side: every file outside the execution side and the tracker that names the
    // lane. `.beads/` holds records quoting the history of these claims, not claims.
    let mut files = Vec::new();
    walk(&root, &root, &mut files);
    let mut claim_sites = Vec::new();
    let mut scanned = 0;
    let mut self_seen = 0;
    for file in &files {
        if file == SELF {
            self_seen += 1;
            continue;
        }
        if file == "scripts/check.sh" || file == LANE {
            continue;
        }
        let Ok(text) = std::fs::read_to_string(root.join(file)) else {
            continue;
        };
        if !text.contains(LANE_NAME) {
            continue;
        }
        scanned += 1;
        for (claim, phrase) in claims(&text) {
            claim_sites.push((file.clone(), claim, phrase));
        }
    }
    assert_eq!(
        self_seen, 1,
        "the guard must find and exclude exactly itself"
    );
    assert!(scanned > 0, "no file names {LANE_NAME}: a broken scan");
    assert!(
        !claim_sites.is_empty(),
        "no file states whether {LANE} executes; the kernel council and the claim matrix both \
         do, so an empty claim scan is a broken scan"
    );
    let problems = disagreements(&claim_sites, &check_sh, &workflows);
    println!(
        "witness lane: check.sh mentions {:?}; workflow mentions {:?}; {} claim site(s) in {} file(s)",
        check_sh,
        workflows,
        claim_sites.len(),
        scanned
    );
    assert!(
        problems.is_empty(),
        "the witness lane's claims disagree with its execution:\n{}",
        problems.join("\n")
    );
}

#[test]
fn a_check_sh_mention_is_classified_by_its_context() {
    let script = "INPUT_PATHS=(\n  a.sh\n  scripts/tribunal/leanchecker_witness.sh\n)\n\
                  run_stage shellcheck shellcheck -e SC1 a.sh \\\n  scripts/tribunal/leanchecker_witness.sh \\\n  b.sh\n\
                  # bash scripts/tribunal/leanchecker_witness.sh\n\
                  run_stage witness bash \"$REPO/scripts/tribunal/leanchecker_witness.sh\"\n\
                  OTHER=(\n  scripts/tribunal/leanchecker_witness.sh\n)\n";
    let roles: Vec<Mention> = classify_shell(script).into_iter().map(|(_, m)| m).collect();
    assert_eq!(
        roles,
        [
            Mention::HashedInput,
            Mention::Shellchecked,
            Mention::Executed,
            Mention::Unclassified
        ]
    );
    let workflow = "on:\n  push:\n    paths:\n      - scripts/tribunal/leanchecker_witness.sh\n\
                    jobs:\n  x:\n    steps:\n      - run: bash scripts/tribunal/leanchecker_witness.sh\n";
    let roles: Vec<Mention> = classify_workflow(workflow)
        .into_iter()
        .map(|(_, m)| m)
        .collect();
    assert_eq!(roles, [Mention::PathFilter, Mention::Executed]);
}

#[test]
fn a_claim_is_held_to_the_execution_it_names_in_both_directions() {
    let runs = "The lane `scripts/tribunal/leanchecker_witness.sh` already runs in \
                `scripts/check.sh`.";
    let idle = "// The lane scripts/tribunal/leanchecker_witness.sh is shellchecked\n\
                // but executed by no CI step today.";
    let hashed = [(1, Mention::HashedInput), (2, Mention::Shellchecked)];
    let executed = [(3, Mention::Executed)];
    let claim = |text: &str| -> Vec<(String, Claim, String)> {
        claims(text)
            .into_iter()
            .map(|(c, p)| ("f".to_owned(), c, p))
            .collect()
    };
    // "runs in check.sh" with check.sh only hashing it: refused.
    assert!(!disagreements(&claim(runs), &hashed, &[]).is_empty());
    assert!(disagreements(&claim(runs), &executed, &[]).is_empty());
    // "executed by no CI step" once check.sh or a workflow runs it: refused.
    assert!(disagreements(&claim(idle), &hashed, &[]).is_empty());
    assert!(!disagreements(&claim(idle), &executed, &[]).is_empty());
    let weekly = [("w.yml".to_owned(), 9, Mention::Executed)];
    assert!(!disagreements(&claim(idle), &hashed, &weekly).is_empty());
    let weekly_claim = "leanchecker_witness.sh is executed weekly by contract-drift.yml";
    assert!(disagreements(&claim(weekly_claim), &hashed, &weekly).is_empty());
    assert!(!disagreements(&claim(weekly_claim), &hashed, &[]).is_empty());
}

// ---- the receipt ----------------------------------------------------------------------

/// The value of a flat string field `"key":"value"` in one JSON line.
fn field<'a>(line: &'a str, key: &str) -> Option<&'a str> {
    let needle = format!("\"{key}\":\"");
    let start = line.find(&needle)? + needle.len();
    let end = line[start..].find('"')?;
    Some(&line[start..start + end])
}

fn digest(bytes: &[u8]) -> String {
    hash(Domain::Fixture, bytes).to_hex()
}

/// The receipt header binding a run to the bytes it ran on.
fn header(root: &Path, pin_tag: &str, pin_commit: &str, fixtures: &[String]) -> String {
    let lane = std::fs::read(root.join(LANE)).expect("the lane script is readable");
    let mut text = format!(
        "{{\"schema\":\"fln.witness-lane-receipt/1\",\"bead\":\"franken_lean-z8j.1.17\",\
         \"lane\":\"{LANE}\",\"lane_digest\":\"{}\",\"pin_tag\":\"{pin_tag}\",\
         \"pin_commit\":\"{pin_commit}\",\"authority\":\"ReferenceKernelOracle\",\
         \"scope\":\"the lane's own scope: the C3 fixture modules it names, re-checked by the \
pinned leanchecker, plus its nonexistent-module control\"",
        digest(&lane)
    );
    for fixture in fixtures {
        let bytes = std::fs::read(root.join(C3).join(fixture)).expect("a C3 fixture is readable");
        text.push_str(&format!(
            ",\"fixture_digest:{fixture}\":\"{}\"",
            digest(&bytes)
        ));
    }
    text.push('}');
    text
}

#[test]
fn the_witness_lane_receipt_is_a_real_run_on_these_inputs() {
    let root = fln_conformance::checked_workspace_root!();
    let pin_tag = fln_conformance::pin::pinned_tag().expect("SUITE.lock pins a Reference tag");
    let pin_commit = fln_conformance::pin::pinned_commit().expect("SUITE.lock pins a commit");
    let path = root.join(RECEIPTS).join(format!("{pin_tag}.ndjson"));
    let rerun = format!(
        "re-run the lane where the pin is installed and retain it:\n  \
         bash {LANE}\n  FLN_WITNESS_LANE_RECEIPT_FROM=target/e2e/<that run dir> \
         cargo test -p fln-conformance --test witness_lane the_witness_lane_receipt"
    );

    if let Some(run_dir) = std::env::var_os("FLN_WITNESS_LANE_RECEIPT_FROM") {
        let run = std::fs::read_to_string(Path::new(&run_dir).join("run.ndjson"))
            .expect("the run directory holds run.ndjson");
        let fixtures: Vec<String> = run
            .lines()
            .filter(|line| field(line, "step") == Some("witness"))
            .filter_map(|line| field(line, "fixture").map(str::to_owned))
            .collect();
        let mut text = header(&root, &pin_tag, &pin_commit, &fixtures);
        text.push('\n');
        text.push_str(&run);
        std::fs::create_dir_all(path.parent().expect("receipt directory")).expect("mkdir");
        std::fs::write(&path, text).expect("write the receipt");
    }

    let receipt = std::fs::read_to_string(&path).unwrap_or_else(|_| {
        panic!(
            "no witness-lane receipt for {pin_tag} at {}; {rerun}",
            path.display()
        )
    });
    let mut lines = receipt.lines();
    let first = lines.next().unwrap_or_default();
    let run: Vec<&str> = lines.collect();
    let step = |name: &str| -> Vec<&str> {
        run.iter()
            .copied()
            .filter(|line| field(line, "step") == Some(name))
            .collect()
    };

    // The run itself: started, Reference provenance at the pinned commit, every named
    // fixture accepted, the control rejected, and a passing end.
    assert_eq!(step("run_start").len(), 1, "one run per receipt");
    let provenance = step("provenance");
    assert!(
        provenance.len() == 1
            && field(provenance[0], "status") == Some("passed")
            && field(provenance[0], "oracle").is_some_and(|oracle| oracle.contains(&pin_commit)),
        "the run's oracle is not the pinned Reference at {pin_commit}: {provenance:?}"
    );
    let witnesses = step("witness");
    assert!(!witnesses.is_empty(), "the run witnessed no module");
    for line in &witnesses {
        assert!(
            field(line, "status") == Some("passed") && field(line, "verdict") == Some("accepted"),
            "a witnessed module was not accepted: {line}"
        );
    }
    let control = step("discriminate");
    assert!(
        control.len() == 1
            && field(control[0], "status") == Some("passed")
            && field(control[0], "verdict") == Some("rejected"),
        "the nonexistent-module control did not discriminate: {control:?}"
    );
    let end = step("run_end");
    assert!(
        end.len() == 1 && field(end[0], "status") == Some("passed"),
        "the run did not pass: {end:?}"
    );

    // The binding: the receipt describes these bytes. A moved lane script, fixture or pin
    // expires it rather than letting an old run vouch for new inputs.
    let fixtures: Vec<String> = witnesses
        .iter()
        .filter_map(|line| field(line, "fixture").map(str::to_owned))
        .collect();
    assert_eq!(
        fixtures.len(),
        witnesses.len(),
        "a witness row names no fixture"
    );
    let expected = header(&root, &pin_tag, &pin_commit, &fixtures);
    assert_eq!(
        first, expected,
        "the witness-lane receipt no longer describes this tree (lane script, C3 fixtures or \
         pin moved); {rerun}"
    );
}
