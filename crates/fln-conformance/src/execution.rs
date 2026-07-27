//! **Did the evidence a terminal coverage row cites actually run?** — the CI-execution
//! join (bead `fln-rgha`, AGENTS.md "Evidence & Census Pins" item 7).
//!
//! Nine terminal `complete` rows in `ci/VERIFICATION_MANIFEST.jsonl` were found by hand to
//! cite conformance suites that CI executes **without the pinned Reference toolchain
//! installed**, so the pin-dependent half of each suite takes a typed skip and the run
//! reports `ok`. The skip notice is correct — `pin::skip_notice` says outright that
//! nothing was established — and it goes to stderr, which cargo captures and discards for
//! a *passing* test. There is no misleading text to notice and no failure to investigate:
//! a green run looks identical whether the rig ran or not.
//!
//! This module is the derivation half of the guard that fails on recurrence. It is
//! deliberately **pure**: every function takes text and returns a judgement, so the guard
//! in `tests/ci_execution_join.rs` can plant mutants against the logic directly instead of
//! mutating the repository to find out whether the logic works.
//!
//! **Why the scope is derived rather than written down.** `franken_lean-worktree-gitdir-refusal-hugg`
//! is criticised in item 7's own table for hand-listing its affected surfaces, so a new
//! lane that starts refusing goes unnamed and nothing notices. The scope here is resolved
//! from the root manifest's own `members` globs and the workspace's directory layout, so a
//! surface added tomorrow is in scope the day it lands. What *is* declared is an
//! exclusion allowance (files whose text carries a coordinate for a reason other than
//! reaching the pin) and the population of already-affected rows — both bounded, both
//! checked in **both** directions, so each can only shrink.
//!
//! **What this module does not attempt.** It measures *reach* — whether a surface's code
//! can consult the pinned Reference — not *decline*. A surface that hard-failed without
//! the pin would also be reported, and that is deliberate: it is still a surface whose CI
//! behaviour differs from the host its row was verified on. Distinguishing skip from
//! failure requires observing a run, which is the bead's eventual mechanism (a structured
//! execution record the gate collects) and is not this.

use std::collections::BTreeSet;

// ---------------------------------------------------------------------------
// Reaching the pinned Reference
// ---------------------------------------------------------------------------

/// Every coordinate by which code in this workspace can reach the pinned Reference.
///
/// These are **facts about the world**, not prose: the elan layout the toolchain installs
/// into, the two environment overrides that relocate it, and the sanctioned locator in
/// [`crate::pin`]. A rig cannot consult the Reference without naming one of them, because
/// there is no other way to find it — which is the property that makes this a derivation
/// rather than a needle that vanishes when someone rewords a skip message.
///
/// `pinned_lean` earns its place separately from the path: `ext_observable_capture.rs` and
/// `pin_ctor_inventory.rs` call [`crate::pin::pinned_lean`] and never spell the elan path
/// themselves. It is also a **compiled symbol** — renaming it stops the workspace
/// building, so unlike a message fragment it cannot go stale in silence.
///
/// Measured at `7b1af002`, the two derivations anyone would reach for first are wrong in
/// opposite directions and this one is not: scoping by `pin::` references misses
/// `kernel_replay.rs` entirely (five skip sites, zero `pin::` references — it writes its
/// own locator) while falsely including `mandated_mutants.rs` and
/// `digest_preimage_encoding.rs`, which import `pin::workspace_root` and never touch the
/// Reference; scoping by the skip *text* catches `kernel_replay.rs` today and empties
/// itself the moment somebody rewords the notice.
pub const PIN_COORDINATES: &[&str] = &[
    ".elan/toolchains",
    "FLN_REFERENCE_BIN",
    "FLN_REFERENCE_LIB",
    "pinned_lean",
];

/// Drop whole-line comments, so a file that merely *records* where its fixtures came from
/// is not mistaken for one that goes and reads them.
///
/// Three files in this tree name the elan path in a `//!` provenance header and never
/// touch it at runtime (`crates/fln-parse/tests/pratt_precedence_model.rs`,
/// `registration_state_model.rs`, and `crates/fln-kernel/tests/REFERENCE_DIFFERENTIAL.md`'s
/// Rust sibling). Including them would redden rows whose evidence is a frozen fixture.
///
/// Only lines whose *first* non-space token opens a comment are dropped. A trailing `//`
/// is left in place: stripping it needs a lexer that knows string literals from comments,
/// and a coordinate in a trailing comment over-reports, which is the loud direction.
pub fn code_only(source: &str) -> String {
    source
        .lines()
        .filter(|line| !line.trim_start().starts_with("//"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Can this source text reach the pinned Reference?
pub fn reaches_the_pinned_reference(source: &str) -> bool {
    let code = code_only(source);
    PIN_COORDINATES.iter().any(|needle| code.contains(needle))
}

// ---------------------------------------------------------------------------
// The workspace's own member globs
// ---------------------------------------------------------------------------

/// The `members` patterns of a root `Cargo.toml`, verbatim (`crates/*`, `tools/*`, …).
///
/// Taken from the manifest rather than assumed, because `cargo test` at the workspace root
/// compiles **every** member and `tools/structure-guard` is one. A guard that equated the
/// workspace with `crates/` would report six terminal rows citing `tools/structure-guard`
/// tests as evidence CI never runs, which is false — measured, and the reason this
/// function exists.
///
/// Returns `None` when the array cannot be located: a manifest this cannot read is a
/// refusal, never an empty member set that would silently pass everything.
pub fn workspace_member_patterns(manifest: &str) -> Option<Vec<String>> {
    let body = manifest
        .split_once("members")?
        .1
        .split_once('[')?
        .1
        .split_once(']')?
        .0;
    let patterns: Vec<String> = body
        .split(',')
        .map(|raw| raw.trim().trim_matches('"').trim().to_string())
        .filter(|pattern| !pattern.is_empty())
        .collect();
    (!patterns.is_empty()).then_some(patterns)
}

// ---------------------------------------------------------------------------
// What CI runs
// ---------------------------------------------------------------------------

/// One job of one workflow, as the text of its steps.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CiJob {
    pub workflow: String,
    pub id: String,
    pub body: String,
}

/// Split a workflow into jobs by indentation.
///
/// **Job granularity is not decoration.** `contract-drift.yml` installs the pin and runs no
/// tests; `ci.yml` runs the whole suite and installs nothing. Judged per *file* the two
/// would be indistinguishable from one workflow that did both, and the guard would report
/// the pin as present in CI when the job that runs the tests has never seen it — a false
/// clean in the direction that empties the population.
///
/// This is an indentation reader, not a YAML parser (D1 forbids pulling one in). It
/// recognises the block mapping GitHub's own documentation uses and every workflow in this
/// tree is written in: `jobs:` at column zero, job ids at two spaces. A flow-style
/// `jobs: {…}` or a merge key would defeat it — which is why the guard refuses on an empty
/// job list rather than treating "no jobs found" as "no jobs".
pub fn ci_jobs(workflow: &str, text: &str) -> Vec<CiJob> {
    let mut jobs: Vec<CiJob> = Vec::new();
    let mut inside = false;
    for line in text.lines() {
        if line.trim_end() == "jobs:" {
            inside = true;
            continue;
        }
        if !inside {
            continue;
        }
        // A new top-level key ends the jobs block.
        if !line.is_empty() && !line.starts_with(' ') && !line.starts_with('#') {
            inside = false;
            continue;
        }
        if let Some(id) = job_id(line) {
            jobs.push(CiJob {
                workflow: workflow.to_string(),
                id,
                body: String::new(),
            });
            continue;
        }
        if let Some(job) = jobs.last_mut() {
            job.body.push_str(line);
            job.body.push('\n');
        }
    }
    jobs
}

/// `  some-job:` and nothing else — two spaces, a key, a colon, end of line.
///
/// Trailing whitespace is trimmed first. A job key written `"  gate:  "` would otherwise
/// fail the suffix test and be dropped silently, and a job the reader cannot see is a job
/// whose pin installation it cannot count — a false clean in the dangerous direction.
fn job_id(line: &str) -> Option<String> {
    let rest = line.trim_end().strip_prefix("  ")?;
    if rest.starts_with(' ') {
        return None;
    }
    let name = rest.strip_suffix(':').map(str::trim_end)?;
    let ok = !name.is_empty()
        && name
            .chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '-');
    ok.then(|| name.to_string())
}

/// Fold backslash continuations into one logical command and drop comment lines, so a
/// flag several continuation lines below its verb is still read as part of it.
pub fn logical_lines(body: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut pending = String::new();
    for line in body.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('#') {
            continue;
        }
        if let Some(head) = trimmed.strip_suffix('\\') {
            pending.push_str(head);
            pending.push(' ');
            continue;
        }
        pending.push_str(trimmed);
        out.push(std::mem::take(&mut pending));
    }
    if !pending.is_empty() {
        out.push(pending);
    }
    out
}

/// How a CI job installs the Reference, if it does at all.
///
/// Comment lines are dropped first, and that is load-bearing: `ci.yml` carries the phrase
/// "needs an elan" in a comment explaining why a step uses `--validate` instead of
/// `--check`. A naive grep reads that comment as an installation and concludes the gate
/// job has the pin. The same shape defeated a `toolchain install` grep, which matched
/// `rustup toolchain install` — a different toolchain entirely.
pub fn installs_reference_pin(job: &CiJob) -> bool {
    const INSTALLS: &[&str] = &["elan toolchain install", "lean-action", ".elan/toolchains"];
    logical_lines(&job.body)
        .iter()
        .any(|line| INSTALLS.iter().any(|needle| line.contains(needle)))
}

/// What a single `cargo test` invocation compiles and runs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TestReach {
    /// An unrestricted run over the root workspace: every member's targets.
    Workspace,
    /// `-p <pkg>` without `--test`: that package's targets.
    Packages(BTreeSet<String>),
    /// `--test <stem>`: that integration target only.
    Targets(BTreeSet<String>),
    /// `--manifest-path <dir>/Cargo.toml`: a different workspace entirely.
    Manifest(String),
}

/// Does `scripts/check.sh` run an unrestricted workspace `cargo test`?
///
/// This is the link nothing else supplies. `ci.yml` never invokes `cargo test` for the
/// workspace — its gate step runs `scripts/check.sh`, whose `test` stage does. A guard
/// enumerating CI's tests from the workflow files alone concludes `fln-conformance` is not
/// in CI at all, which is a false clean in the opposite direction and would put every
/// conformance row in the population.
///
/// Both spellings of the stage count, including the branch that appends
/// `-- --skip <name>`: `--skip` filters test *names* and leaves the target set whole.
pub fn check_sh_reaches_workspace(check_sh: &str) -> bool {
    logical_lines(check_sh).iter().any(|line| {
        let line = line.trim();
        line.starts_with("run_stage test cargo test")
            && !line.contains(" -p ")
            && !line.contains("--test ")
            && !line.contains("--manifest-path")
    })
}

/// Every test invocation a job performs, directly or through `scripts/check.sh`.
pub fn test_reach(job: &CiJob, check_sh_reaches_workspace: bool) -> Vec<TestReach> {
    let mut reach = Vec::new();
    for line in logical_lines(&job.body) {
        if check_sh_reaches_workspace && invokes_check_sh(&line) {
            reach.push(TestReach::Workspace);
        }
        if !invokes_cargo_test(&line) {
            continue;
        }
        if let Some(dir) = flag_value(&line, "--manifest-path")
            .and_then(|path| path.strip_suffix("/Cargo.toml").map(str::to_string))
        {
            reach.push(TestReach::Manifest(dir));
            continue;
        }
        let targets = flag_values(&line, "--test");
        if !targets.is_empty() {
            reach.push(TestReach::Targets(targets));
            continue;
        }
        let packages = flag_values(&line, "-p");
        if !packages.is_empty() {
            reach.push(TestReach::Packages(packages));
            continue;
        }
        reach.push(TestReach::Workspace);
    }
    reach
}

fn invokes_check_sh(line: &str) -> bool {
    line.split_whitespace()
        .any(|token| token.ends_with("check.sh") || token.ends_with("check.sh\""))
}

fn invokes_cargo_test(line: &str) -> bool {
    let tokens: Vec<&str> = line.split_whitespace().collect();
    tokens
        .windows(2)
        .any(|pair| pair[0] == "cargo" && pair[1] == "test")
}

fn flag_value<'a>(line: &'a str, flag: &str) -> Option<&'a str> {
    let tokens: Vec<&str> = line.split_whitespace().collect();
    tokens
        .windows(2)
        .find(|pair| pair[0] == flag)
        .map(|pair| pair[1].trim_matches('"'))
}

fn flag_values(line: &str, flag: &str) -> BTreeSet<String> {
    let tokens: Vec<&str> = line.split_whitespace().collect();
    tokens
        .windows(2)
        .filter(|pair| pair[0] == flag)
        .map(|pair| pair[1].trim_matches('"').to_string())
        .collect()
}

/// Does any invocation in `reach` compile and run `surface`?
///
/// `members` are the resolved member directories, workspace-relative (`crates/fln-kernel`,
/// `tools/structure-guard`, …).
pub fn reach_covers(reach: &[TestReach], surface: &str, members: &[String]) -> bool {
    let member = members
        .iter()
        .find(|member| surface.starts_with(&format!("{member}/")));
    let stem = surface
        .rsplit('/')
        .next()
        .and_then(|name| name.strip_suffix(".rs"));
    reach.iter().any(|one| match one {
        TestReach::Workspace => member.is_some(),
        TestReach::Packages(packages) => member
            .and_then(|member| member.rsplit('/').next())
            .is_some_and(|package| packages.contains(package)),
        // `--test` names an integration target, which is a file under `tests/`. A `src/`
        // file is compiled into the lib target and is never named this way.
        TestReach::Targets(targets) => {
            surface.contains("/tests/") && stem.is_some_and(|stem| targets.contains(stem))
        }
        TestReach::Manifest(dir) => surface.starts_with(&format!("{dir}/")),
    })
}

// ---------------------------------------------------------------------------
// Reading the manifest and the tracker
// ---------------------------------------------------------------------------

/// A top-level field of one JSONL record, decoded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Field {
    Text(String),
    List(Vec<String>),
}

/// One named top-level field of a JSONL record, or `None` when the record does not carry
/// it or cannot be read.
///
/// Deliberately not a JSON library (D1 admits none) and deliberately not a regex over the
/// line either: it walks the record's top level and skips the values it was not asked for
/// with a balanced scan that honours string escapes, so a `}` or a `"` inside a behaviour
/// note cannot end the walk early. Every failure returns `None`, and the guard treats a
/// record it could not read as a refusal rather than as a record with no artifacts —
/// which is the difference between a broken reader and a clean tree.
pub fn record_field(line: &str, key: &str) -> Option<Field> {
    let bytes = line.as_bytes();
    let mut at = skip_ws(bytes, 0);
    if bytes.get(at) != Some(&b'{') {
        return None;
    }
    at = skip_ws(bytes, at + 1);
    loop {
        if bytes.get(at) == Some(&b'}') {
            return None;
        }
        let (name, next) = read_string(bytes, at)?;
        at = skip_ws(bytes, next);
        if bytes.get(at) != Some(&b':') {
            return None;
        }
        at = skip_ws(bytes, at + 1);
        if name == key {
            return read_field(bytes, at);
        }
        at = skip_ws(bytes, skip_value(bytes, at)?);
        match bytes.get(at) {
            Some(&b',') => at = skip_ws(bytes, at + 1),
            _ => return None,
        }
    }
}

fn read_field(bytes: &[u8], at: usize) -> Option<Field> {
    match bytes.get(at) {
        Some(&b'"') => read_string(bytes, at).map(|(text, _)| Field::Text(text)),
        Some(&b'[') => {
            let mut items = Vec::new();
            let mut at = skip_ws(bytes, at + 1);
            if bytes.get(at) == Some(&b']') {
                return Some(Field::List(items));
            }
            loop {
                let (item, next) = read_string(bytes, at)?;
                items.push(item);
                at = skip_ws(bytes, next);
                match bytes.get(at) {
                    Some(&b',') => at = skip_ws(bytes, at + 1),
                    Some(&b']') => return Some(Field::List(items)),
                    _ => return None,
                }
            }
        }
        _ => None,
    }
}

fn skip_ws(bytes: &[u8], mut at: usize) -> usize {
    while matches!(bytes.get(at), Some(b' ' | b'\t' | b'\n' | b'\r')) {
        at += 1;
    }
    at
}

/// Walk past a JSON string without decoding it — only the closing quote matters.
///
/// Kept separate from [`read_string`] deliberately, and the separation is load-bearing.
/// Folding the two is invisible until it isn't: a skip that cannot decode, then advances a
/// single byte to recover, walks *into* the string, where the next `,` or `}` inside a
/// behaviour note ends the record early and every later field reads as absent. Measured —
/// that is exactly how the first version of this reader dropped tracker records whose prose
/// contains `§` or `—`, which is 292 of them, and reported the coverage rows naming those
/// beads as orphans.
fn skip_string(bytes: &[u8], at: usize) -> Option<usize> {
    if bytes.get(at) != Some(&b'"') {
        return None;
    }
    let mut at = at + 1;
    loop {
        match *bytes.get(at)? {
            b'"' => return Some(at + 1),
            // The escaped byte cannot end the string, whatever it is.
            b'\\' => at += 2,
            _ => at += 1,
        }
    }
}

/// Read a JSON string starting at `at`, returning its body and the index past its closing
/// quote.
///
/// Bytes are accumulated and validated as UTF-8 once, at the end, so a value containing
/// `§` or `—` decodes rather than refusing. A `\u` escape still refuses: no field this
/// guard reads is ever written that way, and decoding surrogate pairs to reach the same
/// answer is machinery with no caller. The refusal is loud and lands on this reader.
fn read_string(bytes: &[u8], at: usize) -> Option<(String, usize)> {
    if bytes.get(at) != Some(&b'"') {
        return None;
    }
    let mut out: Vec<u8> = Vec::new();
    let mut at = at + 1;
    loop {
        match *bytes.get(at)? {
            b'"' => return String::from_utf8(out).ok().map(|text| (text, at + 1)),
            b'\\' => {
                out.push(match *bytes.get(at + 1)? {
                    b'"' => b'"',
                    b'\\' => b'\\',
                    b'/' => b'/',
                    b'n' => b'\n',
                    b't' => b'\t',
                    b'r' => b'\r',
                    b'b' => 0x08,
                    b'f' => 0x0c,
                    _ => return None,
                });
                at += 2;
            }
            byte => {
                out.push(byte);
                at += 1;
            }
        }
    }
}

/// Advance past one JSON value of any shape, honouring nesting and string escapes.
fn skip_value(bytes: &[u8], at: usize) -> Option<usize> {
    let mut at = at;
    let mut depth = 0usize;
    loop {
        match *bytes.get(at)? {
            b'"' => at = skip_string(bytes, at)?,
            b'[' | b'{' => {
                depth += 1;
                at += 1;
            }
            b']' | b'}' => {
                if depth == 0 {
                    return Some(at);
                }
                depth -= 1;
                at += 1;
                if depth == 0 {
                    return Some(at);
                }
            }
            b',' if depth == 0 => return Some(at),
            _ => at += 1,
        }
    }
}

/// The verification state `scripts/evidence.py` derives for a coverage row.
///
/// Mirrors `derived_verification_coverage_state`: coverage rows never declare their own
/// state, it is read off the tracker. `complete` — the terminal state, and the only one
/// whose evidence arrays must be non-empty — is what this guard judges.
pub fn is_terminal(bead_status: &str, skip: &str) -> bool {
    matches!(bead_status, "closed" | "tombstone") && skip == "none"
}

/// The e2e scenarios `scripts/evidence.py` will validate a step order for.
///
/// This binding *is* declared — `validate_e2e` refuses a scenario absent from
/// `E2E_STEP_ORDERS` — which is why the guard checks citations against it. The binding
/// from a key to the shell script that dispatches it is **not** declared anywhere; see
/// the guard's own notes for what that costs.
pub fn e2e_scenario_keys(evidence_py: &str) -> BTreeSet<String> {
    let Some(block) = evidence_py.split_once("E2E_STEP_ORDERS = {") else {
        return BTreeSet::new();
    };
    let Some((body, _)) = block.1.split_once("\n}\n") else {
        return BTreeSet::new();
    };
    body.lines()
        .filter_map(|line| {
            let key = line.strip_prefix("    \"")?;
            let (key, rest) = key.split_once('"')?;
            rest.trim_start().starts_with(':').then(|| key.to_string())
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_provenance_comment_is_not_a_reach_and_a_call_is() {
        assert!(!reaches_the_pinned_reference(
            "//! Taken by running ~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean\nfn f() {}\n"
        ));
        assert!(reaches_the_pinned_reference(
            "let p = home.join(\".elan/toolchains\");\n"
        ));
        assert!(reaches_the_pinned_reference("pin::pinned_lean()\n"));
        assert!(reaches_the_pinned_reference(
            "std::env::var(\"FLN_REFERENCE_LIB\")\n"
        ));
    }

    #[test]
    fn jobs_are_split_at_two_space_keys_and_end_at_the_next_top_level_key() {
        let text = "name: x\njobs:\n  gate:\n    steps:\n      - run: cargo test\n  other:\n    steps:\n      - run: elan toolchain install lean\nconcurrency:\n  group: g\n";
        let jobs = ci_jobs("ci.yml", text);
        assert_eq!(
            jobs.iter().map(|job| job.id.as_str()).collect::<Vec<_>>(),
            ["gate", "other"]
        );
        assert!(!installs_reference_pin(&jobs[0]));
        assert!(installs_reference_pin(&jobs[1]));
        // `concurrency:` is a top-level key, not a job.
        assert!(!jobs[1].body.contains("group: g"));
    }

    /// A job the reader cannot see is a job whose pin installation it cannot count, and the
    /// miss is silent. Trailing whitespace is the cheapest way to produce one.
    #[test]
    fn a_job_key_with_trailing_whitespace_is_still_a_job() {
        let jobs = ci_jobs(
            "ci.yml",
            "jobs:\n  gate:  \n    steps:\n      - run: cargo test\n",
        );
        assert_eq!(
            jobs.iter().map(|job| job.id.as_str()).collect::<Vec<_>>(),
            ["gate"]
        );
    }

    #[test]
    fn a_comment_mentioning_elan_is_not_an_installation() {
        let jobs = ci_jobs(
            "ci.yml",
            "jobs:\n  gate:\n    steps:\n      - run: |\n          # --check re-walks the Reference and needs an elan\n          rustup toolchain install nightly\n",
        );
        assert_eq!(jobs.len(), 1);
        assert!(!installs_reference_pin(&jobs[0]));
    }

    #[test]
    fn check_sh_is_the_link_between_the_workflow_and_the_workspace_suite() {
        assert!(check_sh_reaches_workspace(
            "  run_stage test cargo test --locked\n"
        ));
        assert!(check_sh_reaches_workspace(
            "  run_stage test cargo test --locked -- \"${args[@]}\"\n"
        ));
        assert!(!check_sh_reaches_workspace(
            "  run_stage test cargo test --locked -p fln-core\n"
        ));
        assert!(!check_sh_reaches_workspace(
            "  run_stage check cargo check\n"
        ));
    }

    #[test]
    fn reach_is_read_from_the_invocation_and_covers_only_what_it_names() {
        let members = ["crates/fln-kernel".to_string(), "tools/sg".to_string()];
        let job = CiJob {
            workflow: "w".into(),
            id: "j".into(),
            body: "      - run: ./scripts/check.sh\n".into(),
        };
        assert_eq!(test_reach(&job, true), vec![TestReach::Workspace]);
        assert_eq!(test_reach(&job, false), vec![]);
        let reach = test_reach(&job, true);
        assert!(reach_covers(&reach, "tools/sg/tests/a.rs", &members));
        assert!(!reach_covers(&reach, "outside/tests/a.rs", &members));

        let narrow = CiJob {
            workflow: "w".into(),
            id: "j".into(),
            body: "      - run: cargo test -p fln-conformance --test mandated_mutants\n".into(),
        };
        let reach = test_reach(&narrow, true);
        assert_eq!(
            reach,
            vec![TestReach::Targets(["mandated_mutants".to_string()].into())]
        );
        assert!(!reach_covers(
            &reach,
            "crates/fln-kernel/tests/other.rs",
            &members
        ));
        assert!(reach_covers(
            &reach,
            "crates/fln-kernel/tests/mandated_mutants.rs",
            &members
        ));
        // A `src/` file is never an integration target, whatever it is called.
        assert!(!reach_covers(
            &reach,
            "crates/fln-kernel/src/mandated_mutants.rs",
            &members
        ));
    }

    #[test]
    fn a_separate_manifest_reaches_only_its_own_tree() {
        let members = ["crates/a".to_string()];
        let job = CiJob {
            workflow: "w".into(),
            id: "j".into(),
            body:
                "      - run: cargo test --locked --manifest-path tribunal/epoch-lab/Cargo.toml\n"
                    .into(),
        };
        let reach = test_reach(&job, true);
        assert_eq!(
            reach,
            vec![TestReach::Manifest("tribunal/epoch-lab".into())]
        );
        assert!(reach_covers(
            &reach,
            "tribunal/epoch-lab/tests/x.rs",
            &members
        ));
        assert!(!reach_covers(&reach, "crates/a/tests/x.rs", &members));
    }

    #[test]
    fn member_patterns_come_from_the_manifest_and_an_unreadable_one_refuses() {
        assert_eq!(
            workspace_member_patterns("[workspace]\nmembers = [\"crates/*\", \"tools/*\"]\n"),
            Some(vec!["crates/*".to_string(), "tools/*".to_string()])
        );
        assert_eq!(
            workspace_member_patterns("[workspace]\nresolver = \"3\"\n"),
            None
        );
        assert_eq!(workspace_member_patterns("members = []\n"), None);
    }

    #[test]
    fn record_fields_survive_braces_and_quotes_inside_earlier_values() {
        let line = r#"{"note":"a } and a \" and a ] inside","bead":"fln-x","artifacts":["a.rs","b.rs"],"skip":"none"}"#;
        assert_eq!(
            record_field(line, "bead"),
            Some(Field::Text("fln-x".into()))
        );
        assert_eq!(record_field(line, "skip"), Some(Field::Text("none".into())));
        assert_eq!(
            record_field(line, "artifacts"),
            Some(Field::List(vec!["a.rs".into(), "b.rs".into()]))
        );
        assert_eq!(record_field(line, "absent"), None);
        assert_eq!(
            record_field(r#"{"a":[],"b":"z"}"#, "a"),
            Some(Field::List(vec![]))
        );
        // Nested containers are skipped whole, not walked into.
        assert_eq!(
            record_field(r#"{"o":{"bead":"wrong"},"bead":"right"}"#, "bead"),
            Some(Field::Text("right".into()))
        );
        // A truncated record refuses rather than reporting the fields it managed to read.
        assert_eq!(record_field(r#"{"bead":"fln-x""#, "artifacts"), None);
        assert_eq!(record_field("not json", "bead"), None);
    }

    /// Non-ASCII prose in a field this reader SKIPS must not derail the walk.
    ///
    /// The first version decoded while skipping, refused on `§`, recovered by advancing one
    /// byte, and walked into the string — where the `,` inside the note ended the record and
    /// every later field read as absent. It dropped 292 of this tracker's records that way
    /// and reported their coverage rows as orphans. Both directions are asserted: the
    /// skipped field must not break the walk, and the same text must decode when it is the
    /// field being read.
    #[test]
    fn prose_with_section_signs_and_em_dashes_does_not_derail_the_walk() {
        let line = "{\"description\":\"the plan's §18 laws — stated exactly, not statistically\",\
                    \"id\":\"fln-2bn5\",\"status\":\"closed\"}";
        assert_eq!(
            record_field(line, "id"),
            Some(Field::Text("fln-2bn5".into()))
        );
        assert_eq!(
            record_field(line, "status"),
            Some(Field::Text("closed".into()))
        );
        assert_eq!(
            record_field(line, "description"),
            Some(Field::Text(
                "the plan's §18 laws — stated exactly, not statistically".into()
            ))
        );
        // An escaped quote inside skipped prose must not close the string early either.
        let tricky = r#"{"note":"he said \"done\", then left","id":"fln-x"}"#;
        assert_eq!(
            record_field(tricky, "id"),
            Some(Field::Text("fln-x".into()))
        );
    }

    #[test]
    fn terminal_is_derived_from_the_tracker_exactly_as_the_validator_derives_it() {
        assert!(is_terminal("closed", "none"));
        assert!(is_terminal("tombstone", "none"));
        assert!(!is_terminal("closed", "blocked"));
        assert!(!is_terminal("open", "none"));
        assert!(!is_terminal("in_progress", "none"));
    }

    #[test]
    fn scenario_keys_come_from_the_registry_block_and_a_missing_block_is_empty() {
        let source = "E2E_STEP_ORDERS = {\n    \"closure_audit\": (\n        \"a\",\n    ),\n    \"env_snapshots\": (\"b\",),\n}\n";
        assert_eq!(
            e2e_scenario_keys(source),
            ["closure_audit".to_string(), "env_snapshots".to_string()].into()
        );
        assert!(e2e_scenario_keys("nothing here").is_empty());
    }
}
