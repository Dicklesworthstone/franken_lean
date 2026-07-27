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
// Tests CI compiles and never runs
// ---------------------------------------------------------------------------

/// Every `#[ignore]`d test in one source file, as `(function, reason)`.
///
/// **Counts the attribute, never the token, and the difference is not pedantry.** Measured
/// at `974fcc5a` the same construct yields three different answers depending on how it is
/// counted: `rg -c '#\[ignore'` returns **22** because guard bodies and module docs discuss
/// the attribute at length; a `#[test]`-with-`#[ignore]`-nearby window returns **6** because
/// a doc-comment mention sits within six lines of an unrelated test; the attribute itself
/// returns **5**. `kernel_replay.rs` is the trap in every version — one of its own guards
/// asserts on the literal `#[ignore` as a *needle*.
///
/// This is the mentions-versus-construct error `fln-bench-apparatus-empty-referent-bkw6`
/// already paid for by counting `[[bench]]` sections, and the guard that reports this
/// carried "fifteen" in its own documentation until `974fcc5a`. Requiring the line to
/// *begin* with the attribute is what separates a declaration from a discussion of one.
pub fn ignored_tests(source: &str) -> Vec<(String, String)> {
    let lines: Vec<&str> = source.lines().collect();
    let mut found = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        if !line.trim_start().starts_with("#[ignore") {
            continue;
        }
        let reason = line
            .split_once('"')
            .and_then(|(_, rest)| rest.rsplit_once('"').map(|(body, _)| body.to_string()))
            .unwrap_or_else(|| "<bare #[ignore], no reason given>".to_string());
        // The attribute may sit above further attributes before the item itself.
        let name = lines[index + 1..lines.len().min(index + 9)]
            .iter()
            .find_map(|candidate| {
                let trimmed = candidate.trim_start();
                let rest = trimmed.strip_prefix("fn ")?;
                let end = rest.find(['(', '<', ' ']).unwrap_or(rest.len());
                Some(rest[..end].to_string())
            })
            .unwrap_or_else(|| "<no function beneath the attribute>".to_string());
        found.push((name, reason));
    }
    found
}

// ---------------------------------------------------------------------------
// Granularity: the unit a row names versus the unit that runs
// ---------------------------------------------------------------------------

/// Every `#[test]`/`#[tokio::test]` function in a source file, by the **attribute**.
///
/// The sibling of [`ignored_tests`], subject to the identical trap and answering it more
/// strictly. `#[test]` appears in this workspace inside doc comments, inside doctests, inside
/// guard assertions and inside the string literals a mutation campaign plants; counting the
/// token instead of the construct is the mentions-versus-construct error
/// `fln-bench-apparatus-empty-referent-bkw6` paid for, and the guard reporting *this* number
/// carried a wrong one for exactly that reason until `974fcc5a`.
///
/// So the attribute must be the **entire** trimmed line, where [`ignored_tests`] accepts a
/// prefix. That is deliberate, because this function has a second caller with the opposite
/// risk profile: `test:<pkg>::<target>::<path>` citations are resolved against it, and there a
/// false *positive* would let a citation naming a function that does not exist resolve anyway
/// — a label that denotes nothing, which is `fln-0rxm`'s shape reproduced inside the repair
/// for its neighbour. Under-reading a `#[test]` that shares its line with something else costs
/// a spurious refusal, which is loud; over-reading one buys a silent pass.
///
/// A `#[test]` with no `fn` beneath it yields the sentinel rather than vanishing, for
/// [`ignored_tests`]'s reason: a construct this cannot resolve is a refusal, never an absence.
pub fn test_functions(source: &str) -> Vec<String> {
    const NO_FUNCTION: &str = "<no function beneath the attribute>";
    let lines: Vec<&str> = source.lines().collect();
    let mut found = Vec::new();
    for (index, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if trimmed != "#[test]" && trimmed != "#[tokio::test]" {
            continue;
        }
        // The attribute may sit above further attributes before the item itself. The scan
        // stops at the *next* test attribute: without that bound a `#[test]` whose item this
        // cannot parse silently captures the following test's name, which is a wrong answer
        // wearing a right one's shape — measured, by this module's own unit test, which
        // caught `async fn` slipping through and returning the next function's name.
        let name = lines[index + 1..lines.len().min(index + 9)]
            .iter()
            .take_while(|candidate| {
                let t = candidate.trim();
                t != "#[test]" && t != "#[tokio::test]"
            })
            .find_map(|candidate| {
                let mut rest = candidate.trim_start();
                // `async fn`, `pub fn`, `pub(crate) async fn`, `unsafe fn` — the item may
                // carry modifiers, and `#[tokio::test]` guarantees at least one of them.
                loop {
                    let stripped = ["pub(crate) ", "pub ", "async ", "unsafe ", "const "]
                        .iter()
                        .find_map(|modifier| rest.strip_prefix(modifier));
                    match stripped {
                        Some(next) => rest = next.trim_start(),
                        None => break,
                    }
                }
                let rest = rest.strip_prefix("fn ")?;
                let end = rest.find(['(', '<', ' ']).unwrap_or(rest.len());
                Some(rest[..end].to_string())
            })
            .unwrap_or_else(|| NO_FUNCTION.to_string());
        found.push(name);
    }
    found
}

/// Every reason a member manifest defeats cargo's integration-test **auto-discovery**.
///
/// The target set is derived from the *layout* — one target per top-level `tests/*.rs` — and
/// that is complete only while nothing overrides it. Two manifest keys can: an explicit
/// `[[test]]` section, whose `path` may point anywhere, and `autotests`, which switches
/// discovery off outright.
///
/// **The direction is the mirror of `bkw6`'s.** `bkw6` counted `[[bench]]` sections and
/// reported a false clean because cargo auto-discovered the rest; here auto-discovery *is* the
/// whole rule, so what would silently break this derivation is one of those keys appearing.
/// Measured at `29852ec1`: zero members declare either, and no `tests/<dir>/main.rs` exists, so
/// the layout rule is exact at 75 targets. The guard asserts that precondition rather than
/// assuming it, so the day a `[[test]]` section lands the scan says its answer has stopped
/// being complete instead of quietly under-counting.
pub fn autodiscovery_overrides(manifest: &str) -> Vec<&'static str> {
    let mut reasons = Vec::new();
    for line in manifest.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with('#') {
            continue;
        }
        if trimmed == "[[test]]" {
            reasons.push("declares an explicit [[test]] target section");
        }
        if trimmed
            .strip_prefix("autotests")
            .is_some_and(|rest| rest.trim_start().starts_with('='))
        {
            reasons.push("sets `autotests`, which turns integration-test auto-discovery off");
        }
    }
    reasons.sort_unstable();
    reasons.dedup();
    reasons
}

/// A `test:<pkg>::<target>::<path>` citation — the **function-granular** evidence kind.
///
/// A coverage row cites a file; cargo compiles a *target*; libtest runs a *function*. The
/// existing `cargo-test:<stem>` token closes half that gap and a bare path closes none of it:
/// both name something cargo can build, neither names something libtest can run. This kind
/// names exactly what a `cargo test` invocation runs, in both target flavours:
///
/// ```text
/// test:fln-conformance::kernel_replay::prelude_replays_through_the_kernel
///   -> cargo test -p fln-conformance --test kernel_replay -- --exact prelude_replays_…
/// test:fln-env::lib::extensions::tests::merge_rejects_conflicting_extensions
///   -> cargo test -p fln-env --lib -- --exact extensions::tests::merge_rejects_…
/// ```
///
/// So it is a **runnable command rather than a label**, which is the property a rig-emitted
/// execution record can later be joined to (`fln-log-derived-disposition-not-execution-xes2`).
///
/// **The split is `::` with maxsplit 2, and the third segment keeps its own `::`.** A lib unit
/// test's libtest name *is* a module path, so a fixed three-segment parse could express the
/// integration half and not the lib half — and the lib half is the worse shape: there is no
/// cargo invocation at all that runs the tests of one `src/*.rs`, the narrowest selectable unit
/// being the whole crate's lib target.
///
/// **It is package-qualified where `cargo-test:<stem>` is not**, and that is not decoration. A
/// stem is unique across this workspace today and nothing makes it stay unique; two crates may
/// each hold `tests/model.rs`. That is the non-injective-projection shape this lineage has paid
/// for repeatedly — a key treated as an identity with nobody checking — so this kind never
/// depends on the stem being unique.
///
/// Returns `None` for anything that is not three non-empty `::`-separated parts after the
/// prefix. A caller must treat a `test:`-prefixed artifact that returns `None` as a **finding**,
/// never as an artifact of some other kind: silently ignoring a malformed citation is how a
/// typo becomes a free exit from the population.
pub fn test_function_citation(artifact: &str) -> Option<(&str, &str, &str)> {
    let rest = artifact.strip_prefix("test:")?;
    let mut parts = rest.splitn(3, "::");
    let package = parts.next()?;
    let target = parts.next()?;
    let path = parts.next()?;
    (!package.is_empty() && !target.is_empty() && !path.is_empty() && !path.starts_with("::"))
        .then_some((package, target, path))
}

/// The module path prefix cargo gives a package source file, from the file layout alone.
///
/// `src/lib.rs` → `""`; `src/foo.rs` → `"foo"`; `src/foo/mod.rs` → `"foo"`;
/// `src/foo/bar.rs` → `"foo::bar"`. `src/main.rs` is a binary target and yields `None`.
///
/// **Sound here because nothing overrides the layout**: measured at `29852ec1`, no source file
/// in the workspace carries a `#[path` attribute, so a file's module path is its directory
/// path. That precondition is checked by the caller, in the loud direction — a `#[path`
/// appearing makes this incomplete and must refuse rather than mis-resolve.
///
/// This is a **prefix**, not the whole libtest name: inner `mod tests { … }` nesting appends
/// further components this does not model. Callers must therefore treat it as a *necessary*
/// condition — the cited path must begin with it — never a sufficient one.
pub fn module_path_prefix(relative_path: &str) -> Option<String> {
    let (_, tail) = relative_path.rsplit_once("/src/")?;
    let tail = tail.strip_suffix(".rs")?;
    if tail == "main" {
        return None;
    }
    let mut parts: Vec<&str> = tail.split('/').collect();
    match parts.last() {
        Some(&"lib") | Some(&"mod") => {
            parts.pop();
        }
        _ => {}
    }
    Some(parts.join("::"))
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
/// from a key to the shell script that dispatches it is declared nowhere either; the
/// functions below derive it from the lane scripts' own text rather than from their names.
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

// ---------------------------------------------------------------------------
// A registered scenario and the lane script that runs it
// ---------------------------------------------------------------------------

/// The schema token every `fln.e2e/2` lane script carries.
///
/// A **compiled contract**, not a needle: `scripts/evidence.py` refuses a run whose records
/// do not declare it, so a lane cannot quietly stop being governed by rewording something.
pub const GOVERNED_E2E_SCHEMA: &str = "fln.e2e/2";

/// Drop whole-line shell comments, for the reason [`code_only`] drops Rust ones.
///
/// It matters more here than there. Every lane script opens with a prose header naming the
/// sibling lanes it was modelled on and the beads it serves, so a scan that read comments
/// would find `closure_audit` inside `structure_gate.sh` and conclude the two are bound.
pub fn shell_code_only(source: &str) -> String {
    source
        .lines()
        .filter(|line| !line.trim_start().starts_with('#'))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Every scenario name a lane script **assigns**, from any variable whose name ends in
/// `SCENARIO`.
///
/// **The variable name is not fixed and assuming it was cost a false measurement.** Six of
/// the eight governed lanes use plain `SCENARIO=`; `kernel_replay.sh` uses `AP6_SCENARIO=`
/// for its nested child bundle. A first pass anchored on a word boundary before `SCENARIO`
/// missed it and reported the lane as declaring no scenario at all — the guard's own
/// spelling-keyed-scan defect, in the guard written about derivation.
///
/// Only `[a-z0-9_]` literals are collected, which is exactly the shape of an
/// `E2E_STEP_ORDERS` key. `IDENTITY_SCENARIO="$scenario"` is a parameter expansion, not a
/// name, and is correctly not one.
pub fn scenario_assignments(shell_source: &str) -> BTreeSet<String> {
    let code = shell_code_only(shell_source);
    let mut found = BTreeSet::new();
    for (index, _) in code.match_indices("SCENARIO=\"") {
        let rest = &code[index + "SCENARIO=\"".len()..];
        let Some(end) = rest.find('"') else {
            continue;
        };
        let literal = &rest[..end];
        if !literal.is_empty()
            && literal
                .chars()
                .all(|c| c.is_ascii_lowercase() || c.is_ascii_digit() || c == '_')
        {
            found.insert(literal.to_string());
        }
    }
    found
}

/// Does this lane script's **code** name `key` as a standalone word?
///
/// The weaker of the two bindings, and the guard declares which keys rest on it. Three
/// scenarios reach their lane as the first argument of a dispatch helper
/// (`run_identity_child declaration_tag_matrix …`) rather than through an assignment, so an
/// assignment-only rule reports them as orphans.
///
/// **Modelling the helper by name is the alternative, and it is a hand-list** — the exact
/// defect `franken_lean-worktree-gitdir-refusal-hugg` is criticised for, and one this
/// codebase has already paid for twice: a scan keyed to one *spelling* is a hand-list
/// wearing a derived scan's clothes (`franken_lean-build-gate-lane-governed-set-98np`).
/// A word scan cannot be defeated by renaming a helper.
///
/// It over-credits an incidental code mention, and that direction never yields a false red:
/// it can only fail to flag an orphan, never invent one. The population resting on it is
/// declared and checked by set equality, so it cannot grow unnoticed.
pub fn names_scenario_in_code(shell_source: &str, key: &str) -> bool {
    fn word_char(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_'
    }
    let code = shell_code_only(shell_source);
    code.match_indices(key).any(|(index, _)| {
        let before = code[..index].chars().next_back();
        let after = code[index + key.len()..].chars().next();
        !before.is_some_and(word_char) && !after.is_some_and(word_char)
    })
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

    /// The decisive control, and the one that would have caught the wrong number this
    /// module's own documentation carried: a file that *discusses* `#[ignore]` — in a module
    /// doc, in a doc comment, in a string literal, and as a scanner's own needle, which is
    /// every shape `kernel_replay.rs` actually contains — must contribute **nothing**.
    #[test]
    fn discussing_the_attribute_is_not_declaring_it() {
        let source = "\
//! The corpus lane is `#[ignore]`d for cost, so a green run proves nothing.\n\
/// `#[ignore]`d because it edits tracked source.\n\
fn discussion_only() {\n\
    let gated = body.contains(\"#[ignore\");\n\
    assert!(gated, \"the campaign is #[ignore]d, so the filter matches nothing\");\n\
}\n";
        assert_eq!(ignored_tests(source), Vec::new());

        // The same file, plus ONE real attribute.
        let with_one =
            format!("{source}#[ignore = \"cost: the whole corpus\"]\nfn real_lane() {{}}\n");
        assert_eq!(
            ignored_tests(&with_one),
            vec![(
                "real_lane".to_string(),
                "cost: the whole corpus".to_string()
            )]
        );
    }

    /// A bare `#[ignore]` names no reason, and an attribute above further attributes still
    /// finds its function. Both are refusals-by-naming rather than silent drops.
    #[test]
    fn an_ignore_reports_its_function_and_says_when_no_reason_was_given() {
        let source = "#[ignore]\n#[should_panic]\nfn bare_one() {}\n";
        assert_eq!(
            ignored_tests(source),
            vec![(
                "bare_one".to_string(),
                "<bare #[ignore], no reason given>".to_string()
            )]
        );
        let orphan = "#[ignore = \"why\"]\n// nothing follows\n";
        assert_eq!(
            ignored_tests(orphan),
            vec![(
                "<no function beneath the attribute>".to_string(),
                "why".to_string()
            )]
        );
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

    #[test]
    fn a_scenario_assignment_is_found_under_any_variable_prefix_and_never_in_a_comment() {
        // Both spellings this tree actually uses, plus the parameter expansion that is not a
        // name, plus the header comment that names a sibling lane and must not bind it.
        let source = concat!(
            "# Modelled on scripts/e2e/closure_audit.sh; SCENARIO=\"from_a_comment\"\n",
            "SCENARIO=\"env_snapshots\"\n",
            "AP6_SCENARIO=\"kernel_replay\"\n",
            "IDENTITY_SCENARIO=\"$scenario\"\n",
        );
        assert_eq!(
            scenario_assignments(source),
            ["env_snapshots".to_string(), "kernel_replay".to_string()].into()
        );
    }

    #[test]
    fn a_word_binding_excludes_comments_and_longer_identifiers() {
        // The dispatch-helper form three scenarios reach their lane through, the step id that
        // merely extends the key, and the provenance header that names a sibling lane.
        let source = concat!(
            "# see scripts/e2e/structure_gate.sh for the closure_audit pattern\n",
            "run_identity_child declaration_tag_matrix fln-amv.12 \\\n",
            "emit declaration_membership_mutant started\n",
        );
        assert!(names_scenario_in_code(source, "declaration_tag_matrix"));
        // Only as a prefix of a longer step id — not a binding.
        assert!(!names_scenario_in_code(source, "declaration_membership"));
        // Present, but only in the header comment.
        assert!(!names_scenario_in_code(source, "closure_audit"));
    }

    #[test]
    fn test_functions_counts_the_attribute_and_never_the_token() {
        // Every shape that actually occurs in this workspace, in one fixture: a module doc
        // that discusses the attribute, a doctest that contains it, and a mutation campaign's
        // planted string literal. All three are mentions; none is a test.
        let source = concat!(
            "//! A module doc that discusses `#[test]` at length.\n",
            "/// ```\n",
            "/// #[test]\n",
            "/// fn documented_but_not_compiled() {}\n",
            "/// ```\n",
            "const PLANTED: &str = \"#[test]\\nfn inside_a_string_literal() {}\";\n",
            "\n",
            "#[test]\n",
            "fn a_real_one() {}\n",
            "\n",
            "#[tokio::test]\n",
            "async fn an_async_one() {}\n",
            "\n",
            "#[test]\n",
            "#[ignore = \"cost\"]\n",
            "fn behind_another_attribute() {}\n",
        );
        assert_eq!(
            test_functions(source),
            vec!["a_real_one", "an_async_one", "behind_another_attribute"],
            "the doc comment, the doctest and the planted literal are mentions of the \
             attribute, not declarations of one — counting them is the error `bkw6` paid for"
        );
    }

    #[test]
    fn a_test_attribute_with_no_function_beneath_it_refuses_rather_than_vanishing() {
        assert_eq!(
            test_functions("#[test]\n"),
            vec!["<no function beneath the attribute>"]
        );
    }

    #[test]
    fn autodiscovery_overrides_names_both_keys_and_ignores_commented_ones() {
        assert!(autodiscovery_overrides("[package]\nname = \"x\"\n").is_empty());
        assert!(
            autodiscovery_overrides("# [[test]]\n# autotests = false\n").is_empty(),
            "a commented-out override does not defeat auto-discovery"
        );
        assert_eq!(autodiscovery_overrides("[[test]]\nname = \"t\"\n").len(), 1);
        assert_eq!(autodiscovery_overrides("autotests = false\n").len(), 1);
        assert_eq!(
            autodiscovery_overrides("autotests=false\n[[test]]\n").len(),
            2
        );
    }

    #[test]
    fn test_function_citation_takes_both_target_flavours_and_refuses_the_rest() {
        assert_eq!(
            test_function_citation("test:fln-conformance::kernel_replay::prelude_replays"),
            Some(("fln-conformance", "kernel_replay", "prelude_replays"))
        );
        // The lib flavour keeps its module path intact in the third part — a fixed
        // three-segment split could not express it.
        assert_eq!(
            test_function_citation("test:fln-env::lib::extensions::tests::merges"),
            Some(("fln-env", "lib", "extensions::tests::merges"))
        );
        for malformed in [
            "test:fln-conformance::kernel_replay",
            "test:::",
            "test:",
            "test:pkg::target::",
            "test:pkg::::path",
            "cargo-test:kernel_replay",
            "crates/fln-conformance/tests/kernel_replay.rs",
        ] {
            assert_eq!(
                test_function_citation(malformed),
                None,
                "{malformed:?} must not parse as a function-granular citation"
            );
        }
    }

    #[test]
    fn module_path_prefix_follows_the_file_layout() {
        assert_eq!(
            module_path_prefix("crates/x/src/lib.rs").as_deref(),
            Some("")
        );
        assert_eq!(
            module_path_prefix("crates/x/src/foo.rs").as_deref(),
            Some("foo")
        );
        assert_eq!(
            module_path_prefix("crates/x/src/foo/mod.rs").as_deref(),
            Some("foo")
        );
        assert_eq!(
            module_path_prefix("crates/x/src/foo/bar.rs").as_deref(),
            Some("foo::bar")
        );
        // A binary target is not part of the lib target's test namespace.
        assert_eq!(module_path_prefix("crates/x/src/main.rs"), None);
        assert_eq!(module_path_prefix("crates/x/tests/foo.rs"), None);
    }
}
