//! The workspace-graph snapshot test (bead fln-8mj): the REAL repository must be
//! structurally clean against its reviewed acknowledgment files. Any new crate or
//! dependency edge fails this test until `ci/WORKSPACE_GRAPH.txt` is edited in the
//! same change — that edit is the review surface.
//!
//! **Every rig here resolves the repository through
//! [`fln_conformance::checked_workspace_root!`], never from its own compile-time
//! manifest dir.** `CARGO_TARGET_DIR` is shared machine-wide, and cargo reuses a test
//! binary built from an identical-bytes copy of this package in another checkout
//! without rebuilding it — so the compile-time value names the tree that *built* this
//! binary, which is not necessarily the tree that launched it. Measured live at
//! `5c5ada4b`: this exact binary carried `/data/tmp/wt-cc_2/tools/structure-guard` and
//! reported `INCONCLUSIVE` about that worktree while the main tree it was invoked from
//! was clean, citing a symlink defect on a path that is a regular file here. Today that
//! direction is a loud false red; swap which checkout is dirty and the identical
//! mechanism reports **structurally clean about a repository nobody tested**. The macro
//! compares the baked value against the one cargo puts in this process's environment and
//! panics naming both paths. Bead `fln-cross-tree-baked-root-k60n`.

#![forbid(unsafe_code)]

use std::process::{Command, Output};

fn run_cli(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_structure-guard"))
        .args(args)
        .output()
        .expect("run structure-guard CLI")
}

fn assert_versioned_robot_lines(stdout: &str, expected_lines: usize) {
    let lines: Vec<_> = stdout.lines().collect();
    assert_eq!(lines.len(), expected_lines, "robot output:\n{stdout}");
    assert!(
        lines.iter().all(|line| line.starts_with('{')),
        "robot mode emitted human output: {stdout}"
    );
    // Bound to the const the producer actually emits, never transcribed. A transcribed
    // version is a second copy of the answer, and the pending `/5` bump (bead
    // `fln-census-empty-referent-no-mock-krb0` for `data_grade`, `t0g7` for
    // `line_count_covenants`) would have had to remember this line to stay green — which is
    // how a test starts asserting a version the tool stopped emitting.
    let needle = format!("\"schema\":\"{}\"", structure_guard::NDJSON_SCHEMA);
    assert!(
        lines.iter().all(|line| line.contains(&needle)),
        "robot output used the wrong schema, expected {needle}: {stdout}"
    );
}

#[test]
fn real_workspace_is_structurally_clean() {
    let root = fln_conformance::checked_workspace_root!();
    let outcome = structure_guard::checks::run(&root).expect("structure-guard setup");
    assert!(
        outcome.findings.is_empty(),
        "structural findings against the real workspace:\n{}",
        structure_guard::report::render_human(&root.display().to_string(), &outcome)
    );
    assert!(
        outcome.crate_count > 0,
        "workspace discovery found no crates"
    );
}

#[test]
fn real_verification_manifest_covers_the_live_tracker() {
    let root = fln_conformance::checked_workspace_root!();
    let output = Command::new("python3")
        .args(["-I", "-S"])
        .arg(root.join("scripts/evidence.py"))
        .arg("validate-verification-manifest")
        .arg("--manifest")
        .arg(root.join("ci/VERIFICATION_MANIFEST.jsonl"))
        .arg("--beads")
        .arg(root.join(".beads/issues.jsonl"))
        .output()
        .expect("run the authoritative verification-manifest validator");
    assert!(
        output.status.success(),
        "verification coverage drifted from the live tracker:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "successful validator wrote stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).expect("validator stdout is UTF-8");
    assert!(stdout.contains("\"schema\":\"fln.validation/1\""));
    assert!(stdout.contains("\"validator\":\"fln.verification-manifest/2\""));
    assert!(stdout.contains("\"coverage_state_source\":\".beads/issues.jsonl\""));
    assert!(stdout.contains("\"valid\":true"));
}

#[test]
fn robot_real_workspace_binds_complete_authority_evidence() {
    let root = fln_conformance::checked_workspace_root!();
    let output = run_cli(&[
        "--root",
        root.to_str().expect("workspace root is UTF-8"),
        "--robot",
    ]);
    assert!(
        output.status.success(),
        "robot guard failed: {}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert!(output.stderr.is_empty(), "robot stderr must be empty");
    let stdout = String::from_utf8(output.stdout).expect("robot stdout is UTF-8");
    assert_versioned_robot_lines(&stdout, 2);
    assert!(stdout.contains("\"root_identity\":\"/"));
    assert!(stdout.contains("\"authority_inventory\":{"));
    assert!(stdout.contains("\"effective_compiler_identity\":{"));
    assert!(stdout.contains("\"contract_declared\":true"));
    assert!(stdout.contains("\"configuration_match\":true"));
    assert!(stdout.contains("\"contract_match\":true"));
    assert!(stdout.contains("\"admitted_environment\":{"));
    assert!(stdout.contains("\"authority\":\"complete\""));
    assert!(stdout.contains("\"authority_count_rule_holds\":true"));
    assert!(stdout.contains("\"governed_root_unchanged\":true"));
    assert!(stdout.contains("\"verdict\":\"pass\""));

    // THE JOIN THIS TEST IS NAMED FOR, and until now it did not make it — which is why this
    // test could not tell a fresh clone from a complete checkout.
    //
    // `authority:"complete"` is a fact about the governed **traversal** closure (`Authority`'s
    // own doc-comment). The contract-handoff audit is a *different* audit, and on a tree with no
    // census it establishes nothing and returns no snapshot — deliberately, since withholding it
    // is what stops an absent census reading as "audited and clean"
    // (`fln-census-empty-referent-no-mock-krb0`, commit `66bfb488`).
    //
    // Measured in a REAL fresh clone at `a0c9b1c8`, one variable — the same binary against the
    // same clone, the four census shards absent then present: `verdict:"pass"` and
    // `authority:"complete"` were **byte-identical in both**, and `contract_handoff_root` was the
    // only field that moved, `null` to a digest. So the snapshot's absence reaches the artifact
    // and reaches nothing else: a claim and its evidence in one artifact with no join between
    // them, which is item 7's shape, and a reader taking `verdict` or `authority` is told
    // "pass"/"complete" about a tree where this audit never ran.
    //
    // The null is bound to the filesystem rather than trusted from the string, for the same
    // reason the no-mock rig's skip is: an absent census and a misdirected root are
    // indistinguishable in the artifact alone.
    if stdout.contains("\"contract_handoff_root\":null") {
        assert!(
            !root.join("contracts/builtin_environment.tsv").exists(),
            "the artifact withheld a contract-handoff root while the census EXISTS at {}; that \
             is a misdirected probe, not a fresh clone",
            root.display()
        );
        eprintln!(
            "PARTIAL robot_real_workspace_binds_complete_authority_evidence at {}: the census is \
             absent, so NOTHING about contract-handoff authority is established by this run. The \
             artifact's `authority`:`complete` covers the governed traversal ONLY. Every other \
             assertion in this test did run. Shards are gitignored and unreachable from main \
             (bead `fln-census-out-of-git-2ya9`).",
            root.display()
        );
    } else {
        assert!(
            stdout.contains("\"contract_handoff_root\":\"fnv1a64:"),
            "a contract-handoff root must be a digest or an explicit null, never absent: {stdout}"
        );
    }
}

/// A `usize` field of a flat JSON object, without a JSON dependency (D1 applies to the
/// apparatus). Returns `None` when the key is absent, so a missing field fails loudly at
/// the assertion rather than defaulting to zero and satisfying the conservation laws.
fn u64_field(object: &str, key: &str) -> Option<u64> {
    let needle = format!("\"{key}\":");
    let rest = &object[object.find(&needle)? + needle.len()..];
    let end = rest.find(|c: char| !c.is_ascii_digit())?;
    rest[..end].parse().ok()
}

/// The D18 mode-closure scope must reach the artifact a reader actually reads, and the
/// numbers in it must be mutually consistent (bead `fln-q8qt`).
///
/// The facts existed on `RunOutcome` from the day D18 was registered and only the test
/// binary could observe them, so `verdict=pass` carried no way to learn that the D18
/// check had traversed nothing at all. This asserts against the terminal `run_end`
/// RECORD, not against the whole stream: an assertion scoped to the file would be
/// satisfied by the object appearing in any line, which is the wrong-scope shape this
/// repository has now produced several times.
///
/// The counts are deliberately not pinned. Today's live scan is vacuous — no crate
/// declares a mode-bound product root — and pinning `"scan_class":"vacuous"` would turn
/// red on whoever lands the first product binary, for doing exactly the right thing. The
/// laws below hold in both scopes, so they survive that transition and still refuse an
/// artifact whose scope word and counts disagree.
///
/// The vacuity this test tolerates is owned by bead `fln-d18-product-half-rgsg` and bound
/// by [`the_deferred_d18_product_half_stays_owned_while_the_scan_is_vacuous`] below, so
/// tolerating it here does not leave it unattended.
#[test]
fn the_terminal_record_discloses_the_d18_scope_of_the_verdict_it_carries() {
    let root = fln_conformance::checked_workspace_root!();
    let output = run_cli(&[
        "--root",
        root.to_str().expect("workspace root is UTF-8"),
        "--robot",
    ]);
    let stdout = String::from_utf8(output.stdout).expect("robot stdout is UTF-8");
    let terminal = stdout.lines().last().expect("robot stream is non-empty");
    assert!(
        terminal.contains("\"event\":\"run_end\""),
        "last record is not the terminal one: {terminal}"
    );
    let start = terminal
        .find("\"mode_closure\":{")
        .unwrap_or_else(|| panic!("run_end carries no D18 scope: {terminal}"));
    let object = &terminal[start..];
    let object = &object[..object.find('}').expect("mode_closure object is closed") + 1];

    let scanned = u64_field(object, "closures_scanned").expect("closures_scanned");
    let closure_nodes = u64_field(object, "closure_nodes").expect("closure_nodes");
    let product_roots = u64_field(object, "product_roots").expect("product_roots");
    let frontier_surfaces = u64_field(object, "frontier_surfaces").expect("frontier_surfaces");
    let nodes = u64_field(object, "nodes").expect("nodes");

    let vacuous = object.contains("\"scan_class\":\"vacuous\"");
    let traversed = object.contains("\"scan_class\":\"traversed\"");
    assert!(
        vacuous ^ traversed,
        "scan class must be exactly one of the two registered words: {object}"
    );
    assert_eq!(
        vacuous,
        scanned == 0,
        "the scope word and the closure count describe the same fact and disagree: \
         {object}"
    );
    assert!(
        scanned <= product_roots,
        "a mode is only scanned when a product declares a root for it: {object}"
    );
    assert!(
        if scanned == 0 {
            closure_nodes == 0
        } else {
            closure_nodes >= scanned
        },
        "a scanned closure contains at least its own root, and an unscanned one \
         submits nothing: {object}"
    );
    assert!(
        product_roots <= nodes && frontier_surfaces <= nodes,
        "a crate cannot be counted more than once per axis: {object}"
    );
}

/// The tracker status of one bead, without a JSON dependency (D1 applies to the
/// apparatus).
///
/// The id is matched against the record's OWN `id` key at the start of its line, so a
/// bead merely *cited* inside another bead's prose cannot answer for it — which matters
/// here, because the ids below are cited in several bead bodies. `,"status":"` is matched
/// unescaped, and that sequence can only occur structurally: a quote inside a JSON string
/// is backslash-escaped, so embedded JSON in a description cannot forge a status.
fn bead_status(tracker: &str, id: &str) -> Option<String> {
    const STATUS: &str = ",\"status\":\"";
    let prefix = format!("{{\"id\":\"{id}\",");
    let line = tracker.lines().find(|line| line.starts_with(&prefix))?;
    let rest = &line[line.find(STATUS)? + STATUS.len()..];
    Some(rest[..rest.find('"')?].to_string())
}

/// The deferred half of D18 stays owned for as long as the production scan is provably
/// vacuous (beads `franken_lean-r2st`, split and closed; `fln-d18-product-half-rgsg`, the
/// remainder, open).
///
/// `r2st` closed on its registration half: the check is wired, derives its closure from
/// governed structure, hands it to the core authority, and a planted refusal reddens a
/// real guard run with a non-zero exit. Its product half — the canonical sidecar, two
/// certified builds compared for byte-identity, the no-mock E2E that BUILDS products,
/// 1/8/32 — moved to the remainder bead intact.
///
/// A split is only legitimate if the remainder keeps its definition, and **a bead comment
/// is not a mechanism**: nothing would stop that remainder being closed later while the
/// gap it names sits here untouched, which is precisely how a split becomes a way to book
/// a win by moving the unfinished part somewhere quieter. This binds the two so that
/// cannot happen quietly.
///
/// The scan class is read from `checks::run` against the real workspace — the same
/// derivation the guard publishes — rather than re-derived here, so this cannot pass by
/// measuring something the production check does not.
///
/// **One-way, plus a floor.** Equality in both directions would be a wall that reddens a
/// correct repair, a shape that has cost this repository before. So it does NOT pin the
/// scan class: whoever lands the first product binary is not failed for doing the right
/// thing. And it stops caring about the bead's status the moment the scan traverses, so
/// the allowance shrinks only toward repair. The floor is that the bead must be FOUND —
/// a lookup matching nothing is a broken scan, not a clean tree, and would otherwise let
/// the whole check pass by silently referring to a bead that no longer exists.
/// Whether the deferral on D18's product half still applies, decided from the two facts
/// the production scan already publishes.
///
/// **Split out as a pure function, and that is the repair, not decoration.** On a clean
/// tree the scan is vacuous, so a degeneracy clause written inline would sit behind a
/// short-circuit and never execute in any real run — dead code that reads as coverage.
/// Here every interesting input is reachable from a test.
///
/// Two states keep the deferral alive:
///
/// * **vacuous** — no crate declares a product root, so no closure was ever submitted.
/// * **degenerate** — every declared product root reaches nothing but itself.
///
/// The second state is why this exists, and it was **measured, not hypothesised**
/// (cc_3, 2026-07-26, at `08688c9a`). A product root is a *marker*: two comment lines,
/// `# fln-product-root: sound` and `# fln-mode-provenance: sound`. Appending them to
/// `crates/fln/Cargo.toml` — a **six-line charter stub with no dependencies**, whose own
/// doc says "Implementation arrives with its workstream beads" — moves the live guard
/// from `scan=vacuous product-roots=0 closure-nodes=0` to
/// `scan=traversed product-roots=1 closures-scanned=1 closure-nodes=1`.
///
/// The old check tested `is_vacuous()` alone, so that flip **silenced it completely**.
/// Measured as a 2×2 with the remainder bead marked closed in a scratch worktree: with
/// the marker absent the guard exits 101 and refuses; with the marker present it exits 0
/// and the whole gap books as done. Two comment lines on a stub defeated the one
/// mechanism that exists to stop precisely that — and nothing anywhere would have said so.
///
/// A closure containing only its own root is not a product. `closure_nodes ==
/// closures_scanned` forces that reading: every closure holds at least its root, so
/// equality means every root is isolated. The first REAL product root carries a
/// dependency cone, so this stops applying the moment the work is genuinely done —
/// **one-way, no wall**, and whoever lands that product is not failed for doing the right
/// thing.
///
/// **What it still does not earn.** A declared closure with a *fabricated* dependency
/// would pass this. Making the product root itself underivable-by-assertion needs the
/// canonical sidecar, which is the remainder bead's own content — so this narrows the
/// hole from "two comments" to "a crate with real edges", it does not close it.
fn deferral_still_applies(closures_scanned: usize, closure_nodes: usize) -> bool {
    closures_scanned == 0 || closure_nodes == closures_scanned
}

#[test]
fn a_vacuous_scan_keeps_the_deferral() {
    assert!(deferral_still_applies(0, 0));
}

/// The measured stub case: one declared root, one node in its closure — itself.
#[test]
fn a_product_root_that_reaches_only_itself_keeps_the_deferral() {
    assert!(
        deferral_still_applies(1, 1),
        "a marker on a dependency-free stub is not a product"
    );
}

#[test]
fn several_isolated_roots_still_keep_the_deferral() {
    assert!(deferral_still_applies(3, 3));
}

/// The release condition. A root with a real cone ends the deferral, in both the
/// single-product and multi-product shapes, so a correct repair is never walled.
#[test]
fn a_root_with_a_dependency_cone_releases_the_deferral() {
    assert!(
        !deferral_still_applies(1, 2),
        "one root reaching one dependency"
    );
    assert!(!deferral_still_applies(2, 7), "two roots over a real cone");
}

#[test]
fn the_deferred_d18_product_half_stays_owned_while_the_scan_is_vacuous() {
    const REMAINDER: &str = "fln-d18-product-half-rgsg";
    let root = fln_conformance::checked_workspace_root!();
    let outcome = structure_guard::checks::run(&root).expect("structure-guard setup");

    let tracker_path = root.join(".beads/issues.jsonl");
    let tracker = std::fs::read_to_string(&tracker_path).unwrap_or_else(|error| {
        panic!(
            "the tracker must be readable to decide whether the deferred D18 half is \
             still owned: {}: {error}",
            tracker_path.display()
        )
    });
    // The floor, checked before the conditional below so that a vanished bead fails
    // loudly instead of being skipped along with the branch that would have used it.
    let status = bead_status(&tracker, REMAINDER).unwrap_or_else(|| {
        panic!(
            "bead {REMAINDER} owns the deferred D18 product half and is absent from the \
             tracker; a lookup that matches nothing is a broken scan, not a clean tree"
        )
    });

    let scanned = outcome.mode_closure.closures_scanned;
    let closure_nodes = outcome.mode_closure.closure_nodes;
    if deferral_still_applies(scanned, closure_nodes) {
        let shape = if scanned == 0 {
            "still vacuous — no crate declares a product root, so no closure has ever \
             been submitted to the core"
        } else {
            "traversed but DEGENERATE — every declared product root reaches nothing but \
             itself, which is what a marker on a dependency-free stub produces. A \
             `# fln-product-root:` comment is a declaration, not a product"
        };
        assert!(
            !matches!(status.as_str(), "closed" | "tombstone"),
            "the registered D18 scan is {shape} — {} product roots, {scanned} closures \
             scanned, {closure_nodes} closure nodes — while {REMAINDER}, which owns making \
             it real, is {status}. Closing the remainder in this state books the gap as \
             done: franken_lean-r2st was split on the condition that this half stay open \
             with its gap intact. Either reopen it, or land a product root with a real \
             dependency cone so this check stops applying.",
            outcome.mode_closure.product_roots,
        );
    }
}

#[test]
fn robot_rejects_an_unbound_rustc_override_without_executing_it() {
    let root = fln_conformance::checked_workspace_root!();
    let output = Command::new(env!("CARGO_BIN_EXE_structure-guard"))
        .args([
            "--root",
            root.to_str().expect("workspace root is UTF-8"),
            "--robot",
        ])
        .env("RUSTC", "/definitely/not/an/admitted/compiler")
        .output()
        .expect("run CLI with a deliberately unbound RUSTC");
    assert_eq!(output.status.code(), Some(3));
    assert!(output.stderr.is_empty(), "robot stderr must be empty");
    let stdout = String::from_utf8(output.stdout).expect("robot stdout is UTF-8");
    assert!(stdout.contains("\"configuration_match\":false"));
    assert!(stdout.contains("\"code\":\"FLN-STRUCT-029\""));
    assert!(stdout.contains("\"authority\":\"incomplete\""));
    assert!(stdout.contains("\"verdict\":\"inconclusive\""));
}

#[test]
fn robot_unknown_argument_is_visible_even_when_robot_flag_comes_later() {
    let output = run_cli(&["--unknown", "--robot"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(output.stderr.is_empty(), "robot stderr must be empty");
    let stdout = String::from_utf8(output.stdout).expect("robot stdout is UTF-8");
    assert_versioned_robot_lines(&stdout, 2);
    assert!(stdout.contains("\"verdict\":\"setup_error\""));
    assert!(stdout.contains("\"reason_code\":\"cli_parse_failure\""));
    assert!(stdout.contains("unknown argument `--unknown`"));
}

#[test]
fn robot_missing_root_value_is_a_machine_visible_parse_failure() {
    for args in [["--root", "--robot"], ["--robot", "--root"]] {
        let output = run_cli(&args);
        assert_eq!(output.status.code(), Some(2));
        assert!(output.stderr.is_empty(), "robot stderr must be empty");
        let stdout = String::from_utf8(output.stdout).expect("robot stdout is UTF-8");
        assert_versioned_robot_lines(&stdout, 2);
        assert!(stdout.contains("\"reason_code\":\"cli_parse_failure\""));
        assert!(stdout.contains("--root requires a path"));
    }
}

#[test]
fn robot_help_remains_machine_only_in_either_argument_order() {
    for args in [["--robot", "--help"], ["--help", "--robot"]] {
        let output = run_cli(&args);
        assert!(output.status.success());
        assert!(output.stderr.is_empty(), "robot stderr must be empty");
        let stdout = String::from_utf8(output.stdout).expect("robot stdout is UTF-8");
        assert_versioned_robot_lines(&stdout, 3);
        assert!(stdout.contains("\"event\":\"help\""));
        assert!(stdout.contains("\"reason_code\":\"help_requested\""));
        assert!(stdout.contains("\"exit_code\":0"));

        // The usage text names the robot schema to a HUMAN reader, and `main.rs` spells that
        // version out as a literal because `USAGE` is a `const` and `concat!` cannot take one.
        // So the two can drift, and the drift is invisible: the help record would carry the new
        // schema in its envelope while the prose inside it advertised the old one.
        //
        // Scoped to the `usage` VALUE, not to the record, because the envelope's own
        // `"schema":"…"` field would satisfy a whole-line search and make this vacuous — the
        // `fln-8zsq` lesson, where a guard's needle was matched by the guard's own text.
        let usage = help_usage_field(&stdout);
        assert!(
            usage.contains("usage: structure-guard"),
            "could not extract the usage field; this assertion is not measuring what it names: \
             {stdout}"
        );
        assert!(
            usage.contains(structure_guard::NDJSON_SCHEMA),
            "the usage text advertises a different robot schema than the tool emits (expected \
             {}): {usage}",
            structure_guard::NDJSON_SCHEMA
        );
    }
}

/// The `usage` string of the help record, unescaped only as far as this assertion needs.
///
/// No JSON dependency: D1 applies to the apparatus as much as to the product. `USAGE`
/// contains no `"`, so scanning to the first unescaped quote is exact here rather than
/// merely adequate — and if that ever stops being true the caller's own anti-vacuity
/// assertion fails rather than silently comparing a truncated slice.
fn help_usage_field(stdout: &str) -> &str {
    let needle = "\"usage\":\"";
    let Some(start) = stdout.find(needle).map(|at| at + needle.len()) else {
        return "";
    };
    let rest = &stdout[start..];
    let mut escaped = false;
    for (offset, ch) in rest.char_indices() {
        match ch {
            _ if escaped => escaped = false,
            '\\' => escaped = true,
            '"' => return &rest[..offset],
            _ => {}
        }
    }
    ""
}

/// The admission tripwire's needle set, bound to what the kernel actually exports.
///
/// **The defect this exists because of** (bead
/// `franken_lean-admission-tripwire-needles-unbound-en9q`): the tripwire's only bare needle was
/// `CheckedExpr`, the *expression* typestate of plan §8.2b — unimplemented, and present nowhere
/// in the workspace except the plan and the needle itself. Meanwhile `CheckedDecl`, the real
/// publication right, and the two types that carry it were unnamed. A needle that matches
/// nothing reports healthy for exactly the same reason a working one does, which is the sharpest
/// form of hollow green: the guard cannot fail, so its silence is uninformative.
///
/// **Why this is not "a needle matching zero sites is an error".** The tripwire scans BOUNDARY
/// crate source, where zero matches is the *healthy* state — `fln_kernel` occurring zero times
/// in `fln-unsafe-abi` is the whole point. Erroring on that would make the guard red on a clean
/// tree, which is a gate people learn to bypass (the `franken_lean-e5k7` lesson). The real
/// property is narrower and has two directions:
///
/// * **liveness** — every needle must NAME something that exists in the workspace, so it is
///   capable of matching. This is the direction that fails on `CheckedExpr`.
/// * **coverage** — every capability type the kernel exports must be named by a needle, or
///   listed in `ADMISSION_TOKEN_EXCLUSIONS` with its reason.
///
/// Both are derived from `crates/fln-kernel/src/capability.rs` at test time rather than
/// transcribed here, so this test cannot drift from the module it guards — and neither
/// direction can be satisfied by editing the needle list alone.
#[test]
fn the_admission_tripwire_names_what_the_kernel_actually_exports() {
    let root = fln_conformance::checked_workspace_root!();

    let capability = std::fs::read_to_string(root.join("crates/fln-kernel/src/capability.rs"))
        .expect("the kernel capability module must be readable");

    // Derived, never transcribed: every `pub struct`/`pub enum` the capability module declares.
    let declared: Vec<String> = capability
        .lines()
        .filter_map(|line| {
            let rest = line
                .strip_prefix("pub struct ")
                .or_else(|| line.strip_prefix("pub enum "))?;
            let name: String = rest
                .chars()
                .take_while(|c| c.is_alphanumeric() || *c == '_')
                .collect();
            (!name.is_empty()).then_some(name)
        })
        .collect();
    assert!(
        declared.len() >= 3,
        "found only {} pub type(s) in the capability module; a scan that cannot see it reports \
         a false clean rather than a kernel with no capabilities: {declared:?}",
        declared.len()
    );

    let needles = structure_guard::ledger::ADMISSION_TOKENS;
    let excluded: Vec<&str> = structure_guard::ledger::ADMISSION_TOKEN_EXCLUSIONS
        .iter()
        .map(|(name, _)| *name)
        .collect();

    // ---- direction 1: coverage — nothing the kernel exports may be silently untripwired ----
    for name in &declared {
        assert!(
            needles.contains(&name.as_str()) || excluded.contains(&name.as_str()),
            "crates/fln-kernel/src/capability.rs declares `{name}`, which is neither tripwired \
             nor declared excluded. A new capability type must be a decision, not a default: \
             add it to ADMISSION_TOKENS, or to ADMISSION_TOKEN_EXCLUSIONS with the reason it \
             cannot be laundered into an admission."
        );
    }

    // ---- direction 2: liveness — a needle must be able to match something ----
    for needle in needles {
        let names_a_crate = root.join("crates").join(needle.replace('_', "-")).is_dir();
        let names_a_capability = declared.iter().any(|d| d == needle);
        assert!(
            names_a_crate || names_a_capability,
            "the admission tripwire trips on `{needle}`, which names neither a crate under \
             crates/ nor a pub type in crates/fln-kernel/src/capability.rs. A needle that can \
             never match reports healthy for the same reason a working one does — this is the \
             state bead franken_lean-admission-tripwire-needles-unbound-en9q was filed for, \
             when the list carried `CheckedExpr` from the plan's unimplemented expression \
             typestate. Remove it, or name the thing that now carries that role."
        );
    }

    // ---- the exclusions are a SHRINKING allowance, not a parking lot ----
    for (name, reason) in structure_guard::ledger::ADMISSION_TOKEN_EXCLUSIONS {
        assert!(
            declared.iter().any(|d| d == name),
            "`{name}` is declared excluded from the admission tripwire but no longer exists in \
             the capability module — a stale exclusion is an allowance that grew for free. \
             Remove the row."
        );
        assert!(
            reason.len() > 60,
            "the exclusion for `{name}` must state why it cannot be laundered into an \
             admission; an undeclared remainder is the silent gap this whole binding exists to \
             prevent"
        );
    }
}

/// The judgement, in one place a forged caller can drive, so the mutants below can
/// demonstrate it discriminates without editing the tree.
///
/// Each arm returns a distinct reason token. **Direction is deliberate everywhere**: every
/// arm treats absence and zero as FAILURE, never as agreement. A floor-only or
/// presence-only reading of a counter goes green forever the day the counter breaks and
/// returns nothing, which is the failure mode a disclosure is least able to survive — the
/// number would simply stop appearing and every check that asked "is it under the limit"
/// would keep saying yes.
fn judge_covenant_disclosure(
    declared: &std::collections::BTreeMap<String, usize>,
    measured: &[structure_guard::checks::CovenantFact],
    human: &str,
) -> Result<(), String> {
    // (0) An empty measurement is a counter that stopped counting, not a crate with no
    // covenant: the walk declares at least `fln-kernel`.
    if measured.is_empty() {
        return Err("no-covenant-measured".to_owned());
    }
    if declared.is_empty() {
        return Err("no-covenant-declared".to_owned());
    }
    // (1)/(2) Equality both ways between what the graph DECLARES and what the walk MEASURED.
    // A declared covenant the walk skipped is a cap nobody is enforcing; a measured one
    // nobody declared is a cap nobody reviewed.
    for name in declared.keys() {
        if !measured.iter().any(|c| &c.crate_name == name) {
            return Err(format!("declared-covenant-not-measured:{name}"));
        }
    }
    for fact in measured {
        let Some(limit) = declared.get(&fact.crate_name) else {
            return Err(format!(
                "measured-covenant-not-declared:{}",
                fact.crate_name
            ));
        };
        // (3) The limit carried out must be the limit declared, or the headroom is fiction.
        if *limit != fact.limit {
            return Err(format!(
                "limit-disagrees-with-declaration:{}:{}-vs-{limit}",
                fact.crate_name, fact.limit
            ));
        }
        // (4) Zero is refused, both sides. A zero count is a broken counter reported as
        // maximal headroom — the single most dangerous value this field can carry.
        if fact.loc == 0 {
            return Err(format!("covenant-counted-zero:{}", fact.crate_name));
        }
        if fact.limit == 0 {
            return Err(format!("covenant-limit-zero:{}", fact.crate_name));
        }
        // (5) The disclosure must carry the measured number. This is the join the bead is
        // about: the value is walked on every run, and until now it was thrown away unless
        // it exceeded the limit.
        if !human.contains(&format!(
            "line-count-covenant {} loc={} max-loc={} headroom={}",
            fact.crate_name,
            fact.loc,
            fact.limit,
            fact.headroom()
        )) {
            return Err(format!("disclosure-omits-measurement:{}", fact.crate_name));
        }
    }
    Ok(())
}

/// The kernel line-count covenant is DISCLOSED by the same walk that ENFORCES it.
///
/// `<= 12 KLOC` (D6 / FL-INV-02) is genuinely walked — `FLN-STRUCT-015` fails the build over
/// it and `FLN-STRUCT-024` refuses to let the declared limit be raised. But `count_loc`'s
/// result was **discarded unless it exceeded the limit**, so the covenant was a wall and
/// never a gauge: nobody could see headroom or its trend, and the first signal would have
/// been a refused commit.
///
/// That absence had already caused two false disclosures, authored independently: 6,535 in
/// `fln-conformance/src/witness.rs` against a covenant of 5,416, and 6,382 in the `ukzx`
/// coverage row against 5,379. Both are the raw `wc -l` count. **That is a cause, not a
/// coincidence** — a person who needed the number had exactly one counter they could invoke,
/// and it was the wrong one (`franken_lean-kernel-loc-covenant-not-disclosed-t0g7`).
///
/// **One producer, not two agreeing.** The disclosed `loc` is the value `count_loc` returned
/// inside the enforcing walk, carried out on `RunOutcome`. There is no second implementation
/// that could drift, which is why the mutant the bead asks for — *move the real count without
/// moving the disclosure* — is **unplantable at this level, by construction**: they are one
/// binding used twice, and no forged input can separate them. Stated rather than quietly
/// dropped, and then made plantable one level up, at the source: the guard below refuses a
/// second `count_loc` call site, which is the only way that mutant could ever exist again.
///
/// **What this does not earn.** Disclosing a number does not make the covenant stronger, and
/// this test must not be read as evidence about kernel size — `fln-8zsq` and
/// `franken_lean-2ki4` both closed on a disclosure and bought nothing about the thing
/// disclosed. It buys exactly two things: the correct number is now reachable, and its
/// movement is now visible. The value is in the sealed human log and **not** in the robot
/// NDJSON, because `require_guard_keys` compares the terminal key set for exact equality —
/// measured, `extra=['line_count_covenants']` — so that half is a `structure-guard/4` to
/// `/5` bump blocked on another pane's uncommitted `scripts/evidence.py`.
#[test]
fn the_line_count_covenant_is_disclosed_by_the_walk_that_enforces_it() {
    let root = fln_conformance::checked_workspace_root!();
    let outcome = structure_guard::checks::run(&root).expect("structure-guard setup");
    let graph_text = std::fs::read_to_string(root.join("ci/WORKSPACE_GRAPH.txt"))
        .expect("ci/WORKSPACE_GRAPH.txt must be readable");
    let declared = structure_guard::graph::parse(&graph_text)
        .expect("the reviewed workspace graph must parse")
        .covenants;
    let human = structure_guard::report::render_human(&root.display().to_string(), &outcome);

    if let Err(reason) = judge_covenant_disclosure(&declared, &outcome.covenants, &human) {
        panic!(
            "the line-count covenant is not disclosed by the walk that enforces it ({reason}). \
             A covenant whose number is invisible is a wall, not a gauge, and the last time it \
             was invisible two people independently published the raw `wc -l` count instead \
             (franken_lean-kernel-loc-covenant-not-disclosed-t0g7). declared={declared:?} \
             measured={:?}",
            outcome.covenants
        );
    }
}

/// Every arm above kills a mutation, each gutted independently, and the one mutant that
/// cannot be planted is named rather than omitted.
#[test]
fn the_covenant_disclosure_guard_kills_each_mutation_it_claims_to() {
    let root = fln_conformance::checked_workspace_root!();
    let outcome = structure_guard::checks::run(&root).expect("structure-guard setup");
    let graph_text = std::fs::read_to_string(root.join("ci/WORKSPACE_GRAPH.txt"))
        .expect("ci/WORKSPACE_GRAPH.txt must be readable");
    let declared = structure_guard::graph::parse(&graph_text)
        .expect("the reviewed workspace graph must parse")
        .covenants;
    let human = structure_guard::report::render_human(&root.display().to_string(), &outcome);
    let measured = outcome.covenants.clone();

    // The unmutated control, judged first, or every mutant below dies on a broken baseline.
    assert_eq!(
        judge_covenant_disclosure(&declared, &measured, &human),
        Ok(()),
        "the unmutated covenant disclosure must hold. declared={declared:?} measured={measured:?}"
    );
    let first = measured.first().expect("at least one covenant").clone();

    let with = |f: fn(&mut structure_guard::checks::CovenantFact)| {
        let mut m = measured.clone();
        f(&mut m[0]);
        m
    };

    // (mutant, declared, measured, human, expected reason) — one gut each.
    let cases: Vec<(
        &str,
        _,
        Vec<structure_guard::checks::CovenantFact>,
        String,
        String,
    )> = vec![
        (
            "counter-returned-nothing",
            declared.clone(),
            Vec::new(),
            human.clone(),
            "no-covenant-measured".to_owned(),
        ),
        (
            "counter-returned-zero-lines",
            declared.clone(),
            with(|c| c.loc = 0),
            human.clone(),
            format!("covenant-counted-zero:{}", first.crate_name),
        ),
        (
            "declared-limit-vanished",
            declared.clone(),
            with(|c| c.limit = 0),
            human.clone(),
            format!(
                "limit-disagrees-with-declaration:{}:0-vs-{}",
                first.crate_name, first.limit
            ),
        ),
        (
            "a-declared-covenant-was-never-walked",
            {
                let mut d = declared.clone();
                d.insert("fln-checker".to_owned(), 4000);
                d
            },
            measured.clone(),
            human.clone(),
            "declared-covenant-not-measured:fln-checker".to_owned(),
        ),
        (
            "a-cap-nobody-reviewed",
            std::collections::BTreeMap::new(),
            measured.clone(),
            human.clone(),
            "no-covenant-declared".to_owned(),
        ),
        (
            "disclosure-dropped-the-number",
            declared.clone(),
            measured.clone(),
            human.replace("line-count-covenant", "line-count-covenant-suppressed"),
            format!("disclosure-omits-measurement:{}", first.crate_name),
        ),
        (
            "disclosure-shows-a-different-number",
            declared.clone(),
            measured.clone(),
            human.replace(
                &format!("loc={}", first.loc),
                &format!("loc={}", first.loc + 1),
            ),
            format!("disclosure-omits-measurement:{}", first.crate_name),
        ),
    ];

    for (name, m_declared, m_measured, m_human, expected) in &cases {
        let moved = *m_declared != declared || *m_measured != measured || *m_human != human;
        assert!(
            moved,
            "mutant {name} is identical to the unmutated base, so it did not apply and \
             scoring it proves nothing"
        );
        let verdict = judge_covenant_disclosure(m_declared, m_measured, m_human);
        assert_eq!(
            verdict.as_ref().map_err(String::as_str),
            Err(expected.as_str()),
            "mutant {name} was not killed for its stated reason. A rig accepting any failure \
             would score a mutant killed by an arm that had stopped testing the property"
        );
    }

    // THE MUTANT THAT CANNOT BE PLANTED AT THIS LEVEL, made plantable one level up.
    //
    // The bead asks for a mutant that moves the real count without moving the disclosure.
    // It does not exist here: `loc` is one binding, produced once by `count_loc` inside the
    // enforcing walk and read twice. No forged `CovenantFact` can separate them, because
    // separating them would require a SECOND counter — which is precisely the defect this
    // repository keeps filing (a re-implementation of a predicate beside the original) and
    // precisely what AGENTS.md refuses for the closure-exempt guard.
    //
    // So the mutant is planted where it could actually reappear: the source. Exactly one
    // call site may exist. A second one is the moment two numbers become possible.
    let checks_src = std::fs::read_to_string(root.join("tools/structure-guard/src/checks.rs"))
        .expect("checks.rs must be readable");
    let call_sites = checks_src
        .lines()
        .filter(|line| line.contains("count_loc(") && !line.trim_start().starts_with("fn "))
        .filter(|line| !line.trim_start().starts_with("//"))
        .count();
    assert_eq!(
        call_sites, 1,
        "there must be exactly one `count_loc` call site, so the enforced number and the \
         disclosed number cannot be two numbers. Found {call_sites}. A second counter is the \
         only way the bead's 'move the count without moving the disclosure' mutant could ever \
         be planted again, and it is how 6,535 and 6,382 were published against covenants of \
         5,416 and 5,379"
    );
    // And the scan must not be vacuous: a renamed counter would make the count 0 and read as
    // "no second producer" rather than "the producer is gone".
    assert!(
        checks_src.contains("fn count_loc("),
        "the counter's definition is gone, so the call-site scan above measured nothing and \
         reported agreement"
    );
}
