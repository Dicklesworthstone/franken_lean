//! The workspace-graph snapshot test (bead fln-8mj): the REAL repository must be
//! structurally clean against its reviewed acknowledgment files. Any new crate or
//! dependency edge fails this test until `ci/WORKSPACE_GRAPH.txt` is edited in the
//! same change — that edit is the review surface.

#![forbid(unsafe_code)]

use std::path::Path;
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
    assert!(
        lines
            .iter()
            .all(|line| line.contains("\"schema\":\"structure-guard/4\"")),
        "robot output used the wrong schema: {stdout}"
    );
}

#[test]
fn real_workspace_is_structurally_clean() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
    let outcome = structure_guard::checks::run(root).expect("structure-guard setup");
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
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
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
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
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
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
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
#[test]
fn the_deferred_d18_product_half_stays_owned_while_the_scan_is_vacuous() {
    const REMAINDER: &str = "fln-d18-product-half-rgsg";
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
    let outcome = structure_guard::checks::run(root).expect("structure-guard setup");

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

    if outcome.mode_closure.is_vacuous() {
        assert!(
            !matches!(status.as_str(), "closed" | "tombstone"),
            "the registered D18 scan is still vacuous — {} product roots, {} closures \
             scanned, so no closure has ever been submitted to the core — while {REMAINDER}, \
             which owns making it non-vacuous, is {status}. Closing the remainder in this \
             state books the gap as done: franken_lean-r2st was split on the condition that \
             this half stay open with its gap intact. Either reopen it, or land the product \
             half so the scan traverses a real closure and this check stops applying.",
            outcome.mode_closure.product_roots,
            outcome.mode_closure.closures_scanned,
        );
    }
}

#[test]
fn robot_rejects_an_unbound_rustc_override_without_executing_it() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root");
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
    }
}
