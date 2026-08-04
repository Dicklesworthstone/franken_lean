//! R15 convergence-governance model cells (bead franken_lean-convergence-wip-governance-149).
//!
//! The policy judge is a sealed Python command because its real surface is `br`/`bv` JSON, not
//! the Rust crate graph.  Its deterministic model and mutation cases remain a plain `cargo test`
//! obligation: a passing exit code with no named cells would be a launcher test, not governance
//! evidence.  The command's live mode is separately read-only and double-snapshots `br` state.

#![forbid(unsafe_code)]

use std::process::Command;

#[test]
fn convergence_policy_model_and_mutation_cells_are_live() {
    let root = fln_conformance::checked_workspace_root!();
    let script = root.join("scripts/convergence_governance.py");
    assert!(
        script.is_file(),
        "R15 policy command must remain checked in"
    );
    let output = Command::new("python3")
        .args(["-I", "-S", "-B"])
        .arg(&script)
        .arg("--self-test")
        .current_dir(root)
        .output()
        .expect("sealed Python interpreter is available");
    assert_eq!(
        output.status.code(),
        Some(0),
        "R15 model/mutation cells failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    assert!(
        String::from_utf8_lossy(&output.stdout).contains("29 named model/mutation cells passed"),
        "the self-test must name its exercised cells; a bare exit zero is not evidence"
    );
}

/// The production command stays read-only: it consumes real `br` JSON and optional `bv` robot
/// telemetry, but its two tracker invocations carry both no-auto flags.  This runs only in the
/// main checkout, whose real `.beads` authority RCH clean overlays intentionally exclude.
#[test]
fn real_workspace_policy_report_is_complete_and_read_only() {
    let root = fln_conformance::checked_workspace_root!();
    let script = root.join("scripts/convergence_governance.py");
    let output = Command::new("python3")
        .args(["-I", "-S", "-B"])
        .arg(&script)
        .args(["--root", ".", "--at", "2026-08-04T10:10:00Z", "--check"])
        .current_dir(root)
        .output()
        .expect("sealed Python interpreter is available");
    assert_eq!(
        output.status.code(),
        Some(0),
        "the real R15 report must reject cap violations, expired adoption rows, stale snapshots, \
         and unclassified active work rather than granting an admission:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("convergence-governance: complete")
            && stdout.contains(r#""schema":"fln.convergence-governance-report/1""#),
        "the human recommendation and its schema-versioned NDJSON record must both be present:\n{stdout}"
    );
}
