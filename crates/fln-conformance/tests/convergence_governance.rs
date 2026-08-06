//! R15 convergence-governance model cells (bead franken_lean-convergence-wip-governance-149).
//!
//! The policy judge is a sealed Python command because its real surface is `br`/`bv` JSON, not
//! the Rust crate graph.  Its deterministic model and mutation cases remain a plain `cargo test`
//! obligation: a passing exit code with no named cells would be a launcher test, not governance
//! evidence.  The command's live mode is separately read-only and double-snapshots `br` state.

#![forbid(unsafe_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

fn executable_permissions(metadata: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        metadata.permissions().mode() & 0o111 != 0
    }
    #[cfg(not(unix))]
    {
        true
    }
}

fn canonical_executable(path: &Path) -> Option<PathBuf> {
    let path = fs::canonicalize(path).ok()?;
    let metadata = fs::metadata(&path).ok()?;
    (metadata.is_file() && executable_permissions(&metadata)).then_some(path)
}

fn operator_executable(name: &str, explicit_env: &str) -> PathBuf {
    if let Some(explicit) = std::env::var_os(explicit_env) {
        let explicit = PathBuf::from(explicit);
        return canonical_executable(&explicit).unwrap_or_else(|| {
            panic!(
                "{explicit_env} does not name a real executable: {}",
                explicit.display()
            )
        });
    }
    if let Some(path) = std::env::var_os("PATH") {
        for directory in std::env::split_paths(&path) {
            if let Some(executable) = canonical_executable(&directory.join(name)) {
                return executable;
            }
        }
    }
    if let Some(home) = std::env::var_os("HOME")
        && let Some(executable) =
            canonical_executable(&PathBuf::from(home).join(".local/bin").join(name))
    {
        return executable;
    }
    panic!("cannot resolve operator executable {name}; set {explicit_env} to its absolute path");
}

fn live_policy(root: &Path, python: &Path, isolated_path: &Path, br: Option<&Path>) -> Output {
    let script = root.join("scripts/convergence_governance.py");
    let mut command = Command::new(python);
    command
        .args(["-I", "-S", "-B"])
        .arg(&script)
        .args(["--root", ".", "--at", "2026-08-04T10:10:00Z", "--check"])
        .env("PATH", isolated_path)
        .current_dir(root);
    if let Some(br) = br {
        command.arg("--br-bin").arg(br);
    }
    command
        .output()
        .expect("sealed Python interpreter is available")
}

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
        String::from_utf8_lossy(&output.stdout).contains("30 named model/mutation cells passed"),
        "the self-test must name its exercised cells; a bare exit zero is not evidence"
    );
}

/// The production command stays read-only: it consumes real `br` JSON and optional `bv` robot
/// telemetry, but its two tracker invocations carry both no-auto flags.  This runs only in the
/// main checkout, whose real `.beads` authority RCH clean overlays intentionally exclude.
#[test]
fn real_workspace_policy_report_is_complete_and_read_only() {
    let root = fln_conformance::checked_workspace_root!();
    let python = operator_executable("python3", "FLN_PYTHON_BIN");
    let br = operator_executable("br", "FLN_BR_BIN");
    let isolated_path = root.join("target/fln-wuu5-path-must-stay-absent");
    assert!(
        !isolated_path.exists(),
        "the sealed-PATH control must name no directory, otherwise a bare br could resolve"
    );

    let bare = live_policy(&root, &python, &isolated_path, None);
    assert_eq!(
        bare.status.code(),
        Some(2),
        "the negative control must prove bare br is unavailable under the isolated PATH:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&bare.stdout),
        String::from_utf8_lossy(&bare.stderr),
    );
    assert!(
        String::from_utf8_lossy(&bare.stdout).contains("command-unavailable: br list"),
        "the negative control failed for a reason other than bare br lookup:\n{}",
        String::from_utf8_lossy(&bare.stdout)
    );

    let output = live_policy(&root, &python, &isolated_path, Some(&br));
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

#[test]
fn explicit_br_authority_refuses_every_non_executable_shape_before_live_commands() {
    let root = fln_conformance::checked_workspace_root!();
    let python = operator_executable("python3", "FLN_PYTHON_BIN");
    let isolated_path = root.join("target/fln-wuu5-path-must-stay-absent");
    let absent = root.join("target/fln-wuu5-absent-br");
    assert!(
        !absent.exists(),
        "the absent-path cell needs an absent path"
    );
    let cases = [
        (PathBuf::from("br"), "br-bin-not-absolute"),
        (absent, "br-bin-unreadable"),
        (root.to_path_buf(), "br-bin-not-regular-file"),
        (root.join("Cargo.toml"), "br-bin-not-executable"),
    ];
    for (candidate, reason) in cases {
        let output = live_policy(&root, &python, &isolated_path, Some(&candidate));
        assert_eq!(
            output.status.code(),
            Some(2),
            "invalid explicit br authority {} was admitted:\nstdout:\n{}\nstderr:\n{}",
            candidate.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr),
        );
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains(reason) && !stdout.contains("command-unavailable"),
            "invalid explicit br authority {} had the wrong typed refusal; expected {reason}:\n{stdout}",
            candidate.display()
        );
    }
}
