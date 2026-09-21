//! Quotient source programs use the installed checking path, not VM shortcuts.
#![forbid(unsafe_code)]
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn source_file(source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-quotients-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("source.lean");
    std::fs::write(&path, source).unwrap();
    path
}
fn check(paths: &[&Path]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .args(paths)
        .output()
        .unwrap()
}
fn example() -> PathBuf {
    fln_core::checked_workspace_root!().join("examples/native_quotients.lean")
}
#[test]
fn installed_checker_checks_quotient_proofs_and_computes_expected_types() {
    let example = example();
    let original = std::fs::read(&example).unwrap();
    let output = check(&[&example]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let json = String::from_utf8(output.stdout).unwrap();
    for required in [
        "\"schema\":\"fln.source-check/1\"",
        "\"authority\":true",
        "\"commands\":7",
        "\"theorems\":4",
        "\"executed\":false",
    ] {
        assert!(json.contains(required), "{json}");
    }
    assert_eq!(std::fs::read(example).unwrap(), original);
}
#[test]
fn invalid_quotient_proof_suffix_never_reports_partial_success() {
    let prefix = example();
    let original = std::fs::read(&prefix).unwrap();
    for bad in [
        "def bad : Nat := Quot.lift (fun (n : Nat) => n) _ (Quot.mk (fun (a b : Nat) => a = b) 7)",
        "theorem bad : 1 = 2 := by rfl",
    ] {
        let suffix = source_file(bad);
        let result = check(&[&prefix, &suffix]);
        assert!(!result.status.success(), "{bad}");
        assert!(result.stdout.is_empty());
        assert!(!result.stderr.is_empty());
        assert_eq!(std::fs::read(&prefix).unwrap(), original);
        assert_eq!(std::fs::read(&suffix).unwrap(), bad.as_bytes());
    }
}
