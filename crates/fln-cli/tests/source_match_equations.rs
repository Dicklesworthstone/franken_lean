//! Installed named match equations cross real source admission.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn file(text: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-match-equations-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("Proof.lean");
    std::fs::write(&path, text).unwrap();
    path
}
fn check(paths: &[&PathBuf]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .args(paths)
        .output()
        .unwrap()
}
#[test]
fn named_equations_compute_and_dependent_results_pass_both_checkers() {
    let source = include_str!("../../../examples/native_match_equations.lean");
    let path = file(source);
    let output = check(&[&path]);
    assert!(output.status.success(), "{:?}", output);
    assert!(output.stderr.is_empty());
    let json = String::from_utf8(output.stdout).unwrap();
    for expected in [
        "\"schema\":\"fln.source-check/1\"",
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"commands\":7",
        "\"theorems\":3",
        "\"executed\":false",
    ] {
        assert!(json.contains(expected), "{json}");
    }
    assert_eq!(std::fs::read_to_string(path).unwrap(), source);
}
#[test]
fn impossible_evidence_and_bad_unselected_branches_are_refused() {
    for source in [
        "theorem bad : 0 = 1 := match h : Nat.zero with | Nat.zero => h | Nat.succ k => rfl",
        "def bad : Nat := match h : Nat.zero with | Nat.zero => 0 | Nat.succ k => h",
        "def missing (n : Nat) : Nat := match h : n with | Nat.zero => 0",
        "def leak (n : Nat) : Nat := let k : Nat := match h : n with | Nat.zero => 0 | Nat.succ k => k; h",
    ] {
        let path = file(source);
        let output = check(&[&path]);
        assert!(!output.status.success(), "{source}");
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
        assert_eq!(std::fs::read_to_string(path).unwrap(), source);
    }
}
#[test]
fn a_bad_suffix_has_no_partial_success_and_recovery_is_deterministic() {
    let source = include_str!("../../../examples/native_match_equations.lean");
    let path = file(source);
    let bad = file("theorem bad : predecessor 5 = 6 := by rfl");
    let before = check(&[&path]);
    assert!(before.status.success());
    let refused = check(&[&path, &bad]);
    assert!(!refused.status.success());
    assert!(refused.stdout.is_empty());
    assert!(String::from_utf8_lossy(&refused.stderr).contains("\"outcome\":\"kernel-rejection\""));
    let after = check(&[&path]);
    assert!(after.status.success());
    assert_eq!(before.stdout, after.stdout);
    assert_eq!(std::fs::read_to_string(path).unwrap(), source);
}
