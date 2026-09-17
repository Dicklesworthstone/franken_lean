//! Installed-command checks of real hypothesis transports, not an execution mock.
#![forbid(unsafe_code)]

use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
const EXAMPLE: &str = include_str!("../../../examples/native_hypothesis_rewriting.lean");

fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-hypothesis-rewriting-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn check(paths: &[&Path]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .args(paths)
        .output()
        .unwrap()
}

#[test]
fn installed_binary_checks_the_hypothesis_rewriting_example_without_artifacts() {
    let dir = directory();
    let path = dir.join("proofs.lean");
    std::fs::write(&path, EXAMPLE).unwrap();
    let output = check(&[&path]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let json = String::from_utf8(output.stdout).unwrap();
    for expected in [
        "\"schema\":\"fln.source-check/1\"",
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"commands\":8",
        "\"theorems\":6",
        "\"executed\":false",
    ] {
        assert!(json.contains(expected), "{json}");
    }
    assert!(output.stderr.is_empty());
    assert_eq!(std::fs::read(&path).unwrap(), EXAMPLE.as_bytes());
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 1);
}

#[test]
fn a_bad_suffix_cannot_publish_valid_hypothesis_transports_or_contaminate_retry() {
    let dir = directory();
    let prefix = dir.join("proofs.lean");
    let suffix = dir.join("later.lean");
    std::fs::write(&prefix, EXAMPLE).unwrap();
    for source in [
        "theorem bad : 1 = 2 := by rfl",
        "theorem bad (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by rewrite [h] at hx missing; exact hx",
        "theorem bad (P : Prop) (p : P) (x y : Nat) (h : P -> x = y) (Q : Nat -> Prop) (hx : Q x) : Q y := by simp only [h] at hx; exact hx",
    ] {
        std::fs::write(&suffix, source).unwrap();
        let output = check(&[&prefix, &suffix]);
        assert!(!output.status.success(), "{source}");
        assert!(output.stdout.is_empty(), "no partial-success receipt");
        let diagnostic = String::from_utf8(output.stderr).unwrap();
        assert!(!diagnostic.is_empty());
        assert!(!diagnostic.contains("\"outcome\":\"complete\""));
        assert_eq!(std::fs::read_to_string(&suffix).unwrap(), source);
        let repaired = check(&[&prefix]);
        assert!(repaired.status.success(), "{diagnostic}");
        assert!(repaired.stderr.is_empty());
    }
    assert_eq!(std::fs::read_to_string(&prefix).unwrap(), EXAMPLE);
    assert_eq!(std::fs::read_dir(dir).unwrap().count(), 2);
}
