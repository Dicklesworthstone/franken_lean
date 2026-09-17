//! Installed source checking of dependent binders, not a simulated frontend.
#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn source_file(source: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-term-binders-{}-{}",
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

#[test]
fn installed_checker_accepts_the_complete_dependent_binder_example() {
    let example =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/native_term_binders.lean");
    let original = std::fs::read(&example).unwrap();
    let result = check(&[&example]);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(result.stderr.is_empty());
    let json = String::from_utf8(result.stdout).unwrap();
    for required in [
        "\"schema\":\"fln.source-check/1\"",
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"commands\":13",
        "\"theorems\":4",
        "\"executed\":false",
    ] {
        assert!(json.contains(required), "{json}");
    }
    assert_eq!(std::fs::read(&example).unwrap(), original);
}

#[test]
fn dependent_functions_are_reusable_across_source_files() {
    let prefix = source_file("def id : {A : Sort _} -> A -> A := fun x => x");
    let suffix = source_file(
        "def low : Nat := id 7\ndef high : Type := id Nat\ntheorem ok : low = 7 := by rfl",
    );
    let result = check(&[&prefix, &suffix]);
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(result.stderr.is_empty());
    let json = String::from_utf8(result.stdout).unwrap();
    assert!(json.contains("\"files\":2"), "{json}");
    assert!(json.contains("\"commands\":4"), "{json}");
    assert!(json.contains("\"executed\":false"), "{json}");
}

#[test]
fn invalid_binder_suffixes_do_not_emit_partial_success_or_change_sources() {
    let prefix = source_file("def id : {A : Type} -> A -> A := fun x => x");
    let before = std::fs::read(&prefix).unwrap();
    for bad in [
        "def bad : Nat -> Nat := fun (x : Bool) => 7",
        "def bad := fun (x : Nat) => _",
        "def bad (A : Type) := fun (A x : A) => x",
    ] {
        let suffix = source_file(bad);
        let result = check(&[&prefix, &suffix]);
        assert!(!result.status.success(), "{bad}");
        assert!(result.stdout.is_empty(), "{bad}");
        assert!(!result.stderr.is_empty(), "{bad}");
        assert_eq!(std::fs::read(&prefix).unwrap(), before);
        assert_eq!(std::fs::read(&suffix).unwrap(), bad.as_bytes());
        assert!(check(&[&prefix]).status.success());
    }
}
