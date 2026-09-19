//! Installed source checking: collections remain proofs, never host evaluation.
#![forbid(unsafe_code)]
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};

static NEXT: AtomicUsize = AtomicUsize::new(0);
fn source(text: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "fln-native-collection-notation-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let path = directory.join("Collections.lean");
    std::fs::write(&path, text).unwrap();
    path
}
fn run(paths: &[&PathBuf], flags: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .args(flags)
        .args(paths)
        .output()
        .unwrap()
}

#[test]
fn installed_checker_accepts_recursive_and_cross_universe_collection_proofs() {
    let text = include_str!("../../../examples/native_collection_notation.lean");
    let path = source(text);
    let output = run(&[&path], &[]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let json = String::from_utf8(output.stdout).unwrap();
    for field in [
        "\"schema\":\"fln.source-check/1\"",
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"commands\":11",
        "\"theorems\":8",
        "\"executed\":false",
    ] {
        assert!(json.contains(field), "{json}");
    }
    assert_eq!(std::fs::read(&path).unwrap(), text.as_bytes());
    assert_eq!(
        std::fs::read_dir(path.parent().unwrap()).unwrap().count(),
        1
    );
}

#[test]
fn invalid_collection_suffixes_do_not_emit_partial_success_or_poison_a_later_run() {
    let library =
        source("def first (xs : List Nat) : Nat := match xs with | [] => 0 | x :: _ => x");
    let invalid = source("theorem bad : first [7] = 8 := by rfl");
    let valid = source("theorem good : first [7] = 7 := by rfl");
    for suffix in [&invalid, &valid, &invalid, &valid] {
        let output = run(&[&library, suffix], &[]);
        if suffix == &valid {
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(output.stderr.is_empty());
            assert!(
                String::from_utf8(output.stdout)
                    .unwrap()
                    .contains("\"theorems\":1")
            );
        } else {
            assert!(!output.status.success());
            assert!(output.stdout.is_empty());
            let error = String::from_utf8(output.stderr).unwrap();
            assert!(
                error.contains("\"outcome\":\"kernel-rejection\""),
                "{error}"
            );
            assert!(!error.contains("\"outcome\":\"complete\""));
        }
    }
}

#[test]
fn resource_refusal_is_not_reported_as_a_failed_collection_theorem() {
    let path = source(include_str!(
        "../../../examples/native_collection_notation.lean"
    ));
    let output = run(&[&path], &["--max-bytes=8"]);
    assert_eq!(output.status.code(), Some(3));
    assert!(output.stdout.is_empty());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("\"authority\":false"), "{error}");
    assert!(!error.contains("\"outcome\":\"kernel-rejection\""));
    assert!(run(&[&path], &[]).status.success());
}
