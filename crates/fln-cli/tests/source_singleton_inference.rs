//! Real installed source checking for singleton-projection inference.
#![forbid(unsafe_code)]

use std::{
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);

fn file(text: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "fln-singleton-inference-{}-{}",
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
fn installed_binary_infers_wrappers_and_record_valued_functions() {
    let source = include_str!("../../../examples/native_singleton_inference.lean");
    let path = file(source);
    let output = check(&[&path]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    let report = String::from_utf8(output.stdout).unwrap();
    for required in [
        "\"schema\":\"fln.source-check/1\"",
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"commands\":7",
        "\"theorems\":2",
        "\"executed\":false",
    ] {
        assert!(report.contains(required), "{report}");
    }
    assert_eq!(std::fs::read_to_string(path).unwrap(), source);
}

#[test]
fn inference_does_not_fabricate_classes_or_unselected_fields() {
    for source in [
        "class Dictionary where\n  value : Nat\ndef recover {d : Dictionary} (h : d.value = 7) : Dictionary := d\ndef bad : Dictionary := recover (rfl : 7 = 7)",
        "structure Pair where\n  left : Nat\n  right : Nat\ndef recover {p : Pair} (h : p.left = 7) : Pair := p\ndef bad : Pair := recover (rfl : 7 = 7)",
    ] {
        let path = file(source);
        let output = check(&[&path]);
        assert!(!output.status.success(), "unexpected acceptance: {source}");
        assert!(output.stdout.is_empty());
        assert!(String::from_utf8_lossy(&output.stderr).contains("\"authority\":false"));
        assert_eq!(std::fs::read_to_string(path).unwrap(), source);
    }
}

#[test]
fn a_false_suffix_emits_no_partial_success_and_recovery_is_repeatable() {
    let source = include_str!("../../../examples/native_singleton_inference.lean");
    let path = file(source);
    let bad = file("theorem bad : inferred.value = 8 := by rfl");
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
    assert_eq!(
        std::fs::read_to_string(bad).unwrap(),
        "theorem bad : inferred.value = 8 := by rfl"
    );
}
