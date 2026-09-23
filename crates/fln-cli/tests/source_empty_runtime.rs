//! Installed empty-elimination execution, import recovery, and independent FLBC replay.
#![forbid(unsafe_code)]
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-empty-runtime-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    path
}
fn run(source: &Path, artifact: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(artifact)
        .arg(source)
        .output()
        .unwrap()
}
fn replay(artifact: &Path) {
    let before = std::fs::read(artifact).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(artifact)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"returnValue\":42"));
    assert_eq!(before, std::fs::read(artifact).unwrap());
}
fn personalities_and_replay(source: &str) {
    let path = directory().join("Main.lean");
    let artifact = path.with_extension("flbc");
    std::fs::write(&path, source).unwrap();
    let output = run(&path, &artifact);
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"finalValue\":42"));
    replay(&artifact);
    let lean = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(lean.status.success(), "{lean:?}");
    assert!(lean.stderr.is_empty(), "{lean:?}");
    assert_eq!(lean.stdout, b"42\n");
    assert_eq!(source, std::fs::read_to_string(&path).unwrap());
}
#[test]
fn checked_empty_branches_execute_through_both_personalities_and_serialized_replay() {
    personalities_and_replay(include_str!(
        "../../../examples/native_empty_elimination.lean"
    ));
}

#[test]
fn imported_empty_elimination_rejects_false_evidence_and_recovers_deterministically() {
    let dir = directory();
    let dependency = dir.join("Empty.lean");
    let entry = dir.join("Main.lean");
    let example = include_str!("../../../examples/native_empty_elimination.lean");
    let (definitions, expression) = example.split_once("#eval").unwrap();
    std::fs::write(&dependency, definitions).unwrap();
    let source = format!("import Empty\n#eval {expression}");
    std::fs::write(&entry, &source).unwrap();
    let artifact = dir.join("good.flbc");
    let output = run(&entry, &artifact);
    assert!(output.status.success(), "{output:?}");
    replay(&artifact);
    let before = std::fs::read(&artifact).unwrap();
    for invalid in [
        format!("{definitions}\ndef invalid : Nat := False.elim True.intro\n"),
        format!("{definitions}\ndef invalidHead : Nat := first 0 Vec.nil (by decide)\n"),
        format!("{definitions}\ndef invalidEvidence : False := by rfl\n"),
    ] {
        std::fs::write(&dependency, invalid).unwrap();
        let failed = dir.join("failed.flbc");
        let output = run(&entry, &failed);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(!failed.exists());
        assert_eq!(before, std::fs::read(&artifact).unwrap());
    }
    std::fs::write(&dependency, definitions).unwrap();
    let recovered = dir.join("recovered.flbc");
    let output = run(&entry, &recovered);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(before, std::fs::read(&recovered).unwrap());
    assert_eq!(source, std::fs::read_to_string(&entry).unwrap());
    replay(&recovered);
}
