//! Installed indexed-data execution, import recovery, and independent FLBC replay.
#![forbid(unsafe_code)]
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-indexed-runtime-{}-{}",
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
fn indexed_mapping_executes_through_both_personalities_and_serialized_replay() {
    personalities_and_replay(include_str!(
        "../../../examples/native_indexed_vectors.lean"
    ));
}
#[test]
fn imported_indexed_families_reject_wrong_indices_without_publishing_artifacts() {
    let dir = directory();
    let dependency = dir.join("Vector.lean");
    let entry = dir.join("Main.lean");
    let example = include_str!("../../../examples/native_indexed_vectors.lean");
    let (definitions, expression) = example.split_once("#eval").unwrap();
    std::fs::write(&dependency, definitions).unwrap();
    let source = format!("import Vector\n#eval {expression}");
    std::fs::write(&entry, &source).unwrap();
    let artifact = dir.join("good.flbc");
    let output = run(&entry, &artifact);
    assert!(output.status.success(), "{output:?}");
    replay(&artifact);
    let before = std::fs::read(&artifact).unwrap();
    for invalid in [
        format!("{definitions}\ndef invalidLength : Vec Nat 1 := Vec.nil\n"),
        format!("{definitions}\ntheorem invalidEvidence : 0 = 1 := by rfl\n"),
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
    assert!(run(&entry, &recovered).status.success());
    assert_eq!(before, std::fs::read(&recovered).unwrap());
    assert_eq!(source, std::fs::read_to_string(&entry).unwrap());
}

#[test]
fn refined_recursive_matches_and_transports_have_independent_bytecode_replay() {
    personalities_and_replay(include_str!(
        "../../../examples/native_equality_transport.lean"
    ));
}
#[test]
fn imported_transports_keep_false_evidence_out_of_executable_artifacts() {
    let dir = directory();
    let dependency = dir.join("Transport.lean");
    let entry = dir.join("Main.lean");
    let definition = "def transport (a b : Nat) (h : a = b) (x : Nat) : Nat := Eq.rec (motive := fun k proof => Nat) x h\n";
    std::fs::write(&dependency, definition).unwrap();
    let source = "import Transport\n#eval transport 1 1 (by rfl) 42";
    std::fs::write(&entry, source).unwrap();
    let artifact = dir.join("good.flbc");
    assert!(run(&entry, &artifact).status.success());
    replay(&artifact);
    let before = std::fs::read(&artifact).unwrap();
    std::fs::write(&entry, source.replace("transport 1 1", "transport 1 2")).unwrap();
    let failed = dir.join("failed.flbc");
    let output = run(&entry, &failed);
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty());
    assert!(!failed.exists());
    assert_eq!(before, std::fs::read(&artifact).unwrap());
    std::fs::write(&entry, source).unwrap();
    let recovered = dir.join("recovered.flbc");
    assert!(run(&entry, &recovered).status.success());
    assert_eq!(before, std::fs::read(&recovered).unwrap());
}
