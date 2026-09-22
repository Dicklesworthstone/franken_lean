//! Installed proof-erasure consumers and independent serialized FLBC replay.
#![forbid(unsafe_code)]
use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-proof-runtime-{}-{}",
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
fn checked_proof_computations_are_not_native_runtime_work() {
    personalities_and_replay(include_str!("../../../examples/native_proof_erasure.lean"));
}
#[test]
fn dependent_proof_fields_and_callable_slots_replay_without_source() {
    personalities_and_replay(include_str!("../../../examples/native_proof_data.lean"));
}
#[test]
fn imported_defaults_recover_and_invalid_proofs_publish_no_artifacts() {
    let dir = directory();
    let dependency = dir.join("Certified.lean");
    let entry = dir.join("Main.lean");
    let definitions = include_str!("../../../examples/native_proof_data.lean")
        .split("#eval")
        .next()
        .unwrap();
    std::fs::write(&dependency, definitions).unwrap();
    let source = "import Certified\n#eval answer.callback answer.value answer.proof\n";
    std::fs::write(&entry, source).unwrap();
    let artifact = dir.join("good.flbc");
    let output = run(&entry, &artifact);
    assert!(output.status.success(), "{output:?}");
    replay(&artifact);
    let before = std::fs::read(&artifact).unwrap();
    for invalid in [
        format!("{definitions}\ntheorem invalidUnusedProof : 0 = 1 := by rfl\n"),
        definitions.replace("value = value := by rfl", "0 = 1 := by rfl"),
    ] {
        std::fs::write(&dependency, invalid).unwrap();
        let failed = dir.join("failed.flbc");
        let output = run(&entry, &failed);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(!output.stderr.is_empty());
        assert!(!failed.exists());
        assert_eq!(before, std::fs::read(&artifact).unwrap());
    }
    std::fs::write(&dependency, definitions).unwrap();
    let recovered = dir.join("recovered.flbc");
    assert!(run(&entry, &recovered).status.success());
    assert_eq!(before, std::fs::read(&recovered).unwrap());
    assert_eq!(source, std::fs::read_to_string(&entry).unwrap());
    assert_eq!(definitions, std::fs::read_to_string(&dependency).unwrap());
}
