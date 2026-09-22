//! Installed source projection execution and independent serialized-bytecode replay.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn file(source: &str) -> PathBuf {
    let directory = std::env::temp_dir().join(format!(
        "fln-record-runtime-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let path = directory.join("records.lean");
    std::fs::write(&path, source).unwrap();
    path
}
#[test]
fn field_functions_and_record_updates_export_and_replay() {
    let source = include_str!("../../../examples/native_ground_projections.lean");
    let path = file(source);
    let artifact = path.with_extension("flbc");
    let result = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&artifact)
        .arg(&path)
        .output()
        .unwrap();
    assert!(result.status.success(), "{result:?}");
    assert!(result.stderr.is_empty());
    assert!(String::from_utf8_lossy(&result.stdout).contains("\"finalValue\":42"));
    let bytes = std::fs::read(&artifact).unwrap();
    let replay = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(&artifact)
        .output()
        .unwrap();
    assert!(replay.status.success(), "{replay:?}");
    assert!(replay.stderr.is_empty());
    assert!(String::from_utf8_lossy(&replay.stdout).contains("\"returnValue\":42"));
    let lean = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(lean.status.success(), "{lean:?}");
    assert!(lean.stderr.is_empty());
    assert_eq!(lean.stdout, b"42\n42\n");
    assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    assert_eq!(std::fs::read(&artifact).unwrap(), bytes);
}
#[test]
fn rejected_record_programs_emit_neither_results_nor_bytecode() {
    let source = include_str!("../../../examples/native_ground_projections.lean");
    for suffix in [
        "theorem falseSuffix : entry.count = 37 := by rfl",
        "def bad : Box Nat := { value := true }",
    ] {
        let text = format!("{source}\n{suffix}");
        let path = file(&text);
        let artifact = path.with_extension("flbc");
        let result = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&path)
            .output()
            .unwrap();
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        assert!(!result.stderr.is_empty());
        assert!(!artifact.exists());
        assert_eq!(std::fs::read_to_string(&path).unwrap(), text);
        std::fs::write(&path, source).unwrap();
        let recovered = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .arg(&path)
            .output()
            .unwrap();
        assert!(recovered.status.success(), "{recovered:?}");
        assert!(String::from_utf8_lossy(&recovered.stdout).contains("\"finalValue\":42"));
    }
}
