//! Real native CLI execution, imports, and portable bytecode for function-bearing data.
#![forbid(unsafe_code)]
use std::{
    path::PathBuf,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-closure-data-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    path
}
fn run(path: &PathBuf, artifact: &PathBuf) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(artifact)
        .arg(path)
        .output()
        .unwrap()
}
fn replay(artifact: &PathBuf) {
    let bytes = std::fs::read(artifact).unwrap();
    let result = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(artifact)
        .output()
        .unwrap();
    assert!(result.status.success(), "{result:?}");
    assert!(result.stderr.is_empty());
    assert!(String::from_utf8_lossy(&result.stdout).contains("\"returnValue\":42"));
    assert_eq!(std::fs::read(artifact).unwrap(), bytes);
}
#[test]
fn installed_personalities_and_serialized_bytecode_execute_stored_functions() {
    let source = include_str!("../../../examples/native_closure_data.lean");
    let path = directory().join("Main.lean");
    let artifact = path.with_extension("flbc");
    std::fs::write(&path, source).unwrap();
    let output = run(&path, &artifact);
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty());
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"finalValue\":42"));
    replay(&artifact);
    let lean = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(lean.status.success(), "{lean:?}");
    assert!(lean.stderr.is_empty());
    assert_eq!(lean.stdout, b"42\n42\n42\n");
    assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
}
#[test]
fn imported_method_payloads_reject_false_suffixes_without_publishing_artifacts() {
    let dir = directory();
    let dependency = dir.join("Handlers.lean");
    let entry = dir.join("Main.lean");
    let source = "structure Handler where\n  run : Nat -> Nat\ndef make (offset : Nat) : Handler := { run := fun n => n + offset }\n";
    std::fs::write(&dependency, source).unwrap();
    let program = "import Handlers\n#eval (make 2).run 40\n";
    std::fs::write(&entry, program).unwrap();
    let artifact = dir.join("good.flbc");
    let output = run(&entry, &artifact);
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty());
    let bytes = std::fs::read(&artifact).unwrap();
    replay(&artifact);
    for suffix in [
        "theorem falseSuffix : 0 = 1 := by rfl",
        "def bad : Handler := { run := fun (n : Nat) => true }",
    ] {
        let text = format!("{program}\n{suffix}");
        std::fs::write(&entry, &text).unwrap();
        let failed = dir.join("failed.flbc");
        let output = run(&entry, &failed);
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
        assert!(!failed.exists());
        assert_eq!(std::fs::read(&artifact).unwrap(), bytes);
        assert_eq!(std::fs::read_to_string(&entry).unwrap(), text);
    }
    std::fs::write(&entry, program).unwrap();
    let recovered = run(&entry, &dir.join("recovered.flbc"));
    assert!(recovered.status.success(), "{recovered:?}");
    assert!(recovered.stderr.is_empty());
    assert_eq!(std::fs::read_to_string(&dependency).unwrap(), source);
}
