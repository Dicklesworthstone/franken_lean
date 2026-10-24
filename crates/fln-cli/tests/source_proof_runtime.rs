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
/// The pinned `lean` v4.32.0's stdout on `examples/native_proof_erasure.lean` (2026-10-22), with
/// `{path}` for the file as the command line names it.
const PROOF_ERASURE_LEAN: &str = "{path}:5:0: warning: Definition `evidence` is a proposition; use `theorem` instead of `def`\n\nNote: This linter can be disabled with `set_option linter.defProp false`\n{path}:9:10: warning: Variable name `h` is not explicitly referenced.\n\nThe binding can be removed (if unused) or named `_` (if used implicitly).\n\nNote: This linter can be disabled with `set_option linter.unusedVariables false`\n42\n";

/// Run both personalities on `source`, replay the artifact, and compare the `lean` door's stdout
/// with the pin's, `expected` (`{path}` stands for the file).
fn personalities_and_replay(source: &str, expected: &str) {
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
    assert_eq!(
        String::from_utf8(lean.stdout).unwrap(),
        expected.replace("{path}", &path.display().to_string())
    );
    assert_eq!(source, std::fs::read_to_string(&path).unwrap());
}
#[test]
fn checked_proof_computations_are_not_native_runtime_work() {
    personalities_and_replay(
        include_str!("../../../examples/native_proof_erasure.lean"),
        PROOF_ERASURE_LEAN,
    );
}
#[test]
fn dependent_proof_fields_and_callable_slots_replay_without_source() {
    personalities_and_replay(
        include_str!("../../../examples/native_proof_data.lean"),
        "42\n",
    );
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
