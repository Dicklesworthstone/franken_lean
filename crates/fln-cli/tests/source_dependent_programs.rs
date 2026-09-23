//! Default-budget dependent source execution, checked imports, and standalone FLBC.
#![forbid(unsafe_code)]
use std::{
    path::Path,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
const EXAMPLE: &str = include_str!("../../../examples/native_dependent_vector_pipeline.lean");
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-dependent-runtime-{}-{}",
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
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(artifact)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"returnValue\":42"));
}
#[test]
fn default_budget_runs_nested_dependent_apis_in_both_personalities_and_replay() {
    let dir = directory();
    let path = dir.join("Main.lean");
    let artifact = dir.join("main.flbc");
    std::fs::write(&path, EXAMPLE).unwrap();
    let output = run(&path, &artifact);
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"finalValue\":42"));
    replay(&artifact);
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&path)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(output.stdout, b"42\n");
    assert_eq!(std::fs::read_to_string(&path).unwrap(), EXAMPLE);
}
#[test]
fn imported_dependent_apis_preserve_rejection_and_deterministic_artifact_recovery() {
    let dir = directory();
    let dependency = dir.join("Vectors.lean");
    let entry = dir.join("Main.lean");
    let (defs, eval) = EXAMPLE.split_once("#eval").unwrap();
    std::fs::write(&dependency, defs).unwrap();
    std::fs::write(&entry, format!("import Vectors\n#eval {eval}")).unwrap();
    let good = dir.join("good.flbc");
    assert!(run(&entry, &good).status.success());
    let before = std::fs::read(&good).unwrap();
    for suffix in [
        "\ndef bad : Nat := first 0 Vec.nil\n",
        "\ndef bad (xs : Vec Nat 1) : Vec Nat 2 := rest 0 xs\n",
    ] {
        std::fs::write(&dependency, format!("{defs}{suffix}")).unwrap();
        let failed = dir.join("failed.flbc");
        let output = run(&entry, &failed);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(!failed.exists());
        assert_eq!(std::fs::read(&good).unwrap(), before);
    }
    std::fs::write(&dependency, defs).unwrap();
    let recovered = dir.join("recovered.flbc");
    assert!(run(&entry, &recovered).status.success());
    assert_eq!(std::fs::read(&recovered).unwrap(), before);
    replay(&recovered);
}
