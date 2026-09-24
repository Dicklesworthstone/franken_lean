//! Installed nested-let execution, admission failures and independent replay.
#![forbid(unsafe_code)]
use std::{
    path::Path,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

const EXAMPLE: &str = include_str!("../../../examples/native_nested_lets.lean");
static NEXT: AtomicUsize = AtomicUsize::new(0);

fn directory() -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-nested-let-{}-{}",
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
fn nested_let_callbacks_run_in_both_personalities_and_replay() {
    let dir = directory();
    let source = dir.join("Main.lean");
    let artifact = dir.join("main.flbc");
    std::fs::write(&source, EXAMPLE).unwrap();
    let output = run(&source, &artifact);
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"finalValue\":42"));
    replay(&artifact);
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&source)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    assert_eq!(output.stdout, b"42\n");
    assert_eq!(std::fs::read_to_string(&source).unwrap(), EXAMPLE);
}

#[test]
fn imported_nested_lets_preserve_artifacts_after_invalid_inputs_and_recover() {
    let dir = directory();
    let dependency = dir.join("Nested.lean");
    let source = dir.join("Main.lean");
    let (defs, eval) = EXAMPLE.split_once("#eval").unwrap();
    std::fs::write(&dependency, defs).unwrap();
    std::fs::write(&source, format!("import Nested\n#eval {eval}")).unwrap();
    let good = dir.join("good.flbc");
    let output = run(&source, &good);
    assert!(output.status.success(), "{output:?}");
    let before = std::fs::read(&good).unwrap();
    for bad in [
        "def bad : Nat := (fun x : Nat => let y : Nat := \"bad\"; x) 0",
        "def bad : Nat := (fun x : Nat => let h : False := (by rfl); x) 0",
        "def bad : Nat := (fun x : Nat => let y := y; x) 0",
        "def bad : Nat := (fun x : Nat => let y := 1;) 0",
    ] {
        std::fs::write(&dependency, format!("{defs}\n{bad}\n")).unwrap();
        let failed = dir.join("failed.flbc");
        let output = run(&source, &failed);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(!failed.exists());
        // A failed run must not replace an already published good artifact.
        let output = run(&source, &good);
        assert_eq!(output.status.code(), Some(1), "{output:?}");
        assert_eq!(std::fs::read(&good).unwrap(), before);
    }
    std::fs::write(&dependency, defs).unwrap();
    let recovered = dir.join("recovered.flbc");
    let output = run(&source, &recovered);
    assert!(output.status.success(), "{output:?}");
    assert_eq!(std::fs::read(&recovered).unwrap(), before);
    replay(&recovered);
}
