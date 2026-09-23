//! Installed source entry points and independent replay of mutual callback folds.
#![forbid(unsafe_code)]
use std::{
    path::Path,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

const EXAMPLE: &str = include_str!("../../../examples/native_mutual_function_children.lean");
static NEXT: AtomicUsize = AtomicUsize::new(0);

fn directory() -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-mutual-child-{}-{}",
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
fn escaped_mutual_children_run_in_both_personalities_and_replay() {
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
fn imported_callback_failures_preserve_artifacts_and_recover_deterministically() {
    let dir = directory();
    let dependency = dir.join("Trees.lean");
    let source = dir.join("Main.lean");
    let (defs, eval) = EXAMPLE.split_once("#eval").unwrap();
    std::fs::write(&dependency, defs).unwrap();
    std::fs::write(&source, format!("import Trees\n#eval {eval}")).unwrap();
    let good = dir.join("good.flbc");
    let output = run(&source, &good);
    assert!(output.status.success(), "{output:?}");
    let before = std::fs::read(&good).unwrap();
    for bad in [
        "def bad : Tree 0 := Tree.node (fun i => Forest.leaf 0 i)",
        "def bad : 0 = 1 := by rfl",
        "mutual\ninductive Bad where | node (f : Worse -> Nat)\ninductive Worse where | node (b : Bad)\nend",
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
