//! Installed source and serialized bytecode consumers of native mutual layouts.
#![forbid(unsafe_code)]
use std::{
    path::Path,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

fn directory() -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-mutual-data-{}-{}",
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
    assert!(output.stderr.is_empty());
    assert!(String::from_utf8_lossy(&output.stdout).contains("\"returnValue\":42"));
    assert_eq!(before, std::fs::read(artifact).unwrap());
}

#[test]
fn mutual_blocks_execute_through_both_personalities_and_independent_bytecode() {
    let source = include_str!("../../../examples/native_mutual_data.lean");
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
    assert_eq!(lean.stdout, b"42\n");
    assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
}

#[test]
fn imports_preserve_mutual_ownership_and_bad_suffixes_publish_no_outputs() {
    let dir = directory();
    let dependency = dir.join("Data.lean");
    let entry = dir.join("Main.lean");
    let definitions = include_str!("../../../examples/native_mutual_data.lean")
        .split("#eval")
        .next()
        .unwrap();
    std::fs::write(&dependency, definitions).unwrap();
    let source = "import Data\n#eval first (Forest.cons (Tree.node 40 (@Forest.nil Nat)) (@Forest.nil Nat))\n";
    std::fs::write(&entry, source).unwrap();
    let artifact = dir.join("good.flbc");
    let output = run(&entry, &artifact);
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty());
    replay(&artifact);
    let bytes = std::fs::read(&artifact).unwrap();
    for suffix in [
        "theorem falseSuffix : 0 = 1 := by rfl",
        "mutual\ninductive X where | mk (y : Y)\ninductive Y where | bad (x : X -> Nat)\nend",
        "mutual\ninductive X where | mk\n",
    ] {
        std::fs::write(&entry, format!("{source}{suffix}")).unwrap();
        let failed = dir.join("failed.flbc");
        let output = run(&entry, &failed);
        assert!(!output.status.success(), "{output:?}");
        assert!(output.stdout.is_empty(), "{output:?}");
        assert!(!output.stderr.is_empty());
        assert!(!failed.exists());
        assert_eq!(bytes, std::fs::read(&artifact).unwrap());
    }
    std::fs::write(&entry, source).unwrap();
    let recovered = dir.join("recovered.flbc");
    assert!(run(&entry, &recovered).status.success());
    assert_eq!(bytes, std::fs::read(&recovered).unwrap());
    assert_eq!(definitions, std::fs::read_to_string(&dependency).unwrap());
}
