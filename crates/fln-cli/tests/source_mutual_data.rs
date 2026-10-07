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
    check_source_and_replay(include_str!("../../../examples/native_mutual_data.lean"));
}

/// `examples/native_mutual_folds.lean` applies `Forest.rec` directly. The pin refuses it at
/// line 12 ("code generator does not support recursor `Forest.rec`"), and so do both installed
/// personalities in their default mode (bead `franken_lean-z8j.1.6.6`). A valid form needs `mutual`
/// structural recursion, which FrankenLean does not elaborate; executing the fold is the
/// `frontier` lane, covered by the `fln` runtime tests on this same example. The refusal
/// publishes no artifact and leaves the source as it was.
#[test]
fn direct_mutual_folds_are_refused_by_both_personalities_as_the_pin_does() {
    let dir = directory();
    let source = dir.join("Main.lean");
    let artifact = dir.join("main.flbc");
    std::fs::write(
        &source,
        include_str!("../../../examples/native_mutual_folds.lean"),
    )
    .unwrap();
    let message = "code generator does not support recursor `Forest.rec` yet";
    let output = run(&source, &artifact);
    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(message),
        "{output:?}"
    );
    assert!(!artifact.exists());
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&source)
        .output()
        .unwrap();
    assert!(!output.status.success(), "{output:?}");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(message),
        "{output:?}"
    );
    assert_eq!(
        std::fs::read_to_string(&source).unwrap(),
        include_str!("../../../examples/native_mutual_folds.lean")
    );
}

#[test]
fn function_children_survive_mapping_and_independent_bytecode_replay() {
    check_source_and_replay(include_str!(
        "../../../examples/native_function_child_runtime.lean"
    ));
}

#[test]
fn imported_function_children_preserve_closures_and_failed_runs_preserve_artifacts() {
    let dir = directory();
    let dependency = dir.join("Data.lean");
    let entry = dir.join("Main.lean");
    let definitions = include_str!("../../../examples/native_function_child_runtime.lean")
        .split("#eval")
        .next()
        .unwrap();
    std::fs::write(&dependency, definitions).unwrap();
    let source = "import Data\n#eval follow (map 3 sample) 19\n";
    std::fs::write(&entry, source).unwrap();
    let artifact = dir.join("children.flbc");
    let output = run(&entry, &artifact);
    assert!(output.status.success(), "{output:?}");
    replay(&artifact);
    let original = std::fs::read(&artifact).unwrap();
    std::fs::write(&entry, format!("{source}theorem bad : 0 = 1 := by rfl")).unwrap();
    let failed = dir.join("failed.flbc");
    let output = run(&entry, &failed);
    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty());
    assert!(!failed.exists());
    assert_eq!(original, std::fs::read(&artifact).unwrap());
    std::fs::write(&entry, source).unwrap();
    let recovered = dir.join("recovered.flbc");
    assert!(run(&entry, &recovered).status.success());
    assert_eq!(original, std::fs::read(&recovered).unwrap());
}

fn check_source_and_replay(source: &str) {
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
