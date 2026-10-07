//! The installed consumers refuse the mutually indexed example, which the pin refuses.
#![forbid(unsafe_code)]
use std::{
    path::Path,
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};
const EXAMPLE: &str = include_str!("../../../examples/native_mutual_indexed.lean");
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-mutual-indexed-runtime-{}-{}",
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
/// The pin refuses `examples/native_mutual_indexed.lean` at line 11 (an application type
/// mismatch inside `map`'s `Forest.rec`, which FrankenLean's elaborator still accepts:
/// franken_lean-z8j.1.6.3). Both installed personalities refuse it too, in their default mode,
/// because it applies `Forest.rec` directly (franken_lean-z8j.1.6.6). Only the outcome is
/// asserted here, so fixing z8j.1.6.3 cannot break the test. The refusal publishes no artifact
/// and leaves the source as it was.
#[test]
fn mutual_indexed_example_is_refused_by_both_personalities_as_the_pin_does() {
    let dir = directory();
    let source = dir.join("Main.lean");
    let artifact = dir.join("main.flbc");
    std::fs::write(&source, EXAMPLE).unwrap();
    let output = run(&source, &artifact);
    assert!(!output.status.success(), "{output:?}");
    assert!(output.stdout.is_empty(), "{output:?}");
    assert!(!output.stderr.is_empty(), "{output:?}");
    assert!(!artifact.exists());
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&source)
        .output()
        .unwrap();
    assert!(!output.status.success(), "{output:?}");
    assert!(!output.stderr.is_empty(), "{output:?}");
    assert_eq!(std::fs::read_to_string(&source).unwrap(), EXAMPLE);
}
