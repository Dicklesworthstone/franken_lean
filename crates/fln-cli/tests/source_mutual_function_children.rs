//! Installed source entry points refuse a directly written mutual callback fold as the pin does.
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

/// `examples/native_mutual_function_children.lean` applies `Tree.rec` directly. The pin refuses it at
/// line 10 ("code generator does not support recursor `Tree.rec`"), and so do both installed
/// personalities in their default mode (bead `franken_lean-z8j.1.6.6`). A valid form needs `mutual`
/// structural recursion, which FrankenLean does not elaborate; executing the fold is the
/// `frontier` lane, covered by the `fln` runtime tests on this same example. The refusal
/// publishes no artifact and leaves the source as it was.
#[test]
fn direct_mutual_child_folds_are_refused_by_both_personalities_as_the_pin_does() {
    let dir = directory();
    let source = dir.join("Main.lean");
    let artifact = dir.join("main.flbc");
    std::fs::write(&source, EXAMPLE).unwrap();
    let message = "code generator does not support recursor `Tree.rec` yet";
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
    assert_eq!(std::fs::read_to_string(&source).unwrap(), EXAMPLE);
}
