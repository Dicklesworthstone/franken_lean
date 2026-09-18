//! Installed variant admission, source imports, native FLBC and late refusal.
#![forbid(unsafe_code)]
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-variant-runtime-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    path
}
fn success(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    String::from_utf8(output.stdout).unwrap()
}
#[test]
fn installed_variants_check_execute_and_replay() {
    let dir = directory();
    let source = dir.join("Example.lean");
    let bytes = dir.join("Example.flbc");
    let proof = include_str!("../../../examples/native_variants.lean");
    std::fs::write(&source, proof).unwrap();
    let checked = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(checked.contains("\"authority\":true"), "{checked}");
    assert!(checked.contains("\"theorems\":1"), "{checked}");
    std::fs::write(&source, format!("{proof}\n#eval answer")).unwrap();
    assert_eq!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&source)
                .output()
                .unwrap()
        ),
        "42\n"
    );
    let run = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&bytes)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(run.contains("\"finalValue\":42"), "{run}");
    let replay = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&bytes)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":42"), "{replay}");
}
#[test]
fn imported_variants_keep_module_visibility_and_failure_atomicity() {
    let dir = directory();
    let types = dir.join("Types.lean");
    let entry = dir.join("Entry.lean");
    let artifact = dir.join("Good.flbc");
    let failed = dir.join("Failed.flbc");
    std::fs::write(
        &types,
        "inductive Response where\n | missing\n | value (n : Nat)",
    )
    .unwrap();
    let good = "import Types\ndef count (r : Response) : Nat := match r with | .missing => 0 | .value n => n\n#eval count (Response.value 42)";
    std::fs::write(&entry, good).unwrap();
    assert_eq!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&entry)
                .output()
                .unwrap()
        ),
        "42\n"
    );
    success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--emit-flbc"])
            .arg(&artifact)
            .args([&types, &entry])
            .output()
            .unwrap(),
    );
    let before = std::fs::read(&artifact).unwrap();
    for bad in [
        "def broken : Response := Response.value true",
        "theorem broken : 1 = 2 := by rfl",
    ] {
        std::fs::write(&entry, format!("{good}\n{bad}")).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&failed)
            .args([&types, &entry])
            .output()
            .unwrap();
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
        assert!(!output.stderr.is_empty());
        assert!(!failed.exists());
        assert_eq!(std::fs::read(&artifact).unwrap(), before);
    }
    let sibling = dir.join("Sibling.lean");
    std::fs::write(&sibling, "def stolen : Response := Response.value 42").unwrap();
    std::fs::write(&entry, "import Types Sibling\n#eval 42").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
}
