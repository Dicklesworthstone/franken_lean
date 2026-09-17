//! Source -> both checkers -> FIR/FLBC -> VM, including saved bytecode replay.
#![forbid(unsafe_code)]
use std::process::{Command, Output};

fn successful(output: Output) -> String {
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stderr.is_empty());
    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn installed_conditionals_are_lazy_and_saved_bytecode_is_executable() {
    let root = std::env::temp_dir().join(format!("fln-runtime-branches-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("Branch.lean");
    let artifact = root.join("Branch.flbc");
    let good = "def select (b : Bool) (x : Nat) : Nat := if b then x + 1 else 2 ^ 1000000000\n#eval select true 41\n";
    std::fs::write(&source, good).unwrap();
    let native = successful(
        Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert_eq!(native, "42\n");
    let receipt = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(receipt.contains("\"finalValue\":42"), "{receipt}");
    let bytes = std::fs::read(&artifact).unwrap();
    assert!(!bytes.is_empty());
    let replay = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":42"), "{replay}");

    let failed_artifact = root.join("Failed.flbc");
    std::fs::write(
        &source,
        "#eval 42\ndef broken : Nat := if true then 17 else \"wrong\"",
    )
    .unwrap();
    let failed = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&failed_artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert!(
        failed.stdout.is_empty(),
        "a late bad branch must suppress partial output"
    );
    assert!(!failed_artifact.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), bytes);
    std::fs::write(&source, good).unwrap();
    let recovered = successful(
        Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert_eq!(recovered, native);
}
