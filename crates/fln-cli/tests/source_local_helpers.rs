//! Installed proof checking, native execution, FLBC replay, and late refusal.
#![forbid(unsafe_code)]
use std::process::{Command, Output};

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
fn local_helpers_check_execute_replay_and_refuse_atomically() {
    let root = std::env::temp_dir().join(format!("fln-local-helpers-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let proof = root.join("Proof.lean");
    std::fs::write(
        &proof,
        include_str!("../../../examples/native_local_helpers.lean"),
    )
    .unwrap();
    let report = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&proof)
            .output()
            .unwrap(),
    );
    for required in [
        "\"outcome\":\"complete\"",
        "\"authority\":true",
        "\"theorems\":3",
        "\"executed\":false",
    ] {
        assert!(report.contains(required), "{report}");
    }
    let source = root.join("Run.lean");
    let artifact = root.join("Run.flbc");
    let good = "def compute (n : Nat) : Nat := let outer (x : Nat) : Nat := let inner (y : Nat) : Nat := n + x + y; inner 2; outer 3\n#eval compute 37\n";
    std::fs::write(&source, good).unwrap();
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
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(run.contains("\"finalValue\":42"), "{run}");
    let bytes = std::fs::read(&artifact).unwrap();
    let replay = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":42"), "{replay}");

    std::fs::write(
        &source,
        "#eval 42\ndef broken : Nat := let unused (x : Nat) : Bool := x; 7",
    )
    .unwrap();
    let failed_artifact = root.join("Failed.flbc");
    let failed = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&failed_artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert!(failed.stdout.is_empty());
    assert!(!failed.stderr.is_empty());
    assert!(!failed_artifact.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), bytes);
    std::fs::write(&source, good).unwrap();
    assert_eq!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&source)
                .output()
                .unwrap()
        ),
        "42\n"
    );
}
