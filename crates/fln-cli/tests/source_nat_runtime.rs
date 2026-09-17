//! Installed source proofs and native recursive FLBC export/replay.
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
fn recursive_source_checks_executes_and_replays_without_a_reference_runtime() {
    let root = std::env::temp_dir().join(format!("fln-native-recursion-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let proof = root.join("Proof.lean");
    let proofs = include_str!("../../../examples/native_nat_recursion.lean");
    std::fs::write(&proof, proofs).unwrap();
    let report = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&proof)
            .output()
            .unwrap(),
    );
    for field in ["\"authority\":true", "\"theorems\":3", "\"executed\":false"] {
        assert!(report.contains(field), "{report}");
    }
    assert_eq!(std::fs::read_to_string(&proof).unwrap(), proofs);
    let source = root.join("Run.lean");
    let artifact = root.join("Run.flbc");
    let good = "def sum (n acc : Nat) : Nat := match n with | .zero => acc | .succ k => let plus (x : Nat) : Nat := x + n; sum k (plus acc)\n#eval sum 100 2";
    std::fs::write(&source, good).unwrap();
    assert_eq!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&source)
                .output()
                .unwrap()
        ),
        "5052\n"
    );
    let run = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(run.contains("\"finalValue\":5052"), "{run}");
    let bytes = std::fs::read(&artifact).unwrap();
    let replay = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":5052"), "{replay}");

    // A late invalid unused branch cannot publish the earlier #eval output,
    // a new artifact, or modifications to an existing successful artifact.
    std::fs::write(&source, "#eval 42\ndef bad (n : Nat) : Nat := match n with | .zero => 0 | .succ k => let unused : Bool := 1; bad k").unwrap();
    let failed_path = root.join("Failed.flbc");
    let failed = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&failed_path)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert!(failed.stdout.is_empty());
    assert!(!failed.stderr.is_empty());
    assert!(!failed_path.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), bytes);
    std::fs::write(&source, good).unwrap();
    assert_eq!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&source)
                .output()
                .unwrap()
        ),
        "5052\n"
    );
}
