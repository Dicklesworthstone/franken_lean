//! Installed fln check/run commands and bytecode replay execute partial companions.
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
fn installed_partial_recursion_executes_and_replays_without_logical_unfolding() {
    let root = std::env::temp_dir().join(format!("fln-source-partial-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("Partial.lean");
    let artifact = root.join("Partial.flbc");
    let definition = "partial def gcd' (a b : Nat) : Nat := if b == 0 then a else gcd' b (a % b)\n";
    std::fs::write(&source, definition).unwrap();
    let check = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(check.contains("\"executed\":false"), "{check}");
    let good = format!("{definition}#eval gcd' 48 18\n");
    std::fs::write(&source, &good).unwrap();
    let receipt = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(receipt.contains("\"finalValue\":6"), "{receipt}");
    let retained = std::fs::read(&artifact).unwrap();
    let replay = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":6"), "{replay}");

    // Even a true computational equation is not a proof by unfolding an opaque
    // partial definition. A late invalid proof must suppress earlier output.
    let failed_artifact = root.join("Refused.flbc");
    std::fs::write(
        &source,
        format!("{good}theorem noUnfolding : gcd' 48 18 = 6 := by rfl\n"),
    )
    .unwrap();
    let refused = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&failed_artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!refused.status.success());
    assert!(refused.stdout.is_empty());
    assert!(!failed_artifact.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), retained);
    std::fs::write(&source, &good).unwrap();
    let recovered = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(recovered.contains("\"finalValue\":6"), "{recovered}");
}

#[test]
fn installed_mutual_partial_group_replays_both_companions_and_refuses_late_failure() {
    let root =
        std::env::temp_dir().join(format!("fln-source-mutual-partial-{}", std::process::id()));
    std::fs::create_dir(&root).unwrap();
    let source = root.join("Mutual.lean");
    let artifact = root.join("Mutual.flbc");
    let group = "mutual\npartial def ping (n : Nat) : Nat := if n == 0 then 7 else pong (n - 1)\npartial def pong (n : Nat) : Nat := if n == 0 then 13 else ping (n - 1)\nend\n";
    std::fs::write(&source, group).unwrap();
    let checked = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(checked.contains("\"executed\":false"), "{checked}");
    let good = format!("{group}#eval ping 5\n");
    std::fs::write(&source, &good).unwrap();
    let output = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(output.contains("\"finalValue\":13"), "{output}");
    let retained = std::fs::read(&artifact).unwrap();
    let replay = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":13"), "{replay}");
    let failed = root.join("Refused.flbc");
    std::fs::write(
        &source,
        format!("{good}theorem noUnfold : ping 0 = 7 := by rfl\n"),
    )
    .unwrap();
    let refusal = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&failed)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!refusal.status.success());
    assert!(refusal.stdout.is_empty());
    assert!(!failed.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), retained);
    std::fs::write(&source, &good).unwrap();
    let recovered = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(recovered.contains("\"finalValue\":13"), "{recovered}");
}
