//! Lifted helper names reach checking, execution and independent bytecode replay.
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
fn installed_local_helpers_execute_replay_and_reject_late_collisions_atomically() {
    let root = std::env::temp_dir().join(format!("fln-local-lifting-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let source = root.join("Helpers.lean");
    let artifact = root.join("Helpers.flbc");
    let failed = root.join("Rejected.flbc");
    let declarations = "def count (offset n : Nat) : Nat :=\n  let rec go (m : Nat) : Nat := match m with\n    | 0 => offset\n    | k+1 => go k + 1\n  go n\ntheorem independent : count.go 7 3 = 10 := rfl\n";
    std::fs::write(&source, declarations).unwrap();
    let checked = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(checked.contains("\"executed\":false"), "{checked}");
    let good = format!("{declarations}#eval count.go 7 3\n");
    std::fs::write(&source, &good).unwrap();
    let execution = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(execution.contains("\"finalValue\":10"), "{execution}");
    let retained = std::fs::read(&artifact).unwrap();
    let replay = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":10"), "{replay}");
    let bad = format!(
        "{good}def duplicate.go : Nat := 1\ndef duplicate : Nat := let rec go : Nat := 2; go\n"
    );
    std::fs::write(&source, &bad).unwrap();
    for destination in [&failed, &artifact] {
        let result = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(destination)
            .arg(&source)
            .output()
            .unwrap();
        assert!(!result.status.success());
        assert!(result.stdout.is_empty());
        assert!(!failed.exists());
        assert_eq!(std::fs::read(&artifact).unwrap(), retained);
        assert_eq!(std::fs::read_to_string(&source).unwrap(), bad);
    }
    std::fs::write(&source, good).unwrap();
    let recovered = successful(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(recovered.contains("\"finalValue\":10"), "{recovered}");
}
