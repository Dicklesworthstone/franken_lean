//! Installed quotient execution, independent FLBC replay and late failure.
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
fn quotient_functions_execute_export_replay_and_preserve_artifacts_on_failure() {
    let directory = std::env::temp_dir().join(format!("fln-quotient-runtime-{}", std::process::id()));
    std::fs::create_dir(&directory).unwrap();
    let source = directory.join("Example.lean");
    let artifact = directory.join("Example.flbc");
    let program = include_str!("../../../examples/native_quotient_runtime.lean");
    std::fs::write(&source, program).unwrap();
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
    let replay = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":42"), "{replay}");
    let retained = std::fs::read(&artifact).unwrap();
    let invalid = format!("{program}\n#eval Quot.lift (fun (n : Nat) => n) (fun (a b : Nat) (h : True) => rfl) (Quot.mk (fun (a b : Nat) => True) 7)\n");
    std::fs::write(&source, &invalid).unwrap();
    for destination in [artifact.clone(), directory.join("Failed.flbc")] {
        let failure = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&destination)
            .arg(&source)
            .output()
            .unwrap();
        assert!(!failure.status.success());
        assert!(failure.stdout.is_empty());
        assert!(!failure.stderr.is_empty());
        assert_eq!(std::fs::read(&artifact).unwrap(), retained);
        assert!(!directory.join("Failed.flbc").exists());
    }
    assert_eq!(std::fs::read_to_string(&source).unwrap(), invalid);
    std::fs::write(&source, program).unwrap();
    let recovered = directory.join("Recovered.flbc");
    success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&recovered)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert_eq!(std::fs::read(&recovered).unwrap(), retained);
}
