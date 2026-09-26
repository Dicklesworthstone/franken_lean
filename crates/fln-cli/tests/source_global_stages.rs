//! Installed global producer execution, serialized replay and late failure.
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
fn producers_and_successive_callbacks_compile_execute_and_replay_atomically() {
    let directory = std::env::temp_dir().join(format!(
        "fln-global-producer-stages-{}",
        std::process::id()
    ));
    std::fs::create_dir(&directory).unwrap();
    let source = directory.join("Example.lean");
    let artifact = directory.join("Example.flbc");
    let program = include_str!("../../../examples/native_global_stages.lean");
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
    let failed_artifact = directory.join("Failed.flbc");
    let invalid = format!("{program}\n#eval makeAdder 1 true\n");
    std::fs::write(&source, &invalid).unwrap();
    let failure = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&failed_artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!failure.status.success());
    assert!(failure.stdout.is_empty());
    assert!(!failure.stderr.is_empty());
    assert!(!failed_artifact.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), retained);
    assert_eq!(std::fs::read_to_string(&source).unwrap(), invalid);

    std::fs::write(&source, program).unwrap();
    let recovered = directory.join("Recovered.flbc");
    let run = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&recovered)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(run.contains("\"finalValue\":42"), "{run}");
    assert_eq!(std::fs::read(&recovered).unwrap(), retained);
    assert_eq!(std::fs::read_to_string(&source).unwrap(), program);
}
