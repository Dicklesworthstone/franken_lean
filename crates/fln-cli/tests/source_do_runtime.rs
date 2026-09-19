//! Installed monadic source compilation, canonical artifact replay and refusal.
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
fn native_do_checks_executes_exports_and_replays_through_installed_commands() {
    let dir = std::env::temp_dir().join(format!("fln-native-do-{}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let source = dir.join("Example.lean");
    let artifact = dir.join("Example.flbc");
    let proof = include_str!("../../../examples/native_do.lean");
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
    let program = format!("{proof}\n#eval answer\n");
    std::fs::write(&source, &program).unwrap();
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
    let failed_path = dir.join("Failed.flbc");
    std::fs::write(
        &source,
        format!("{program}\ndef invalid.{{u}} {{A : Type u}} (a : A) : A := 7"),
    )
    .unwrap();
    let failure = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&failed_path)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!failure.status.success());
    assert!(failure.stdout.is_empty());
    assert!(!failure.stderr.is_empty());
    assert!(!failed_path.exists());
    assert_eq!(std::fs::read(&artifact).unwrap(), retained);
}

#[test]
fn alias_results_keep_bool_nat_and_string_distinct_in_both_presentations() {
    let dir = std::env::temp_dir().join(format!("fln-native-do-kinds-{}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    let source = dir.join("Kinds.lean");
    let proof = include_str!("../../../examples/native_do.lean");
    std::fs::write(&source, format!("{proof}\ndef boolAnswer : Id Bool := do return true\ndef stringAnswer : Id String := do return \"hello\"\ndef natAnswer : Id Nat := do return 1\n#eval boolAnswer\n#eval stringAnswer\n#eval natAnswer\n")).unwrap();
    assert_eq!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&source)
                .output()
                .unwrap()
        ),
        "true\n\"hello\"\n1\n"
    );
    let output = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    for expected in [
        "\"kind\":\"bool\",\"value\":true",
        "\"kind\":\"string\",\"value\":\"hello\"",
        "\"kind\":\"nat\",\"value\":1",
    ] {
        assert!(output.contains(expected), "{output}");
    }
}
