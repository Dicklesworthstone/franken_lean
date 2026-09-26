//! Installed source Float execution, rendering and portable bytecode replay.
#![forbid(unsafe_code)]

use std::{
    path::{Path, PathBuf},
    process::{Command, Output},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);
const EXAMPLE: &str = include_str!("../../../examples/native_floats.lean");

fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-source-floats-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn run(source: &Path) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json"])
        .arg(source)
        .output()
        .unwrap()
}

#[test]
fn float_programs_execute_through_both_installed_source_personalities() {
    let dir = directory();
    let source = dir.join("Main.lean");
    std::fs::write(&source, EXAMPLE).unwrap();
    let lean = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&source)
        .output()
        .unwrap();
    assert!(lean.status.success(), "{lean:?}");
    assert!(lean.stderr.is_empty(), "{lean:?}");
    assert_eq!(lean.stdout, b"10.500000\n3.750000\n6.000000\n-1.250000\n");
    let native = run(&source);
    assert!(native.status.success(), "{native:?}");
    assert!(native.stderr.is_empty(), "{native:?}");
    let json = String::from_utf8(native.stdout).unwrap();
    assert!(json.contains("\"finalKind\":\"float32\""), "{json}");
    assert!(json.contains("\"finalValue\":-1.250000"), "{json}");
    assert!(json.contains("\"evaluations\":4"), "{json}");
    assert_eq!(std::fs::read_to_string(&source).unwrap(), EXAMPLE);
}

#[test]
fn ieee_special_values_have_valid_json_and_pinned_human_rendering() {
    let dir = directory();
    let source = dir.join("Main.lean");
    for (term, json_value, human) in [
        ("(0.0 / 0.0 : Float)", "\"NaN\"", "NaN\n"),
        ("(1.0 / 0.0 : Float)", "\"inf\"", "inf\n"),
        ("(-1.0 / 0.0 : Float32)", "\"-inf\"", "-inf\n"),
        ("(-0.0 : Float)", "-0.000000", "-0.000000\n"),
    ] {
        std::fs::write(&source, format!("#eval {term}\n")).unwrap();
        let native = run(&source);
        assert!(native.status.success(), "{term}: {native:?}");
        assert!(native.stderr.is_empty(), "{term}: {native:?}");
        let json = String::from_utf8(native.stdout).unwrap();
        assert!(
            json.contains(&format!("\"finalValue\":{json_value}")),
            "{json}"
        );
        let lean = Command::new(env!("CARGO_BIN_EXE_lean"))
            .arg(&source)
            .output()
            .unwrap();
        assert!(lean.status.success(), "{term}: {lean:?}");
        assert!(lean.stderr.is_empty(), "{term}: {lean:?}");
        assert_eq!(lean.stdout, human.as_bytes());
    }
}

#[test]
fn float_bytecode_replays_and_late_type_errors_preserve_existing_artifacts() {
    let dir = directory();
    let source = dir.join("Main.lean");
    let artifact = dir.join("main.flbc");
    let good =
        "def delta (x : Float) : Float := x + 0.1\n#eval Float.toString (delta 2.0) ++ \"!\"\n";
    std::fs::write(&source, good).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let before = std::fs::read(&artifact).unwrap();
    let replay = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["flbc", "run", "--json"])
        .arg(&artifact)
        .output()
        .unwrap();
    assert!(replay.status.success(), "{replay:?}");
    assert!(replay.stderr.is_empty(), "{replay:?}");
    assert!(
        String::from_utf8_lossy(&replay.stdout).contains("\"returnValue\":\"2.100000!\""),
        "{replay:?}"
    );
    std::fs::write(
        &source,
        format!("{good}def bad : Float32 := (1.0 : Float)\n"),
    )
    .unwrap();
    let failed = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["run", "--json", "--emit-flbc"])
        .arg(&artifact)
        .arg(&source)
        .output()
        .unwrap();
    assert!(!failed.status.success(), "{failed:?}");
    assert!(failed.stdout.is_empty(), "{failed:?}");
    assert_eq!(std::fs::read(&artifact).unwrap(), before);
}
