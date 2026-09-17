//! Installed declarations-to-record-runtime path, imports and canonical replay.
#![forbid(unsafe_code)]
use std::path::PathBuf;
use std::process::{Command, Output};
use std::sync::atomic::{AtomicUsize, Ordering};
static NEXT: AtomicUsize = AtomicUsize::new(0);
fn directory() -> PathBuf {
    let path = std::env::temp_dir().join(format!(
        "fln-record-runtime-{}-{}",
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
fn installed_record_source_checks_executes_and_replays() {
    let dir = directory();
    let source = dir.join("Run.lean");
    let artifact = dir.join("Run.flbc");
    let proof = include_str!("../../../examples/native_record_runtime.lean");
    std::fs::write(&source, proof).unwrap();
    let report = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&source)
            .output()
            .unwrap(),
    );
    for field in ["\"authority\":true", "\"theorems\":1", "\"executed\":false"] {
        assert!(report.contains(field), "{report}");
    }
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
    let report = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    for field in [
        "\"finalValue\":42",
        "\"commands\":7",
        "\"definitions\":6",
        "\"evaluations\":1",
        "\"command\":6",
    ] {
        assert!(report.contains(field), "{report}");
    }
    let replay = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["flbc", "run", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(replay.contains("\"returnValue\":42"), "{replay}");
    let bytes = std::fs::read(&artifact).unwrap();
    let again = dir.join("Again.flbc");
    success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--emit-flbc"])
            .arg(&again)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert_eq!(std::fs::read(&again).unwrap(), bytes);
    assert_eq!(std::fs::read_to_string(&source).unwrap(), program);
}

#[test]
fn installed_record_imports_and_declaration_only_files_work() {
    let dir = directory();
    let types = dir.join("Types.lean");
    let ops = dir.join("Ops.lean");
    let entry = dir.join("Entry.lean");
    std::fs::write(&types, "structure Point where\n  x : Nat\n  y : Nat\n").unwrap();
    std::fs::write(
        &ops,
        "import Types\ndef sum (p : Point) : Nat := match p with | .mk x y => x + y",
    )
    .unwrap();
    std::fs::write(&entry, "import Ops\n#eval sum { x := 17, y := 25 }").unwrap();
    assert_eq!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&entry)
                .output()
                .unwrap()
        ),
        "42\n"
    );
    let report = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json"])
            .args([&ops, &types, &entry])
            .output()
            .unwrap(),
    );
    assert!(report.contains("\"finalValue\":42"), "{report}");
    assert!(report.contains("\"command\":2"), "{report}");
    assert!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&types)
                .output()
                .unwrap()
        )
        .is_empty()
    );
    std::fs::write(&entry, "import Types\n").unwrap();
    assert!(
        success(
            Command::new(env!("CARGO_BIN_EXE_lean"))
                .arg(&entry)
                .output()
                .unwrap()
        )
        .is_empty()
    );
    std::fs::write(&ops, "def leak (p : Point) : Nat := p.x").unwrap();
    std::fs::write(&entry, "import Types Ops\n#eval 42").unwrap();
    let failed = Command::new(env!("CARGO_BIN_EXE_lean"))
        .arg(&entry)
        .output()
        .unwrap();
    assert!(!failed.status.success());
    assert!(failed.stdout.is_empty());
    assert!(!failed.stderr.is_empty());
}

#[test]
fn invalid_record_suffix_never_leaks_output_or_an_artifact() {
    let dir = directory();
    let source = dir.join("Run.lean");
    let artifact = dir.join("Good.flbc");
    let prefix = "structure Point where\n  x : Nat\n  y : Nat\n#eval (Point.mk 17 25).x + (Point.mk 17 25).y\n";
    std::fs::write(&source, prefix).unwrap();
    success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--emit-flbc"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    let bytes = std::fs::read(&artifact).unwrap();
    for bad in [
        "structure Broken where\n  value : Missing",
        "theorem wrong : 1 = 2 := by rfl",
        "def wrong : Point := { x := true, y := 7 }",
    ] {
        let program = format!("{prefix}{bad}");
        std::fs::write(&source, &program).unwrap();
        let failed_path = dir.join("Failed.flbc");
        let result = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-flbc"])
            .arg(&failed_path)
            .arg(&source)
            .output()
            .unwrap();
        assert!(!result.status.success(), "{bad}");
        assert!(result.stdout.is_empty());
        assert!(!result.stderr.is_empty());
        assert!(!failed_path.exists());
        assert_eq!(std::fs::read(&artifact).unwrap(), bytes);
        assert_eq!(std::fs::read_to_string(&source).unwrap(), program);
    }
}

#[test]
fn installed_record_snapshot_retains_all_checked_declarations() {
    let dir = directory();
    let source = dir.join("Snapshot.lean");
    let artifact = dir.join("Snapshot.olean");
    std::fs::write(&source, "structure Point where\n  x : Nat\n  y : Nat\n#eval (Point.mk 17 25).x + (Point.mk 17 25).y\n").unwrap();
    let report = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["run", "--json", "--emit-olean-snapshot"])
            .arg(&artifact)
            .arg(&source)
            .output()
            .unwrap(),
    );
    assert!(report.contains("\"commands\":2"), "{report}");
    // One block, two projections and one generated evaluation declaration.
    assert!(report.contains("\"checker\":{\"admissions\":4"), "{report}");
    let checked = success(
        Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-olean", "--json"])
            .arg(&artifact)
            .output()
            .unwrap(),
    );
    assert!(checked.contains("\"outcome\":\"complete\""), "{checked}");
    assert!(checked.contains("\"authority\":true"), "{checked}");
}
