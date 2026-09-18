//! Installed-binary coverage of dependency-aware source proof generalization.
#![forbid(unsafe_code)]
use std::{path::PathBuf, process::Command};

#[test]
fn installed_context_generalization_checks_all_files_or_reports_no_success() {
    let dir = std::env::temp_dir().join(format!("fln-context-proof-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let good = dir.join("generalization.lean");
    let bad = dir.join("bad.lean");
    let source = include_str!("../../../examples/native_context_generalization.lean");
    std::fs::write(&good, source).unwrap();
    std::fs::write(
        &bad,
        "theorem bad (P : Prop) (p : P) : P := by revert p; exact p",
    )
    .unwrap();
    let original: Vec<(PathBuf, Vec<u8>)> = [&good, &bad]
        .into_iter()
        .map(|path| (path.clone(), std::fs::read(path).unwrap()))
        .collect();
    for success in [true, false, true] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
        command.args(["check-source", "--json"]).arg(&good);
        if !success {
            command.arg(&bad);
        }
        let output = command.output().unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let json = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"theorems\":8",
                "\"executed\":false",
                "\"outcome\":\"complete\"",
            ] {
                assert!(json.contains(expected), "{json}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        for (path, bytes) in &original {
            assert_eq!(std::fs::read(path).unwrap(), *bytes);
        }
    }
}

#[test]
fn installed_generalize_retains_its_universal_type_obligation() {
    let dir = std::env::temp_dir().join(format!("fln-generalize-refusal-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("invalid-generic-proof.lean");
    // The original goal is provable, but p cannot prove P m for arbitrary m.
    // Specializing the resulting candidate must not erase that failed step.
    let source =
        "theorem bad (P : Nat -> Prop) (n : Nat) (p : P n) : P n := by generalize n = m; exact p";
    std::fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&path)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(!output.stderr.is_empty());
    assert_eq!(std::fs::read(&path).unwrap(), source.as_bytes());
}
