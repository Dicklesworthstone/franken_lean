//! Installed source checking consumes generalized families and default helpers.
#![forbid(unsafe_code)]
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

#[test]
fn installed_cli_checks_section_data_without_execution_or_source_mutation() {
    for (name, count) in [
        ("native_section_inductives.lean", 6),
        ("native_section_records.lean", 13),
    ] {
        let path = fln_core::checked_workspace_root!()
            .join("examples")
            .join(name);
        let before = std::fs::read(&path).unwrap();
        for json in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
            command.arg("check-source");
            if json {
                command.arg("--json");
            }
            let output = command.arg(&path).output().unwrap();
            assert!(output.status.success(), "{name}: {output:?}");
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            if json {
                for field in [
                    format!("\"commands\":{count}"),
                    "\"theorems\":1".into(),
                    "\"executed\":false".into(),
                    "\"authority\":true".into(),
                ] {
                    assert!(text.contains(&field), "{text}");
                }
            } else {
                assert!(
                    text.contains(&format!("Checked {count} source commands (1 theorems)")),
                    "{text}"
                );
            }
        }
        assert_eq!(std::fs::read(&path).unwrap(), before);
    }
}

static NEXT: AtomicUsize = AtomicUsize::new(0);
#[test]
fn imported_generalized_records_keep_defaults_and_reject_false_suffixes() {
    let dir = std::env::temp_dir().join(format!(
        "fln-section-data-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let data = "section\nvariable (fallback : Nat)\nstructure Config where\n  value : Nat := fallback\nend\n";
    std::fs::write(dir.join("Data.lean"), data).unwrap();
    let good = "import Data\ndef config : Config 41 := {}\ntheorem correct : config.value = 41 := by rfl\n";
    let entry = dir.join("Main.lean");
    for source in [
        good.to_owned(),
        format!("{good}theorem forged : config.value = 42 := by rfl"),
        good.to_owned(),
    ] {
        std::fs::write(&entry, &source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json", "Main.lean"])
            .current_dir(&dir)
            .output()
            .unwrap();
        if source == good {
            assert!(output.status.success(), "{output:?}");
            assert!(output.stderr.is_empty());
            let text = String::from_utf8_lossy(&output.stdout);
            assert!(
                text.contains("\"files\":2") && text.contains("\"executed\":false"),
                "{text}"
            );
        } else {
            assert_eq!(output.status.code(), Some(1), "{output:?}");
            assert!(
                output.stdout.is_empty(),
                "failed suffix exposed a success receipt"
            );
            let error = String::from_utf8_lossy(&output.stderr);
            assert!(
                error.contains("\"outcome\":\"kernel-rejection\""),
                "{error}"
            );
            assert!(!error.contains("\"outcome\":\"complete\""));
        }
        assert_eq!(std::fs::read_to_string(&entry).unwrap(), source);
        assert_eq!(
            std::fs::read_to_string(dir.join("Data.lean")).unwrap(),
            data
        );
        assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 2);
    }
}

#[test]
fn invalid_record_result_ascriptions_are_authoritative_rejections_not_successes() {
    let dir = std::env::temp_dir().join(format!(
        "fln-record-sort-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&dir).unwrap();
    let path = dir.join("Invalid.lean");
    let source = "variable (A : Type)\nstructure Bad : (Type : Nat) where\n  value : A";
    std::fs::write(&path, source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&path)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(1), "{output:?}");
    assert!(output.stdout.is_empty());
    let error = String::from_utf8_lossy(&output.stderr);
    assert!(
        error.contains("\"outcome\":\"kernel-rejection\""),
        "{error}"
    );
    assert!(error.contains("\"authority\":true"), "{error}");
    assert_eq!(std::fs::read_to_string(path).unwrap(), source);
    assert_eq!(std::fs::read_dir(&dir).unwrap().count(), 1);
}
