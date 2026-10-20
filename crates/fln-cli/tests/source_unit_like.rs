//! The installed checker uses unit-like conversion without weakening batch failure.
#![forbid(unsafe_code)]
use std::path::Path;
use std::process::{Command, Output};

fn run(paths: &[&Path]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .args(paths)
        .output()
        .unwrap()
}

#[test]
fn installed_checker_reuses_empty_record_indices_and_retains_failed_suffixes() {
    let directory = std::env::temp_dir().join(format!("fln-unit-like-{}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let prefix = directory.join("prefix.lean");
    let suffix = directory.join("invalid.lean");
    let source = "structure Marker where\nclass Keyed (key : Marker) where\n  value : Nat\ndef reuse (a b : Marker) [i : Keyed a] : Keyed b := inferInstance\ntheorem selected (a b : Marker) [i : Keyed a] : reuse a b = i := by rfl\n";
    let bad = "theorem bad (a b : Keyed Marker.mk) : a = b := by rfl";
    std::fs::write(&prefix, source).unwrap();
    std::fs::write(&suffix, bad).unwrap();
    for failing in [false, true, false] {
        let output = if failing {
            run(&[&prefix, &suffix])
        } else {
            run(&[&prefix])
        };
        assert_eq!(
            output.status.success(),
            !failing,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if failing {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        } else {
            assert!(output.stderr.is_empty());
            let json = String::from_utf8(output.stdout).unwrap();
            for expected in [
                "\"authority\":true",
                "\"commands\":4",
                "\"theorems\":1",
                "\"executed\":false",
            ] {
                assert!(json.contains(expected), "{json}");
            }
        }
        assert_eq!(std::fs::read(&prefix).unwrap(), source.as_bytes());
        assert_eq!(std::fs::read(&suffix).unwrap(), bad.as_bytes());
    }
}
