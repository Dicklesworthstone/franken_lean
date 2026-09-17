//! Installed-command coverage for native proof-carrying equality decisions.
#![forbid(unsafe_code)]
use std::{
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);
#[test]
fn installed_command_checks_generic_equality_without_publishing_a_bad_suffix() {
    let directory = std::env::temp_dir().join(format!(
        "fln-equality-decisions-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let prefix = directory.join("prefix.lean");
    let proof = directory.join("proof.lean");
    let prefix_source =
        "def choose {A : Type} [DecidableEq A] (a b : A) : Nat := if a = b then 7 else 9";
    let valid = r#"
        theorem arithmetic : 2 + 3 = 5 := by decide
        theorem different : Not (2 = 3) := by decide
        theorem booleans : Not (true = false) := by decide
        theorem positive_branch : choose 4 4 = 7 := by rfl
        theorem negative_branch : choose true false = 9 := by rfl
    "#;
    std::fs::write(&prefix, prefix_source).unwrap();
    let mut successful_output = None;
    for source in [
        valid,
        "theorem invalid : 2 = 3 := by decide",
        "theorem invalid : Not (true = true) := by decide",
        valid,
    ] {
        std::fs::write(&proof, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(&proof)
            .output()
            .unwrap();
        if source == valid {
            assert_eq!(
                output.status.code(),
                Some(0),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            for required in [
                "\"schema\":\"fln.source-check/1\"",
                "\"outcome\":\"complete\"",
                "\"authority\":true",
                "\"files\":2",
                "\"commands\":6",
                "\"theorems\":5",
                "\"executed\":false",
            ] {
                assert!(text.contains(required), "{text}");
            }
            if let Some(previous) = &successful_output {
                assert_eq!(&text, previous, "recovery must be deterministic");
            } else {
                successful_output = Some(text);
            }
        } else {
            assert_eq!(output.status.code(), Some(1));
            assert!(output.stdout.is_empty(), "no partial successful receipt");
            assert!(!output.stderr.is_empty());
            assert!(!String::from_utf8_lossy(&output.stderr).contains("\"authority\":true"));
        }
        assert_eq!(std::fs::read_to_string(&prefix).unwrap(), prefix_source);
        assert_eq!(std::fs::read_to_string(&proof).unwrap(), source);
        assert_eq!(std::fs::read_dir(&directory).unwrap().count(), 2);
    }
}
