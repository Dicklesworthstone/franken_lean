//! Installed-command logical rewriting, failure atomicity, and recovery.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn logical_rewrites_check_real_files_and_never_publish_a_failed_batch() {
    let dir = std::env::temp_dir().join(format!("fln-logical-rewrites-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let good = dir.join("logical.lean");
    let bad = dir.join("invalid.lean");
    let source = include_str!("../../../examples/native_logical_rewriting.lean");
    std::fs::write(&good, source).unwrap();
    for invalid in [
        "@[simp] theorem invalid (P Q : Prop) : P ↔ Q := by constructor; intro h; exact h",
        "theorem invalid (P Q R : Prop) (h : R -> (P ↔ Q)) (q : Q) : P := by simp only [h]; exact q",
        "theorem invalid : (0 : Nat) = 1 := by simp",
    ] {
        std::fs::write(&bad, invalid).unwrap();
        for success in [false, true] {
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
                for field in [
                    "\"theorems\":5",
                    "\"executed\":false",
                    "\"outcome\":\"complete\"",
                ] {
                    assert!(json.contains(field), "{json}");
                }
                assert!(output.stderr.is_empty());
            } else {
                assert!(output.stdout.is_empty(), "no partial success");
                assert!(!output.stderr.is_empty());
            }
            assert_eq!(std::fs::read(&good).unwrap(), source.as_bytes());
            assert_eq!(std::fs::read(&bad).unwrap(), invalid.as_bytes());
        }
    }
}
