//! Installed wildcard proof selection and multi-file failure atomicity.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_wildcards_preserve_proofs_and_failed_batches_publish_nothing() {
    let dir = std::env::temp_dir().join(format!("fln-simp-hypotheses-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let good = dir.join("proofs.lean");
    let bad = dir.join("invalid.lean");
    let source = include_str!("../../../examples/native_simp_hypotheses.lean");
    std::fs::write(&good, source).unwrap();
    for invalid in [
        "theorem missing (P : Prop) : P := by simp only [*]",
        "theorem invalid : (0 : Nat) = 1 := by simp [*]",
        "theorem malformed (P : Prop) (p : P) : P := by simp [* p]",
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
            } else {
                assert!(output.stdout.is_empty());
                assert!(!output.stderr.is_empty());
            }
            assert_eq!(std::fs::read(&good).unwrap(), source.as_bytes());
            assert_eq!(std::fs::read(&bad).unwrap(), invalid.as_bytes());
        }
    }
}
