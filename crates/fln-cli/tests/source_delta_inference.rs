//! Installed-command coverage for ordinary implicit conversion and alternatives.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_command_checks_plain_rfl_and_preserves_failed_alternatives() {
    let directory = std::env::temp_dir().join(format!(
        "fln-delta-cli-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir(&directory).unwrap();
    let prefix = directory.join("prefix.lean");
    let proof = directory.join("proof.lean");
    std::fs::write(&prefix, "def wrap (n : Nat) : Nat := n").unwrap();
    for (source, success) in [
        ("theorem t (n : Nat) : wrap (wrap n) = n := rfl", true),
        (
            "theorem t (x y : Nat) (h : x = y) : wrap x = y := by first | exact rfl | exact h",
            true,
        ),
        ("theorem t : wrap 0 = 1 := rfl", false),
    ] {
        std::fs::write(&proof, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(&proof)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(if success { 0 } else { 1 }),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            for field in ["\"authority\":true", "\"theorems\":1", "\"executed\":false"] {
                assert!(text.contains(field), "{text}");
            }
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
            assert!(!String::from_utf8_lossy(&output.stderr).contains("\"outcome\":\"complete\""));
        }
        assert_eq!(std::fs::read_to_string(&proof).unwrap(), source);
        assert_eq!(std::fs::read_dir(&directory).unwrap().count(), 2);
    }
}
