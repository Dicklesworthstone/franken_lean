//! Installed expression case analysis and induction, including batch refusal.
#![forbid(unsafe_code)]

use std::process::Command;

#[test]
fn installed_expression_elimination_checks_the_real_example_and_fails_atomically() {
    let dir = std::env::temp_dir().join(format!("fln-expression-cases-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let good = dir.join("computed.lean");
    let bad = dir.join("bad.lean");
    let source = include_str!("../../../examples/native_expression_elimination.lean");
    let invalid = "theorem invalid : (0 : Nat) = 0 := by cases ((fun (n : Nat) => true) false) with | false => rfl | true => rfl";
    std::fs::write(&good, source).unwrap();
    std::fs::write(&bad, invalid).unwrap();
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
            for field in [
                "\"theorems\":3",
                "\"executed\":false",
                "\"outcome\":\"complete\"",
            ] {
                assert!(json.contains(field), "{json}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&good).unwrap(), source.as_bytes());
        assert_eq!(std::fs::read(&bad).unwrap(), invalid.as_bytes());
    }
}
