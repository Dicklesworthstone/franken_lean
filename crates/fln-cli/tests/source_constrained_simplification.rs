//! Default-budget simplification of a recursively defined indexed family.
#![forbid(unsafe_code)]

use std::process::Command;

const SOURCE: &str = "\
inductive Loop : Nat -> Type where
 | base (n : Nat) : Loop n
 | step (n : Nat) (child : Loop n) : Loop n
def copy (x : Loop 7) : Loop 7 := match x with
 | .base n => Loop.base n
 | .step n rest => Loop.step n (copy rest)
theorem identity (x : Loop 7) : copy x = x := by
 induction x with
 | base n => rfl
 | step n rest ih => simp only [copy, ih]
";

#[test]
fn installed_simplification_of_constrained_recursion_preserves_admission() {
    let dir = std::env::temp_dir().join(format!("fln-constrained-simp-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let good = dir.join("copy.lean");
    let bad = dir.join("false.lean");
    let invalid = "theorem falseEquality : (1 : Nat) = 2 := by simp only []";
    std::fs::write(&good, SOURCE).unwrap();
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
                "\"theorems\":1",
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
        assert_eq!(std::fs::read(&good).unwrap(), SOURCE.as_bytes());
        assert_eq!(std::fs::read(&bad).unwrap(), invalid.as_bytes());
    }
}
