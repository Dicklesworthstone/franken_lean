//! Default-budget simplification of a recursively defined family whose index is
//! promoted to a parameter. Every program here was run through the pinned
//! Reference `lean` v4.32.0: `SOURCE` is accepted there, and `DIALECT` and the
//! false theorem are refused there.
#![forbid(unsafe_code)]

use std::process::Command;

/// `Loop`'s index is promoted (`fixedIndicesToParams`), so `Loop 7` keeps `7`
/// fixed: patterns put `_` in that position and `induction` binds no field
/// for it.
const SOURCE: &str = "\
inductive Loop : Nat -> Type where
 | base (n : Nat) : Loop n
 | step (n : Nat) (child : Loop n) : Loop n
def copy (x : Loop 7) : Loop 7 := match x with
 | .base _ => Loop.base 7
 | .step _ rest => Loop.step 7 (copy rest)
theorem identity (x : Loop 7) : copy x = x := by
 induction x with
 | base => rfl
 | step rest ih => simp only [copy, ih]
";

/// The former source: a named variable in the promoted parameter position,
/// which the pin refuses ("Type mismatch") and FrankenLean refuses as
/// `Match(InaccessibleParameter)`.
const DIALECT: &str = "\
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
fn installed_simplification_of_fixed_parameter_recursion_preserves_admission() {
    let dir = std::env::temp_dir().join(format!("fln-constrained-simp-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let good = dir.join("copy.lean");
    let bad = dir.join("false.lean");
    let dialect = dir.join("dialect.lean");
    let invalid = "theorem falseEquality : (1 : Nat) = 2 := by simp only []";
    std::fs::write(&good, SOURCE).unwrap();
    std::fs::write(&bad, invalid).unwrap();
    std::fs::write(&dialect, DIALECT).unwrap();
    let mut first = None;
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
                "\"commands\":3",
                "\"theorems\":1",
                "\"executed\":false",
                "\"outcome\":\"complete\"",
            ] {
                assert!(json.contains(field), "{json}");
            }
            assert!(output.stderr.is_empty());
            // A refused suffix leaves nothing behind: recovery reports the same result.
            assert_eq!(first.get_or_insert_with(|| json.clone()), &json);
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&good).unwrap(), SOURCE.as_bytes());
        assert_eq!(std::fs::read(&bad).unwrap(), invalid.as_bytes());
    }
    let refused = Command::new(env!("CARGO_BIN_EXE_fln"))
        .args(["check-source", "--json"])
        .arg(&dialect)
        .output()
        .unwrap();
    let stderr = String::from_utf8_lossy(&refused.stderr);
    assert!(!refused.status.success(), "{stderr}");
    assert!(refused.stdout.is_empty(), "{stderr}");
    assert!(
        stderr.contains("a constructor parameter is inaccessible in a pattern"),
        "{stderr}"
    );
    assert_eq!(std::fs::read(&dialect).unwrap(), DIALECT.as_bytes());
}
