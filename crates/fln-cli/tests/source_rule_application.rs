//! The executable distinguishes unfinished proof obligations from admission.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_rule_tactics_preserve_proof_authority_and_resource_failures() {
    let root = std::env::temp_dir().join(format!("fln-rules-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Rules.lean");
    for (source, status, count) in [
        (
            "theorem one (P Q : Prop) (hp : P) (f : P -> Q) : Q := by apply_assumption only [f]; exact hp\ntheorem two : (0 = 0) ∧ (true = true) := by apply_rules only [And.intro, Eq.refl]\n",
            0,
            2,
        ),
        (
            "def preceding : Nat := 7\ntheorem bad (P Q : Prop) (f : P -> Q) : Q := by apply_rules only [f]\n",
            1,
            0,
        ),
        (
            "theorem bad (P Q R : Prop) (hp : P) (first : Q -> R) (later : P -> R) : R := by apply_rules only [first, later, hp]\n",
            1,
            0,
        ),
        (
            "theorem bad (P : Prop) (loop : P -> P) : P := by apply_rules (maxDepth := 18446744073709551616) only [loop]\n",
            3,
            0,
        ),
        (
            "theorem recovered (P Q : Prop) (hp : P) (no : P -> False) : Q := by apply_rules only [no, hp]\n",
            0,
            1,
        ),
    ] {
        std::fs::write(&path, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(status),
            "{source}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if status == 0 {
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            for field in [
                "\"authority\":true".to_owned(),
                "\"executed\":false".to_owned(),
                format!("\"theorems\":{count}"),
            ] {
                assert!(text.contains(&field), "{text}");
            }
        } else {
            assert!(output.stdout.is_empty());
            let text = String::from_utf8(output.stderr).unwrap();
            assert!(text.contains("\"authority\":false"), "{text}");
            if status == 3 {
                assert!(text.contains("\"outcome\":\"resource\""), "{text}");
            }
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
