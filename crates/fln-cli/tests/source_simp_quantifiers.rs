//! Quantified goals and hypotheses use the same checked simplifier in the CLI.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn quantified_simp_keeps_its_binders_and_never_publishes_unproved_prefixes() {
    let root = std::env::temp_dir().join(format!("fln-simp-quantified-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let file = root.join("Quantified.lean");
    for (source, accepted, safety) in [
        (
            "theorem t (f g : Nat -> Nat) (P : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> P (g n)) : (n : Nat) -> P (f n) := by\n  simp only [h]\n  guard_target = (n : Nat) -> P (g n)\n  exact ready\ntheorem reflexive (A : Type) : (a : A) -> a = a := by simp only []\n",
            true,
            false,
        ),
        (
            "def prefix : Nat := 7\ntheorem bad (f g : Nat -> Nat) (h : f 0 = g 0) : (n : Nat) -> f n = g n := by simp only [h]",
            false,
            false,
        ),
        (
            "unsafe def forged (f g : Nat -> Nat) (n : Nat) : f n = g n := forged f g n\ntheorem bad (f g : Nat -> Nat) : (n : Nat) -> f n = g n := by simp only [forged f g]",
            false,
            true,
        ),
        (
            "theorem t (f g : Nat -> Nat) (P : Nat -> Prop) (h : (n : Nat) -> f n = g n) (ready : (n : Nat) -> P (f n)) : (n : Nat) -> P (g n) := by simpa only [h] using ready",
            true,
            false,
        ),
    ] {
        std::fs::write(&file, source).unwrap();
        let result = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&file)
            .output()
            .unwrap();
        assert_eq!(
            result.status.code(),
            Some(if accepted { 0 } else { 1 }),
            "{source}\n{}",
            String::from_utf8_lossy(&result.stderr)
        );
        if accepted {
            assert!(result.stderr.is_empty());
            let text = String::from_utf8(result.stdout).unwrap();
            assert!(text.contains("\"authority\":true"), "{text}");
            assert!(text.contains("\"executed\":false"), "{text}");
        } else {
            assert!(result.stdout.is_empty());
            let text = String::from_utf8(result.stderr).unwrap();
            assert!(
                text.contains(if safety {
                    "SafetyViolation"
                } else {
                    "\"authority\":false"
                }),
                "{text}"
            );
        }
        assert_eq!(std::fs::read_to_string(&file).unwrap(), source);
    }
}
