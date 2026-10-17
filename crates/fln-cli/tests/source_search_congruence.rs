//! Congruence is real proof construction at the installed executable boundary.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_congruence_preserves_verdicts_input_and_refusal_recovery() {
    let root = std::env::temp_dir().join(format!("fln-congruence-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Proofs.lean");
    for (source, status, outcome, authority) in [
        (
            "theorem argument (f : Nat -> Nat) (a b : Nat) (h : a = b) : f a = f b := by solve_by_elim\ntheorem function (A : Type) (B : A -> Type) (f g : (x : A) -> B x) (h : f = g) (a : A) : f a = g a := by apply_rules\n",
            0,
            "complete",
            true,
        ),
        (
            "def preceding : Nat := 7\ntheorem bad (f : Nat -> Nat) (a b : Nat) : f a = f b := by apply_assumption\n",
            1,
            "elaboration",
            false,
        ),
        (
            "unsafe def forged (f g : Nat -> Nat) : f = g := forged f g\ntheorem bad (f g : Nat -> Nat) (a : Nat) : f a = g a := by solve_by_elim [forged f g]\n",
            1,
            "kernel-rejection",
            true,
        ),
        (
            "theorem recovered (f : Nat -> Nat) (a b : Nat) (h : a = b) : f a = f b := by\n  apply_assumption\n  exact h\n",
            0,
            "complete",
            true,
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
        let text = if status == 0 {
            assert!(output.stderr.is_empty());
            String::from_utf8(output.stdout).unwrap()
        } else {
            assert!(output.stdout.is_empty());
            String::from_utf8(output.stderr).unwrap()
        };
        assert!(
            text.contains(&format!("\"authority\":{authority}")),
            "{text}"
        );
        assert!(
            text.contains(&format!("\"outcome\":\"{outcome}\"")),
            "{text}"
        );
        if status == 0 {
            assert!(text.contains("\"executed\":false"), "{text}");
        }
        if outcome == "kernel-rejection" {
            assert!(text.contains("SafetyViolation"), "{text}");
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
