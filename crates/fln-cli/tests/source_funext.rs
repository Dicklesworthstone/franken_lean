//! Installed function-extensionality proofs, refusal and clean retry.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_funext_checks_complete_evidence_and_never_publishes_failed_prefixes() {
    let root = std::env::temp_dir().join(format!("fln-funext-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let file = root.join("Extensionality.lean");
    for (source, status, expected) in [
        (
            "theorem t (A : Type) (B : A -> Type) (f g : (x : A) -> B x) (h : (x : A) -> f x = g x) : f = g := by funext x; exact h x\n",
            0,
            "\"theorems\":1",
        ),
        (
            "def preceding : Nat := 7\ntheorem bad (f g : Nat -> Nat) : f = g := by funext x\n",
            1,
            "\"authority\":false",
        ),
        (
            "unsafe def forged (x y : Nat) : x = y := forged x y\ntheorem bad (f g : Nat -> Nat) : f = g := by funext x; exact forged (f x) (g x)\n",
            1,
            "SafetyViolation",
        ),
        (
            "theorem recovered (f : Nat -> Nat -> Nat) : f = f := by funext; rfl\n",
            0,
            "\"theorems\":1",
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
            Some(status),
            "{source}\n{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let text = if status == 0 {
            assert!(result.stderr.is_empty());
            let text = String::from_utf8(result.stdout).unwrap();
            assert!(text.contains("\"authority\":true"), "{text}");
            assert!(text.contains("\"executed\":false"), "{text}");
            text
        } else {
            assert!(result.stdout.is_empty());
            String::from_utf8(result.stderr).unwrap()
        };
        assert!(text.contains(expected), "{text}");
        assert_eq!(std::fs::read_to_string(&file).unwrap(), source);
    }
}

#[test]
fn installed_typed_and_tuple_introductions_share_checked_term_pattern_execution() {
    let root = std::env::temp_dir().join(format!("fln-funext-patterns-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Patterns.lean");
    let prelude = "structure Prod (A B : Type) where\n  fst : A\n  snd : B\n";
    for (body, accepted) in [
        (
            "theorem t (f g : Nat × Nat -> Nat) (h : (a b : Nat) -> f (a, b) = g (a, b)) : f = g := by funext (a, b); exact h a b",
            true,
        ),
        (
            "def Alias : Type := Nat\ntheorem t (f : Alias -> Nat) : f = f := by funext (x : Nat); rfl",
            true,
        ),
        (
            "theorem t (P Q : Prop) : P ∧ Q -> Q := by intro ⟨hp, hq⟩; exact hq",
            true,
        ),
        (
            "def preceding : Nat := 7\ntheorem bad (f : Nat -> Nat) : f = f := by funext (x : Bool); rfl",
            false,
        ),
        (
            "theorem bad (P Q : Prop) : P ∧ Q -> True := by intro (a, b); constructor",
            false,
        ),
        (
            "theorem recovered : (x : Nat) -> x = x := by intro (x : Nat); rfl",
            true,
        ),
    ] {
        let source = format!("{prelude}{body}\n");
        std::fs::write(&path, &source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&path)
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(if accepted { 0 } else { 1 }),
            "{source}\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if accepted {
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            assert!(text.contains("\"authority\":true"), "{text}");
            assert!(text.contains("\"theorems\":1"), "{text}");
            assert!(text.contains("\"executed\":false"), "{text}");
        } else {
            assert!(output.stdout.is_empty());
        }
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
