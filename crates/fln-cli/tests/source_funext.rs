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
