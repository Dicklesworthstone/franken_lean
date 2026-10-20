//! Binder simplification through the installed source-checking executable.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_simp_binders_keep_checked_evidence_and_recover_after_refusal() {
    let root = std::env::temp_dir().join(format!("fln-simp-binders-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Binders.lean");
    for (source, status, diagnostic) in [
        (
            "theorem t (F : Nat -> Type) (f g : (n : Nat) -> F n -> Nat) (h : (n : Nat) -> (a : F n) -> f n a = g n a) : (fun n a => f n a) = (fun n a => g n a) := by simp only [h]",
            0,
            "\"theorems\":1",
        ),
        (
            "def prefix : Nat := 7\ntheorem bad (f g : Nat -> Nat) (h : f 0 = g 0) : (fun n => f n) = (fun n => g n) := by simp only [h]",
            1,
            "\"authority\":false",
        ),
        (
            "unsafe def forged (f g : Nat -> Nat) (n : Nat) : f n = g n := forged f g n\ntheorem bad (f g : Nat -> Nat) : (fun n => f n) = (fun n => g n) := by simp only [forged f g]",
            1,
            "SafetyViolation",
        ),
        (
            "theorem recovered (f g : Nat -> Nat) (h : (n : Nat) -> f n = g n) : (fun n => f n) = (fun n => g n) := by simp only [h]",
            0,
            "\"theorems\":1",
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
            let text = String::from_utf8(output.stdout).unwrap();
            assert!(text.contains("\"authority\":true"));
            assert!(text.contains("\"executed\":false"));
            text
        } else {
            assert!(output.stdout.is_empty());
            String::from_utf8(output.stderr).unwrap()
        };
        assert!(text.contains(diagnostic), "{text}");
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
