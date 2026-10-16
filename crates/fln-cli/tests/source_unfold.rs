//! Installed CLI exercises native explicit unfolding through both checkers.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_unfold_checks_success_refusal_and_recovery() {
    let root = std::env::temp_dir().join(format!("fln-unfold-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Proofs.lean");
    for (source, accepted) in [
        (
            "def wrapped (n : Nat) : Nat := n\ntheorem result : wrapped 9 = 9 := by unfold wrapped; rfl\n",
            true,
        ),
        (
            "def wrapped (n : Nat) : Nat := n\ntheorem bad : True := by unfold wrapped; exact True.intro\n",
            false,
        ),
        (
            "def wrapped (n : Nat) : Nat := n\ntheorem recovered : wrapped 11 = 11 := by unfold wrapped; rfl\n",
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
            output.status.success(),
            accepted,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
