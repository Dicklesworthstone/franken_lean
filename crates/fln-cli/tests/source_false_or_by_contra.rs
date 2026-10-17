//! Installed CLI success and refusal for native contradiction preparation.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_false_or_by_contra_keeps_real_proof_obligations() {
    let root = std::env::temp_dir().join(format!("fln-false-or-by-contra-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Proofs.lean");
    for (source, accepted) in [
        (
            "theorem t (p : Prop) : p -> ((p -> False) -> False) := by false_or_by_contra; contradiction\n",
            true,
        ),
        (
            "def t {A : Type} (h : False) : A := by false_or_by_contra; exact h\n",
            true,
        ),
        (
            "theorem t (h : False) : False := by false_or_by_contra; exact h\n",
            true,
        ),
        ("theorem bad : False := by false_or_by_contra\n", false),
        ("def bad : Nat := by false_or_by_contra\n", false),
        (
            "theorem bad : False := by false_or_by_contra; exact True.intro\n",
            false,
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
            "{source}\nstdout: {}\nstderr: {}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
