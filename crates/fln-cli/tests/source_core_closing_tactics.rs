//! Installed CLI covers `exfalso` and `infer_instance` success and refusal.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_core_closing_tactics_run_through_checked_source_admission() {
    let root = std::env::temp_dir().join(format!("fln-core-tactics-{}", std::process::id()));
    std::fs::create_dir_all(&root).unwrap();
    let path = root.join("Proofs.lean");
    for (source, accepted) in [
        (
            "theorem t (P : Prop) (h : False) : P := by exfalso; exact h\n",
            true,
        ),
        (
            "class Ready : Prop where\n  ok : True\ninstance ready : Ready := ⟨True.intro⟩\ntheorem t : Ready := by infer_instance\n",
            true,
        ),
        (
            "class Missing : Prop where\n  ok : True\ntheorem bad : Missing := by infer_instance\n",
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
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), source);
    }
}
