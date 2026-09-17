//! Installed source checking uses the same checked logical seed as the library.
#![forbid(unsafe_code)]
use std::{
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};
static NEXT: AtomicUsize = AtomicUsize::new(0);

#[test]
fn installed_logic_proofs_preserve_atomic_receipts_and_recover() {
    let directory = std::env::temp_dir().join(format!(
        "fln-source-logic-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir(&directory).unwrap();
    let prefix = directory.join("logic.lean");
    let proof = directory.join("proof.lean");
    let example = include_str!("../../../examples/native_propositional_logic.lean");
    std::fs::write(&prefix, example).unwrap();
    let valid = r"theorem ascii : (True /\ ¬False) \/ False <-> True := by decide";
    let mut successful_output = None;
    for source in [
        valid,
        "theorem invalid : True ∧ False := by decide",
        "theorem invalid : False ∨ False := by decide",
        "theorem invalid : True ↔ False := by decide",
        "def invalid (p : Prop) : Bool := decide (True ∨ p)",
        "theorem invalid : ¬False ∧ := by decide",
        valid,
    ] {
        std::fs::write(&proof, source).unwrap();
        let output = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .arg(&prefix)
            .arg(&proof)
            .output()
            .unwrap();
        if source == valid {
            assert_eq!(
                output.status.code(),
                Some(0),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert!(output.stderr.is_empty());
            let text = String::from_utf8(output.stdout).unwrap();
            for required in [
                "\"schema\":\"fln.source-check/1\"",
                "\"outcome\":\"complete\"",
                "\"authority\":true",
                "\"files\":2",
                "\"commands\":12",
                "\"theorems\":11",
                "\"executed\":false",
            ] {
                assert!(text.contains(required), "{text}");
            }
            if let Some(previous) = &successful_output {
                assert_eq!(
                    &text, previous,
                    "recovery must preserve deterministic receipts"
                );
            } else {
                successful_output = Some(text);
            }
        } else {
            assert_eq!(output.status.code(), Some(1));
            assert!(output.stdout.is_empty(), "no partial successful receipt");
            assert!(!output.stderr.is_empty());
            assert!(!String::from_utf8_lossy(&output.stderr).contains("\"authority\":true"));
        }
        assert_eq!(std::fs::read_to_string(&prefix).unwrap(), example);
        assert_eq!(std::fs::read_to_string(&proof).unwrap(), source);
        assert_eq!(std::fs::read_dir(&directory).unwrap().count(), 2);
    }
}
