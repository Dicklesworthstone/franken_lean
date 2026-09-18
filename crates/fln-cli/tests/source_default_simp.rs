//! Installed command coverage: registered simp sets, erasure and atomic failure.
#![forbid(unsafe_code)]
use std::process::Command;

#[test]
fn installed_simp_registry_checks_real_proofs_and_never_publishes_failed_batches() {
    let dir = std::env::temp_dir().join(format!("fln-default-simp-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let good = dir.join("default-simp.lean");
    let bad = dir.join("bad.lean");
    let source = include_str!("../../../examples/native_default_simp.lean");
    let false_proof = "theorem falseProof (n : Nat) : Wrapper.wrap n = 0 := by simp";
    std::fs::write(&good, source).unwrap();
    std::fs::write(&bad, false_proof).unwrap();
    for success in [true, false, true] {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_fln"));
        cmd.args(["check-source", "--json"]).arg(&good);
        if !success {
            cmd.arg(&bad);
        }
        let output = cmd.output().unwrap();
        assert_eq!(
            output.status.success(),
            success,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if success {
            let json = String::from_utf8(output.stdout).unwrap();
            for required in [
                "\"theorems\":6",
                "\"executed\":false",
                "\"outcome\":\"complete\"",
            ] {
                assert!(json.contains(required), "{json}");
            }
            assert!(output.stderr.is_empty());
        } else {
            assert!(output.stdout.is_empty());
            assert!(!output.stderr.is_empty());
        }
        assert_eq!(std::fs::read(&good).unwrap(), source.as_bytes());
        assert_eq!(std::fs::read(&bad).unwrap(), false_proof.as_bytes());
    }
}
