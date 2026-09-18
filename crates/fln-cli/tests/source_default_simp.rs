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
                "\"theorems\":9",
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

#[test]
fn installed_simp_exclusions_are_per_call_and_failed_files_publish_nothing() {
    let dir = std::env::temp_dir().join(format!("fln-simp-exclusions-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let library = dir.join("library.lean");
    let use_rules = dir.join("use.lean");
    let invalid = dir.join("invalid.lean");
    let library_source = "namespace N\ndef wrap (n : Nat) : Nat := n\n\
        @[simp] theorem unwrap (n : Nat) : wrap n = n := by rfl\nend N";
    let use_source = "open N\n\
        theorem restored (n : Nat) : wrap n = n := by simp [-unwrap, unwrap]\n\
        theorem unfold (n : Nat) : wrap n = n := by simp only [(wrap)]\n\
        theorem retained (n : Nat) : wrap (wrap n) = n := by simp";
    std::fs::write(&library, library_source).unwrap();
    std::fs::write(&use_rules, use_source).unwrap();
    for bad in [
        "theorem excluded (n : Nat) : N.wrap n = n := by simp [-N.unwrap]",
        "theorem unknown (n : Nat) : n = n := by simp [-N.missing]",
        "@[simp] theorem falseProof : (0 : Nat) = 1 := by rfl",
    ] {
        std::fs::write(&invalid, bad).unwrap();
        let refused = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .args([&library, &use_rules, &invalid])
            .output()
            .unwrap();
        assert!(!refused.status.success());
        assert!(refused.stdout.is_empty(), "no partial success receipt");
        assert!(!refused.stderr.is_empty());
        let recovered = Command::new(env!("CARGO_BIN_EXE_fln"))
            .args(["check-source", "--json"])
            .args([&library, &use_rules])
            .output()
            .unwrap();
        assert!(
            recovered.status.success(),
            "{}",
            String::from_utf8_lossy(&recovered.stderr)
        );
        let json = String::from_utf8(recovered.stdout).unwrap();
        for field in ["\"files\":2", "\"theorems\":4", "\"executed\":false"] {
            assert!(json.contains(field), "{json}");
        }
        assert!(recovered.stderr.is_empty());
        assert_eq!(std::fs::read(&library).unwrap(), library_source.as_bytes());
        assert_eq!(std::fs::read(&use_rules).unwrap(), use_source.as_bytes());
        assert_eq!(std::fs::read(&invalid).unwrap(), bad.as_bytes());
    }
}
