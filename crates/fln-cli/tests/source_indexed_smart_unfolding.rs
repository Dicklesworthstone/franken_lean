//! The actual command must preserve indexed recursive calls, reject false
//! branches atomically, and agree with the pinned oracle when it is provisioned.
#![forbid(unsafe_code)]
use std::process::Command;

const SOURCE: &str = include_str!("../../../examples/native_indexed_smart_unfolding.lean");

#[test]
fn installed_indexed_smart_unfolding_checks_real_proofs_and_recovers() {
    let dir = std::env::temp_dir().join(format!("fln-indexed-unfold-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let good = dir.join("good.lean");
    let bad = dir.join("bad.lean");
    std::fs::write(&good, SOURCE).unwrap();
    let reference = std::env::var_os("FLN_SMART_REFERENCE_LEAN");
    if let Some(reference) = &reference {
        let version = Command::new(reference).arg("--githash").output().unwrap();
        assert!(version.status.success());
        assert_eq!(
            String::from_utf8(version.stdout).unwrap().trim(),
            "8c9756b28d64dab099da31a4c09229a9e6a2ef35",
            "wrong oracle epoch"
        );
        let oracle = Command::new(reference).arg(&good).output().unwrap();
        assert!(oracle.status.success(), "{oracle:?}");
        assert!(
            oracle.stdout.is_empty() && oracle.stderr.is_empty(),
            "{oracle:?}"
        );
    }
    let mut first = None;
    for invalid in [
        "theorem unknown {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : copyTrace a v t = t := by simp only [copyTrace]",
        "theorem wrong {A : Type} {P : A -> Type} (a : A) (v : P a) (t : Trace A P a v) : copyTrace a v t = Trace.stop a v := by induction t with | stop x vx => rfl | step x y vx vy child ih => simp only [copyTrace, ih]",
    ] {
        std::fs::write(&bad, invalid).unwrap();
        for success in [false, true] {
            let mut command = Command::new(env!("CARGO_BIN_EXE_fln"));
            command.args(["check-source", "--json"]).arg(&good);
            if !success {
                command.arg(&bad);
            }
            let output = command.output().unwrap();
            assert_eq!(output.status.success(), success, "{output:?}");
            if success {
                let json = String::from_utf8(output.stdout).unwrap();
                for field in [
                    "\"theorems\":2",
                    "\"executed\":false",
                    "\"outcome\":\"complete\"",
                ] {
                    assert!(json.contains(field), "{json}");
                }
                assert!(output.stderr.is_empty());
                assert_eq!(first.get_or_insert_with(|| json.clone()), &json);
            } else {
                assert!(output.stdout.is_empty(), "no prefix success receipt");
                assert!(!output.stderr.is_empty());
            }
        }
        if let Some(reference) = &reference {
            let combined = dir.join("refused.lean");
            std::fs::write(&combined, format!("{SOURCE}\n{invalid}\n")).unwrap();
            let oracle = Command::new(reference).arg(&combined).output().unwrap();
            assert!(!oracle.status.success(), "{invalid}\n{oracle:?}");
        }
        assert_eq!(std::fs::read(&good).unwrap(), SOURCE.as_bytes());
        assert_eq!(std::fs::read(&bad).unwrap(), invalid.as_bytes());
    }
}
