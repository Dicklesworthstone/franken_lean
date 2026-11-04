//! Exercise quantified proofs over the real, smaller logical import closure.
//! The oracle uses the complete grind header because its tactic implementation
//! requires additional Lean.Grind helper lemmas. Native proofs use ordinary
//! logical eliminators from this smaller admitted environment. The full suite
//! separately checks the complete import closure and arithmetic composition.
#![forbid(unsafe_code)]

use super::*;

const LOGICAL_ROOTS: &[&str] = &["Init.Grind.Tactics", "Init.Classical"];

#[test]
fn existential_proofs_refusals_and_exhaustion_use_both_checkers() {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(|| {
            let Some(library) = std::env::var_os("FLN_REFERENCE_LIB").map(std::path::PathBuf::from)
            else {
                assert!(
                    std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                    "Reference required"
                );
                eprintln!("SKIP: locked Reference absent");
                return;
            };
            let compiler = library.parent().unwrap().parent().unwrap().join("bin/lean");
            let version = Command::new(&compiler).arg("--version").output().unwrap();
            assert!(version.status.success());
            assert!(
                String::from_utf8_lossy(&version.stdout)
                    .contains("8c9756b28d64dab099da31a4c09229a9e6a2ef35")
            );
            let accepted: Vec<_> = ACCEPT
                .iter()
                .copied()
                .filter(|(label, _)| {
                    label.contains("existential") && *label != "existential_arithmetic"
                })
                .collect();
            let refused: Vec<_> = REFUSE
                .iter()
                .copied()
                .filter(|(label, _)| label.contains("existential"))
                .collect();
            let exhaustion = [("existential_instantiation_limit", EXISTENTIAL_EXHAUST)];
            let directory =
                std::env::temp_dir().join(format!("fln-grind-existentials-{}", std::process::id()));
            std::fs::create_dir_all(&directory).unwrap();
            for (success, cases) in [
                (true, accepted.as_slice()),
                (false, refused.as_slice()),
                (false, exhaustion.as_slice()),
            ] {
                for (label, source) in cases {
                    let path = directory.join(format!("{label}.lean"));
                    std::fs::write(&path, format!("{HEADER}{source}\n")).unwrap();
                    let output = Command::new(&compiler)
                        .arg("-j1")
                        .arg(&path)
                        .output()
                        .unwrap();
                    assert_eq!(
                        output.status.success(),
                        success,
                        "pin {label}: {}{}",
                        String::from_utf8_lossy(&output.stdout),
                        String::from_utf8_lossy(&output.stderr)
                    );
                }
            }
            let engine = base_with_roots(&library, LOGICAL_ROOTS, 1);
            let options = KVMap::new();
            let before = engine.logical_root(&options);
            let mut failures = Vec::new();
            for (success, cases) in [(true, accepted.as_slice()), (false, refused.as_slice())] {
                for (label, source) in cases {
                    eprintln!("grind existential: native {label} (accept={success})");
                    let result =
                        engine.check_source_files(&[source.as_bytes()], &options, limits());
                    match (success, result) {
                        (true, Ok(Outcome::Complete(_))) => {}
                        (false, Err(error))
                            if error.disposition().0 == "elaboration"
                                && error.disposition().2 == 1 => {}
                        (_, result) => {
                            record_failure(&mut failures, label, format!("{result:?}"));
                        }
                    }
                    assert_eq!(engine.logical_root(&options), before, "{label}");
                }
            }
            eprintln!("grind existential: native exhaustion and recovery");
            match engine.check_source_files(&[EXISTENTIAL_EXHAUST.as_bytes()], &options, limits()) {
                Err(error) if error.disposition().2 == 3 => {}
                Ok(Outcome::Inconclusive(_)) => {}
                other => record_failure(
                    &mut failures,
                    "existential_instantiation_limit",
                    format!("typed resource non-answer required: {other:?}"),
                ),
            }
            assert_eq!(engine.logical_root(&options), before);
            let recovery = accepted
                .iter()
                .find(|(label, _)| *label == "existential_witness_transport")
                .unwrap()
                .1;
            let first = engine.check_source_files(&[recovery.as_bytes()], &options, limits());
            let second = engine.check_source_files(&[recovery.as_bytes()], &options, limits());
            match (first, second) {
                (Ok(Outcome::Complete(first)), Ok(Outcome::Complete(second))) => {
                    assert_eq!(first.result_logical_root, second.result_logical_root);
                }
                other => {
                    record_failure(&mut failures, "existential_recovery", format!("{other:?}"))
                }
            }
            assert_eq!(engine.logical_root(&options), before);
            assert!(
                failures.is_empty(),
                "existential grind failed checks: {}",
                failures.join(", ")
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
