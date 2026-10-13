//! The same empty-matrix cases are checked natively and by the pinned oracle.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

const FIXTURES: &str = include_str!("fixtures/rcases.tsv");

fn cases() -> impl Iterator<Item = (&'static str, bool, String)> {
    FIXTURES
        .lines()
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .map(|line| {
            let fields: Vec<_> = line.splitn(3, '\t').collect();
            assert_eq!(fields.len(), 3, "malformed empty-matrix fixture");
            let accepted = match fields[1] {
                "accept" => true,
                "reject" => false,
                _ => panic!("unknown verdict"),
            };
            (fields[0], accepted, fields[2].replace("\\n", "\n"))
        })
}

fn verify(engine: &Engine, stack: usize) {
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let mut counts = [0usize; 2];
    for (id, accepted, source) in cases() {
        let result = engine.check_source_files(
            &[source.as_bytes()],
            &options,
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(stack))),
        );
        match result {
            Ok(Outcome::Complete(checked)) => {
                assert!(accepted, "{id}: incorrectly accepted {source}");
                assert!(
                    checked.engine.environment().constants().count()
                        > engine.environment().constants().count()
                );
                counts[0] += 1;
            }
            Err(error) => {
                assert!(!accepted, "{id}: {source}\n{error:?}");
                assert_eq!(error.disposition().0, "elaboration", "{id}: {error:?}");
                counts[1] += 1;
            }
            Ok(_) => panic!("{id}: a nonanswer is not a verdict"),
        }
        assert_eq!(
            engine.logical_root(&options),
            root,
            "{id}: input environment changed"
        );
        eprintln!("RCASES {id} {}", if accepted { "accept" } else { "reject" });
    }
    assert_eq!(counts, [16, 11]);
    engine
        .check_source_files(
            &[b"def retry : Nat := 42"],
            &options,
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(stack))),
        )
        .expect("clean retry after all refused cases")
        .into_complete()
        .expect("retry completes");
}

#[test]
fn rcases_and_functions_pass_both_checkers() {
    const STACK: usize = 2 * 1024 * 1024;
    let engine =
        Engine::with_source_seed(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)))
            .unwrap()
            .into_complete()
            .unwrap();
    verify(&engine, STACK);
}

#[test]
fn actual_imported_core_checks_the_same_rcases() {
    use fln::source_check::modules::imported::SourceOleanImportLimits;
    use fln::{Environment, Name, OleanCheckLimits, OleanDecodeLimits, OleanModuleInput};
    use std::collections::{BTreeMap, BTreeSet};
    use std::path::PathBuf;
    let library = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from);
    let Some(library) = library else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "actual Reference artifacts required"
        );
        eprintln!("SKIP: FLN_REFERENCE_LIB is not configured");
        return;
    };
    const STACK: usize = 256 * 1024 * 1024;
    const BYTES: usize = 256 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let root = Name::from_components(["Init", "RCases"]);
            let mut pending = vec![(root.clone(), false)];
            let mut seen = BTreeSet::new();
            let mut ordered = Vec::new();
            let mut artifacts = BTreeMap::new();
            while let Some((module, finished)) = pending.pop() {
                if finished {
                    ordered.push(module);
                    continue;
                }
                if !seen.insert(module.clone()) {
                    continue;
                }
                assert!(seen.len() <= 64, "bounded actual Init.Core closure");
                let path = library
                    .join(module.to_display_string().replace('.', "/"))
                    .with_extension("olean");
                let parts = [
                    std::fs::read(&path).unwrap(),
                    std::fs::read(path.with_extension("olean.server")).unwrap(),
                    std::fs::read(path.with_extension("olean.private")).unwrap(),
                ];
                let imports =
                    fln::olean_module_imports(&parts[0], OleanDecodeLimits::new(BYTES)).unwrap();
                artifacts.insert(module.clone(), parts);
                pending.push((module, true));
                pending.extend(imports.into_iter().rev().map(|name| (name, false)));
            }
            let inputs: Vec<_> = ordered
                .iter()
                .map(|name| {
                    let [exported, server, private] = &artifacts[name];
                    OleanModuleInput {
                        name,
                        artifact: exported,
                        server_artifact: Some(server),
                        private_artifact: Some(private),
                    }
                })
                .collect();
            let imported = Engine::from_environment(Environment::new())
                .import_olean_modules_for_source(
                    &inputs,
                    &[root],
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        BYTES,
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .expect("actual artifacts admitted through both checkers")
                .into_complete()
                .expect("actual import completes");
            verify(&imported.engine, STACK);
        })
        .unwrap()
        .join()
        .unwrap();
}
