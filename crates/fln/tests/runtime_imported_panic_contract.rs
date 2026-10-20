//! Imported panicCore uses the pin's projection, not the source seed's alias.
//! The Reference is consumed only as checked artifact data, never executed.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, Environment, KVMap, Name,
    OleanCheckLimits, OleanModuleInput,
};
use std::path::PathBuf;

const STACK: usize = 256 * 1024 * 1024;

#[test]
fn imported_panic_returns_the_selected_default_including_partial_and_function_values() {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.is_dir());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Reference is absent"
        );
        eprintln!("SKIP: pinned Reference lib/lean is absent");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let path = lib.join("Init/Prelude.olean");
            let parts = [
                std::fs::read(&path).unwrap(),
                std::fs::read(path.with_extension("olean.server")).unwrap(),
                std::fs::read(path.with_extension("olean.private")).unwrap(),
            ];
            let name = Name::from_components(["Init", "Prelude"]);
            let inputs = [OleanModuleInput {
                name: &name,
                artifact: &parts[0],
                server_artifact: Some(&parts[1]),
                private_artifact: Some(&parts[2]),
            }];
            let options = KVMap::new();
            let imported = Engine::from_environment(Environment::new())
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&name),
                    &options,
                    SourceOleanImportLimits::new(OleanCheckLimits::new(
                        256 * 1024 * 1024,
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let engine = &imported.engine;
            assert!(
                engine
                    .environment()
                    .find(&Name::from_components(["default"]))
                    .is_none(),
                "the import must not be repaired by installing the seed-only alias"
            );
            let root = engine.logical_root(&options);
            for (source, expected) in [
                ("#eval (panicCore \"imported panic\" : Nat)", 0),
                ("#eval @panicCore Nat (Inhabited.mk 42) \"imported default\"", 42),
                ("#eval let fail : String -> Nat := @panicCore Nat (Inhabited.mk 42); fail \"partial imported panic\"", 42),
                ("#eval @panicCore (Nat -> Nat) (Inhabited.mk (fun n => n + 2)) \"function imported panic\" 40", 42),
            ] {
                let run = || {
                    engine
                        .execute_source_commands_with_checks(
                            source.as_bytes(),
                            &options,
                            EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)),
                        )
                        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
                        .into_complete()
                        .unwrap_or_else(|outcome| panic!("{source}\n{outcome:?}"))
                };
                let first = run();
                let last = first.batch.executions.last().unwrap();
                assert_eq!(
                    fln::closed_vm_value(&last.exit).unwrap(),
                    Some(ClosedVmValue::Scalar(expected)),
                    "{source}"
                );
                let second = run();
                assert_eq!(
                    last.flbc_artifact,
                    second.batch.executions.last().unwrap().flbc_artifact,
                    "deterministic imported panic execution: {source}"
                );
                assert_eq!(root, engine.logical_root(&options));
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
