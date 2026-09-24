//! Per-module council frontier over a closed `.olean` set (bead
//! `franken_lean-z8j.1.16`): a failing module blocks exactly its dependents, an
//! independent sibling is still checked, and nothing is checked against a failed
//! import. Typed SKIP without the pin; `FLN_REQUIRE_REFERENCE=1` makes absence fail.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};

use fln::{
    Budget, Engine, Environment, KVMap, Name, OleanCheckError, OleanCheckLimits, OleanModuleInput,
    OleanModuleVerdict,
};

const STACK: usize = 256 * 1024 * 1024;

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    lib
}

fn read_parts(lib: &Path, module: &str) -> [Vec<u8>; 3] {
    let base = module
        .split('.')
        .fold(lib.to_path_buf(), |path, part| path.join(part))
        .with_extension("olean");
    let read = |path: PathBuf| std::fs::read(&path).expect("pinned olean part");
    [
        read(base.clone()),
        read(base.with_extension("olean.server")),
        read(base.with_extension("olean.private")),
    ]
}

fn name(module: &str) -> Name {
    Name::from_components(module.split('.'))
}

#[test]
fn a_failing_module_blocks_only_its_dependents() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            // Init.Coe and Init.MethodSpecsSimp each import only Init.Prelude;
            // Init.Notation imports Init.Coe.
            let modules = [
                "Init.Prelude",
                "Init.Coe",
                "Init.Notation",
                "Init.MethodSpecsSimp",
            ];
            let names: Vec<Name> = modules.iter().map(|module| name(module)).collect();
            let mut parts: Vec<[Vec<u8>; 3]> =
                modules.iter().map(|module| read_parts(&lib, module)).collect();
            let limits =
                OleanCheckLimits::new(256 * 1024 * 1024, Budget::for_stack_bytes(STACK));

            // Control: the untouched Init.Coe decodes, so the failure below is the
            // planted corruption and nothing else.
            let [exported, server, private] = &parts[1];
            assert!(
                fln::decode_olean_module_artifacts(exported, server, private, limits.decode)
                    .is_ok()
            );
            let middle = parts[1][0].len() / 2;
            parts[1][0][middle] ^= 0xFF;
            parts[1][0][middle + 1] ^= 0xFF;

            let inputs: Vec<OleanModuleInput<'_>> = names
                .iter()
                .zip(&parts)
                .map(|(name, [exported, server, private])| OleanModuleInput {
                    name,
                    artifact: exported,
                    server_artifact: Some(server),
                    private_artifact: Some(private),
                })
                .collect();
            let frontier = Engine::from_environment(Environment::new())
                .check_olean_frontier(&inputs, &KVMap::new(), limits)
                .expect("the set itself is well formed");

            assert_eq!(frontier.rows.len(), 4, "every module gets exactly one row");
            let verdict = |module: &str| {
                &frontier
                    .rows
                    .iter()
                    .find(|row| row.name == name(module))
                    .expect("a row per module")
                    .verdict
            };
            assert!(matches!(
                verdict("Init.Coe"),
                OleanModuleVerdict::Failed(OleanCheckError::ModuleDecode { .. })
            ));
            assert!(
                matches!(verdict("Init.Notation"), OleanModuleVerdict::Blocked { by } if *by == name("Init.Coe")),
                "a dependent of a failed module is blocked, never checked"
            );
            assert!(matches!(
                verdict("Init.Prelude"),
                OleanModuleVerdict::Accepted { declarations: 2314 }
            ));
            assert!(
                matches!(verdict("Init.MethodSpecsSimp"), OleanModuleVerdict::Accepted { declarations } if *declarations > 0),
                "an independent sibling of the failed module is still checked"
            );
            let admitted: Vec<&Name> = frontier.engine.imported_modules().iter().collect();
            assert_eq!(
                admitted,
                [&name("Init.MethodSpecsSimp"), &name("Init.Prelude")],
                "the engine holds exactly the accepted modules"
            );
        })
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes");
}
