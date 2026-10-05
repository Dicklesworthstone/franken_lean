//! Names the pin brings into scope with `export` resolve against real imports
//! (bead `fln-export-aliases-ub7i`). `export Decidable (isTrue isFalse decide)`
//! (vendored `src/Init/Prelude.lean`) records aliases in the pin's
//! `aliasExtension`; the import decodes and activates them, and identifier
//! resolution consults them beside declarations.
//!
//! The pinned Reference accepts each `ACCEPTED` declaration alone, after
//! `prelude` and `import Init.Core`:
//!
//! ```text
//! ulimit -v 40000000
//! ~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean file.lean
//! ```
//!
//! Typed SKIP without the pin; `FLN_REQUIRE_REFERENCE=1` makes absence fail.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, Environment, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, Outcome, SourceCheckLimits,
};
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;

/// `Init.Core` and its import closure, dependency first.
const INIT_CORE: &[&str] = &[
    "Init.Prelude",
    "Init.Coe",
    "Init.Notation",
    "Init.Tactics",
    "Init.SizeOf",
    "Init.Core",
];

const ACCEPTED: &[&str] = &[
    "def b : Bool := decide (2 = 2)",
    "def c : Bool := not true",
    "theorem t : decide (2 + 2 = 4) = true := rfl",
];

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

/// The closure admitted through the council with its metadata activated.
fn import_pinned(lib: &Path, closure: &[&str]) -> (Engine, usize) {
    let names: Vec<Name> = closure
        .iter()
        .map(|module| Name::from_components(module.split('.')))
        .collect();
    let parts: Vec<[Vec<u8>; 3]> = closure
        .iter()
        .map(|module| {
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
        })
        .collect();
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
    let limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        256 * 1024 * 1024,
        Budget::for_stack_bytes(STACK),
    ));
    match Engine::from_environment(Environment::new()).import_olean_modules_for_source(
        &inputs,
        &[names.last().expect("a nonempty closure").clone()],
        &KVMap::new(),
        limits,
    ) {
        Ok(Outcome::Complete(imported)) => {
            let aliases = imported.modules.iter().map(|module| module.aliases).sum();
            (imported.engine, aliases)
        }
        other => panic!("the pinned closure passes the council: {other:?}"),
    }
}

#[test]
fn imported_export_aliases_resolve_as_the_pins_names() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let (engine, aliases) = import_pinned(&lib, INIT_CORE);
            assert!(aliases > 0, "the closure's export aliases are activated");
            let limits =
                SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)));
            for source in ACCEPTED {
                let checked =
                    engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limits);
                assert!(
                    matches!(checked, Ok(Outcome::Complete(_))),
                    "{source} must be admitted: {checked:?}"
                );
            }
            // A name no declaration and no alias provides is still refused.
            let before = engine.logical_root(&KVMap::new());
            let unknown = "def u : Bool := notAnExportedName true";
            assert!(
                engine
                    .check_source_files(&[unknown.as_bytes()], &KVMap::new(), limits)
                    .is_err(),
                "{unknown} must be refused"
            );
            assert_eq!(engine.logical_root(&KVMap::new()), before);
        })
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes");
}
