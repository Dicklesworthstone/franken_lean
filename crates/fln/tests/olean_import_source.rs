//! Source modules import real `.olean` modules that the base engine admitted
//! through the council (bead `franken_lean-z8j.1.8`).
//!
//! The pinned Reference's `Init.Prelude` is read as data and admitted by K1 and
//! the independent checker; user source importing it then elaborates against
//! those real declarations instead of the hand-built seed. Typed SKIP without
//! the pin; `FLN_REQUIRE_REFERENCE=1` makes absence fail.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};

use fln::source_check::modules::{SourceModuleCheckError, SourceModuleCheckLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, Environment, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, Outcome, SourceCheckLimits, SourceModuleInput,
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

fn admit_modules(lib: &Path, modules: &[&str]) -> Engine {
    let names: Vec<Name> = modules
        .iter()
        .map(|module| Name::from_components(module.split('.')))
        .collect();
    let parts: Vec<[Vec<u8>; 3]> = modules
        .iter()
        .map(|module| read_parts(lib, module))
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
    let limits = OleanCheckLimits::new(256 * 1024 * 1024, Budget::for_stack_bytes(STACK));
    match Engine::from_environment(Environment::new()).check_olean_modules(
        &inputs,
        &KVMap::new(),
        limits,
    ) {
        Ok(Outcome::Complete(checked)) => Some(checked.engine),
        _ => None,
    }
    .expect("the pinned modules pass the council")
}

fn check(
    engine: &Engine,
    source: &str,
) -> Result<Outcome<fln::source_check::modules::SourceModuleCheck>, SourceModuleCheckError> {
    let entry = Name::from_components(["Main"]);
    let inputs = [SourceModuleInput {
        name: &entry,
        source: source.as_bytes(),
    }];
    let admission = EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK));
    engine.check_source_modules(
        &inputs,
        &entry,
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(admission)),
    )
}

fn on_a_big_stack<T: Send + 'static>(work: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(work)
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes")
}

#[test]
fn source_importing_the_real_prelude_checks_against_council_admitted_declarations() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    on_a_big_stack(move || {
        let prelude = admit_modules(&lib, &["Init.Prelude"]);
        assert!(
            prelude
                .imported_modules()
                .contains(&Name::from_components(["Init", "Prelude"]))
        );
        assert!(
            prelude.environment().len() > 2000,
            "the real Prelude, not a seed"
        );

        let source = "import Init.Prelude\n\ntheorem two_plus_two : 2 + 2 = 4 := rfl\n";
        let checked = match check(&prelude, source) {
            Ok(Outcome::Complete(checked)) => Some(checked),
            other => {
                eprintln!("unexpected: {other:?}");
                None
            }
        }
        .expect("the source checks against the imported Prelude");
        assert_eq!(checked.checked.theorems, 1);

        // The same source against a base that never admitted the module: the
        // import is unsatisfied, not silently served by whatever is present.
        let empty = Engine::from_environment(Environment::new());
        assert!(matches!(
            check(&empty, source),
            Err(SourceModuleCheckError::MissingModule { .. })
        ));
    });
}
