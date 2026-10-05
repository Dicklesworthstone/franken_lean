//! Instance selection unfolds what the pin's `instances` transparency unfolds
//! (bead `fln-gkhu`). The pin's `tryResolve` is one `isDefEq` at
//! `TransparencyMode.instances` (vendored `src/Lean/Meta/SynthInstance.lean`
//! :356, configured at :879), which unfolds definitions whose reducibility status
//! is `reducible` or `implicitReducible` (`src/Lean/Meta/GetUnfoldableConst.lean`).
//! The status is decoded from the pin's `reducibilityCore` extension.
//!
//! A local `[OfNat α 1]` elaborates its `1` as `@OfNat.ofNat Nat 1 (instOfNatNat 1)`,
//! while the numeral's goal is `OfNat α 1` with a raw literal. Equating them needs
//! `instOfNatNat` unfolded, which is `implicitReducible`. A plain `def` is
//! `semireducible` and must stay folded, so `[OfNat α myOne]` must not answer `1`.
//!
//! The pinned Reference gives each verdict below on the identical file, after
//! `prelude` and `import Init.Prelude`:
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

/// The pin accepts each alone.
const ACCEPTED: &[&str] = &[
    "def z {α : Type} [OfNat α 1] : α := 1",
    "def z {α : Type} [OfNat α (OfNat.ofNat 1)] : α := 1",
];

/// The pin refuses it: "failed to synthesize instance of type class OfNat α 1".
const REFUSED: &str = "def myOne : Nat := 1\ndef z {α : Type} [OfNat α myOne] : α := 1";

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

/// `Init.Prelude` admitted through the council with its metadata activated, and
/// the number of reducibility statuses activated.
fn import_prelude(lib: &Path) -> (Engine, usize) {
    let name = Name::from_components(["Init", "Prelude"]);
    let base = lib.join("Init").join("Prelude").with_extension("olean");
    let read = |path: PathBuf| std::fs::read(&path).expect("pinned olean part");
    let [exported, server, private] = [
        read(base.clone()),
        read(base.with_extension("olean.server")),
        read(base.with_extension("olean.private")),
    ];
    let inputs = [OleanModuleInput {
        name: &name,
        artifact: &exported,
        server_artifact: Some(&server),
        private_artifact: Some(&private),
    }];
    let limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        256 * 1024 * 1024,
        Budget::for_stack_bytes(STACK),
    ));
    match Engine::from_environment(Environment::new()).import_olean_modules_for_source(
        &inputs,
        std::slice::from_ref(&name),
        &KVMap::new(),
        limits,
    ) {
        Ok(Outcome::Complete(imported)) => {
            let statuses = imported
                .modules
                .iter()
                .map(|module| module.reducibility)
                .sum();
            (imported.engine, statuses)
        }
        other => panic!("the pinned Prelude passes the council: {other:?}"),
    }
}

#[test]
fn instance_selection_unfolds_implicit_reducible_definitions_and_nothing_semireducible() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let (engine, statuses) = import_prelude(&lib);
            assert_eq!(
                statuses, 1061,
                "the Prelude's reducibilityCore entries are activated"
            );
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
            // The control: a semireducible definition stays folded, so the local
            // instance does not answer the numeral and the search itself fails.
            let before = engine.logical_root(&KVMap::new());
            let refused = engine.check_source_files(&[REFUSED.as_bytes()], &KVMap::new(), limits);
            let Err(error) = refused else {
                panic!("{REFUSED} must be refused: {refused:?}");
            };
            let rendered = format!("{error}");
            assert!(
                rendered.contains("instance search"),
                "refused by instance search, not by something earlier: {rendered}"
            );
            assert_eq!(engine.logical_root(&KVMap::new()), before);
        })
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes");
}
