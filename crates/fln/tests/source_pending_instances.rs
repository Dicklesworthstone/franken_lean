//! A unification stuck on an instance metavariable synthesizes it once the
//! class inputs are determined, as the pin's `isDefEq` calls `synthPending`
//! (vendored `Lean/Meta/ExprDefEq.lean` `unstuckMVar`,
//! `Lean/Meta/SynthInstance.lean` `synthPendingImp`), and continues with the
//! assignments it already made (bead `fln-pv1`).
//!
//! `change 5 = 5` against `(2 : Int) + 3 = 5`: the written target's numerals
//! elaborate as `@OfNat.ofNat ?α 5 ?i`. Unifying with the goal fixes
//! `?α := Int`; the instance `?i : OfNat Int 5` must then be synthesized
//! inside that same unification for its projection to reduce. Defaulting
//! `?α := Nat` afterwards cannot rescue it.
//!
//! The pin's verdicts, from the pinned Reference run on each declaration alone
//! (`Init` imported implicitly):
//!
//! ```text
//! ulimit -v 40000000
//! ~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean file.lean
//! ```
//!
//! - `POSITIVE`: exit 0.
//! - `NEGATIVE`: exit 1, `'change' tactic failed, pattern 6 = 6 is not
//!   definitionally equal to target 2 + 3 = 5`.
//!
//! Typed SKIP without the pin; `FLN_REQUIRE_REFERENCE=1` makes absence fail.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, Environment, KVMap, Name, OleanCheckLimits,
    OleanModuleInput, Outcome, SourceCheckError, SourceCheckLimits, SourceFileCheck,
};
use fln_env::constants::ConstantInfo;

const STACK: usize = 256 * 1024 * 1024;

const POSITIVE: &str = "theorem t : (2 : Int) + 3 = 5 := by change 5 = 5; rfl";
const NEGATIVE: &str = "theorem t : (2 : Int) + 3 = 5 := by change 6 = 6; rfl";

/// `Init.Data.Int.Basic` and its import closure, dependency first.
const INT_CLOSURE: &[&str] = &[
    "Init.Prelude",
    "Init.Coe",
    "Init.Data.Cast",
    "Init.Notation",
    "Init.Tactics",
    "Init.SizeOf",
    "Init.Core",
    "Init.SimpLemmas",
    "Init.Data.Zero",
    "Init.Data.NeZero",
    "Init.Grind.Attr",
    "Init.Grind.Interactive",
    "Init.Grind.Tactics",
    "Init.Data.Nat.Basic",
    "Init.Data.Int.Basic",
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

/// Admit the pinned modules through the council, then activate their class,
/// instance and default-instance journals for source elaboration.
fn import_modules(lib: &Path, modules: &[&str], root: &str) -> Engine {
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
    let limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        256 * 1024 * 1024,
        Budget::for_stack_bytes(STACK),
    ));
    match Engine::from_environment(Environment::new()).import_olean_modules_for_source(
        &inputs,
        &[Name::from_components(root.split('.'))],
        &KVMap::new(),
        limits,
    ) {
        Ok(Outcome::Complete(imported)) => imported.engine,
        other => panic!("the pinned modules pass the council: {other:?}"),
    }
}

fn check(engine: &Engine, source: &str) -> Result<Outcome<SourceFileCheck>, SourceCheckError> {
    engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))),
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
fn change_synthesizes_the_instance_its_unification_determined() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    on_a_big_stack(move || {
        let base = import_modules(&lib, INT_CLOSURE, "Init.Data.Int.Basic");

        // The pin accepts (exit 0).
        let checked = match check(&base, POSITIVE) {
            Ok(Outcome::Complete(checked)) => checked,
            other => panic!("{POSITIVE} must be admitted: {other:?}"),
        };
        assert!(
            matches!(
                checked
                    .engine
                    .environment()
                    .find(&Name::from_components(["t"])),
                Some(ConstantInfo::Thm(_))
            ),
            "{POSITIVE} must admit the theorem `t`"
        );

        // The pin refuses: `'change' tactic failed, pattern 6 = 6 is not
        // definitionally equal to target 2 + 3 = 5`. Matched by variant name,
        // since the tactic error type is private to the elaborator.
        match check(&base, NEGATIVE) {
            Err(error @ SourceCheckError::Command { .. }) => assert!(
                format!("{error:?}").contains("Tactic(ChangeMismatch)"),
                "{NEGATIVE} must be refused as a change mismatch: {error:?}"
            ),
            other => panic!("{NEGATIVE} must be refused: {other:?}"),
        }
    });
}
