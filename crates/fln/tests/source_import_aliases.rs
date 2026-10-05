//! Names the pin brings into scope with `export`, and keeps out of it with
//! `protected`, resolve against real imports as at the pin.
//!
//! - `export Decidable (isTrue isFalse decide)` (vendored `src/Init/Prelude.lean`)
//!   records aliases in the pin's `aliasExtension`; the import decodes and
//!   activates them, and identifier resolution consults them beside declarations
//!   (bead `fln-export-aliases-ub7i`).
//! - `protected def Nat.add` and its kin are tagged in the pin's `protectedExt`;
//!   the import activates the tags, and an atomic identifier never resolves to a
//!   protected declaration through a namespace or `open` (bead `fln-eq4k`).
//!
//! Every program's expected verdict is the pinned Reference's own, each run alone
//! after `prelude` and `import Init.Core`:
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

/// Programs the pin REJECTS because the atomic name is a protected declaration
/// (`Nat.add`, `Nat.lt_irrefl` and `Lean.SourceInfo.none` are protected at the pin;
/// its first errors: "Function expected at add", "Unknown identifier `lt_irrefl`",
/// "Function expected at add", "Unknown identifier `add`", and "Type mismatch",
/// where `none` falls through to `Option.none`).
const PROTECTED_REFUSED: &[&str] = &[
    "open Nat\ntheorem t : add 1 2 = 3 := rfl",
    "open Nat in\ntheorem t : add 1 2 = 3 := rfl",
    "open Nat\ntheorem t : \u{ac} (1 < 1) := lt_irrefl 1",
    "namespace Nat\ntheorem t : add 1 2 = 3 := rfl\nend Nat",
    "open Nat\ndef x : Nat := add 1 2",
    "open Lean.SourceInfo\ndef x : Lean.SourceInfo := none",
];

/// Programs the pin ACCEPTS: a protected name written non-atomically, and the
/// unprotected `Nat.pred` and `Nat.ble` by their atomic names.
const PROTECTED_ACCEPTED: &[&str] = &[
    "open Nat\ntheorem t : Nat.add 1 2 = 3 := rfl",
    "open Nat in\ntheorem t : Nat.add 1 2 = 3 := rfl",
    "theorem t : Nat.add 1 2 = 3 := rfl",
    "open Nat\ntheorem t : \u{ac} (1 < 1) := Nat.lt_irrefl 1",
    "open Nat\ntheorem t : pred 3 = 2 := rfl",
    "open Nat\ntheorem t : ble 1 2 = true := rfl",
    "namespace Nat\ntheorem t : pred 3 = 2 := rfl\nend Nat",
    "open Lean\ndef x : SourceInfo := SourceInfo.none",
];

/// A file's own `protected` declarations, which the pin REJECTS. Its first errors:
/// "protected declarations must be in a namespace", then "Unknown identifier `bar`"
/// four times (inside the namespace, under `open`, under `open ... in`, and the
/// recursive call in its own body) and "Unknown identifier `t`".
const LOCAL_PROTECTED_REFUSED: &[&str] = &[
    "protected def foo : Nat := 1",
    "namespace Foo\nprotected def bar : Nat := 1\ndef y : Nat := bar\nend Foo",
    "namespace Foo\nprotected def bar : Nat := 1\nend Foo\nopen Foo\ndef x : Nat := bar",
    "namespace Foo\nprotected def bar : Nat := 1\nend Foo\nopen Foo in\ndef x : Nat := bar",
    "namespace Foo\nprotected def bar (n : Nat) : Nat := match n with | .zero => 0 | .succ k => bar k\nend Foo",
    "namespace Foo\nprotected theorem t : True := True.intro\nend Foo\nopen Foo\ntheorem u : True := t",
];

/// A file's own `protected` declarations, which the pin ACCEPTS: each reached by a
/// non-atomic name, and an unprotected sibling by its atomic one. Each pair is the
/// declaration and the name it must be recorded as protected under.
const LOCAL_PROTECTED_ACCEPTED: &[(&str, Option<&str>)] = &[
    ("protected def Foo.bar : Nat := 1", Some("Foo.bar")),
    (
        "namespace Foo\nprotected def bar : Nat := 1\nend Foo\ndef z : Nat := Foo.bar",
        Some("Foo.bar"),
    ),
    (
        "namespace Foo\nprotected def bar : Nat := 1\nend Foo\nopen Foo in\ndef x : Nat := Foo.bar",
        Some("Foo.bar"),
    ),
    (
        "namespace Foo\ndef bar : Nat := 1\nend Foo\nopen Foo\ndef x : Nat := bar",
        None,
    ),
    (
        "namespace Foo\nprotected def bar (n : Nat) : Nat := match n with | .zero => 0 | .succ k => Foo.bar k\nend Foo",
        Some("Foo.bar"),
    ),
    (
        "namespace Foo\ndef bar (n : Nat) : Nat := match n with | .zero => 0 | .succ k => bar k\nend Foo",
        None,
    ),
    (
        "namespace Foo\nprotected theorem t : True := True.intro\nend Foo\ntheorem u : True := Foo.t",
        Some("Foo.t"),
    ),
    (
        "namespace A\nnamespace Foo\nprotected def bar : Nat := 1\nend Foo\ndef y : Nat := Foo.bar\nend A",
        Some("A.Foo.bar"),
    ),
];

/// The closure admitted through the council with its metadata activated.
fn import_pinned(lib: &Path, closure: &[&str]) -> (Engine, usize) {
    let (engine, reports) = import_pinned_reports(lib, closure);
    (engine, reports.iter().map(|module| module.aliases).sum())
}

/// [`import_pinned`], with every module's metadata report.
fn import_pinned_reports(
    lib: &Path,
    closure: &[&str],
) -> (
    Engine,
    Vec<fln::source_check::modules::imported::SourceMetadataReport>,
) {
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
        Ok(Outcome::Complete(imported)) => (imported.engine, imported.modules),
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

/// The `Init.Core` closure's `protected` tags are activated, and an atomic name
/// does not reach a protected declaration through `open` or the current
/// namespace, while the qualified name and unprotected siblings still resolve.
#[test]
fn imported_protected_declarations_are_held_back_from_atomic_names() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let (engine, reports) = import_pinned_reports(&lib, INIT_CORE);
            // The pinned `lean` reports `(protectedExt.getModuleEntries env i).size`
            // per module: Init.Prelude 611, Init.Coe 48, Init.Notation 5,
            // Init.Tactics 12, Init.SizeOf 6, Init.Core 212.
            let protected: Vec<(String, usize)> = reports
                .iter()
                .map(|module| (module.module.to_display_string(), module.protected))
                .collect();
            assert_eq!(
                protected,
                [
                    ("Init.Prelude", 611),
                    ("Init.Coe", 48),
                    ("Init.Notation", 5),
                    ("Init.Tactics", 12),
                    ("Init.SizeOf", 6),
                    ("Init.Core", 212),
                ]
                .map(|(module, count)| (module.to_owned(), count))
            );
            assert!(
                reports.iter().all(|module| !module
                    .uninterpreted
                    .iter()
                    .any(|name| name == &Name::from_components(["Lean", "protectedExt"]))),
                "protectedExt is interpreted"
            );
            let limits =
                SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)));
            let root = engine.logical_root(&KVMap::new());
            for source in PROTECTED_ACCEPTED {
                let checked =
                    engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limits);
                assert!(
                    matches!(checked, Ok(Outcome::Complete(_))),
                    "{source} must be admitted, as the pin admits it: {checked:?}"
                );
            }
            // Refused by elaboration, never by the parser: a parse refusal would pass
            // without ever reaching name resolution.
            let refused_past_the_parser = |checked: &Result<_, _>| {
                checked.is_err() && !format!("{checked:?}").contains("Frontend(Parse(")
            };
            for source in PROTECTED_REFUSED {
                let checked =
                    engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limits);
                assert!(
                    refused_past_the_parser(&checked),
                    "{source} must be refused, as the pin rejects it: {checked:?}"
                );
            }
            // A file's own `protected` declarations: tagged once admitted, and held
            // back from atomic names exactly as an imported one is.
            for (source, tagged) in LOCAL_PROTECTED_ACCEPTED {
                let checked =
                    engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limits);
                let Ok(Outcome::Complete(checked)) = checked else {
                    panic!("{source} must be admitted, as the pin admits it: {checked:?}");
                };
                let journal =
                    fln_elab::protected_names::ProtectedNames::read(checked.engine.environment())
                        .expect("the protected journal reads");
                if let Some(tagged) = tagged {
                    assert!(
                        journal.contains(&Name::from_components(tagged.split('.'))),
                        "{source} records {tagged} as protected"
                    );
                }
                assert_eq!(
                    journal.len(),
                    894 + usize::from(tagged.is_some()),
                    "{source}: the import's 894 tags plus at most its own one"
                );
            }
            for source in LOCAL_PROTECTED_REFUSED {
                let checked =
                    engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limits);
                assert!(
                    refused_past_the_parser(&checked),
                    "{source} must be refused, as the pin rejects it: {checked:?}"
                );
            }
            assert_eq!(engine.logical_root(&KVMap::new()), root);
        })
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes");
}
