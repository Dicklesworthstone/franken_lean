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
//! The import and overload verdicts below are checked against the pinned
//! Reference, each run alone after `prelude` and `import Init.Core`. Additional
//! conservative controls exercise cases native synthesis cannot yet settle:
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
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, Environment, KVMap, Name,
    OleanCheckLimits, OleanModuleInput, Outcome, SourceCheckLimits,
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

/// Each admitted by the pin (`prelude`, `import Init.Core`, the line; exit 0). The last
/// names the real declaration `Decidable.decide` directly, so a declaration keeps its
/// precedence over the alias that shadows nothing here (pinned `lean` v4.32.0, 2026-10-05).
const ACCEPTED: &[&str] = &[
    "def b : Bool := decide (2 = 2)",
    "def c : Bool := not true",
    "theorem t : decide (2 + 2 = 4) = true := rfl",
    "def b3 : Bool := Decidable.decide (2 = 2)",
];

/// Names nothing provides, with the pin's message for each file (`prelude`,
/// `import Init.Core`, the line), run as above on 2026-10-05:
/// `3:16: error(lean.unknownIdentifier): Unknown identifier `fooBarUnknown``, the same at
/// 3:16 for `notAnExportedName`, and `3:15: error(lean.unknownIdentifier): Unknown constant
/// `Nat.nope`` (a proper prefix, `Nat`, is a constant).
const UNKNOWN: &[(&str, &str)] = &[
    (
        "def b : Bool := fooBarUnknown (2 = 2)",
        "Unknown identifier `fooBarUnknown`",
    ),
    (
        "def u : Bool := notAnExportedName true",
        "Unknown identifier `notAnExportedName`",
    ),
    ("def n : Nat := Nat.nope", "Unknown constant `Nat.nope`"),
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
            // A name no declaration and no alias provides is refused at elaboration, in the
            // pin's words, never as a kernel rejection of a reference to a missing constant.
            let before = engine.logical_root(&KVMap::new());
            for (unknown, expected) in UNKNOWN {
                let refused = engine
                    .check_source_files(&[unknown.as_bytes()], &KVMap::new(), limits)
                    .expect_err(unknown);
                assert_eq!(
                    refused.disposition().0,
                    "elaboration",
                    "{unknown}: {refused}"
                );
                assert!(
                    refused.to_string().contains(expected),
                    "{unknown}: {refused}"
                );
                assert_eq!(engine.logical_root(&KVMap::new()), before);
            }
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

/// Overloaded identifiers against the real `Init.Core` closure (bead `fln-wh2j`): a root
/// declaration and an opened namespace's one are both interpretations, and the pin's
/// `elabAppAux` keeps those that elaborate against the expected type. Each program is
/// the pinned Reference's verdict, run alone after `prelude` and `import Init.Core`
/// (2026-10-06). Refused: "Ambiguous term foo" with interpretations `_root_.foo : Nat`,
/// `P.foo : Nat` (and `_root_.foo 1 : Nat`, `P.foo 1 : Nat` for the application).
const OVERLOAD_AMBIGUOUS: &[&str] = &[
    "def foo : Nat := 1\nnamespace P\ndef foo : Nat := 2\nend P\nopen P\ndef bar : Nat := foo",
    "def foo (n : Nat) : Nat := n\nnamespace P\ndef foo (n : Nat) : Nat := n\nend P\nopen P\ndef bar : Nat := foo 1",
];

/// Accepted by the pin (exit 0), run as above: one interpretation has the expected type,
/// either by type alone, or through the closure's `Bool` to `Prop` coercion, which the
/// `Nat` interpretation has no counterpart of. The second element is the declaration the
/// definition must reference.
const OVERLOAD_BY_TYPE: &[(&str, &str)] = &[
    (
        "def foo : Nat := 1\nnamespace P\ndef foo : Bool := true\nend P\nopen P\ndef bar : Nat := foo",
        "foo",
    ),
    (
        "def foo (n : Nat) : Nat := n\nnamespace P\ndef foo (_n : Nat) : Bool := true\nend P\nopen P\ndef bar : Nat := foo 1",
        "foo",
    ),
    (
        "def foo : Bool := true\nnamespace P\ndef foo : Nat := 2\nend P\nopen P\ndef bar : Nat := foo",
        "P.foo",
    ),
    (
        "def foo : Bool := true\nnamespace P\ndef foo : Nat := 2\nend P\nopen P\ndef bar : Prop := foo",
        "foo",
    ),
    (
        "def foo : 0 = 0 := rfl\nnamespace P\ndef foo : 1 = 1 := rfl\nend P\nopen P\ndef bar : 0 = 0 := foo",
        "foo",
    ),
];

/// Whether `expr` mentions the constant `name` anywhere.
fn mentions(expr: &fln_core::expr::Expr, name: &Name) -> bool {
    use fln_core::expr::ExprNode;
    let mut pending = vec![expr.clone()];
    while let Some(expr) = pending.pop() {
        match expr.node() {
            ExprNode::Const { name: found, .. } if found == name => return true,
            ExprNode::App { f, a } => pending.extend([f.clone(), a.clone()]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => pending.extend([binder_type.clone(), body.clone()]),
            ExprNode::LetE {
                type_, value, body, ..
            } => pending.extend([type_.clone(), value.clone(), body.clone()]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                pending.push(expr.clone())
            }
            _ => {}
        }
    }
    false
}

#[test]
fn imported_overloads_are_ambiguous_unless_the_type_chooses_as_at_the_pin() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let (engine, _) = import_pinned(&lib, INIT_CORE);
            let limits =
                SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)));
            let root = engine.logical_root(&KVMap::new());
            // Rigid/noncanonical coercion failures still provide no new
            // overload evidence. Do not blanket-filter ExpectedFunction.
            let undetermined = "def foo (n : Nat) : Nat := n\nnamespace P\ndef foo : Nat := 1\nend P\nopen P\ndef bar : Nat := foo 0";
            let refused = engine
                .check_source_files(&[undetermined.as_bytes()], &KVMap::new(), limits)
                .expect_err("an unsupported candidate must remain undetermined");
            assert!(
                refused
                    .to_string()
                    .contains("can be neither established nor ruled out"),
                "{undetermined}: {refused:?}"
            );
            for source in OVERLOAD_AMBIGUOUS {
                let refused = engine
                    .check_source_files(&[source.as_bytes()], &KVMap::new(), limits)
                    .expect_err(source);
                assert_eq!(
                    refused.disposition().0,
                    "elaboration",
                    "{source}: {refused}"
                );
                assert!(
                    refused.to_string().contains(
                        "Ambiguous term `foo`; Possible interpretations: `_root_.foo`, `P.foo`"
                    ),
                    "{source} must be refused as the pin refuses it: {refused}"
                );
            }
            for (source, chosen) in OVERLOAD_BY_TYPE {
                let checked =
                    engine.check_source_files(&[source.as_bytes()], &KVMap::new(), limits);
                assert!(
                    matches!(checked, Ok(Outcome::Complete(_))),
                    "{source} must be admitted, as the pin admits it: {checked:?}"
                );
                let checked = checked
                    .expect("admitted")
                    .into_complete()
                    .expect("complete");
                let value = match checked
                    .engine
                    .environment()
                    .find(&Name::from_components(["bar"]))
                {
                    Some(fln_env::constants::ConstantInfo::Defn(bar)) => Some(bar.value.clone()),
                    _ => None,
                };
                assert!(value.is_some(), "{source}: bar is admitted as a definition");
                let value = value.expect("bar is a definition");
                let chosen = Name::from_components(chosen.split('.'));
                let other = if chosen == Name::from_components(["foo"]) {
                    Name::from_components(["P", "foo"])
                } else {
                    Name::from_components(["foo"])
                };
                assert!(
                    mentions(&value, &chosen) && !mentions(&value, &other),
                    "{source}: bar must reference {} and not {}",
                    chosen.to_display_string(),
                    other.to_display_string()
                );
            }
            // Init exports polymorphic `read` and `get`. Their implicit
            // telescopes end in an unknown monadic carrier when used as these
            // ordinary functions; Init provides no CoeFun instances for the
            // pin's terminal coercion attempt. The root interpretation must
            // remain available without restoring root-name precedence.
            for (name, imported) in [("read", "MonadReader.read"), ("get", "MonadState.get")] {
                let source =
                    format!("def {name} (n : Nat) : Nat := n + 2\ndef bar : Nat := {name} 40");
                let checked = engine
                    .check_source_files(&[source.as_bytes()], &KVMap::new(), limits)
                    .unwrap_or_else(|error| panic!("{source}: {error:?}"))
                    .into_complete()
                    .expect("complete imported overload check");
                let Some(fln_env::constants::ConstantInfo::Defn(bar)) = checked
                    .engine
                    .environment()
                    .find(&Name::from_components(["bar"]))
                else {
                    panic!("bar is an admitted definition");
                };
                assert!(mentions(&bar.value, &Name::from_components([name])));
                assert!(!mentions(
                    &bar.value,
                    &Name::from_components(imported.split('.'))
                ));
            }
            // Exercise the two complete source programs that exposed this
            // Init regression, including structural recursion and the Item
            // dictionary inferred for the user's `get`.
            let executed = engine
                .execute_source_commands_with_checks(
                    include_bytes!("../../../examples/native_indexed_function_children.lean"),
                    &KVMap::new(),
                    EngineExecutionLimits::new(limits.admission.kernel),
                )
                .expect("Init must check and execute the indexed regression program")
                .into_complete()
                .expect("indexed regression execution completes");
            assert_eq!(executed.batch.source_evaluation_indices.len(), 1);
            let index = executed.batch.source_evaluation_indices[0];
            let fln::VmExit::Returned(returned) = &executed.batch.executions[index].exit else {
                panic!("the indexed regression must return a Nat");
            };
            assert_eq!(
                fln_vm::interpreter::nat_decimal(&returned.value).as_deref(),
                Some("42")
            );
            let checked = engine.check_source_files(
                &[include_bytes!("../../../examples/native_term_binders.lean")],
                &KVMap::new(),
                limits,
            );
            assert!(
                matches!(checked, Ok(Outcome::Complete(_))),
                "Init must elaborate the term-binder regression program: {checked:?}"
            );
            // A genuinely unavailable initial callee still waits for its
            // containing argument. Imported CoeFun metadata must not turn
            // this suspension into an overload or tactic failure.
            let delayed = "def use {A : Type} (run : A -> Nat) (value : A) : Nat := run value
              def bar : Nat := use (fun f => f 20) (fun n => n + 22)
              theorem computes : bar = 42 := by rfl";
            let checked = engine.check_source_files(&[delayed.as_bytes()], &KVMap::new(), limits);
            assert!(matches!(checked, Ok(Outcome::Complete(_))), "{checked:?}");
            // A nested overload trial has its own empty argument queue. Its
            // caller can nevertheless have synthetic work waiting to run, so
            // the absence of CoeFun providers is not yet terminal evidence.
            let consume = "def consume {A : Type} (value : A -> Nat) (answer : Nat) : Nat := answer
              def read (n : Nat) : Nat := n + 2\n";
            let pending = format!("{consume}def bar : Nat := consume (fun f => f 20) (read 40)");
            let error = engine
                .check_source_files(&[pending.as_bytes()], &KVMap::new(), limits)
                .expect_err("an enclosing pending argument vetoes terminal overload evidence");
            assert!(
                error
                    .to_string()
                    .contains("can be neither established nor ruled out"),
                "{pending}: {error:?}"
            );
            let resolved = format!(
                "{consume}def bar : Nat := consume (fun (f : Nat -> Nat) => f 20) (read 40)
                 theorem computes : bar = 42 := by rfl"
            );
            let checked = engine.check_source_files(&[resolved.as_bytes()], &KVMap::new(), limits);
            assert!(
                matches!(checked, Ok(Outcome::Complete(_))),
                "the same overload without pending work must complete: {checked:?}"
            );
            // Q.make's implicit dictionary determines A only after its earlier
            // callback suspended. Resuming that callback can then reveal that
            // B is a function. Empty CoeFun search must not silently select the
            // root interpretation before the awakened callback is processed.
            let awakened = "class Pick (key : Type) (A : outParam Type) where
                value : A
              instance pick : Pick Nat (Nat -> Nat) := { value := fun n => n + 41 }
              def make (run : (Nat -> Nat) -> Nat -> Nat) (n : Nat) : Nat :=
                run (fun x => x) n
              namespace Q
              def make {A B : Type} (run : A -> B) [i : Pick Nat A] : B :=
                run (@Pick.value Nat A i)
              end Q
              open Q
              def bar : Nat := make (fun f => let x := f 0; fun n : Nat => x + n) 1";
            let error = engine
                .check_source_files(&[awakened.as_bytes()], &KVMap::new(), limits)
                .expect_err("a ready callback can still expose the alternate function type");
            assert!(
                error
                    .to_string()
                    .contains("can be neither established nor ruled out"),
                "{awakened}: {error:?}"
            );
            // A provider can match without determining the unknown carrier.
            // Its presence must veto empty-search evidence, even where this
            // elaborator cannot yet complete the resulting inference. Include
            // scoped and ordinary-local dictionaries, not only globals.
            for providers in [
                "instance anyCallable (A : Type) : CoeFun A (fun _ => Nat -> Nat) :=
                   { coe := fun _ n => n }\n",
                "namespace Scoped
                 def anyCallable (A : Type) : CoeFun A (fun _ => Nat -> Nat) :=
                   { coe := fun _ n => n }
                 attribute [scoped instance] anyCallable
                 end Scoped
                 open scoped Scoped\n",
            ] {
                let source = format!(
                    "{providers}def read (n : Nat) : Nat := n + 2\ndef bar : Nat := read 40"
                );
                let error = engine
                    .check_source_files(&[source.as_bytes()], &KVMap::new(), limits)
                    .expect_err(
                        "a CoeFun provider makes the alternate interpretation undetermined",
                    );
                assert!(
                    error
                        .to_string()
                        .contains("can be neither established nor ruled out"),
                    "{source}: {error:?}"
                );
            }
            for binder in [
                "[CoeFun Nat (fun _ => Nat -> Nat)]",
                "(dictionary : CoeFun Nat (fun _ => Nat -> Nat))",
            ] {
                let source =
                    format!("def read (n : Nat) : Nat := n + 2\ndef bar {binder} : Nat := read 40");
                let error = engine
                    .check_source_files(&[source.as_bytes()], &KVMap::new(), limits)
                    .expect_err("a possible local provider vetoes empty-search evidence");
                assert!(
                    error
                        .to_string()
                        .contains("can be neither established nor ruled out"),
                    "{source}: {error:?}"
                );
            }
            // Rigid/noncanonical coercion failures still provide no new
            // overload evidence. Do not blanket-filter ExpectedFunction.
            let undetermined = "def foo (n : Nat) : Nat := n\nnamespace P\ndef foo : Nat := 1\nend P\nopen P\ndef bar : Nat := foo 0";
            let refused = engine
                .check_source_files(&[undetermined.as_bytes()], &KVMap::new(), limits)
                .expect_err("an unsupported candidate must remain undetermined");
            assert!(
                refused
                    .to_string()
                    .contains("can be neither established nor ruled out"),
                "{undetermined}: {refused:?}"
            );
            assert_eq!(engine.logical_root(&KVMap::new()), root);
        })
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes");
}
