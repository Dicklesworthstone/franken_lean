//! Executable metadata crosses source/artifact boundaries without changing logic.
#![cfg(test)]
#![forbid(unsafe_code)]
use super::*;
use fln_elab::externs::{ExternEntry, ExternTable};
use fln_elab::implemented_by::ImplementedByTable;

const BASE: &str = r##"prelude
def right.{v} (A : Sort v) (x y : A) : A := y
@[implemented_by right] def logical.{u} (A : Sort u) (x y : A) : A := x
@[extern c inline "#1" cpp "foreign_λ"] axiom foreign.{u} : (A : Sort u) -> A -> A
"##;

const MAIN: &str = r#"prelude
import Left
import Right
def left.{u} (A : Sort u) (x y : A) : A := x
@[implemented_by right, implemented_by left] def final.{v} (A : Sort v) (x y : A) : A := y
@[extern "old", extern "last"] axiom last.{u} : (A : Sort u) -> A -> A
@[extern] axiom adhoc.{u} : (A : Sort u) -> A -> A
"#;

const UNBOX_BASE: &str = r#"prelude
namespace Boxing
structure Prod (A : Type) (B : Type) where
  /-- The constructor spelling used by Init.Prelude. -/
  mk ::
  fst : A
  snd : B
attribute [unbox] Prod Prod
@[unbox] structure Inline (A : Type) where
  value : A
@[unbox] inductive Choice (A : Type) where
  | none
  | some (value : A)
structure Untagged (A : Type) where
  value : A
end Boxing
"#;

const ANONYMOUS_CONSTRUCTOR_BASE: &str = r#"prelude
namespace Tagging
@[pp_using_anonymous_constructor] structure Pair (A : Type) where
  first : A
  second : A
@[pp_using_anonymous_constructor] structure Nested (A : Type) where
  pair : Pair A
  last : A
@[pp_using_anonymous_constructor] structure Empty where
@[pp_using_anonymous_constructor] inductive Atom where | mk
@[pp_using_anonymous_constructor] inductive Phantom (A : Type) where | mk
@[pp_using_anonymous_constructor] inductive Recursive where | stop | next (tail : Recursive)
structure Plain (A : Type) where
  value : A
attribute [pp_using_anonymous_constructor] Plain.mk
@[pp_using_anonymous_constructor] def identity (A : Type) (x : A) : A := x
@[pp_using_anonymous_constructor] axiom arbitrary : Type
attribute [pp_using_anonymous_constructor] Pair Pair identity
end Tagging
"#;

#[test]
fn coercion_functions_survive_metadata_only_modules_and_diamond_imports() {
    use fln_elab::delaborator_tags::{CoeFnInfo, CoeFnKind, DelaboratorTags};

    let built = compiled(&[
        ("Main", "prelude\nimport Left\nimport Right"),
        (
            "Left",
            "prelude\nimport Base\nattribute [coe] Coercion.later",
        ),
        (
            "Right",
            "prelude\nimport Base\nattribute [coe] Coercion.later",
        ),
        (
            "Base",
            r#"prelude
namespace Coercion
inductive A where | mk
def a : A := A.mk
@[coe] def custom (x : A) : A := x
@[coe] def generic {X : Type} (x : X) : X := x
@[coe] def toFunction (x : A) : A -> A := fun y => y
def later (x : A) : A := x
def ordinary (x : A) : A := x
end Coercion
"#,
        ),
    ]);
    let before = DelaboratorTags::read(built.checked.checked.engine.environment()).unwrap();
    for (target, num_args, coercee) in [
        ("Coercion.custom", 1, 0),
        ("Coercion.generic", 2, 1),
        ("Coercion.toFunction", 1, 0),
        ("Coercion.later", 1, 0),
    ] {
        assert_eq!(
            before.coercion(&name(target)),
            Some(&CoeFnInfo {
                num_args,
                coercee,
                kind: CoeFnKind::Coe,
            })
        );
    }
    assert!(before.coercion(&name("Coercion.ordinary")).is_none());
    let receipt = imported(&built);
    assert_eq!(
        before,
        DelaboratorTags::read(receipt.engine.environment()).unwrap()
    );
    let constant = |text| fln::Expr::const_(name(text), Vec::new());
    let value = constant("Coercion.a");
    for environment in [
        built.checked.checked.engine.environment(),
        receipt.engine.environment(),
    ] {
        let mut printer = fln::pretty::Printer::new(environment);
        for (function, args, expected) in [
            ("Coercion.custom", vec![value.clone()], "↑Coercion.a"),
            ("Coercion.later", vec![value.clone()], "↑Coercion.a"),
            (
                "Coercion.generic",
                vec![constant("Coercion.A"), value.clone()],
                "↑Coercion.a",
            ),
            (
                "Coercion.toFunction",
                vec![value.clone(), value.clone()],
                "↑Coercion.a Coercion.a",
            ),
            (
                "Coercion.ordinary",
                vec![value.clone()],
                "Coercion.ordinary Coercion.a",
            ),
        ] {
            let application = args.into_iter().fold(constant(function), fln::Expr::app);
            assert_eq!(printer.expr(&application, 0).unwrap(), expected);
        }
    }
    aliases::reference_import_stdout(
        &built,
        r#"prelude
import Lean
import Main
run_cmd do
  for decl in [`Coercion.custom, `Coercion.toFunction, `Coercion.later] do
    let some info ← Lean.Meta.getCoeFnInfo? decl
      | throwError "missing coercion registration: {decl}"
    unless info.numArgs == 1 && info.coercee == 0 && info.type == .coe do
      throwError "incorrect coercion registration: {decl}"
  let some info ← Lean.Meta.getCoeFnInfo? `Coercion.generic
    | throwError "missing generic coercion registration"
  unless info.numArgs == 2 && info.coercee == 1 && info.type == .coe do
    throwError "incorrect generic coercion registration"
#check Coercion.custom Coercion.a
#check Coercion.later Coercion.a
#check Coercion.generic Coercion.a
#check Coercion.toFunction Coercion.a Coercion.a
#check Coercion.ordinary Coercion.a
"#,
        true,
        Some(
            "↑Coercion.a : Coercion.A\n↑Coercion.a : Coercion.A\n↑Coercion.a : Coercion.A\n↑Coercion.a Coercion.a : Coercion.A\nCoercion.ordinary Coercion.a : Coercion.A\n",
        ),
    );
}

#[test]
fn pre_notation_coe_attribute_registers_coercion() {
    use fln_elab::delaborator_tags::{CoeFnInfo, CoeFnKind, DelaboratorTags};

    // Mirrors `Init/Data/Cast.lean`: a `module` + `prelude` file with imports that do not
    // include `Init.Notation`, so `fln-parse` reads `@[coe]` as `Attr.simple("coe", [])`.
    let built = compiled(&[
        (
            "Main",
            r#"module
prelude
public import Init.Prelude
public section
class CastBox (R : Type) where
  protected castBox : Nat → R
@[coe, expose, reducible, match_pattern, inherit_doc CastBox]
protected def castVal {R : Type} [CastBox R] : Nat → R :=
  CastBox.castBox
"#,
        ),
        (
            "Init.Prelude",
            r#"module
prelude
public section
inductive Nat where
  | zero
  | succ (n : Nat)
"#,
        ),
    ]);
    let tags = DelaboratorTags::read(built.checked.checked.engine.environment()).unwrap();
    assert_eq!(
        tags.coercion(&name("castVal")),
        Some(&CoeFnInfo {
            num_args: 3,
            coercee: 2,
            kind: CoeFnKind::Coe,
        })
    );
}

#[test]
fn anonymous_constructor_tags_survive_owned_artifacts_and_diamond_imports() {
    let built = compiled(&[
        ("Main", "prelude\nimport Left\nimport Right"),
        ("Left", "prelude\nimport Base"),
        ("Right", "prelude\nimport Base"),
        ("Base", ANONYMOUS_CONSTRUCTOR_BASE),
    ]);
    let before = fln_elab::delaborator_tags::DelaboratorTags::read(
        built.checked.checked.engine.environment(),
    )
    .unwrap();
    for target in [
        "Pair",
        "Nested",
        "Empty",
        "Atom",
        "Phantom",
        "Recursive",
        "Plain.mk",
        "identity",
        "arbitrary",
    ] {
        assert!(before.anonymous_constructor(&name(&format!("Tagging.{target}"))));
    }
    assert!(!before.anonymous_constructor(&name("Tagging.Plain")));
    assert_eq!(
        built
            .artifacts
            .iter()
            .map(|artifact| metadata(&artifact.bytes).pp_anonymous_constructor.len())
            .collect::<Vec<_>>(),
        [9, 0, 0, 0]
    );
    let receipt = imported(&built);
    let after =
        fln_elab::delaborator_tags::DelaboratorTags::read(receipt.engine.environment()).unwrap();
    assert_eq!(before, after);
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|report| report.pp_anonymous_constructor)
            .collect::<Vec<_>>(),
        [9, 0, 0, 0]
    );
    // Both nullary paths use the admitted structure table after physical import.
    let mut printer = fln::pretty::Printer::new(receipt.engine.environment());
    for (constructor, expected) in [
        ("Tagging.Empty.mk", "⟨⟩"),
        ("Tagging.Atom.mk", "Tagging.Atom.mk"),
    ] {
        assert_eq!(
            printer
                .expr(&fln::Expr::const_(name(constructor), Vec::new()), 0)
                .unwrap(),
            expected
        );
    }
    aliases::reference_import_stdout(
        &built,
        r#"prelude
import Lean
import Main
run_cmd do
  let env ← Lean.getEnv
  for decl in [`Tagging.Pair, `Tagging.Nested, `Tagging.Empty, `Tagging.Atom,
      `Tagging.Phantom, `Tagging.Recursive, `Tagging.Plain.mk, `Tagging.identity, `Tagging.arbitrary] do
    unless Lean.hasPPUsingAnonymousConstructorAttribute env decl do
      throwError "missing anonymous-constructor tag: {decl}"
  if Lean.hasPPUsingAnonymousConstructorAttribute env `Tagging.Plain then
    throwError "a constructor tag was incorrectly transferred to its type"
#check (Tagging.Pair.mk (A := Nat) 1 2)
#check (Tagging.Nested.mk (A := Nat) (Tagging.Pair.mk 1 2) 3)
#check (Tagging.Empty.mk : Tagging.Empty)
#check (Tagging.Atom.mk : Tagging.Atom)
#check (Tagging.Plain.mk (A := Nat) 4)
"#,
        true,
        Some(
            "⟨1, 2⟩ : Tagging.Pair Nat\n⟨⟨1, 2⟩, 3⟩ : Tagging.Nested Nat\n⟨⟩ : Tagging.Empty\nTagging.Atom.mk : Tagging.Atom\n{ value := 4 } : Tagging.Plain Nat\n",
        ),
    );
}

#[test]
fn anonymous_constructor_tags_follow_target_visibility_in_a_private_section() {
    let built = compiled(&[(
        "Main",
        r#"module
prelude
public structure Visible (A : Type) where
  value : A
structure Hidden (A : Type) where
  value : A
attribute [unbox, pp_using_anonymous_constructor] Visible Hidden
public def visible (A : Type) (x : A) : A := x
def hidden (A : Type) (x : A) : A := x
attribute [pp_using_anonymous_constructor] visible hidden
@[pp_using_anonymous_constructor] public axiom visibleA : Type
@[pp_using_anonymous_constructor] axiom hiddenA : Type
"#,
    )]);
    let exported: std::collections::BTreeSet<_> = metadata(&built.artifacts[0].bytes)
        .pp_anonymous_constructor
        .into_iter()
        .collect();
    assert_eq!(
        exported,
        std::collections::BTreeSet::from([name("Visible"), name("visible"), name("visibleA")])
    );
    assert_eq!(metadata(&built.artifacts[0].bytes).unbox, [name("Visible")]);
    let before = fln_elab::delaborator_tags::DelaboratorTags::read(
        built.checked.checked.engine.environment(),
    )
    .unwrap();
    assert_eq!(
        fln_elab::delaborator_tags::source_anonymous_constructors(
            built.checked.checked.engine.environment()
        )
        .unwrap()
        .len(),
        6
    );
    assert_eq!(
        before,
        fln_elab::delaborator_tags::DelaboratorTags::read(imported(&built).engine.environment())
            .unwrap()
    );
    aliases::reference_import_stdout(
        &built,
        r#"prelude
import Lean
import Main
run_cmd do
  let env ← Lean.getEnv
  for decl in [`Visible, `visible, `visibleA] do
    unless Lean.hasPPUsingAnonymousConstructorAttribute env decl do
      throwError "public tag was lost in a private section: {decl}"
"#,
        true,
        Some(""),
    );
}

#[test]
fn invalid_anonymous_constructor_attribute_forms_and_imported_retagging_are_refused() {
    let engine = Engine::builder().build_empty();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "prelude\n@[local pp_using_anonymous_constructor] axiom A : Type",
        "prelude\n@[scoped pp_using_anonymous_constructor] structure S where",
        "prelude\n@[pp_using_anonymous_constructor argument] structure S where",
        "prelude\naxiom A : Type\nattribute [local pp_using_anonymous_constructor] A",
        "prelude\naxiom A : Type\nattribute [scoped pp_using_anonymous_constructor] A",
        "prelude\naxiom A : Type\nattribute [pp_using_anonymous_constructor argument] A",
        "prelude\naxiom A : Type\nattribute [-pp_using_anonymous_constructor] A",
        "prelude\nattribute [pp_using_anonymous_constructor] missing",
        "prelude\naxiom A : Type\nattribute [pp_using_anonymous_constructor, unknown] A",
    ] {
        let error = build(&engine, &[("Main", source)], OleanWriteBudget::default()).unwrap_err();
        assert_eq!(error.disposition().2, 1, "{source}: {error:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    for target in ["Tagging.Pair", "Tagging.Plain"] {
        let source =
            format!("prelude\nimport Base\nattribute [pp_using_anonymous_constructor] {target}");
        let error = build(
            &engine,
            &[("Main", &source), ("Base", ANONYMOUS_CONSTRUCTOR_BASE)],
            OleanWriteBudget::default(),
        )
        .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("cannot modify imported declarations"),
            "{error:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn unbox_tags_survive_artifacts_and_diamond_imports_without_reexporting_inherited_tags() {
    let built = compiled(&[
        ("Main", "prelude\nimport Left\nimport Right"),
        ("Left", "prelude\nimport Base"),
        ("Right", "prelude\nimport Base"),
        ("Base", UNBOX_BASE),
    ]);
    let expected = std::collections::BTreeSet::from([
        name("Boxing.Prod"),
        name("Boxing.Inline"),
        name("Boxing.Choice"),
    ]);
    assert_eq!(
        fln_elab::unbox::read(built.checked.checked.engine.environment()).unwrap(),
        expected
    );
    assert_eq!(
        built
            .artifacts
            .iter()
            .map(|artifact| metadata(&artifact.bytes).unbox.len())
            .collect::<Vec<_>>(),
        [3, 0, 0, 0]
    );
    let receipt = imported(&built);
    assert_eq!(
        fln_elab::unbox::read(receipt.engine.environment()).unwrap(),
        expected
    );
    assert_eq!(
        receipt
            .modules
            .iter()
            .map(|report| report.unbox)
            .collect::<Vec<_>>(),
        [3, 0, 0, 0]
    );
    let probe = "theorem first (A B : Type) (a : A) (b : B) (P : A -> Prop) (h : P a) :\n\
        P ((Boxing.Prod.mk a b).fst) := h";
    receipt
        .engine
        .check_source_files(&[probe.as_bytes()], &KVMap::new(), limits().source)
        .unwrap()
        .into_complete()
        .unwrap();
    // The pin reads the serialized tag extension itself, not our native journal.
    aliases::reference_import_stdout(
        &built,
        r#"prelude
import Lean
import Main
run_cmd do
  let env ← Lean.getEnv
  for decl in [`Boxing.Prod, `Boxing.Inline, `Boxing.Choice] do
    unless Lean.IR.UnboxResult.hasUnboxAttr env decl do
      throwError "missing unbox tag: {decl}"
  for decl in [`Boxing.Untagged, `Boxing.Prod.mk, `Boxing.Prod.fst] do
    if Lean.IR.UnboxResult.hasUnboxAttr env decl then
      throwError "unexpected unbox tag: {decl}"
example (A B : Type) (a : A) (b : B) : (Boxing.Prod.mk a b).fst = a := rfl
"#,
        true,
        Some(""),
    );
}

#[test]
fn invalid_unbox_attributes_and_imported_target_updates_are_refused_atomically() {
    let engine = Engine::builder().build_empty();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "prelude\naxiom A : Type\nattribute [unbox] A",
        "prelude\n@[unbox] axiom A : Type",
        "prelude\ninductive Loop where | stop | step (tail : Loop)\nattribute [unbox] Loop",
        "prelude\n@[unbox] inductive Loop where | stop | step (tail : Loop)",
        "prelude\nstructure Box where\nattribute [unbox] Box.mk",
        "prelude\n@[local unbox] structure Box where",
        "prelude\n@[scoped unbox] inductive Box where | mk",
        "prelude\nstructure Box where\nattribute [local unbox] Box",
        "prelude\nstructure Box where\nattribute [scoped unbox] Box",
        "prelude\n@[unbox argument] structure Box where",
        "prelude\nstructure Box where\nattribute [unbox argument] Box",
        "prelude\nstructure Box where\nattribute [-unbox] Box",
        "prelude\nstructure Box where\nattribute [unbox] missing",
        "prelude\nstructure Box where\nattribute [unbox, unknown] Box",
    ] {
        let error = build(&engine, &[("Main", source)], OleanWriteBudget::default()).unwrap_err();
        assert_eq!(error.disposition().2, 1, "{source}: {error:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    for target in ["Boxing.Prod", "Boxing.Untagged"] {
        let source = format!("prelude\nimport Base\nattribute [unbox] {target}");
        let error = build(
            &engine,
            &[("Main", &source), ("Base", UNBOX_BASE)],
            OleanWriteBudget::default(),
        )
        .unwrap_err();
        assert_eq!(error.disposition().2, 1, "{source}: {error:?}");
        assert!(
            error
                .to_string()
                .contains("cannot modify imported declarations"),
            "{error:?}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn unbox_export_follows_target_visibility_for_a_mixed_private_section_command() {
    let built = compiled(&[(
        "Main",
        "module\nprelude\n\
         public structure Visible (A : Type) where\n  value : A\n\
         structure Hidden (A : Type) where\n  value : A\n\
         attribute [unbox] Visible Hidden\n\
         @[unbox] public structure InlineVisible (A : Type) where\n  value : A\n\
         @[unbox] structure InlineHidden (A : Type) where\n  value : A\n",
    )]);
    let exported: std::collections::BTreeSet<_> = metadata(&built.artifacts[0].bytes)
        .unbox
        .into_iter()
        .collect();
    assert_eq!(
        exported,
        std::collections::BTreeSet::from([name("Visible"), name("InlineVisible")])
    );
    let tags = fln_elab::unbox::read(built.checked.checked.engine.environment()).unwrap();
    assert_eq!(tags.len(), 4);
    assert!(tags.contains(&name("Visible")));
    assert!(tags.contains(&name("InlineVisible")));
    assert_eq!(
        fln_elab::unbox::read(imported(&built).engine.environment()).unwrap(),
        tags
    );
    aliases::reference_import_stdout(
        &built,
        r#"prelude
import Lean
import Main
run_cmd do
  let env ← Lean.getEnv
  unless Lean.IR.UnboxResult.hasUnboxAttr env `Visible &&
      Lean.IR.UnboxResult.hasUnboxAttr env `InlineVisible do
    throwError "public unbox metadata was lost in a private section"
"#,
        true,
        Some(""),
    );
}

#[test]
fn executable_attributes_export_owned_final_maps_across_a_diamond() {
    let built = compiled(&[
        ("Main", MAIN),
        ("Left", "prelude\nimport Base"),
        ("Right", "prelude\nimport Base"),
        ("Base", BASE),
    ]);
    let before = built.checked.checked.engine.environment();
    let receipt = imported(&built);
    let after = receipt.engine.environment();
    let implementations = ImplementedByTable::read(after).unwrap();
    assert_eq!(ImplementedByTable::read(before).unwrap(), implementations);
    assert_eq!(implementations.get(&name("logical")), Some(&name("right")));
    assert_eq!(implementations.get(&name("final")), Some(&name("left")));
    let externs = ExternTable::read(after).unwrap();
    assert_eq!(ExternTable::read(before).unwrap(), externs);
    assert_eq!(
        externs.get(&name("last")),
        Some(
            [ExternEntry::Standard {
                backend: name("all"),
                symbol: "last".into(),
            }]
            .as_slice()
        )
    );
    assert_eq!(
        externs.get(&name("adhoc")),
        Some(
            [ExternEntry::Adhoc {
                backend: name("all"),
            }]
            .as_slice()
        )
    );
    assert_eq!(
        externs.get(&name("foreign")),
        Some(
            [
                ExternEntry::Inline {
                    backend: name("c"),
                    pattern: "#1".into()
                },
                ExternEntry::Standard {
                    backend: name("cpp"),
                    symbol: "foreign_λ".into()
                },
            ]
            .as_slice()
        )
    );
    let counts: Vec<_> = built
        .artifacts
        .iter()
        .map(|artifact| {
            let metadata = metadata(&artifact.bytes);
            (
                artifact.name.clone(),
                metadata.implemented_by.len(),
                metadata.externs.len(),
            )
        })
        .collect();
    assert_eq!(
        counts,
        [
            (name("Base"), 1, 1),
            (name("Left"), 0, 0),
            (name("Right"), 0, 0),
            (name("Main"), 1, 2),
        ]
    );
    aliases::reference_import_stdout(
        &built,
        r##"prelude
import Lean
import Main
example (A : Type) (x y : A) : logical A x y = x := rfl
example (A : Type) (x y : A) : final A x y = y := rfl
run_cmd do
  let env ← Lean.getEnv
  unless Lean.Compiler.getImplementedBy? env `logical == some `right do
    throwError "logical executable replacement changed"
  unless Lean.Compiler.getImplementedBy? env `final == some `left do
    throwError "last implemented_by attribute did not win"
  unless (Lean.externAttr.getParam? env `foreign).map (·.entries) ==
      some [.inline `c "#1", .standard `cpp "foreign_λ"] do
    throwError "extern entry kinds, backends, text, or order changed"
  unless (Lean.externAttr.getParam? env `last).map (·.entries) ==
      some [.standard `all "last"] do
    throwError "last extern attribute did not win"
  unless (Lean.externAttr.getParam? env `adhoc).map (·.entries) ==
      some [.adhoc `all] do
    throwError "empty extern syntax lost its adhoc entry"
"##,
        true,
        Some(""),
    );
}

#[test]
fn invalid_executable_attributes_and_post_compilation_updates_are_refused_atomically() {
    let engine = Engine::builder().build_empty();
    let root = engine.logical_root(&KVMap::new());
    for source in [
        "prelude\n@[implemented_by missing] def f (A : Type) (x : A) : A := x",
        "prelude\n@[implemented_by f] def f (A : Type) (x : A) : A := x",
        "prelude\ndef target (A : Type) (x : A) : A := x\n@[implemented_by target] def f (A : Type) : Type := A",
        "prelude\ndef target (A : Type) (x : A) : A := x\n@[local implemented_by target] def f (A : Type) (x : A) : A := x",
        "prelude\n@[scoped extern \"symbol\"] axiom f : Type",
        // The pin's earlier generated IR is not reconstructible from a final
        // journal, so these post-compilation updates are explicitly unsupported.
        "prelude\ndef target (A : Type) (x : A) : A := x\ndef f (A : Type) (x : A) : A := x\nattribute [implemented_by target] f",
        "prelude\naxiom f : Type\nattribute [extern \"symbol\"] f",
        "prelude\ndef target (A : Type) (x : A) : A := x\naxiom f : (A : Type) -> A -> A\nattribute [implemented_by target] f\nattribute [implemented_by target] f",
        // Standalone `attribute [extern ...]` is allowed on constructors and
        // non-theorem generated structure projections (`ExternAttr.lean:66-73`),
        // never on ordinary definitions, theorem projections, or duplicates.
        "prelude\ndef f (A : Type) (x : A) : A := x\nattribute [extern \"symbol\"] f",
        "prelude\ninductive UnitP : Prop where | intro : UnitP\nstructure PropBox where\n  proof : UnitP\nattribute [extern \"symbol\"] PropBox.proof",
        "prelude\ninductive N : Type where | z : N\nstructure Box where\n  mk ::\n  val : N\nattribute [extern \"first\"] Box.mk\nattribute [extern \"second\"] Box.mk",
    ] {
        let error = build(&engine, &[("Main", source)], OleanWriteBudget::default()).unwrap_err();
        assert_eq!(error.disposition().2, 1, "{source}: {error:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }

    // Positive control: initial standalone `attribute [extern ...]` on a
    // structure constructor and generated non-theorem projection succeeds and
    // round-trips through exported .olean artifacts (`UInt8.ofBitVec` / `UInt8.toBitVec`).
    let built = build(
        &engine,
        &[(
            "Main",
            "prelude\n\
             inductive N : Type where | z : N\n\
             structure Box where\n\
               mk ::\n\
               val : N\n\
             attribute [extern \"box_mk\"] Box.mk\n\
             attribute [extern \"box_val\"] Box.val\n",
        )],
        OleanWriteBudget::default(),
    )
    .expect("standalone extern on structure ctor and projection succeeds")
    .into_complete()
    .expect("standalone extern build completes");
    let receipt = imported(&built);
    let externs = ExternTable::read(receipt.engine.environment()).unwrap();
    assert_eq!(
        externs.get(&name("Box.mk")),
        Some(
            [ExternEntry::Standard {
                backend: name("all"),
                symbol: "box_mk".into(),
            }]
            .as_slice()
        )
    );
    assert_eq!(
        externs.get(&name("Box.val")),
        Some(
            [ExternEntry::Standard {
                backend: name("all"),
                symbol: "box_val".into(),
            }]
            .as_slice()
        )
    );
}

#[test]
fn private_decl_bridges_private_proofs_without_leaking_private_types() {
    let engine = Engine::builder().build_empty();
    let root = engine.logical_root(&KVMap::new());

    // Positive control: inside an `@[expose]` public definition in a `module`,
    // `private_decl%` can call a private helper theorem (`isValidChar_UInt32`
    // shape from `Init/Prelude.lean:2855`), exposing only a checked public
    // auxiliary signature while retaining the checked private proof in the
    // private artifact.
    let built = build(
        &engine,
        &[(
            "Main",
            "module\n\
             prelude\n\
             public section\n\
             inductive N : Type where | z : N | s : N -> N\n\
             inductive P : N -> Prop where | ok (n : N) : P n\n\
             inductive Q : N -> Prop where | ok (n : N) : Q n\n\
             structure Box where\n\
               val : N\n\
               proof : Q val\n\
             private theorem pToQ (n : N) (h : P n) : Q n := Q.ok n\n\
             private def stepN (n : N) : N := N.s n\n\
             private axiom privAx : N\n\
             @[expose] def mkBox (n : N) (h : P n) : Box :=\n\
               Box.mk n (private_decl% pToQ n h)\n\
             @[expose] def pubStep (n : N) : N :=\n\
               private_decl% stepN n\n\
             @[expose] noncomputable def pubNoncomp : N :=\n\
               private_decl% privAx\n\
             @[extern \"ext_pdecl\"] def nonExposeExtern : N :=\n\
               private_decl% privAx\n\
             theorem pubThm : P N.z :=\n\
               let x := private_decl% privAx\n\
               P.ok N.z\n\
             private def nonExporting (n : N) (h : P n) : Q n :=\n\
               private_decl% pToQ n h\n",
        )],
        OleanWriteBudget::default(),
    )
    .expect("private_decl% in exposed public definition succeeds")
    .into_complete()
    .expect("private_decl% build completes");
    let receipt = imported(&built);
    assert!(receipt.engine.environment().contains(&name("mkBox")));
    assert!(
        receipt
            .engine
            .environment()
            .contains(&name("mkBox._private_1"))
    );
    assert!(receipt.engine.environment().contains(&name("pubStep")));
    assert!(
        receipt
            .engine
            .environment()
            .contains(&name("pubStep._private_1"))
    );

    // Negative controls: `private_decl%` must never leak a private type into the
    // exported public world, and must refuse noncomputable private data inside a
    // computable exposed definition.
    for bad in [
        "module\n\
         prelude\n\
         public section\n\
         private inductive Secret : Type where | mk : Secret\n\
         private def secretVal : Secret := Secret.mk\n\
         inductive UnitT : Type where | u : UnitT\n\
         @[expose] def leak : UnitT :=\n\
           (fun (_ : _) => UnitT.u) (private_decl% secretVal)\n",
        "module\n\
         prelude\n\
         public section\n\
         inductive N : Type where | z : N\n\
         private axiom privAx : N\n\
         @[expose] def badNoncomp : N := private_decl% privAx\n",
        "module\n\
         prelude\n\
         public section\n\
         inductive N : Type where | z : N\n\
         private axiom privAx : N\n\
         @[expose, extern \"ext_bad\"] def badExposeExtern : N := private_decl% privAx\n",
        "module\n\
         prelude\n\
         public section\n\
         inductive N : Type where | z : N\n\
         inductive P : N -> Prop where | ok (n : N) : P n\n\
         private axiom privAx : N\n\
         class PropCls : Prop where ok : P N.z\n\
         @[expose] instance : PropCls := let x := private_decl% privAx; PropCls.mk (P.ok N.z)\n",
    ] {
        let err = build(&engine, &[("Main", bad)], OleanWriteBudget::default()).unwrap_err();
        assert_eq!(err.disposition().2, 1, "{bad}: {err:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn tagged_return_requires_extern_and_non_scalar_return_type() {
    let engine = Engine::builder().build_empty();
    let root = engine.logical_root(&KVMap::new());

    let built = build(
        &engine,
        &[(
            "Main",
            "prelude\n\
             inductive Tr : Prop where | ok : Tr\n\
             inductive N : Type where | z : N | s : N -> N\n\
             inductive One : Type where | unit : One\n\
             structure UInt8 where val : N\n\
             structure PairU8 where\n  a : UInt8\n  b : UInt8\n\
             @[extern \"tr_after\", tagged_return] def trAfter (n : N) : N := n\n\
             @[tagged_return, extern \"tr_before\"] def trBefore (n : N) : N := n\n\
             @[extern \"tr_opaque\", tagged_return] opaque trOpaque (n : N) : N := N.z\n\
             @[extern \"tr_standalone\"] def trStandalone (n : N) : N := n\n\
             attribute [tagged_return] trStandalone\n\
             def nonExternStandalone (n : N) : N := n\n\
             attribute [tagged_return] nonExternStandalone\n\
             @[tagged_return] theorem thmNoExtern : Tr := Tr.ok\n\
             @[tagged_return] noncomputable def noncompNoExtern (n : N) : N := n\n\
             @[extern \"tr_one\", tagged_return] def trOne (x : One) : One := x\n\
             @[extern \"tr_pair\", tagged_return] def trPair (x : PairU8) : PairU8 := x\n",
        )],
        OleanWriteBudget::default(),
    )
    .expect("valid @[tagged_return] declarations succeed")
    .into_complete()
    .expect("tagged_return build completes");
    let receipt = imported(&built);
    for decl in [
        "trAfter",
        "trBefore",
        "trOpaque",
        "trStandalone",
        "nonExternStandalone",
        "thmNoExtern",
        "noncompNoExtern",
        "trOne",
        "trPair",
    ] {
        assert!(
            receipt.engine.environment().contains(&name(decl)),
            "missing {decl}"
        );
    }

    for bad in [
        "prelude\n\
         inductive N : Type where | z : N | s : N -> N\n\
         @[tagged_return] def nonExtern (n : N) : N := n\n",
        "prelude\n\
         inductive N : Type where | z : N | s : N -> N\n\
         @[tagged_return] opaque nonExternOpaque (n : N) : N := N.z\n",
        "prelude\n\
         inductive N : Type where | z : N | s : N -> N\n\
         @[extern \"tr_loc\"] def f (n : N) : N := n\n\
         attribute [local tagged_return] f\n",
        "prelude\n\
         inductive Two : Type where | a : Two | b : Two\n\
         @[extern \"tr_enum\", tagged_return] def scalarEnum (x : Two) : Two := x\n",
        "prelude\n\
         inductive N : Type where | z : N\n\
         structure UInt8 where val : N\n\
         @[extern \"tr_u8\", tagged_return] def scalarU8 (x : UInt8) : UInt8 := x\n",
        "prelude\n\
         inductive N : Type where | z : N\n\
         structure Int8 where val : N\n\
         @[extern \"tr_i8\", tagged_return] def scalarI8 (x : Int8) : Int8 := x\n",
        "prelude\n\
         inductive N : Type where | z : N\n\
         structure UInt8 where val : N\n\
         abbrev MyU8 := UInt8\n\
         @[extern \"tr_abbrev\", tagged_return] def scalarAbbrev (x : MyU8) : MyU8 := x\n",
        "prelude\n\
         inductive Tr : Prop where | ok : Tr\n\
         inductive N : Type where | z : N\n\
         structure UInt8 where val : N\n\
         structure WrapU8 where\n  val : UInt8\n  h : Tr\n\
         @[extern \"tr_wrap\", tagged_return] def scalarWrap (x : WrapU8) : WrapU8 := x\n",
    ] {
        let err = build(&engine, &[("Main", bad)], OleanWriteBudget::default()).unwrap_err();
        assert_eq!(err.disposition().2, 1, "{bad}: {err:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn unsafe_opaque_declarations_follow_pinned_safety_and_visibility_rules() {
    let engine = Engine::builder().build_empty();
    let root = engine.logical_root(&KVMap::new());

    let built = build(
        &engine,
        &[(
            "Main",
            "module\n\
             prelude\n\
             public section\n\
             inductive N : Type where | z : N | s : N -> N\n\
             class Inhabited (α : Type) where default : α\n\
             export Inhabited (default)\n\
             instance : Inhabited N where default := N.z\n\
             @[extern \"uo_body\"] unsafe opaque withBody (n : N) : N := n\n\
             @[extern \"uo_default\"] unsafe opaque withDefault {α : Type} [@&Inhabited α] (n : N) : α\n\
             unsafe opaque recOpaque (n : N) : N := recOpaque n\n\
             noncomputable unsafe opaque noncompOpaque (n : N) : N := n\n\
             unsafe def caller (n : N) : N := withBody (withDefault n)\n",
        )],
        OleanWriteBudget::default(),
    )
    .expect("valid unsafe opaque declarations succeed")
    .into_complete()
    .expect("unsafe opaque build completes");
    let receipt = imported(&built);
    for decl in [
        "withBody",
        "withDefault",
        "recOpaque",
        "noncompOpaque",
        "caller",
    ] {
        assert!(
            receipt.engine.environment().contains(&name(decl)),
            "missing {decl}"
        );
    }

    for bad in [
        // Safe def cannot reference an unsafe opaque.
        "prelude\n\
         inductive N : Type where | z : N\n\
         unsafe opaque u : N := N.z\n\
         def safeCaller : N := u\n",
        // Pinned kernel `add_opaque` checks unsafe opaque bodies in safe mode.
        "prelude\n\
         inductive N : Type where | z : N\n\
         unsafe axiom uAx : N\n\
         unsafe opaque badBody : N := uAx\n",
        // `partial` + `unsafe` remains refused.
        "prelude\n\
         inductive N : Type where | z : N\n\
         unsafe partial opaque badMod (n : N) : N := n\n",
    ] {
        let err = build(&engine, &[("Main", bad)], OleanWriteBudget::default()).unwrap_err();
        assert_eq!(err.disposition().2, 1, "{bad}: {err:?}");
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn native_producer_replacements_execute_in_fresh_native_and_pinned_consumers() {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(std::path::PathBuf::from)
        .filter(|path| path.is_dir());
    let Some(lib) = lib else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the actual pinned Prelude and runtime oracle are required",
        );
        eprintln!("SKIP: pinned v4.32.0 lib/lean is unavailable");
        return;
    };
    const STACK: usize = 64 * 1024 * 1024;
    std::thread::Builder::new().stack_size(STACK).spawn(move || {
        let path = lib.join("Init/Prelude.olean");
        let exported = std::fs::read(&path).unwrap();
        let server = std::fs::read(path.with_extension("olean.server")).unwrap();
        let private = std::fs::read(path.with_extension("olean.private")).unwrap();
        let prelude = name("Init.Prelude");
        let prelude_input = OleanModuleInput {
            name: &prelude,
            artifact: &exported,
            server_artifact: Some(&server),
            private_artifact: Some(&private),
        };
        let import_limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
            STACK, Budget::for_stack_bytes(STACK),
        ));
        let producer = Engine::builder().build_empty()
            .import_olean_modules_for_source(
                &[prelude_input],
                std::slice::from_ref(&prelude),
                &KVMap::new(),
                import_limits,
            ).unwrap().into_complete().unwrap().engine;
        let source = r#"prelude
import Init.Prelude
@[implemented_by Nat.succ] def replaced (n : Nat) : Nat := 0
@[implemented_by replaced] def chained (n : Nat) : Nat := 0
axiom late : Nat -> Nat
attribute [implemented_by Nat.succ] late
@[extern "franken_lean_missing_callable"] def blocked (n : Nat) : Nat := 99
@[extern "franken_lean_missing_poly"] def blockedPoly.{u} (A : Type u) (x : A) : A := x
@[extern "franken_lean_missing_pair"] def blockedPair : Nat × Nat := (99, 100)
@[extern "franken_lean_missing_lift"] def blockedLift (n : Nat) : ULift.{0,0} Nat := ULift.up n
@[reducible, extern "franken_lean_missing_dictionary"] def blockedDefault : Inhabited Nat := ⟨99⟩
"#;
        let built = build(&producer, &[("Main", source)], OleanWriteBudget::default())
            .unwrap().into_complete().unwrap();
        let mut inputs = vec![OleanModuleInput {
            name: &prelude,
            artifact: &exported,
            server_artifact: Some(&server),
            private_artifact: Some(&private),
        }];
        inputs.extend(built.artifacts.iter().map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        }));
        let engine = Engine::builder().build_empty()
            .import_olean_modules_for_source(
                &inputs,
                &[name("Main")],
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(
                    STACK, Budget::for_stack_bytes(STACK),
                )),
            ).unwrap().into_complete().unwrap().engine;
        let logical = "example (n : Nat) : replaced n = 0 := rfl\nexample (n : Nat) : chained n = 0 := rfl\n";
        engine.check_source_files(
            &[logical.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))),
        ).unwrap().into_complete().unwrap();
        let queries = concat!(
            "#eval replaced 5\n#eval chained 11\n#eval late 19\n",
            "#eval (fun (f : Nat -> Nat -> Nat) => f 10 13) Nat.add\n",
            "#eval @default Nat ⟨41⟩\n",
        );
        let bounded = fln::EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
        let run = engine.execute_source_commands_with_checks(
            queries.as_bytes(), &KVMap::new(), bounded,
        ).unwrap().into_complete().unwrap();
        let values: Vec<_> = run.batch.executions.iter()
            .map(|execution| fln::closed_vm_value(&execution.exit).unwrap()).collect();
        assert_eq!(values, [
            Some(fln::ClosedVmValue::Scalar(6)),
            Some(fln::ClosedVmValue::Scalar(12)),
            Some(fln::ClosedVmValue::Scalar(20)),
            Some(fln::ClosedVmValue::Scalar(23)),
            Some(fln::ClosedVmValue::Scalar(41)),
        ]);
        assert_eq!(
            ExternTable::read(engine.environment()).unwrap().get(&name("blocked")),
            Some([ExternEntry::Standard {
                backend: name("all"),
                symbol: "franken_lean_missing_callable".into(),
            }].as_slice()),
        );
        for query in [
            "#eval blocked 4",
            "#eval blockedPoly Nat 7",
            "#eval blockedPair.fst",
            "#eval (blockedLift 4).down",
            "#eval @default Nat blockedDefault",
        ] {
            let error = match engine.execute_source_commands_with_checks(
                query.as_bytes(), &KVMap::new(), bounded,
            ) {
                Err(error) => error,
                Ok(_) => panic!("{query}: an unknown extern executed its logical default"),
            };
            assert!(format!("{error:?}").contains("native extern attribute does not match the supported ABI"), "{query}: {error:?}");
        }
        // Nat.succ already has the pin's compiled code. Owned implementation
        // bodies requiring an IR/LCNF facet are not claimed by this test.
        aliases::reference_import_stdout(
            &built,
            &format!("import Main\n{logical}{queries}"),
            true,
            Some("6\n12\n20\n23\n41\n"),
        );
        aliases::reference_import(&built, "import Main\n#eval blocked 4", false);
    }).unwrap().join().unwrap();
}
