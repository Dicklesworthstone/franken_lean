//! Instance indices retain the reducibility world in which they were registered.
#![forbid(unsafe_code)]
use super::*;
use source_extensions::DiscrTreeKey as Key;

const CARRIER: &str = r#"prelude
inductive Token where
  | left
  | right
class Supply (A : Type) where
  value : A
def Carrier : Type := Token
abbrev VisibleCarrier := Carrier
instance (priority := 2000) before : Supply VisibleCarrier := Supply.mk Token.left
"#;

#[test]
fn alias_instance_indices_remain_frozen_across_reducibility_and_physical_imports() {
    let source = format!(
        r#"{CARRIER}
def selectedBefore : Carrier := Supply.value
theorem beforeCorrect (P : Token -> Prop) (h : P Token.left) : P selectedBefore := h
attribute [reducible] Carrier
instance (priority := 1000) after : Supply VisibleCarrier := Supply.mk Token.right
namespace Regional
scoped instance (priority := 3000) regional : Supply VisibleCarrier := Supply.mk Token.left
end Regional
"#
    );
    let built = compiled(&[("Main", &source)]);
    let rows = metadata(&built.artifacts[0].bytes).instances;
    assert_eq!(rows.len(), 3);
    for (row, declaration, priority, carrier, scope) in [
        (&rows[0], "before", 2000, "Carrier", None),
        (&rows[1], "after", 1000, "Token", None),
        (
            &rows[2],
            "Regional.regional",
            3000,
            "Token",
            Some("Regional"),
        ),
    ] {
        assert_eq!(row.declaration, name(declaration));
        assert_eq!(row.priority, priority);
        assert_eq!(row.scope, scope.map(name));
        assert!(row.synth_order.is_empty());
        assert_eq!(
            row.keys,
            [Key::Const(name("Supply"), 1), Key::Const(name(carrier), 0)]
        );
    }
    let receipt = imported(&built);
    assert_eq!(receipt.modules[0].instances, 3);
    for engine in [&built.checked.checked.engine, &receipt.engine] {
        let root = engine.logical_root(&KVMap::new());
        for (scope, selected, wrong) in [
            ("", "right", "left"),
            ("open scoped Regional\n", "left", "right"),
        ] {
            let consumer = format!(
                "{scope}def chosen : Carrier := Supply.value\ntheorem correct (P : Token -> Prop) (h : P Token.{selected}) : P chosen := h"
            );
            engine
                .check_source_files(&[consumer.as_bytes()], &KVMap::new(), limits().source)
                .unwrap()
                .into_complete()
                .unwrap();
            let refused = format!(
                "{scope}def chosen : Carrier := Supply.value\ntheorem wrong (P : Token -> Prop) (h : P Token.{wrong}) : P chosen := h"
            );
            assert!(
                engine
                    .check_source_files(&[refused.as_bytes()], &KVMap::new(), limits().source)
                    .is_err()
            );
            assert_eq!(engine.logical_root(&KVMap::new()), root);
        }
    }
    aliases::reference_import(
        &built,
        "prelude\nimport Main\nnoncomputable section\ndef chosen : Carrier := Supply.value\ntheorem correct (P : Token -> Prop) (h : P Token.right) : P chosen := h\nopen scoped Regional\ndef scopedChoice : Carrier := Supply.value\ntheorem scopedCorrect (P : Token -> Prop) (h : P Token.left) : P scopedChoice := h",
        true,
    );
}

#[test]
fn aliases_can_hide_instance_telescopes_targets_and_dependent_prerequisites() {
    let source = r#"prelude
universe u
inductive Token where
  | left
  | right
class Answer {A : Type u} (a : A) where
  value : Token
class Result (A : Type u) where
  apply : A -> Token
abbrev Family (A : Type u) := (a : A) -> Answer a
abbrev HaveResult (A : Type u) := Result A
instance tokenAnswer : Family Token := fun a => @Answer.mk Token a Token.right
instance viaAlias {A : Type u} [dict : Family A] : HaveResult A :=
  Result.mk (fun a => @Answer.value A a (dict a))
"#;
    let built = compiled(&[("Main", source)]);
    let rows = metadata(&built.artifacts[0].bytes).instances;
    assert_eq!(rows.len(), 2);
    assert_eq!(rows[0].declaration, name("tokenAnswer"));
    assert_eq!(
        rows[0].keys,
        [
            Key::Const(name("Answer"), 2),
            Key::Const(name("Token"), 0),
            Key::Star,
        ]
    );
    assert!(rows[0].synth_order.is_empty());
    assert_eq!(rows[1].declaration, name("viaAlias"));
    assert_eq!(rows[1].keys, [Key::Const(name("Result"), 1), Key::Star]);
    assert_eq!(rows[1].synth_order, [1]);
    let receipt = imported(&built);
    let consumer = "def chosen : Token := Result.apply Token.left\ntheorem selectedRight (P : Token -> Prop) (h : P Token.right) : P chosen := h";
    for engine in [&built.checked.checked.engine, &receipt.engine] {
        let root = engine.logical_root(&KVMap::new());
        engine
            .check_source_files(&[consumer.as_bytes()], &KVMap::new(), limits().source)
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(
            engine
                .check_source_files(
                    &[b"def chosen : Token := Result.apply Token.left\ntheorem wrong (P : Token -> Prop) (h : P Token.left) : P chosen := h"],
                    &KVMap::new(),
                    limits().source,
                )
                .is_err()
        );
        assert_eq!(engine.logical_root(&KVMap::new()), root);
    }
    aliases::reference_import(
        &built,
        &format!("prelude\nimport Main\nnoncomputable section\n{consumer}"),
        true,
    );
}

#[test]
fn an_irreducible_instance_telescope_falls_through_without_corrupting_its_saved_order() {
    let prefix = r#"prelude
inductive Token where
  | left
  | right
class Need where
  value : Token
class Goal where
  value : Token
instance need : Need := Need.mk Token.left
instance (priority := 500) fallback : Goal := Goal.mk Token.right
abbrev Candidate := [n : Need] -> Goal
instance (priority := 2000) hidden : Candidate := fun [n : Need] => Goal.mk Need.value
"#;
    for (change, selected, wrong) in [
        ("", "left", "right"),
        (
            "set_option allowUnsafeReducibility true\nattribute [irreducible] Candidate\n",
            "right",
            "left",
        ),
    ] {
        let source = format!("{prefix}{change}");
        let built = compiled(&[("Main", &source)]);
        let rows = metadata(&built.artifacts[0].bytes).instances;
        let hidden = rows
            .iter()
            .find(|row| row.declaration == name("hidden"))
            .unwrap();
        assert_eq!(hidden.keys, [Key::Const(name("Goal"), 0)]);
        assert_eq!(hidden.synth_order, [0]);
        assert_eq!(hidden.priority, 2000);
        let receipt = imported(&built);
        for engine in [&built.checked.checked.engine, &receipt.engine] {
            let root = engine.logical_root(&KVMap::new());
            let consumer = format!(
                "def chosen : Token := Goal.value\ntheorem correct (P : Token -> Prop) (h : P Token.{selected}) : P chosen := h"
            );
            engine
                .check_source_files(&[consumer.as_bytes()], &KVMap::new(), limits().source)
                .unwrap_or_else(|error| panic!("{change}{consumer}: {error:?}"))
                .into_complete()
                .unwrap();
            let refused = format!(
                "def chosen : Token := Goal.value\ntheorem wrong (P : Token -> Prop) (h : P Token.{wrong}) : P chosen := h"
            );
            assert!(
                engine
                    .check_source_files(&[refused.as_bytes()], &KVMap::new(), limits().source)
                    .is_err(),
                "{change}{refused}"
            );
            assert_eq!(engine.logical_root(&KVMap::new()), root);
            assert!(!engine.environment().contains(&name("chosen")));
        }
    }
}

#[test]
fn path_changing_instance_reregistration_is_an_atomic_capability_refusal() {
    let checked = Engine::builder()
        .build_empty()
        .check_source_files(
            &[CARRIER.strip_prefix("prelude\n").unwrap().as_bytes()],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = checked.engine;
    for (declaration, expected) in [
        (
            "Carrier",
            fln_elab::reducibility::Reducibility::Semireducible,
        ),
        (
            "VisibleCarrier",
            fln_elab::reducibility::Reducibility::Reducible,
        ),
        (
            "before",
            fln_elab::reducibility::Reducibility::ImplicitReducible,
        ),
    ] {
        assert_eq!(
            fln_elab::reducibility::known_status(engine.environment(), &name(declaration)).unwrap(),
            Some(expected),
            "{declaration}"
        );
    }
    let root = engine.logical_root(&KVMap::new());
    let error = engine
        .check_source_files(
            &[b"set_option allowUnsafeReducibility true\nattribute [reducible] Carrier\ndef uncommitted : Token := Token.right\nattribute [instance 3000] before"],
            &KVMap::new(),
            limits().source,
        )
        .unwrap_err();
    assert_eq!(error.disposition(), ("capability", false, 5), "{error:?}");
    let fln::SourceCheckError::Command { error, .. } = error else {
        panic!("expected the unsupported registration update")
    };
    assert!(matches!(
        error.as_ref(),
        fln::EngineExecutionError::Frontend(fln::DefinitionFrontendError::Elaborate(
            fln_elab::NatDefinitionElabError::Inference(
                fln_elab::source::SourceInferenceError::InstanceRegistry(
                    fln_elab::instances::InstanceRegistryError::UnsupportedIndexUpdate(declaration)
                )
            )
        )) if *declaration == name("before")
    ));
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    assert!(!engine.environment().contains(&name("uncommitted")));
    engine
        .check_source_files(
            &[b"attribute [instance 3000] before\ndef recovered : Carrier := Supply.value\ntheorem correct (P : Token -> Prop) (h : P Token.left) : P recovered := h"],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn an_unsupported_alias_index_cannot_be_repaired_by_later_reducibility() {
    let prefix = r#"prelude
inductive Token where
  | left
  | right
class Higher (F : Type -> Type) where
  value : Token
abbrev IdentityType (A : Type) := A
set_option allowUnsafeReducibility true
"#;
    let declaration = "instance higher : Higher IdentityType := Higher.mk Token.right\n";
    let change = "attribute [irreducible] IdentityType\n";
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    // An unapplied reducible alias requires lambda indexing, which this
    // fragment does not support. A later folded shape cannot rewrite its past.
    let unsupported = format!("{prefix}{declaration}{change}");
    initial
        .check_source_files(
            &[unsupported.strip_prefix("prelude\n").unwrap().as_bytes()],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let error = build(
        &initial,
        &[("Main", &unsupported)],
        OleanWriteBudget::default(),
    )
    .unwrap_err();
    assert!(matches!(
        error,
        SourceModuleBuildError::Check(SourceModuleCheckError::Extension { extension, .. })
            if extension == name("FrankenLean.sourceInstances.v1")
    ));
    assert_eq!(initial.logical_root(&KVMap::new()), root);
    let supported = format!("{prefix}{change}{declaration}");
    let built = compiled(&[("Main", &supported)]);
    let rows = metadata(&built.artifacts[0].bytes).instances;
    assert_eq!(rows.len(), 1);
    assert_eq!(
        rows[0].keys,
        [
            Key::Const(name("Higher"), 1),
            Key::Const(name("IdentityType"), 0),
        ]
    );
    let receipt = imported(&built);
    receipt
        .engine
        .check_source_files(
            &[b"def chosen : Token := Higher.value (F := IdentityType)\ntheorem correct (P : Token -> Prop) (h : P Token.right) : P chosen := h"],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
}
