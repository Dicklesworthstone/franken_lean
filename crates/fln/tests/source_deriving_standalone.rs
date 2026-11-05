//! Standalone deriving commands share the checked handler/admission path with
//! declaration suffixes. Visibility, freshness and defaults were compared with
//! the SUITE.lock Lean v4.32.0 executable, including mixed private/public groups.
#![forbid(unsafe_code)]

use fln::source_check::modules::{SourceModuleCheck, SourceModuleCheckLimits};
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, SourceCheckLimits,
    SourceModuleInput, VmExit,
};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}

fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .expect("every generated declaration passes both checkers")
    .engine
}

fn modules(base: &Engine, files: &[(&str, &str)]) -> SourceModuleCheck {
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let inputs: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    base.check_source_modules(
        &inputs,
        &names[0],
        &KVMap::new(),
        SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
    )
    .unwrap_or_else(|error| panic!("{files:?}\n{error:?}"))
    .into_complete()
    .unwrap()
}

#[test]
fn multiple_handlers_and_targets_admit_checked_helpers_in_source_order() {
    let base = engine();
    let result = checked(
        &base,
        r#"
        inductive Shade where
          | dark | light
        structure Point where
          count : Nat := 7
        deriving instance Inhabited, BEq, DecidableEq for Shade, Point
        theorem defaultShade : (default : Shade) = Shade.dark := by rfl
        theorem defaultPoint : (default : Point).count = 7 := by rfl
        theorem differentShade : (Shade.dark == Shade.light) = false := by rfl
        theorem differentPoint : Not (Point.mk 7 = Point.mk 9) := by decide
        theorem enumFirst : Shade.ofNat 0 = Shade.dark := by rfl
        theorem enumLast : Shade.ofNat 100 = Shade.light := by rfl
    "#,
    );
    for (class, helper) in [
        ("Inhabited", "default"),
        ("BEq", "beq"),
        ("DecidableEq", "decEq"),
    ] {
        for target in ["Shade", "Point"] {
            for name in [
                format!("inst{class}{target}"),
                format!("inst{class}{target}.{helper}"),
            ] {
                let Some(ConstantInfo::Defn(definition)) = result.environment().find(&n(&name))
                else {
                    panic!("missing generated definition {name}");
                };
                assert_eq!(definition.safety, DefinitionSafety::Safe);
                assert!(!definition.value.has_expr_mvar());
                assert!(!definition.value.has_fvar());
                assert!(!base.environment().contains(&n(&name)));
            }
        }
    }
}

#[test]
fn executable_files_run_the_derived_helpers_and_serialized_code() {
    let result = engine()
        .execute_source_definitions(
            &[br#"
structure Settings where
  count : Nat := 7
  next : Nat := count + 2
  enabled : Bool := true
deriving instance Inhabited, BEq, DecidableEq for Settings
#eval (default : Settings).next
#eval if (Settings.mk 7 9 true == Settings.mk 7 9 true) then 1 else 0
#eval if decide (Settings.mk 7 9 true = Settings.mk 7 10 true) then 1 else 0
"#],
            &KVMap::new(),
            EngineExecutionLimits::new(limits().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(result.executions.len(), 3);
    for (execution, expected) in result.executions.iter().zip(["9", "1", "0"]) {
        let VmExit::Returned(value) = &execution.exit else {
            panic!("returned value")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
        let replay =
            fln::execute_flbc_artifact(&execution.flbc_artifact, &KVMap::new(), Default::default())
                .unwrap()
                .into_complete()
                .unwrap();
        let VmExit::Returned(value) = &replay else {
            panic!("replayed returned value")
        };
        assert_eq!(
            fln_vm::interpreter::nat_decimal(&value.value).as_deref(),
            Some(expected)
        );
    }
}

#[test]
fn namespaces_class_aliases_and_section_variables_resolve_global_targets() {
    checked(
        &engine(),
        r#"
        namespace Types
        inductive Shade where
          | dark | light
        end Types
        namespace Classes
        export _root_ (Inhabited BEq)
        end Classes
        namespace Consumer
        open Types
        section
        variable (Shade : Type)
        deriving instance Classes.Inhabited, Classes.BEq for Shade
        end
        def selected : Types.Shade := default
        theorem chosen : selected = Types.Shade.dark := by rfl
        theorem equal : (Types.Shade.dark == Types.Shade.dark) = true := by rfl
        end Consumer
    "#,
    );
}

#[test]
fn root_export_prefers_exact_root_names_and_refuses_self_export() {
    let base = checked(
        &engine(),
        r#"
def choice : Nat := 7
namespace Outer
def choice : Nat := 9
namespace Aliases
export _root_ (choice)
theorem rootChosen : choice = 7 := by rfl
end Aliases
end Outer
"#,
    );
    for source in [
        "theorem captured : Outer.Aliases.choice = 9 := by rfl",
        "export _root_ (Inhabited)",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .is_err(),
            "{source}"
        );
    }
}

#[test]
fn record_defaults_avoid_unneeded_parameter_dictionaries() {
    checked(
        &engine(),
        r#"
        inductive Empty where
        structure Optional (A : Type) where
          value : Option A := Option.none
        deriving instance Inhabited for Optional
        def noInhabitedParameter : Optional Empty := default
        theorem noValue : noInhabitedParameter.value = Option.none := by rfl
        def expected {A : Type} : Inhabited (Optional A) := instInhabitedOptional
    "#,
    );
}

#[test]
fn repeated_derivation_freshens_helpers_and_keeps_the_enum_collision() {
    let base = checked(
        &engine(),
        r#"
        inductive Tone where
          | low | high
        structure Box where
          value : Nat
        deriving instance Inhabited, BEq for Tone
        deriving instance Inhabited, BEq for Tone
        deriving instance DecidableEq for Box
        deriving instance DecidableEq for Box
        theorem stillEqual : decide (Box.mk 3 = Box.mk 3) = true := by rfl
    "#,
    );
    for name in [
        "instInhabitedTone_1",
        "instInhabitedTone_1.default",
        "instBEqTone_1",
        "instBEqTone_1.beq",
        "instDecidableEqBox_1.decEq",
    ] {
        assert!(base.environment().contains(&n(name)), "{name}");
    }
    let once = checked(&base, "deriving instance DecidableEq for Tone");
    let root = once.logical_root(&KVMap::new());
    assert!(
        once.admit_source_command(
            b"deriving instance DecidableEq for Tone",
            &KVMap::new(),
            limits(),
        )
        .is_err(),
        "the pin rejects a second Tone.ofNat"
    );
    assert_eq!(once.logical_root(&KVMap::new()), root);
    assert!(!once.environment().contains(&n("instDecidableEqTone_1")));
}

#[test]
fn later_target_or_handler_failure_publishes_no_successful_prefix() {
    let base = checked(
        &engine(),
        r#"
        structure Point where
          count : Nat
        inductive Empty where
        structure FunctionBox where
          function : Nat -> Nat
        class Unknown (A : Type) where
          value : A
        def Alias := Point
        abbrev Defaulted := Inhabited
    "#,
    );
    let root = base.logical_root(&KVMap::new());
    for command in [
        "deriving instance Inhabited for Point, Empty",
        "deriving instance Inhabited, BEq for Point, FunctionBox",
        "deriving instance Inhabited, Unknown for Point",
        "deriving instance Inhabited for Point, Missing",
        "deriving instance Inhabited for Alias",
        "deriving instance Defaulted for Point",
    ] {
        assert!(
            base.admit_source_command(command.as_bytes(), &KVMap::new(), limits())
                .is_err(),
            "{command}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&n("instInhabitedPoint")));
        assert!(
            !base
                .environment()
                .contains(&n("instInhabitedPoint.default"))
        );
    }
    checked(
        &base,
        "deriving instance Inhabited for Point\ntheorem recovered : (default : Point).count = 0 := by rfl",
    );
}

#[test]
fn modern_public_derivation_uses_public_dictionary_history() {
    let result = modules(
        &engine(),
        &[
            (
                "Main",
                "module\nprelude\npublic import Api\npublic theorem chosen : (default : Box).value = Signal.off := by rfl",
            ),
            (
                "Api",
                r#"module
prelude
public inductive Signal where
  | off | on
public instance visible : Inhabited Signal where
  default := Signal.off
private instance hidden : Inhabited Signal where
  default := Signal.on
public structure Box where
  value : Signal
deriving instance Inhabited for Box
"#,
            ),
        ],
    );
    assert!(matches!(
        result
            .checked
            .engine
            .environment()
            .find(&n("instInhabitedBox.default")),
        Some(ConstantInfo::Defn(_))
    ));
    assert!(result.checked.engine.environment().contains(&n("chosen")));
}

#[test]
fn mixed_visibility_is_private_and_later_public_derivation_has_a_fresh_export() {
    let api = r#"module
prelude
public inductive Tone where
  | low | high
private inductive Hidden where
  | only
deriving instance Inhabited for Tone, Hidden
deriving instance Inhabited for Tone
"#;
    let result = modules(
        &engine(),
        &[
            (
                "Main",
                "module\nprelude\npublic import Api\npublic def exported : Inhabited Tone := instInhabitedTone_1\npublic theorem chosen : (default : Tone) = Tone.low := by rfl",
            ),
            ("Api", api),
        ],
    );
    let env = result.checked.engine.environment();
    assert!(env.contains(&n("instInhabitedTone_1")));
    assert!(env.contains(&n("instInhabitedTone_1.default")));
    let hidden = Name::num(n("_private.Api"), 0).append_core(&n("instInhabitedTone"));
    assert!(!env.contains(&hidden));
    assert!(!env.contains(&n("instInhabitedTone")));

    let names = [n("Main"), n("Api")];
    let inputs = [
        SourceModuleInput { name: &names[0], source: b"module\nprelude\npublic import Api\npublic def missing : Tone := default" },
        SourceModuleInput { name: &names[1], source: b"module\nprelude\npublic inductive Tone where\n| low\nprivate inductive Hidden where\n| only\nderiving instance Inhabited for Tone, Hidden" },
    ];
    assert!(
        engine()
            .check_source_modules(
                &inputs,
                &names[0],
                &KVMap::new(),
                SourceModuleCheckLimits::new(SourceCheckLimits::new(limits()))
            )
            .is_err()
    );
}

#[test]
fn imported_types_can_derive_in_a_downstream_namespace() {
    let result = modules(
        &engine(),
        &[
            (
                "Main",
                "prelude\nimport Consumer\ndef selected : Types.Shade := default\ntheorem chosen : selected = Types.Shade.dark := by rfl",
            ),
            (
                "Consumer",
                "prelude\nimport Types\nnamespace Client\nopen Types\nderiving instance Inhabited, BEq for Shade\nend Client",
            ),
            (
                "Types",
                "prelude\nnamespace Types\ninductive Shade where\n| dark\n| light\nend Types",
            ),
        ],
    );
    assert!(result.checked.engine.environment().contains(&n("chosen")));
}

#[test]
fn private_enum_helpers_cannot_be_republished_by_a_later_public_derivation() {
    let initial = "module\nprelude\npublic inductive Tone where\n| low\n| high\nprivate inductive Hidden where\n| only\nderiving instance DecidableEq for Tone, Hidden";
    let base = engine();
    let first = modules(&base, &[("Api", initial)]);
    assert!(
        first
            .checked
            .engine
            .environment()
            .contains(&n("Tone.ofNat"))
    );
    let later = format!("{initial}\nderiving instance DecidableEq for Tone");
    let module = n("Api");
    let error = base
        .check_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: later.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
        )
        .expect_err("the private predecessor already owns Tone.ofNat");
    assert!(format!("{error:?}").contains("ofNat"), "{error:?}");
    assert!(!base.environment().contains(&n("Tone.ofNat")));
}
