//! Parent projections and explicitly registered conversions match the pin.
//!
//! `extends` alone does not install `Coe`/`CoeDep` instances in Lean 4.32.0.
//! Keep the former automatic-conversion expectations as rejection regressions,
//! alongside the same value-preservation checks with user-declared instances.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::name::Name;
use fln_elab::instances::InstanceRegistry;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_coercion_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, text: &str) -> Engine {
    base.check_source_files(
        &[text.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{text}: {e:?}"))
    .into_complete()
    .expect("both checkers must complete")
    .engine
}

fn refused(base: &Engine, text: &str) {
    let before = base.logical_root(&KVMap::new());
    let error = base
        .check_source_files(
            &[text.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err(text);
    // Retain main's rigid-mismatch diagnostic guarantee as well as refusal.
    assert_eq!(error.disposition().0, "elaboration", "{text}: {error}");
    assert!(
        error.to_string().contains("Type mismatch"),
        "{text}: {error}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), before);
}

#[test]
fn structure_extends_does_not_install_automatic_parent_coercions() {
    let base = checked(
        &engine(),
        "structure Base where\n  value : Nat\nstructure Child extends Base where\n  tag : Nat\ndef getValue (b : Base) : Nat := b.value\ndef c : Child := { value := 37, tag := 9 }",
    );
    for text in ["def asParent : Base := c", "def result : Nat := getValue c"] {
        refused(&base, text);
    }
    checked(
        &base,
        "def asParent : Base := c.toBase\ndef result : Nat := getValue c.toBase\ntheorem result_ok : result = 37 := by rfl\ntheorem cast_ok : asParent.value = 37 := by rfl",
    );
    for class in ["Coe", "CoeDep"] {
        assert!(
            !InstanceRegistry::read(base.environment())
                .unwrap()
                .candidates(&Name::from_components([class]))
                .iter()
                .any(|row| row.declaration.parent()
                    == Name::from_components(["Child", "_parentCoe"]))
        );
    }
}

#[test]
fn registered_parent_coercions_accept_child_values_in_parent_functions() {
    checked(
        &engine(),
        "structure Base where\n  value : Nat\nstructure Child extends Base where\n  tag : Nat\ninstance childToBase : Coe Child Base := Coe.mk (fun x => x.toBase)\ndef getValue (b : Base) : Nat := b.value\ndef c : Child := { value := 37, tag := 9 }\ndef asParent : Base := c\ndef result : Nat := getValue c\ntheorem result_ok : result = 37 := by rfl\ntheorem cast_ok : asParent.value = 37 := by rfl",
    );
}

#[test]
fn parameterized_and_transitive_parent_coercions_preserve_actual_fields() {
    let base = checked(
        &engine(),
        "structure Base (A : Type) where\n  value : A\nstructure Middle (A : Type) extends Base A where\n  tag : Nat\nstructure Leaf (A : Type) extends Middle A where\n  last : Nat\ndef getValue (b : Base Nat) : Nat := b.value\ndef c : Leaf Nat := { value := 19, tag := 23, last := 29 }",
    );
    refused(&base, "def asBase : Base Nat := c");
    refused(&base, "def toMiddle : Middle Nat := c");
    checked(
        &base,
        "def projectedMiddle : Middle Nat := c.toMiddle\ntheorem projected_base : getValue c.toBase = 19 := by rfl\ntheorem projected_middle : projectedMiddle.tag = 23 := by rfl",
    );
    checked(
        &base,
        "instance middleToBase (A : Type) : Coe (Middle A) (Base A) := Coe.mk (fun x => x.toBase)\ninstance leafToMiddle (A : Type) : Coe (Leaf A) (Middle A) := Coe.mk (fun x => x.toMiddle)\ntheorem transitive_ok : getValue c = 19 := by rfl\ndef toMiddle : Middle Nat := c\ntheorem middle_ok : toMiddle.tag = 23 := by rfl",
    );
}

#[test]
fn dependent_parent_coercions_keep_target_types_tied_to_the_source_value() {
    // The pin refuses a bare `31` at the semireducible type `b.carrier`
    // (fln-5efd: OfNat synthesis uses instances transparency). Give the numeral
    // its own Nat type before conversion, and also check a symbolic receiver
    // so the dependent parent type cannot be replaced by this fixture's Nat.
    let base = checked(
        &engine(),
        "structure Carrier where\n  carrier : Type\nstructure Value (A : Type) where\n  value : A\nstructure Both extends Carrier, Value carrier where\n  tag : Nat\ndef b : Both := { carrier := Nat, value := 31, tag := 37 }",
    );
    refused(&base, "def castParent (x : Both) : Value x.carrier := x");
    checked(
        &base,
        "def castByProjection (x : Both) : Value x.carrier := x.toValue\ntheorem projected_value (x : Both) : (castByProjection x).value = x.value := rfl",
    );
    let result = checked(
        &base,
        "instance bothToValue (x : Both) : CoeDep Both x (Value x.carrier) := CoeDep.mk x.toValue\ndef castParent (x : Both) : Value x.carrier := x\ntheorem dependent_ok : (castParent b).value = (31 : Nat) := by rfl\ntheorem parent_value (x : Both) : (castParent x).value = x.toValue.value := by rfl",
    );
    assert!(
        InstanceRegistry::read(result.environment())
            .unwrap()
            .candidates(&Name::from_components(["CoeDep"]))
            .iter()
            .any(|row| row.declaration == Name::from_components(["bothToValue"]))
    );
}

#[test]
fn failed_parent_conversion_does_not_publish_partial_files_or_instances() {
    let base = checked(
        &engine(),
        "structure Base where\n  value : Nat\nstructure Other where\n  value : Bool\nstructure Child extends Base where\n  tag : Nat\ninstance childToBase : Coe Child Base := Coe.mk (fun x => x.toBase)\ndef c : Child := { value := 5, tag := 7 }",
    );
    let before = base.logical_root(&KVMap::new());
    for text in [
        "def bad : Other := c",
        "structure Temporary extends Child where\n  more : Nat\ninstance temporaryToChild : Coe Temporary Child := Coe.mk (fun x => x.toChild)\ndef bad : Other := c",
        "def validPrefix : Base := c\ndef bad : Child := Base.mk 7",
    ] {
        assert!(
            base.check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{text}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["Temporary"]))
        );
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["validPrefix"]))
        );
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["temporaryToChild"]))
        );
    }
    checked(
        &base,
        "def valid : Base := c\ntheorem recovery : valid.value = 5 := by rfl",
    );
}

#[test]
fn omitted_class_parent_uses_instances_but_explicit_fields_override_them() {
    checked(
        &engine(),
        "class Base (A : Type) where\n  value : A\ninstance natural : Base Nat := Base.mk 17\nclass Child (A : Type) extends Base A where\n  tag : Nat\ninstance fromParent : Child Nat := { tag := 19 }\ndef explicit : Child Nat := { value := 23, tag := 29 }\ntheorem inferred_parent : fromParent.value = 17 := by rfl\ntheorem explicit_wins : explicit.value = 23 := by rfl",
    );
}

#[test]
fn class_parent_dictionary_instances_do_not_install_value_coercions() {
    let base = checked(
        &engine(),
        "class Base where\n  value : Nat\nclass Child extends Base where\n  tag : Nat\ninstance child : Child := { value := 17, tag := 19 }\ndef parentValue [b : Base] : Nat := b.value\ntheorem inferred_parent : parentValue = 17 := by rfl",
    );
    assert!(
        InstanceRegistry::read(base.environment())
            .unwrap()
            .candidates(&Name::from_components(["Base"]))
            .iter()
            .any(|row| row.declaration == Name::from_components(["Child", "toBase"]))
    );
    refused(&base, "def parentFromValue (x : Child) : Base := x");
}

#[test]
fn parent_defaults_remain_available_after_failed_instance_search() {
    checked(
        &engine(),
        "class Base where\n  value : Nat := 17\nclass Child extends Base where\n  tag : Nat\ninstance fromDefault : Child := { tag := 19 }\ntheorem fallback : fromDefault.value = 17 := by rfl",
    );
}

#[test]
fn parent_defaults_remain_available_after_failed_instance_prerequisites() {
    checked(
        &engine(),
        "class ParentPrerequisite where\n  witness : Nat\nclass Base where\n  value : Nat := 17\ninstance unavailable [ParentPrerequisite] : Base := Base.mk 99\nclass Child extends Base where\n  tag : Nat\ninstance fromDefault : Child := { tag := 19 }\ntheorem fallback : fromDefault.value = 17 := by rfl",
    );
}
