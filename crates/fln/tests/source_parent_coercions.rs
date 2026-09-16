//! Inheritance conversions use normal typeclass search and pass both checkers.
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

#[test]
fn automatic_parent_coercions_accept_child_values_in_parent_functions() {
    checked(
        &engine(),
        "structure Base where\n  value : Nat\nstructure Child extends Base where\n  tag : Nat\ndef get (b : Base) : Nat := b.value\ndef c : Child := { value := 37, tag := 9 }\ndef asParent : Base := c\ndef result : Nat := get c\ntheorem result_ok : result = 37 := by rfl\ntheorem cast_ok : asParent.value = 37 := by rfl",
    );
}

#[test]
fn parameterized_and_transitive_parent_coercions_preserve_actual_fields() {
    checked(
        &engine(),
        "structure Base (A : Type) where\n  value : A\nstructure Middle (A : Type) extends Base A where\n  tag : Nat\nstructure Leaf (A : Type) extends Middle A where\n  last : Nat\ndef get (b : Base Nat) : Nat := b.value\ndef c : Leaf Nat := { value := 19, tag := 23, last := 29 }\ntheorem transitive_ok : get c = 19 := by rfl\ndef toMiddle : Middle Nat := c\ntheorem middle_ok : toMiddle.tag = 23 := by rfl",
    );
}

#[test]
fn dependent_parent_coercions_keep_target_types_tied_to_the_source_value() {
    let result = checked(
        &engine(),
        "structure Carrier where\n  carrier : Type\nstructure Value (A : Type) where\n  value : A\nstructure Both extends Carrier, Value carrier where\n  tag : Nat\ndef b : Both := { carrier := Nat, value := 31, tag := 37 }\ndef cast (b : Both) : Value b.carrier := b\ntheorem dependent_ok : (cast b).value = 31 := by rfl",
    );
    assert!(
        InstanceRegistry::read(result.environment())
            .unwrap()
            .candidates(&Name::from_components(["CoeDep"]))
            .iter()
            .any(|row| row.declaration.parent() == Name::from_components(["Both", "_parentCoe"]))
    );
}

#[test]
fn failed_parent_conversion_does_not_publish_partial_files_or_instances() {
    let base = checked(
        &engine(),
        "structure Base where\n  value : Nat\nstructure Other where\n  value : Bool\nstructure Child extends Base where\n  tag : Nat\ndef c : Child := { value := 5, tag := 7 }",
    );
    let before = base.logical_root(&KVMap::new());
    for text in [
        "def bad : Other := c",
        "structure Temporary extends Child where\n  more : Nat\ndef bad : Other := c",
        "def prefix : Base := c\ndef bad : Child := Base.mk 7",
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
                .contains(&Name::from_components(["prefix"]))
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
fn parent_defaults_remain_available_after_failed_instance_search() {
    checked(
        &engine(),
        "class Base where\n  value : Nat := 17\nclass Child extends Base where\n  tag : Nat\ninstance fromDefault : Child := { tag := 19 }\ntheorem fallback : fromDefault.value = 17 := by rfl",
    );
}
