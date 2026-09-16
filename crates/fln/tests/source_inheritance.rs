//! Real source inheritance: parsing, native elaboration, both checking engines,
//! transactional metadata publication, instance synthesis and proof reduction.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::name::Name;
use fln_elab::instances::InstanceRegistry;

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
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
fn checked(base: &Engine, text: &str) -> Engine {
    base.check_source_files(
        &[text.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|e| panic!("{text}: {e:?}"))
    .into_complete()
    .expect("checking must complete")
    .engine
}
#[test]
fn embedded_parent_projection_and_inherited_dot_access_compute() {
    let result = checked(
        &engine(),
        "structure Base where\n  x : Nat\nstructure Child extends Base where\n  y : Nat\ndef c : Child := Child.mk (Base.mk 7) 9\ntheorem parent : Base.x (Child.toBase c) = 7 := by rfl\ntheorem inherited : c.x = 7 := by rfl\ntheorem own : c.y = 9 := by rfl",
    );
    assert!(result.environment().contains(&n("Child.toBase")));
}
#[test]
fn class_parents_are_real_instances_and_preserve_the_child_dictionary() {
    let result = checked(
        &engine(),
        "class Base (A : Type) where\n  value : A\nclass Child (A : Type) extends Base A where\n  tag : Nat\ninstance child : Child Nat := { toBase := Base.mk 17, tag := 9 }\ndef inherited : Nat := Base.value\ntheorem inherited_ok : inherited = 17 := by rfl",
    );
    let registry = InstanceRegistry::read(result.environment()).unwrap();
    assert!(
        registry
            .candidates(&n("Base"))
            .iter()
            .any(|r| r.declaration == n("Child.toBase"))
    );
}
#[test]
fn inherited_fields_can_type_new_fields_and_defaults() {
    checked(
        &engine(),
        "structure Package where\n  carrier : Type\n  value : carrier\nstructure Extended extends Package where\n  extra : carrier\n  again : carrier := value\ndef p : Package := Package.mk Nat 23\ndef e : Extended := { toPackage := p, extra := 41 }\ntheorem original : e.value = 23 := by rfl\ntheorem default_ok : e.again = 23 := by rfl\ntheorem extra_ok : e.extra = 41 := by rfl",
    );
}
#[test]
fn named_and_disjoint_multiple_parents_preserve_field_paths() {
    checked(
        &engine(),
        "structure First where\n  x : Nat\nstructure Second where\n  y : Bool\nstructure Combined extends first : First, Second where\n  z : Nat\ndef c : Combined := Combined.mk (First.mk 8) (Second.mk true) 9\ntheorem first_ok : c.x = 8 := by rfl\ntheorem second_ok : c.y = true := by rfl\ntheorem named_ok : First.x (Combined.first c) = 8 := by rfl",
    );
}

#[test]
fn flat_inherited_literals_build_parent_subobjects_and_use_inherited_defaults() {
    checked(
        &engine(),
        "structure Base where\n  x : Nat := 11\n  y : Nat := x + 1\nstructure Child extends Base where\n  z : Nat := x + y\ndef c : Child := { x := 20 }\ntheorem inherited : c.y = 21 := by rfl\ntheorem own : c.z = 41 := by rfl\ndef defaults : Child := {}\ntheorem default_ok : defaults.z = 23 := by rfl",
    );
}

#[test]
fn inherited_updates_rebuild_only_the_modified_parent_and_preserve_other_fields() {
    checked(
        &engine(),
        "structure Base where\n  x : Nat\n  y : Nat\nstructure Child extends Base where\n  z : Nat\ndef before : Child := { x := 7, y := 9, z := 11 }\ndef after : Child := { before with x := 23 }\ntheorem replaced : after.x = 23 := by rfl\ntheorem copied_parent : after.y = 9 := by rfl\ntheorem copied_own : after.z = 11 := by rfl\ntheorem unchanged : before.x = 7 := by rfl",
    );
}

#[test]
fn multilevel_parent_literals_updates_and_instance_search_compose() {
    checked(
        &engine(),
        "class Base (A : Type) where\n  value : A\nclass Middle (A : Type) extends Base A where\n  middle : Nat\nclass Leaf (A : Type) extends Middle A where\n  leaf : Nat\ninstance chosen : Leaf Nat := { value := 13, middle := 17, leaf := 19 }\ndef inherited : Nat := Base.value\ntheorem instance_ok : inherited = 13 := by rfl\ndef modified : Leaf Nat := { chosen with value := 29 }\ntheorem update_ok : modified.value = 29 := by rfl\ntheorem middle_ok : modified.middle = 17 := by rfl\ntheorem leaf_ok : modified.leaf = 19 := by rfl",
    );
}

#[test]
fn dependent_parent_values_remain_tied_to_their_actual_carrier() {
    let base = checked(
        &engine(),
        "structure Package where\n  carrier : Type\n  value : carrier\nstructure Extended extends Package where\n  extra : carrier\ndef good : Extended := { carrier := Nat, value := 23, extra := 41 }",
    );
    checked(
        &base,
        "theorem flat_ok : good.value = 23 := by rfl\ndef updated : Extended := { good with value := 7 }\ntheorem updated_ok : updated.value = 7 := by rfl",
    );
    let before = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Extended := { good with carrier := Bool }",
        "def bad : Extended := { carrier := Bool, value := 23, extra := true }",
        "def bad : Extended := { toPackage := Package.mk Nat 7, value := 9, extra := 3 }",
        "def bad : Extended := { value := 23, extra := 1 }",
        "def bad : Extended := { carrier := Nat, value := 23, extra := 1, absent := 7 }",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), before);
        assert!(
            base.environment()
                .find(&Name::from_components(["bad"]))
                .is_none()
        );
    }
}

#[test]
fn overlapping_or_invalid_parent_declarations_do_not_publish_any_successor() {
    let base = checked(
        &engine(),
        "structure Base where\n  x : Nat\nstructure Other where\n  x : Nat\nstructure Left extends Base\nstructure Right extends Base",
    );
    let before = base.logical_root(&KVMap::new());
    for text in [
        "structure Bad extends Base, Other",
        "structure Bad extends Left, Right",
        "structure Bad extends Base, Base",
        "structure Bad extends Base where\n  x : Nat",
        "structure Bad extends Base where\n  toBase : Nat",
        "structure Bad extends Nat",
        "structure Bad extends Bool",
        "structure Bad extends absent",
        "structure Bad extends Base where\n  invalid : UnknownType",
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
        for n in ["Bad", "Bad.mk", "Bad.toBase"] {
            assert!(
                base.environment()
                    .find(&Name::from_components(n.split('.')))
                    .is_none()
            );
        }
    }
    checked(
        &base,
        "structure Good extends Base where\n  y : Nat\ndef recovered : Good := { x := 7, y := 9 }",
    );
}
