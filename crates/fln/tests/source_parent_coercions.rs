//! A structure value is not a value of its parent: the pinned Lean has no automatic parent
//! coercion, and refuses each such use at elaboration with "Type mismatch" (bead fln-azxg,
//! comment 3217, every verdict below taken from the pinned lean v4.32.0). The parent is
//! reached by its projection (`c.toBase`). A class's parents are a different mechanism: the
//! parent projection is an instance, which the pin does have.
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

/// Refused during elaboration with the pin's "Type mismatch", never only by the kernel: an
/// ill-typed body must not reach K1 as though elaboration had succeeded.
fn refused_at_elaboration(base: &Engine, text: &str) {
    let error = base
        .check_source_files(
            &[text.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err(text);
    assert_eq!(error.disposition().0, "elaboration", "{text}: {error}");
    assert!(
        error.to_string().contains("Type mismatch"),
        "{text}: {error}"
    );
}

const BASE_CHILD: &str = "structure Base where\n  value : Nat\nstructure Child extends Base where\n  tag : Nat\ndef c : Child := { value := 37, tag := 9 }\ndef getV (b : Base) : Nat := b.value\n";

#[test]
fn a_child_value_is_not_a_parent_value_without_its_projection() {
    // The pin: "Type mismatch c has type Child but is expected to have type Base", and
    // "Application type mismatch" for the argument.
    refused_at_elaboration(&engine(), &format!("{BASE_CHILD}def asParent : Base := c"));
    refused_at_elaboration(&engine(), &format!("{BASE_CHILD}def r : Nat := getV c"));
    // The pin accepts the projection.
    checked(
        &engine(),
        &format!(
            "{BASE_CHILD}def asParent : Base := c.toBase\ntheorem t : getV c.toBase = 37 := by rfl"
        ),
    );
}

#[test]
fn a_grandchild_value_reaches_its_ancestors_only_by_projection() {
    let family = "structure Base (A : Type) where\n  value : A\nstructure Middle (A : Type) extends Base A where\n  tag : Nat\nstructure Leaf (A : Type) extends Middle A where\n  last : Nat\ndef getV (b : Base Nat) : Nat := b.value\ndef c : Leaf Nat := { value := 19, tag := 23, last := 29 }\n";
    refused_at_elaboration(
        &engine(),
        &format!("{family}def toMiddle : Middle Nat := c"),
    );
    refused_at_elaboration(&engine(), &format!("{family}def r : Nat := getV c"));
    checked(
        &engine(),
        &format!(
            "{family}theorem t : getV c.toBase = 19 := by rfl\ndef toMiddle : Middle Nat := c.toMiddle\ntheorem m : toMiddle.tag = 23 := by rfl"
        ),
    );
}

#[test]
fn a_dependent_parent_is_reached_by_its_projection() {
    let both = "structure Carrier where\n  carrier : Type\nstructure Value (A : Type) where\n  value : A\nstructure Both extends Carrier, Value carrier where\n  tag : Nat\n";
    // The pin: "Type mismatch b has type Both … but is expected to have type Value b.carrier".
    refused_at_elaboration(
        &engine(),
        &format!("{both}def castV (b : Both) : Value b.carrier := b"),
    );
    let result = checked(
        &engine(),
        &format!(
            "{both}def castV (b : Both) : Value b.carrier := b.toValue\ntheorem t (b : Both) : (castV b).value = b.value := rfl"
        ),
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
    // The pin accepts the projection (and refuses `def valid : Base := c`).
    checked(
        &base,
        "def valid : Base := c.toBase\ntheorem recovery : valid.value = 5 := by rfl",
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
