//! Updates are ordinary constructor terms checked by both production checkers.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(e: &Engine, source: &str) -> fln::SourceFileCheck {
    let result = e.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    );
    assert!(
        matches!(result, Ok(Outcome::Complete(_))),
        "{source}\n{result:?}"
    );
    result.unwrap().into_complete().unwrap()
}
#[test]
fn updates_copy_unspecified_fields_without_mutating_the_source() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\n  y : Nat\ndef p : Point := { x := 3, y := 5 }\ndef q := { p with x := p.x + 1 }\ntheorem q_x : q.x = 4 := by rfl\ntheorem q_y : q.y = 5 := by rfl\ntheorem unchanged : p.x = 3 := by rfl",
    );
}
#[test]
fn dependent_updates_substitute_all_replaced_fields_in_telescope_order() {
    check(
        &engine(),
        "structure Package where\n  carrier : Type\n  value : carrier\ndef p : Package := { carrier := Nat, value := 5 }\ndef q := { p with value := \"new\", carrier := String }\ntheorem value_ok : q.value = \"new\" := by rfl",
    );
}
#[test]
fn invalid_dependent_carryover_is_a_kernel_rejection_and_is_atomic() {
    let base = check(&engine(), "structure Package where\n  carrier : Type\n  value : carrier\ndef p : Package := { carrier := Nat, value := 5 }").engine;
    let root = base.logical_root(&KVMap::new());
    let refusal = base
        .check_source_files(
            &[b"def bad := { p with carrier := String }"],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .expect_err("stale dependent field must reject");
    assert_eq!(
        refusal.disposition(),
        ("kernel-rejection", true, 1),
        "{refusal:?}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    check(
        &base,
        "def recovered := { p with value := 9 }\ntheorem ok : recovered.value = 9 := by rfl",
    );
}
#[test]
fn multiple_sources_are_considered_in_written_order() {
    check(
        &engine(),
        "structure XY where\n  x : Nat\n  y : Nat\nstructure XYZ where\n  x : Nat\n  y : Nat\n  z : Nat\ndef p : XY := { x := 1, y := 2 }\ndef q : XYZ := { x := 3, y := 4, z := 5 }\ndef r : XYZ := { p, q with x := 7 }\ntheorem x_ok : r.x = 7 := by rfl\ntheorem y_ok : r.y = 2 := by rfl\ntheorem z_ok : r.z = 5 := by rfl",
    );
}
#[test]
fn nested_update_sources_and_literals_restore_lexical_scopes() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\n  y : Nat\nstructure Outer where\n  inner : Point\ndef revise (p : Outer) : Outer := { p with inner := { p.inner with x := 9 } }\ndef r : Outer := revise { inner := { x := 1, y := 2 } }\ntheorem x_ok : r.inner.x = 9 := by rfl\ntheorem y_ok : r.inner.y = 2 := by rfl\ndef other (x : Nat) : Point := { { x := x, y := 2 : Point } with y := x }",
    );
}
#[test]
fn updated_class_receivers_do_not_use_an_ambient_dictionary() {
    check(
        &engine(),
        "class Choice where\n  value : Nat\ninstance ambient : Choice := { value := 11 }\ndef explicit : Choice := { value := 7 }\ndef copy := { explicit with }\ntheorem ok : copy.value = 7 := by rfl",
    );
}
#[test]
fn malformed_or_unused_ill_typed_sources_never_disappear() {
    let base = check(
        &engine(),
        "structure Point where\n  x : Nat\ndef p : Point := { x := 1 }",
    )
    .engine;
    for source in [
        "def bad : Point := { 1 with x := 2 }",
        "def bad : Point := { (p : String) with x := 2 }",
        "def bad : Point := { (1 : String) with x := 2 }",
        "def bad := { p with x := 2, x := 3 }",
        "def bad := { p with missing := 0 }",
        "def bad := { p with x := \"no\" }",
    ] {
        let root = base.logical_root(&KVMap::new());
        assert!(
            !matches!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "{source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
    }
}
#[test]
fn unchanged_empty_records_and_explicit_result_annotations_work() {
    check(
        &engine(),
        "structure EmptyRecord\ndef p : EmptyRecord := {}\ndef q := { p with }\ntheorem same : q = p := by rfl\nstructure Point where\n  x : Nat\ndef r := { { x := 2 : Point } with : Point }\ntheorem x_ok : r.x = 2 := by rfl",
    );
}
