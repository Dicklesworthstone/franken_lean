//! Real parser, elaborator, kernel and independent-checker record construction.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, Outcome, SourceCheckLimits};

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn check(engine: &Engine, source: &str) -> fln::SourceFileCheck {
    let result = engine.check_source_files(
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
fn named_fields_are_reordered_to_the_constructor_telescope() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\n  y : Nat\ndef point : Point := { y := 9, x := 7 }\ntheorem x_ok : Point.x point = 7 := by rfl\ntheorem y_ok : Point.y point = 9 := by rfl",
    );
}
#[test]
fn dependent_fields_see_actual_earlier_values_even_when_written_last() {
    check(
        &engine(),
        "structure Package where\n  carrier : Type\n  value : carrier\ndef wrapped : Package := { value := 23, carrier := Nat }\ntheorem value_ok : Package.value wrapped = 23 := by rfl",
    );
}
#[test]
fn nested_literals_and_method_lambdas_receive_expected_types() {
    check(
        &engine(),
        "structure Box (A : Type) where\n  value : A\n  transform (x : A) : A\nstructure Outer where\n  inner : Box Nat\ndef wrapped : Outer := { inner := { transform := fun x => x + 1, value := 4 } }\ntheorem value_ok : Box.transform (Outer.inner wrapped) (Box.value (Outer.inner wrapped)) = 5 := by rfl",
    );
}
#[test]
fn literals_construct_registered_class_dictionaries() {
    check(
        &engine(),
        "class Choice (A : Type) where\n  value : A\ninstance selected : Choice Nat := { value := 17 }\ndef answer : Nat := Choice.value\ntheorem answer_ok : answer = 17 := by rfl",
    );
}
#[test]
fn recursive_dictionaries_can_be_written_with_named_fields() {
    check(
        &engine(),
        "class Choice (A : Type) where\n  value : A\ninstance selected : Choice Nat := { value := 11 }\ninstance functions {A : Type} [Choice A] : Choice (Nat -> A) := { value := fun x => Choice.value }\ndef answer : Nat -> Nat -> Nat := Choice.value\ntheorem answer_ok : answer 2 3 = 11 := by rfl",
    );
}
#[test]
fn field_puns_resolve_locals_without_promoting_field_names_to_scope() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\n  y : Nat\ndef point (x y : Nat) : Point := { y, x }\ntheorem point_ok : Point.x (point 4 5) = 4 := by rfl",
    );
}
#[test]
fn both_record_and_parenthesized_annotations_supply_the_expected_type() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\ndef one := { x := 3 : Point }\ndef two := ({ x := 4 } : Point)\ntheorem one_ok : Point.x one = 3 := by rfl\ntheorem two_ok : Point.x two = 4 := by rfl",
    );
}
#[test]
fn literal_types_can_be_definitionally_equal_aliases() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\ndef Alias := Point\ndef one : Alias := { x := 8 }\ntheorem one_ok : Point.x one = 8 := by rfl",
    );
}
#[test]
fn empty_and_trailing_comma_literals_have_exact_constructor_arity() {
    check(
        &engine(),
        "structure EmptyRecord\nstructure Point where\n  x : Nat\ndef empty : EmptyRecord := {}\ndef point : Point := { x := 8, }\ntheorem empty_ok : empty = EmptyRecord.mk := by rfl",
    );
}
#[test]
fn incomplete_unknown_duplicate_and_wrong_typed_fields_cannot_publish() {
    let base = check(&engine(), "structure Point where\n  x : Nat\n  y : Nat").engine;
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad : Point := { x := 1 }",
        "def bad : Point := { x := 1, y := 2, z := 3 }",
        "def bad : Point := { x := 1, y := 2, x := 3 }",
        "def bad : Point := { x := 1, y := Type }",
        "def bad := { x := 1, y := 2 }",
        "def bad : Point := { x := _, y := 2 }",
        "def bad : Point := { x := 1, y := x }",
        "def bad : Nat := { x := 1 }",
        "def bad : Point := { x := 1, y := 2 : Nat }",
    ] {
        assert!(
            !matches!(
                base.check_source_files(
                    &[source.as_bytes()],
                    &KVMap::new(),
                    SourceCheckLimits::new(limits())
                ),
                Ok(Outcome::Complete(_))
            ),
            "accepted {source}"
        );
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
    check(&base, "def recovered : Point := { x := 1, y := 2 }");
}
#[test]
fn dependent_wrong_type_is_vetoed_instead_of_retyping_the_field() {
    let base = check(
        &engine(),
        "structure Package where\n  carrier : Type\n  value : carrier",
    )
    .engine;
    let source = b"def bad : Package := { carrier := Nat, value := \"text\" }";
    assert!(!matches!(
        base.check_source_files(&[source], &KVMap::new(), SourceCheckLimits::new(limits())),
        Ok(Outcome::Complete(_))
    ));
}
#[test]
fn resource_nonanswers_are_preserved_for_literal_declarations() {
    let base = check(&engine(), "structure Point where\n  x : Nat").engine;
    let mut limited = limits();
    limited.kernel = limited.kernel.narrowed(0, limited.kernel.depth);
    let result =
        base.admit_source_declaration(b"def p : Point := { x := 1 }", &KVMap::new(), limited);
    assert!(matches!(result, Ok(Outcome::Inconclusive(_))), "{result:?}");
}

#[test]
fn proof_fields_use_the_ordinary_tactic_and_kernel_path() {
    check(
        &engine(),
        "structure Witness where\n  value : Nat\n  equal : value = 7\ndef witness : Witness := { equal := by rfl, value := 7 }\ntheorem value_ok : Witness.value witness = 7 := by rfl",
    );
}

#[test]
fn named_field_access_carries_receiver_and_dependent_field_types() {
    check(
        &engine(),
        "structure Package where\n  carrier : Type\n  value : carrier\ndef packed : Package := { carrier := Nat, value := 23 }\ndef read (p : Package) : p.carrier := p.value\ntheorem value_ok : packed.value = 23 := by rfl\ntheorem read_ok : read packed = 23 := by rfl",
    );
}
#[test]
fn postfix_field_access_handles_parenthesized_terms_and_nested_paths() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\nstructure Outer where\n  point : Point\ndef make (n : Nat) : Outer := { point := { x := n } }\ntheorem nested : (make 7).point.x = 7 := by rfl\ntheorem literal : ({ x := 8 } : Point).x = 8 := by rfl",
    );
}
#[test]
fn field_methods_stay_functions_and_preserve_application_precedence() {
    check(
        &engine(),
        "structure Box (A : Type) where\n  value : A\n  transform (x : A) : A\ndef box : Box Nat := { value := 4, transform := fun x => x + 1 }\ndef add (a b : Nat) : Nat := a + b\ntheorem method : box.transform box.value = 5 := by rfl\ntheorem precedence : add 2 (box).value = 6 := by rfl",
    );
}
#[test]
fn explicit_class_receiver_is_not_replaced_by_an_ambient_instance() {
    check(
        &engine(),
        "class Choice (A : Type) where\n  value : A\ninstance selected : Choice Nat := { value := 11 }\ndef different : Choice Nat := { value := 7 }\ntheorem receiver : different.value = 7 := by rfl\ntheorem parenthesized : (different).value = 7 := by rfl\ntheorem global : Choice.value = 11 := by rfl",
    );
}
#[test]
fn exact_qualified_names_and_escaped_components_keep_their_identity() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\ndef point : Point := { x := 4 }\ndef point.x : Nat := 99\ndef «point.x» : Nat := 77\ntheorem exact_global : point.x = 99 := by rfl\ntheorem explicit_projection : (point).x = 4 := by rfl\ntheorem escaped : «point.x» = 77 := by rfl\ndef local_name (point.x : Nat) : Nat := point.x\ntheorem exact_local : local_name 3 = 3 := by rfl",
    );
}
#[test]
fn unknown_fields_do_not_resolve_as_arbitrary_namespace_methods() {
    let e = check(&engine(), "structure Point where\n  x : Nat\ndef Point.notAField (p : Point) : Nat := 7\ndef point : Point := { x := 2 }").engine;
    let root = e.environment().logical_root(&KVMap::new());
    for text in [
        "def bad : Nat := point.missing",
        "def bad : Nat := point.notAField",
        "def bad : Nat := (1).x",
        "def bad : Nat := (point) .x",
        "def bad : Nat := (point). x",
    ] {
        assert!(
            e.check_source_files(
                &[text.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{text}"
        );
        assert_eq!(e.environment().logical_root(&KVMap::new()), root);
    }
}
