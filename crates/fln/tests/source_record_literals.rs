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

#[test]
fn expression_ascriptions_cannot_disappear_before_kernel_checking() {
    let e = engine();
    for text in [
        "def bad : Nat := (1 : String)",
        "def bad : Nat := let x := (1 : String); 0",
        "def ignored (x : String) : Nat := 0\ndef bad : Nat := ignored (1 : String)",
        "def bad : Nat := ((fun x => x) : String -> String) 1",
    ] {
        let result = e.check_source_files(
            &[text.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        );
        let refusal = result.expect_err("a false source ascription must reach rejection");
        assert_eq!(
            refusal.disposition(),
            ("kernel-rejection", true, 1),
            "{text}: {refusal:?}"
        );
    }
}

#[test]
fn field_receiver_explicit_projection_is_a_working_control() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\n\
         def point [Inhabited Nat] : Point := { x := default }\n\
         theorem read : Point.x point = 0 := by rfl",
    );
}

#[test]
fn field_receivers_insert_instances_and_preserve_ambient_selection() {
    let base = check(
        &engine(),
        "structure Point where\n  x : Nat\n\
         def point [Inhabited Nat] : Point := { x := default }",
    )
    .engine;
    for receiver in ["point.x", "(point).x"] {
        check(
            &base,
            &format!(
                "theorem global : {receiver} = 0 := by rfl\n\
                 theorem local (i : Inhabited Nat) : {receiver} = default := by rfl"
            ),
        );
    }
}

#[test]
fn field_receiver_implicit_parameters_follow_the_expected_field_type() {
    let base = check(
        &engine(),
        "structure Box (A : Type) where\n  value : A\n\
         def box {A : Type} [Inhabited A] : Box A := { value := default }",
    )
    .engine;
    for receiver in ["box.value", "(box).value"] {
        check(
            &base,
            &format!("def chosen : Nat := {receiver}\ntheorem result : chosen = 0 := by rfl"),
        );
    }
}

#[test]
fn field_receiver_dictionaries_can_determine_the_record_type() {
    let base = check(
        &engine(),
        "structure Point where\n  x : Nat\n\
         class Factory where\n  carrier : Type\n  produce : carrier\n\
         instance pointFactory : Factory := { carrier := Point, produce := { x := 7 } }\n\
         def make [f : Factory] : f.carrier := f.produce",
    )
    .engine;
    for receiver in ["make.x", "(make).x", "Point.x make"] {
        check(&base, &format!("theorem result : {receiver} = 7 := by rfl"));
    }
}

#[test]
fn field_receiver_insertion_preserves_the_explicit_class_value() {
    check(
        &engine(),
        "class Choice (A : Type) where\n  value : A\n\
         instance selected : Choice Nat := { value := 11 }\n\
         def factory [Inhabited Nat] : Choice Nat := { value := default }\n\
         theorem dotted : factory.value = 0 := by rfl\n\
         theorem postfix : (factory).value = 0 := by rfl\n\
         theorem global : Choice.value = 11 := by rfl",
    );
}

#[test]
fn field_receivers_refuse_missing_instances_and_unapplied_parameters_atomically() {
    let base = check(
        &engine(),
        "structure Point where\n  x : Nat\n\
         def point [Inhabited Nat] : Point := { x := default }\n\
         structure Box (A : Type) where\n  value : A\n\
         def box {A : Type} [Inhabited A] : Box A := { value := default }\n\
         def strict ⦃A : Type⦄ [Inhabited A] : Box A := { value := default }\n\
         def takes (x : Nat) : Point := { x }",
    )
    .engine;
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad (A : Type) : A := box.value",
        "def bad : Nat := strict.value",
        "def bad : Nat := (strict).value",
        "def bad : Nat := takes.x",
        "def bad : Nat := point.missing",
        "theorem bad (i : Inhabited Nat) : point.x = 0 := by rfl",
    ] {
        let error = base
            .check_source_files(
                &[source.as_bytes()],
                &KVMap::new(),
                SourceCheckLimits::new(limits()),
            )
            .unwrap_err();
        assert_eq!(error.disposition().2, 1, "{source}: {error:?}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
    check(&base, "theorem recovery : point.x = 0 := by rfl");
}

fn type_factory() -> Engine {
    check(
        &engine(),
        "class Factory where\n  carrier : Type\n  produce : carrier\n\
         instance natFactory : Factory := { carrier := Nat, produce := 7 }",
    )
    .engine
}

#[test]
fn type_positions_insert_class_receivers_in_result_arrow_let_and_ascription() {
    let base = type_factory();
    for (declaration, result) in [
        ("def answer : Factory.carrier := Factory.produce", "answer = 7"),
        ("def answer : Factory.carrier -> Nat := fun x => x", "answer 7 = 7"),
        ("def answer : Nat -> Factory.carrier := fun x => x", "answer 7 = 7"),
        ("def answer : Nat := let x : Factory.carrier := Factory.produce; x", "answer = 7"),
        ("def answer : Nat := (Factory.produce : Factory.carrier)", "answer = 7"),
        ("structure Wrapped where\n  value : Factory.carrier\ndef answer : Wrapped := { value := 7 }", "answer.value = 7"),
    ] {
        check(&base, &format!("{declaration}\ntheorem result : {result} := by rfl"));
    }
}

#[test]
fn type_positions_keep_anonymous_named_and_ordinary_local_dictionaries() {
    check(
        &type_factory(),
        "def make [Factory] : Factory.carrier := Factory.produce\n\
         def keep [Factory] (x : Factory.carrier) : Factory.carrier := x\n\
         def local (f : Factory) : f.carrier := (Factory.produce : Factory.carrier)\n\
         theorem global : make = 7 := by rfl\n\
         theorem kept : keep 9 = 9 := by rfl\n\
         theorem selected : local { carrier := Nat, produce := 9 } = 9 := by rfl",
    );
}

#[test]
fn type_positions_resolve_explicit_record_annotations_before_field_elaboration() {
    check(
        &engine(),
        "structure Point where\n  x : Nat\n\
         class Factory where\n  carrier : Type\n  produce : carrier\n\
         instance pointFactory : Factory := { carrier := Point, produce := { x := 7 } }\n\
         def one := { x := 3 : Factory.carrier }\n\
         def two := ({ x := 4 } : Factory.carrier)\n\
         def make [Factory] : Factory.carrier := Factory.produce\n\
         theorem one_ok : one.x = 3 := by rfl\n\
         theorem two_ok : two.x = 4 := by rfl\n\
         theorem made : make.x = 7 := by rfl",
    );
}

#[test]
fn type_positions_allow_later_header_constraints_before_resolving_instances() {
    check(
        &engine(),
        "def inferred {A : Type} [Inhabited A] : Type := A\n\
         def keep (x : inferred) (h : x = (0 : Nat)) : Nat := x\n\
         theorem result : keep 0 (by rfl) = 0 := by rfl",
    );
}

#[test]
fn type_positions_preserve_pending_outer_and_nested_annotation_inference() {
    check(
        &engine(),
        "def choose {A : Type} [Inhabited A] (x : A) : A := default\n\
         def inferred {A : Type} [Inhabited A] : Type := A\n\
         def family {A : Type} : Type := A\n\
         def ascribed : Nat := choose (0 : Nat)\n\
         def nested : Nat := ((0 : Nat) : inferred)\n\
         def local (n : Nat) : Nat := let x : inferred := n; x\n\
         def ordinary (x : family) := (x : Nat)\n\
         theorem ascribed_ok : ascribed = 0 := by rfl\n\
         theorem nested_ok : nested = 0 := by rfl\n\
         theorem local_ok : local 9 = 9 := by rfl\n\
         theorem ordinary_ok : ordinary 8 = 8 := by rfl",
    );
}

#[test]
fn type_positions_refuse_unresolved_headers_and_unapplied_types_atomically() {
    let base = check(
        &engine(),
        "class Missing where\n  carrier : Type\n\
         class Witness (A : Type) where\n  value : A\n\
         def carrier {A : Type} [Witness A] : Type := A\n\
         def inferred {A : Type} [Inhabited A] : Type := A\n\
         def family {A : Type} : Type := A\n\
         def strict ⦃A : Type⦄ : Type := A\n\
         def explicit (A : Type) : Type := A",
    )
    .engine;
    let root = base.logical_root(&KVMap::new());
    for source in [
        "def bad (n : Nat) : inferred := n",
        "def bad (n : Nat) : family := n",
        "def bad (x : inferred) := (x : Nat)",
        "def bad (x : carrier) [Witness Nat] (h : x = (0 : Nat)) : Nat := x",
        "def bad : Missing.carrier := 0",
        "def bad : strict := 0",
        "def bad : explicit := 0",
        "def bad : 7 := 0",
        "def bad : Nat := (7 : Missing)",
    ] {
        let error = base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        ).unwrap_err();
        assert_eq!(error.disposition().2, 1, "{source}: {error:?}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
    check(&base, "theorem recovered : 0 = 0 := by rfl");
}
