//! Collection operations cross the real source elaborator and both admission seats.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
use fln_env::constants::{ConstantInfo, DefinitionSafety};

fn engine() -> (Engine, EngineAdmissionLimits) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .expect("source seed admission")
        .into_complete()
        .expect("source seed council");
    (engine, limits)
}
fn check(source: &str) {
    let (engine, limits) = engine();
    engine
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .expect("source collection check must complete");
}

#[test]
fn option_operations_compute_both_constructor_branches() {
    check(
        r#"
        theorem present : Option.getD (Option.some 7) 9 = 7 := by rfl
        theorem absent : Option.getD (Option.none : Option Nat) 9 = 9 := by rfl
        theorem map_some : Option.map Nat.succ (Option.some 7) = Option.some 8 := by rfl
        theorem map_none : Option.map Nat.succ (Option.none : Option Nat) = Option.none := by rfl
        theorem bind_some : Option.bind (Option.some 7) (fun n => Option.some (Nat.succ n)) = Option.some 8 := by rfl
        theorem bind_none : Option.bind (Option.none : Option Nat) (fun n => Option.some (Nat.succ n)) = Option.none := by rfl
        theorem bind_drop : Option.bind (Option.some 7) (fun n => (Option.none : Option Nat)) = Option.none := by rfl
        theorem some_yes : Option.isSome (Option.some 7) = true := by rfl
        theorem none_no : Option.isSome (Option.none : Option Nat) = false := by rfl
        theorem some_no : Option.isNone (Option.some 7) = false := by rfl
        theorem none_yes : Option.isNone (Option.none : Option Nat) = true := by rfl
        "#,
    );
}

#[test]
fn option_maps_across_universes_and_nested_payloads() {
    check(
        r#"
        theorem polymorphic.{u,v} {A : Type u} {B : Type v} (f : A -> B) (a : A) :
            Option.map f (Option.some a) = Option.some (f a) := by rfl
        theorem fallback.{u} {A : Type u} (a : A) :
            Option.getD (Option.none : Option A) a = a := by rfl
        theorem universe_change : Option.map (fun n => Nat) (Option.some 3) = Option.some Nat := by rfl
        theorem payload : Option.getD (Option.some (Option.some 11)) Option.none = Option.some 11 := by rfl
        theorem boolean_payload : Option.map (fun n => true) (Option.some 4) = Option.some true := by rfl
        "#,
    );
}

#[test]
fn option_false_proofs_and_wrong_payloads_preserve_the_input_environment() {
    let (engine, limits) = engine();
    let before = engine.logical_root(&KVMap::new());
    for source in [
        "theorem invalid : Option.getD (Option.some 7) 9 = 9 := by rfl",
        "theorem invalid : Option.isSome (Option.none : Option Nat) = true := by rfl",
        "def invalid : Option Nat := Option.some true",
        "def invalid : Nat := Option.getD (Option.some true) 0",
        "theorem invalid : Option.map Nat.succ (Option.some 7) = Option.some 7 := by rfl",
    ] {
        let result = engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        );
        assert!(
            result.is_err(),
            "accepted invalid collection source: {source}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), before, "{source}");
    }
    // Failed calls must not poison the reusable seed engine.
    engine
        .check_source_files(
            &[b"theorem recovered : Option.getD (Option.some 7) 9 = 7 := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect("recovery after collection refusal")
        .into_complete()
        .expect("recovered council");
}

#[test]
fn option_seed_contains_real_inductive_data_and_safe_definitions() {
    let (engine, _) = engine();
    assert!(matches!(
        engine
            .environment()
            .find(&Name::from_components(["Option"])),
        Some(ConstantInfo::Induct(_))
    ));
    for label in [
        "Option.getD",
        "Option.map",
        "Option.bind",
        "Option.isSome",
        "Option.isNone",
    ] {
        let Some(ConstantInfo::Defn(definition)) = engine
            .environment()
            .find(&Name::from_components(label.split('.')))
        else {
            panic!("{label} must have an admitted definition, not an axiom");
        };
        assert_eq!(definition.safety, DefinitionSafety::Safe);
        assert!(!definition.value.has_expr_mvar(), "{label}");
        assert!(!definition.value.has_level_mvar(), "{label}");
        assert!(!definition.value.has_loose_bvars(), "{label}");
    }
}

#[test]
fn list_empty_singleton_and_recursive_branches_compute() {
    check(
        r#"
        def xs : List Nat := List.cons 1 (List.cons 2 (List.cons 3 List.nil))
        theorem empty_length : List.length (List.nil : List Nat) = 0 := by rfl
        theorem singleton_length : List.length (List.cons 9 List.nil) = 1 := by rfl
        theorem length_three : List.length xs = 3 := by rfl
        theorem left_empty : List.append List.nil xs = xs := by rfl
        theorem right_empty : List.append xs List.nil = xs := by rfl
        theorem appended : List.append (List.cons 0 List.nil) xs = List.cons 0 xs := by rfl
        theorem mapped_empty : List.map Nat.succ (List.nil : List Nat) = List.nil := by rfl
        theorem mapped : List.map Nat.succ xs = List.cons 2 (List.cons 3 (List.cons 4 List.nil)) := by rfl
        theorem empty_head : List.head? (List.nil : List Nat) = Option.none := by rfl
        theorem head : List.head? xs = Option.some 1 := by rfl
        theorem empty_tail : List.tail (List.nil : List Nat) = List.nil := by rfl
        theorem tail : List.tail xs = List.cons 2 (List.cons 3 List.nil) := by rfl
        theorem reverse_empty : List.reverse (List.nil : List Nat) = List.nil := by rfl
        theorem reverse_singleton : List.reverse (List.cons 9 List.nil) = List.cons 9 List.nil := by rfl
        theorem reverse_three : List.reverse xs = List.cons 3 (List.cons 2 (List.cons 1 List.nil)) := by rfl
        theorem round_trip : List.reverse (List.reverse xs) = xs := by rfl
        theorem composition : Option.getD (List.head? (List.reverse xs)) 0 = 3 := by rfl
        "#,
    );
}

#[test]
fn list_folds_keep_argument_order_and_distinct_accumulator_types() {
    check(
        r#"
        def xs : List Nat := List.cons 5 (List.cons 2 List.nil)
        theorem empty_left : List.foldl Nat.sub 10 (List.nil : List Nat) = 10 := by rfl
        theorem empty_right : List.foldr Nat.sub 10 (List.nil : List Nat) = 10 := by rfl
        theorem left_order : List.foldl Nat.sub 10 xs = 3 := by rfl
        theorem right_order : List.foldr Nat.sub 10 xs = 5 := by rfl
        theorem rebuild : List.foldr (fun n tail => List.cons n tail) List.nil xs = xs := by rfl
        theorem left_boolean : List.foldl (fun acc n => true) false xs = true := by rfl
        theorem right_boolean : List.foldr (fun n acc => true) false xs = true := by rfl
        theorem left_type : List.foldl (fun acc n => Nat) Bool xs = Nat := by rfl
        theorem right_type : List.foldr (fun n acc => Nat) Bool xs = Nat := by rfl
        "#,
    );
}

#[test]
fn list_polymorphism_is_not_specialized_to_nat_or_one_universe() {
    check(
        r#"
        theorem map_cons.{u,v} {A : Type u} {B : Type v} (f : A -> B) (a : A) (tail : List A) :
            List.map f (List.cons a tail) = List.cons (f a) (List.map f tail) := by rfl
        theorem append_cons.{u} {A : Type u} (a : A) (as bs : List A) :
            List.append (List.cons a as) bs = List.cons a (List.append as bs) := by rfl
        theorem length_cons.{u} {A : Type u} (a : A) (tail : List A) :
            List.length (List.cons a tail) = Nat.succ (List.length tail) := by rfl
        theorem tail_cons.{u} {A : Type u} (a : A) (tail : List A) :
            List.tail (List.cons a tail) = tail := by rfl
        theorem head_cons.{u} {A : Type u} (a : A) (tail : List A) :
            List.head? (List.cons a tail) = Option.some a := by rfl
        theorem change_universe : List.map (fun n => Nat) (List.cons 1 List.nil) = List.cons Nat List.nil := by rfl
        theorem nested : List.head? (List.cons (Option.some true) List.nil) = Option.some (Option.some true) := by rfl
        theorem boolean_length : List.length (List.cons true (List.cons false List.nil)) = 2 := by rfl
        "#,
    );
}

#[test]
fn list_generated_recursor_is_usable_by_source_code() {
    check(
        r#"
        def count.{u} {A : Type u} (xs : List A) : Nat :=
            List.rec 0 (fun head tail ih => Nat.succ ih) xs
        theorem count_two : count (List.cons true (List.cons false List.nil)) = 2 := by rfl
        def fallback (x : Option Nat) : Nat := Option.rec 11 (fun n => n) x
        theorem fallback_none : fallback Option.none = 11 := by rfl
        theorem fallback_some : fallback (Option.some 5) = 5 := by rfl
        "#,
    );
}

#[test]
fn list_false_results_wrong_payloads_and_poisoned_tails_are_refused() {
    let (engine, limits) = engine();
    let before = engine.logical_root(&KVMap::new());
    for source in [
        "theorem invalid : List.length (List.cons 1 List.nil) = 0 := by rfl",
        "theorem invalid : List.head? (List.nil : List Nat) = Option.some 0 := by rfl",
        "theorem invalid : List.reverse (List.cons 1 (List.cons 2 List.nil)) = List.cons 1 (List.cons 2 List.nil) := by rfl",
        "theorem invalid : List.foldl Nat.sub 10 (List.cons 5 (List.cons 2 List.nil)) = 5 := by rfl",
        "theorem invalid : List.foldr Nat.sub 10 (List.cons 5 (List.cons 2 List.nil)) = 3 := by rfl",
        "def invalid : List Nat := List.cons true List.nil",
        "def invalid : List Nat := List.cons 1 (Option.some 2)",
        "def invalid : Nat := List.foldl (fun acc n => true) 0 (List.cons 1 List.nil)",
    ] {
        let result = engine.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        );
        assert!(
            result.is_err(),
            "accepted invalid collection source: {source}"
        );
        assert_eq!(engine.logical_root(&KVMap::new()), before, "{source}");
    }
    engine
        .check_source_files(
            &[b"theorem recovered : List.length (List.cons 1 List.nil) = 1 := by rfl"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .expect("recovery after list refusal")
        .into_complete()
        .expect("recovered list council");
}

#[test]
fn list_seed_preserves_positive_recursion_and_checked_bodies() {
    let (engine, _) = engine();
    let Some(ConstantInfo::Induct(family)) =
        engine.environment().find(&Name::from_components(["List"]))
    else {
        panic!("List must be an admitted family");
    };
    assert!(family.is_rec);
    assert!(!family.is_unsafe);
    assert_eq!(family.num_params, 1);
    assert_eq!(family.num_indices, 0);
    for label in [
        "List.length",
        "List.append",
        "List.map",
        "List.foldr",
        "List.foldl",
        "List.reverse",
        "List.head?",
        "List.tail",
    ] {
        let Some(ConstantInfo::Defn(definition)) = engine
            .environment()
            .find(&Name::from_components(label.split('.')))
        else {
            panic!("{label} must have an admitted body");
        };
        assert_eq!(definition.safety, DefinitionSafety::Safe);
        assert!(!definition.value.has_expr_mvar(), "{label}");
        assert!(!definition.value.has_level_mvar(), "{label}");
        assert!(!definition.value.has_loose_bvars(), "{label}");
    }
}

#[test]
fn generic_collection_laws_use_native_induction_and_checked_rewriting() {
    check(
        r#"
        theorem append_nil.{u} {A : Type u} (xs : List A) : List.append xs List.nil = xs := by
          induction xs with
          | nil => rfl
          | cons x tail ih => simp only [List.append]; rw [ih]
        theorem map_identity.{u} {A : Type u} (xs : List A) : List.map (fun x => x) xs = xs := by
          induction xs with
          | nil => rfl
          | cons x tail ih => simp only [List.map]; rw [ih]
        "#,
    );
}
