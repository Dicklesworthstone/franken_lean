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
        theorem map_none : Option.map Nat.succ (Option.none : Option Nat) = (Option.none : Option Nat) := by rfl
        theorem bind_some : Option.bind (Option.some 7) (fun n => Option.some (Nat.succ n)) = Option.some 8 := by rfl
        theorem bind_none : Option.bind (Option.none : Option Nat) (fun n => Option.some (Nat.succ n)) = (Option.none : Option Nat) := by rfl
        theorem bind_drop : Option.bind (Option.some 7) (fun n => (Option.none : Option Nat)) = (Option.none : Option Nat) := by rfl
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
