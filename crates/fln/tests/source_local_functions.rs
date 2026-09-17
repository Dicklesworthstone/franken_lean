//! Local helper declarations reach the production dual checker and native VM.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, Name, SourceCheckLimits};
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
    .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
    .into_complete()
    .unwrap()
    .engine
}
#[test]
fn local_helpers_capture_outer_arguments_and_infer_return_types() {
    checked(
        &engine(),
        "def outer (n : Nat) : Nat := let add (x y : Nat) := n + x + y; add 2 3\ntheorem result : outer 37 = 42 := by rfl",
    );
}
#[test]
fn dependent_local_signatures_and_implicit_arguments_remain_scoped() {
    checked(
        &engine(),
        "def outer (A : Type) (x : A) : A := let id {B : Type} (y : B) : B := y; id x\ndef high : Type := let id (A : Type 1) (x : A) : A := x; id (Type) Nat",
    );
}
#[test]
fn later_local_functions_can_call_earlier_helpers_without_global_declarations() {
    let e = checked(
        &engine(),
        "def outer : Nat := let add (x : Nat) := x + 1; let twice (x : Nat) : Nat := add (add x); twice 40\ntheorem result : outer = 42 := by rfl",
    );
    for name in ["add", "twice"] {
        assert!(!e.environment().contains(&Name::from_components([name])));
    }
}
#[test]
fn local_function_names_do_not_become_recursive_by_accident() {
    checked(
        &engine(),
        "def f (x : Nat) : Nat := x + 1\ndef outer : Nat := let f (x : Nat) : Nat := f x + 1; f 40\ntheorem result : outer = 42 := by rfl",
    );
    assert!(
        engine()
            .check_source_files(
                &[b"def outer : Nat := let absent (x : Nat) : Nat := absent x; absent 0"],
                &KVMap::new(),
                SourceCheckLimits::new(limits())
            )
            .is_err()
    );
}
#[test]
fn branch_helpers_and_match_bearing_parameter_types_preserve_scope() {
    checked(
        &engine(),
        "def outer (b : Bool) : Nat := match b with | true => let f (x : Nat) := x + 1; f 41 | false => let f (x : Nat) := x * 2; f 21\ntheorem yes : outer true = 42 := by rfl\ntheorem no : outer false = 42 := by rfl",
    );
    checked(
        &engine(),
        "def outer (b : Bool) : Nat := if b then let f (x : if true then Nat else Nat) := x; f 42 else 0\ntheorem result : outer true = 42 := by rfl",
    );
}
#[test]
fn instance_parameters_are_available_only_in_the_local_helper_body() {
    checked(
        &engine(),
        "class Item (A : Type) where\n  value : A\ninstance natural : Item Nat := { value := 42 }\ndef outer : Nat := let get {A : Type} [d : Item A] (x : A) : A := Item.value; get 0\ntheorem result : outer = 42 := by rfl",
    );
}
#[test]
fn unused_helpers_keep_invalid_domains_and_result_annotations_as_obligations() {
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "def bad : Nat := let f (x : Nat) : Bool := x; 42",
        "def bad : Nat := let f (x : 7) : Nat := 0; 42",
        "def bad : Nat := let f (x : Nat) : Nat := _; 42",
        "def bad : Nat := let f (x : Nat) : Nat := x; x",
        "def bad : Nat := let f (x : Nat) : Nat := x; f true",
    ] {
        let text = format!("def prefix := 7\n{source}");
        let result = base.check_source_files(
            &[text.as_bytes()],
            &options,
            SourceCheckLimits::new(limits()),
        );
        assert!(
            result.is_err() || result.unwrap().into_complete().is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
        assert!(
            !base
                .environment()
                .contains(&Name::from_components(["prefix"]))
        );
    }
    checked(&base, "def recovered := let f (x : Nat) : Nat := x; f 42");
}

#[test]
fn local_helpers_can_contain_nested_helpers_and_proof_bodies() {
    checked(
        &engine(),
        "def outer (n : Nat) : Nat := let f (x : Nat) : Nat := let g (y : Nat) : Nat := n + x + y; g 2; f 3\ntheorem result : outer 37 = 42 := by rfl\ntheorem proof (n : Nat) : n = n := let reflexive (x : Nat) : x = x := by rfl; reflexive n",
    );
}

#[test]
fn local_helpers_work_inside_structure_field_defaults() {
    checked(
        &engine(),
        "structure Item where\n  value : Nat := let f (x : Nat) : Nat := x + 2; f 40\ndef item : Item := {}\ntheorem result : item.value = 42 := by rfl",
    );
}
