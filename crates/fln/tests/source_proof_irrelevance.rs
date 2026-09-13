//! Typed proof irrelevance must operate under binders without equating data.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn check(source: &str, valid: bool) {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let before = engine.logical_root(&KVMap::new());
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    );
    if valid {
        result
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
            .into_complete()
            .unwrap();
    } else {
        assert!(result.is_err(), "{source}");
    }
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
#[test]
fn generic_proofs_under_function_binders_use_checker_owned_typing() {
    check(
        "theorem same (A : Type) (P : A -> Prop) (f : forall x : A, P x -> Nat) (p q : forall x : A, P x) : (fun x => f x (p x)) = (fun x => f x (q x)) := by rfl",
        true,
    );
}
#[test]
fn dependent_proof_families_remain_convertible_under_nested_binders() {
    check(
        "theorem same (A : Type) (P : A -> Prop) (f : forall x : A, P x -> Nat) (p q : forall x : A, P x) : (fun x y => f x (p x) + f y (p y)) = (fun x y => f x (q x) + f y (q y)) := by rfl",
        true,
    );
}
#[test]
fn proof_dependent_local_lets_retain_their_checked_values() {
    check(
        "def localProof (P : Prop) (p : P) (f : P -> Nat) (n : Nat) : Nat := let saved := p; f saved + n\ntheorem same (P : Prop) (p q : P) (f : P -> Nat) : localProof P p f = localProof P q f := by rfl",
        true,
    );
}
#[test]
fn distinct_data_and_bad_unused_annotations_still_refuse() {
    for source in [
        "theorem bad (A : Type) (a b : A) : a = b := by rfl",
        "theorem bad (P Q : Prop) : P = Q := by rfl",
        "theorem bad (P : Prop) (p q : P) (f : P -> Nat) : f p = f q := by\n  let unused : String := 1\n  rfl",
        "theorem bad (P : Prop) (p q : P) (f : P -> Nat) (x y : Nat) : f p + x = f q + y := by rfl",
    ] {
        check(source, false);
    }
}
