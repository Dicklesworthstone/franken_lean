//! Constructing data/proofs leaves every field as a checked obligation.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn run(source: &str) -> Result<(), String> {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .map_err(|error| format!("{error:?}"))?
        .into_complete()
        .map(|_| ())
        .map_err(|error| format!("{error:?}"))
}
fn check(source: &str) {
    run(source).unwrap_or_else(|error| panic!("{source}\n{error}"));
}
fn reject(source: &str) {
    assert!(run(source).is_err(), "accepted {source}");
}
const LOGIC: &str = "inductive Both (P Q : Prop) : Prop where | intro (left : P) (right : Q)\ninductive Either (P Q : Prop) : Prop where | left (proof : P) | right (proof : Q)\n";
#[test]
fn constructor_builds_conjunction_with_both_obligations() {
    check(&format!(
        "{LOGIC} theorem pair (P Q : Prop) (p : P) (q : Q) : Both P Q := by constructor; exact p; exact q"
    ));
    reject(&format!(
        "{LOGIC} theorem missing (P Q : Prop) (p : P) : Both P Q := by constructor; exact p"
    ));
}
#[test]
fn directional_constructors_retain_the_chosen_branch() {
    check(&format!(
        "{LOGIC} theorem l (P Q : Prop) (p : P) : Either P Q := by left; exact p\ntheorem r (P Q : Prop) (q : Q) : Either P Q := by right; exact q"
    ));
    reject(&format!(
        "{LOGIC} theorem bad (P Q : Prop) (q : Q) : Either P Q := by left; exact q"
    ));
}
#[test]
fn nested_construction_and_introduced_contexts_close_in_order() {
    check(&format!(
        "{LOGIC} theorem nested (P Q R : Prop) : P -> Q -> R -> Both P (Both Q R) := by intro p q r; constructor; exact p; constructor; exact q; exact r"
    ));
}
#[test]
fn dependent_record_fields_are_solved_before_their_consumers() {
    check(
        "structure Package where\n carrier : Type\n value : carrier\ndef package : Package := by constructor; exact Nat; exact 7\ntheorem value : package.value = 7 := by rfl",
    );
}
#[test]
fn existential_witness_and_proof_are_both_checked() {
    check(
        "inductive Witness (P : Nat -> Prop) : Prop where | intro (n : Nat) (proof : P n)\ntheorem exists : Witness (fun n => n = 7) := by constructor; exact 7; rfl",
    );
    reject(
        "inductive Witness (P : Nat -> Prop) : Prop where | intro (n : Nat) (proof : P n)\ntheorem bad : Witness (fun n => n = 7) := by constructor; exact 8; rfl",
    );
}
#[test]
fn indexed_constructor_search_rolls_back_failed_candidates() {
    check(
        "inductive At : Nat -> Type where | zero : At 0 | one : At 1\ndef one : At 1 := by constructor\ntheorem checked : one = At.one := by rfl",
    );
    reject(
        "inductive At : Nat -> Type where | zero : At 0 | one : At 1\ndef bad : At 2 := by constructor",
    );
}
#[test]
fn nullary_constructors_and_index_inference_do_not_leave_spurious_goals() {
    check(
        "def yes : Bool := by right\ndef no : Bool := by left\ntheorem yes_ok : yes = true := by rfl\ntheorem no_ok : no = false := by rfl\ntheorem refl (n : Nat) : n = n := by constructor",
    );
}
#[test]
fn local_shadowing_cannot_impersonate_admitted_constructors() {
    check(&format!(
        "{LOGIC} theorem local (P Q : Prop) (p : P) (q : Q) (intro : Nat) : Both P Q := by constructor; exact p; exact q"
    ));
}
#[test]
fn constructor_tactics_refuse_abstract_targets_and_wrong_arity() {
    for source in [
        "theorem bad (P : Prop) : P := by constructor",
        "def bad : Nat := by right; exact 0; exact 1",
        "structure UnitLike where\n theorem bad : UnitLike := by left",
        "def bad : Nat := by constructor 3",
    ] {
        reject(source);
    }
}
#[test]
fn invalid_unused_fields_and_proof_obligations_are_not_erased() {
    reject(
        "structure Box where\n value : Nat\ndef bad : Box := by constructor; exact (1 : String)",
    );
    reject(&format!(
        "{LOGIC} theorem bad : Both (0 = 0) (0 = 1) := by constructor; rfl; rfl"
    ));
}
