//! Repeat retains successful iterations, restores failed ones, and spends fuel.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn run(source: &str) -> Result<(), String> {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let engine = Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap();
    let root = engine.logical_root(&KVMap::new());
    let result = engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits),
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
    result
        .map_err(|e| format!("{e:?}"))?
        .into_complete()
        .map(|_| ())
        .map_err(|e| format!("{e:?}"))
}
fn check(source: &str) {
    run(source).unwrap_or_else(|e| panic!("{source}\n{e}"));
}
fn reject(source: &str) {
    assert!(run(source).is_err(), "accepted {source}");
}
const BOTH: &str = "inductive Both (P Q : Prop) : Prop where | intro (left : P) (right : Q)\n";
#[test]
fn repeated_introductions_retain_their_dependent_context() {
    check("theorem t (P : Prop) : P -> P -> P := by\n repeat intro h\n exact h");
    check(
        "def identity : forall A : Type, A -> A := by\n repeat intro x\n exact x\ntheorem result : identity Nat 8 = 8 := by rfl",
    );
}
#[test]
fn the_failed_iteration_restores_its_partial_introduction() {
    check(
        "theorem t (P : Prop) : P -> P -> P -> P := by\n repeat (intro x; intro y)\n intro last\n exact last",
    );
    reject("theorem t (P : Prop) : P -> P -> P -> P := by\n repeat (intro x; intro y)\n exact x");
}
#[test]
fn repetition_can_construct_and_discharge_new_goals() {
    check(&format!(
        "{BOTH}theorem t (P : Prop) (p : P) : Both (Both P P) (Both P P) := by\n repeat (first | constructor | exact p)"
    ));
    // `repeat` stops on the unsplittable first goal; unlike `repeat'`, it does
    // not skip that goal and recursively visit the remaining siblings.
    check(&format!(
        "{BOTH}theorem t (P : Prop) (p : P) : Both (Both P P) (Both P P) := by\n repeat constructor\n exact p\n exact p\n constructor <;> exact p"
    ));
    reject(&format!(
        "{BOTH}theorem t (P : Prop) (p : P) : Both (Both P P) (Both P P) := by\n repeat constructor\n all_goals exact p"
    ));
}
#[test]
fn repetition_rolls_back_all_goal_mapping_in_a_failed_iteration() {
    check(&format!(
        "{BOTH}theorem t (P Q : Prop) (p : P) (q : Q) : Both P Q := by\n constructor\n repeat (all_goals exact p)\n exact p\n exact q"
    ));
}
#[test]
fn failed_iteration_after_goal_completion_is_not_a_success() {
    check("theorem t : 0 = 0 := by\n repeat (rfl; fail)\n rfl");
    reject("theorem t : 0 = 0 := by repeat (rfl; fail)");
    check("theorem t : 0 = 0 := by\n rfl\n repeat fail");
}
#[test]
fn parent_choice_can_undo_several_successful_repeat_iterations() {
    check(
        "theorem t (P : Prop) : P -> P := by\n first\n | repeat intro lost\n   fail\n | intro kept\n   exact kept",
    );
}
#[test]
fn repeat_does_not_leak_facts_or_equation_assignments() {
    check("theorem t (P : Prop) (p : P) : P := by\n repeat (have lost := p; fail)\n exact p");
    reject("theorem t (P : Prop) (p : P) : P := by\n repeat (have lost := p; fail)\n exact lost");
    check(
        "structure Package where\n carrier : Type\n value : carrier\ndef package : Package := by\n refine Package.mk ?type ?value\n repeat (exact Nat; fail)\n exact String\n exact \"kept\"\ntheorem result : package.value = \"kept\" := by rfl",
    );
}
#[test]
fn repetition_and_shared_holes_keep_pending_parent_closures() {
    check(&format!(
        "{BOTH}theorem t (P : Prop) (p : P) : Both P P := by\n refine Both.intro ?shared ?shared\n repeat exact p"
    ));
    check(&format!(
        "{BOTH}theorem t (P : Prop) (p : P) : Both (Both P P) P := by\n constructor\n · repeat (first | constructor | exact p)\n · exact p"
    ));
}
#[test]
fn repeat_and_sequencing_do_not_consume_old_siblings() {
    check(&format!(
        "{BOTH}theorem t (P Q : Prop) (p : P) (q : Q) : Both (Both P P) Q := by\n constructor\n repeat (constructor <;> exact p)\n exact q"
    ));
}
#[test]
fn unused_false_proofs_are_not_erased_by_a_successful_iteration() {
    reject("theorem t : 0 = 1 := by repeat rfl");
    reject("theorem t : 0 = 0 := by repeat (have unused : String := 1; rfl)");
    check("theorem t : 0 = 0 := by\n repeat (have unused : String := 1; rfl)\n rfl");
}
