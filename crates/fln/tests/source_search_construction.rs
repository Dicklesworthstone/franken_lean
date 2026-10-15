//! Search fallbacks build ordinary introductions, constructors and False recursors.
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
fn check(base: &Engine, source: &str) -> Engine {
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
fn reject(base: &Engine, source: &str) {
    let root = base.logical_root(&KVMap::new());
    assert!(
        base.check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits())
        )
        .is_err(),
        "{source}"
    );
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert!(!base.environment().contains(&Name::from_components(["bad"])));
}

#[test]
fn search_introduces_arrow_and_dependent_binders_without_escaping_locals() {
    let base = engine();
    for source in [
        "theorem result (P : Prop) : P -> P := by solve_by_elim",
        "theorem result (P Q : Prop) : (P -> Q) -> P -> Q := by solve_by_elim",
        "theorem result (A : Type) (P : A -> Prop) (h : (x : A) -> P x) : (x : A) -> P x := by solve_by_elim",
        "theorem result (P : Prop) (loop : (P -> P) -> (P -> P)) : P -> P := by solve_by_elim",
        "theorem result (P : Prop) : (let Q := P; Q -> Q) := by solve_by_elim",
    ] {
        check(&base, source);
    }
    reject(
        &base,
        "theorem bad (P Q : Prop) : P -> Q := by solve_by_elim",
    );
    reject(
        &base,
        "theorem bad (A : Type) : (x : A) -> False := by solve_by_elim",
    );
}

#[test]
fn search_constructs_nested_propositions_and_closed_data_without_default_lemmas() {
    let base = engine();
    for source in [
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by solve_by_elim",
        "theorem result (P Q : Prop) : (P -> P) ∧ (Q -> Q) := by solve_by_elim",
        "theorem result (P Q : Prop) (hp : P) : P ∨ Q := by solve_by_elim",
        "theorem result : True := by solve_by_elim only []",
        "def result : Nat := by solve_by_elim only []",
        "def result : Bool := by solve_by_elim only []",
    ] {
        check(&base, source);
    }
    reject(
        &base,
        "theorem bad (P Q : Prop) (hp : P) : P ∧ Q := by solve_by_elim",
    );
    // The pin's constructor discharger picks its first applicable constructor,
    // not every constructor whose later premises might become provable.
    reject(
        &base,
        "theorem bad (P : Prop) (hp : P) : False ∨ P := by solve_by_elim",
    );
    reject(
        &base,
        "def bad (A : Type) (loop : A -> A) : A := by solve_by_elim",
    );
}

#[test]
fn search_constructor_witnesses_share_backtracking_with_later_dependent_premises() {
    // Exists is deliberately absent from the small source seed. Admit the
    // ordinary polymorphic inductive rather than manufacturing seed evidence.
    let base = check(
        &engine(),
        "inductive Exists.{u} {A : Sort u} (P : A -> Prop) : Prop where | intro (w : A) (h : P w)",
    );
    for source in [
        "theorem result (P : Nat -> Prop) (x y : Nat) (hx : P x) : Exists P := by solve_by_elim",
        "theorem result (P Q : Nat -> Prop) (x y : Nat) (hx : P x) (hy : Q x) : Exists (fun n => P n ∧ Q n) := by solve_by_elim",
        "theorem result (P Q : Prop) (hp : P) (hq : Q) : (P ∧ Q) ∧ (P -> P) := by\\n  constructor\\n  solve_by_elim*",
    ] {
        check(&base, &source.replace("\\n", "\n"));
    }
}

#[test]
fn search_exfalso_retries_only_a_single_visible_goal_and_keeps_checked_evidence() {
    let base = engine();
    for source in [
        "theorem result (P Q : Prop) (hp : P) (no : P -> False) : Q := by solve_by_elim only [hp, no]",
        "def result (no : False) : Nat := by solve_by_elim only [no]",
        "theorem result (P Q R : Prop) (hp : P) (hq : Q) (no : P -> Q -> False) : R := by solve_by_elim only [no, hp, hq]",
    ] {
        check(&base, source);
    }
    reject(
        &base,
        "theorem bad (P Q R : Prop) (hp : P) (no : P -> Q -> False) : R := by solve_by_elim only [no, hp]",
    );
}

#[test]
fn joint_search_does_not_apply_exfalso_to_one_sibling_in_a_multi_goal_frontier() {
    let base = engine();
    reject(
        &base,
        "theorem bad (P Q : Prop) (hp : P) (no : P -> False) : Q ∧ Q := by\n  constructor\n  solve_by_elim*",
    );
    // Independent tactic invocations each have exactly one initial goal.
    check(
        &base,
        "theorem result (P Q : Prop) (hp : P) (no : P -> False) : Q ∧ Q := by\n  constructor <;> solve_by_elim",
    );
    // Focus must not consume or discharge its suspended sibling.
    check(
        &base,
        "theorem result (P Q : Prop) (hp : P) (no : P -> False) : Q ∧ True := by\n  constructor\n  focus solve_by_elim*\n  constructor",
    );
}

#[test]
fn structural_search_cannot_turn_unsafe_definitions_into_logical_evidence() {
    let base = check(&engine(), "unsafe def impossible : False := impossible");
    reject(
        &base,
        "theorem bad (P : Prop) : P := by solve_by_elim only [impossible]",
    );
    reject(
        &base,
        "theorem bad (P : Prop) : True ∧ P := by solve_by_elim only [impossible]",
    );
    check(
        &base,
        "theorem result : True ∧ (True -> True) := by solve_by_elim",
    );
}
