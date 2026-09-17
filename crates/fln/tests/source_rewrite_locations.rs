//! Hypothesis rewriting through the actual K1/independent-checker council.
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
fn check(source: &str) {
    engine()
        .check_source_files(
            &[source.as_bytes()],
            &KVMap::new(),
            SourceCheckLimits::new(limits()),
        )
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
        .into_complete()
        .unwrap();
}
#[test]
fn named_hypotheses_transport_in_both_directions() {
    check(
        "theorem forward (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by rw [h] at hx; exact hx",
    );
    check(
        "theorem backward (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by rw [← h] at hy; exact hy",
    );
    check("def castValue {A B : Type} (h : A = B) (x : A) : B := by rw [h] at x; exact x");
}
#[test]
fn introduced_locals_and_rule_lists_have_correct_closure_scopes() {
    check(
        "theorem introed (P : Nat -> Prop) (x y z : Nat) : x = y -> y = z -> P x -> P z := by intro h k hx; rewrite [h, k] at hx; exact hx",
    );
    check(
        "theorem both (P : Nat -> Nat -> Prop) (x y z : Nat) (h : x = y) (k : y = z) (hx : P x x) (hy : P x x) : P z z := by rewrite [h, k] at hx hy; exact hy",
    );
    check(
        "theorem local (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by have p := hx; rw [h] at p; exact p",
    );
}
#[test]
fn dependent_hypotheses_and_goals_keep_their_original_identity() {
    check(
        "theorem dependent (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) (Q : P x -> Prop) (q : Q hx) : Q hx := by rewrite [h] at hx; exact q",
    );
    check(
        "def dependentType (A B : Type) (h : A = B) (x : A) (Q : A -> Type) (q : Q x) : Q x := by rewrite [h] at x; exact q",
    );
    check(
        "theorem localDependent (P : Nat -> Prop) (x y : Nat) (h : x = y) : P x -> P y := by intro hx; have saved := hx; rewrite [h] at hx; exact hx",
    );
}
#[test]
fn conditional_rules_retain_their_real_side_goals() {
    check(
        "theorem conditional (P : Prop) (x y : Nat) (h : P -> x = y) (Q : Nat -> Prop) (hx : Q x) (p : P) : Q y := by rewrite [h] at hx; exact hx; exact p",
    );
    check(
        "theorem conditional (P : Prop) (Q : Nat -> Prop) (x y : Nat) : (P -> x = y) -> Q x -> P -> Q y := by intro h hx p; rewrite [h] at hx; exact hx; exact p",
    );
}
#[test]
fn quantified_rules_instantiate_separately_at_each_hypothesis() {
    check(
        "theorem many (f : Nat -> Nat) (h : forall n : Nat, f n = n) (P : Nat -> Prop) (p : P (f 1)) (q : P (f 2)) : P 2 := by rewrite [h] at p q; exact q",
    );
}
#[test]
fn failures_and_speculative_prefixes_do_not_leak_context_changes() {
    check(
        "theorem recover (P : Nat -> Prop) (x y z : Nat) (h : x = y) (k : z = y) (hx : P x) : P x := by\n try (rewrite [h, k] at hx)\n exact hx",
    );
    let base = engine();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for source in [
        "theorem bad (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by rewrite [h] at hx; assumption",
        "theorem bad (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by rewrite [h] at missing; exact hx",
        "theorem bad (P : Prop) (x y : Nat) (h : P -> x = y) (Q : Nat -> Prop) (hx : Q x) : Q y := by rewrite [h] at hx; exact hx",
        "theorem bad (x y : Nat) (h : x = y) : 0 = 1 := by rw [h] at h; rfl",
    ] {
        assert!(
            base.check_source_files(
                &[source.as_bytes()],
                &options,
                SourceCheckLimits::new(limits())
            )
            .is_err(),
            "{source}"
        );
        assert_eq!(base.logical_root(&options), root);
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
    check("theorem again (x y : Nat) (h : x = y) : x = y := by exact h");
}
