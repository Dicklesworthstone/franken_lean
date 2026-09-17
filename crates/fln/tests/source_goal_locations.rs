//! Mixed hypothesis/goal rewriting uses genuine transports in both directions.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};

fn check(source: &str, accepted: bool) {
    let limits = SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )));
    let base = Engine::with_source_seed(limits.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    let result = base.check_source_files(&[source.as_bytes()], &options, limits);
    if accepted {
        result
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
            .into_complete()
            .unwrap();
    } else {
        assert!(result.is_err(), "{source}");
    }
    assert_eq!(root, base.logical_root(&options));
}

#[test]
fn explicit_goal_markers_use_the_normal_rewrite_and_simp_policies() {
    for source in [
        "theorem unicode (x y : Nat) (h : x = y) : x = y := by rw [h] at ⊢",
        "theorem ascii (x y : Nat) (h : x = y) : y = x := by rewrite [← h] at |-; rfl",
        "theorem once (x y : Nat) (h : x = y) : x = y := by rw [h] at ⊢ ⊢",
        "theorem onlyGoal (x y : Nat) (h : x = y) : x = y := by simp only [h] at ⊢",
        "theorem emptyRules (x : Nat) : x = x := by simp only [] at |-",
    ] {
        check(source, true);
    }
    check(
        "theorem open (x y : Nat) (h : x = y) : x = y := by rewrite [h] at ⊢",
        false,
    );
}

#[test]
fn simultaneous_hypothesis_and_goal_transports_preserve_types_and_rule_order() {
    for source in [
        "theorem both (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by rewrite [h] at hx ⊢; exact hx",
        "theorem sequence (P : Nat -> Prop) (x y z : Nat) (h : x = y) (k : y = z) (hx : P x) : P x := by rewrite [h, k] at ⊢ hx; exact hx",
        "def both (A B : Type) (h : A = B) (x : A) : A := by rewrite [h] at x |-; exact x",
        "theorem many (f : Nat -> Nat) (h : forall n : Nat, f n = n) (P : Nat -> Prop) (p : P (f 1)) (q : P (f 2)) : P (f 2) := by rewrite [h] at p q ⊢; exact q",
    ] {
        check(source, true);
    }
}

#[test]
fn conditional_mixed_rewrites_keep_each_unproved_premise() {
    check(
        "theorem conditional (R : Prop) (r : R) (x y : Nat) (h : R -> x = y) (P : Nat -> Prop) (hx : P x) : P x := by rewrite [h] at hx ⊢; exact hx; exact r; exact r",
        true,
    );
    check(
        "theorem conditional (R : Prop) (x y : Nat) (h : R -> x = y) (P : Nat -> Prop) (hx : P x) : P x := by rewrite [h] at hx ⊢; exact hx",
        false,
    );
}

#[test]
fn mixed_simp_accepts_real_hypothesis_progress_even_if_the_goal_is_unchanged() {
    for source in [
        "theorem mixed (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by simp only [h] at hx ⊢; exact hx",
        "theorem unchangedGoal (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by simp only [h] at hx ⊢; exact hx",
        "theorem unchangedHyp (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by simp only [h] at hy |-; exact hy",
        "def both (A B : Type) (h : A = B) (x : A) : A := by simp only [h] at x ⊢; exact x",
    ] {
        check(source, true);
    }
}

#[test]
fn failed_mixed_locations_roll_back_before_an_alternative_continues() {
    for source in [
        "theorem recover (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by\n  try (rw [h] at hx missing ⊢)\n  exact hx",
        "theorem recover (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by\n  try (simp only [h, ← h] at hx ⊢)\n  exact hx",
        "theorem recover (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by\n  try (rewrite [h, ← h] at hx missing ⊢)\n  exact hx",
    ] {
        check(source, true);
    }
    check(
        "theorem missing (x y : Nat) (h : x = y) : x = y := by rw [h] at ⊢ missing",
        false,
    );
}

#[test]
fn escaped_goal_markers_remain_hypothesis_names() {
    check(
        "theorem escaped (P : Nat -> Prop) (x y : Nat) (h : x = y) («⊢» : P x) : P y := by rw [h] at «⊢»; exact «⊢»",
        true,
    );
    check(
        "theorem escaped (P : Nat -> Prop) (x y : Nat) (h : x = y) («|-» : P x) : P y := by simp only [h] at «|-»; exact «|-»",
        true,
    );
    check(
        "theorem escaped (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by rw [h] «at» hx; exact hx",
        false,
    );
}
