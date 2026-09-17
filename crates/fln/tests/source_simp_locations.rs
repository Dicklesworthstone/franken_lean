//! Named-hypothesis simplification is verified by both real checking engines.
#![forbid(unsafe_code)]
use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
fn limits() -> SourceCheckLimits {
    SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(
        2 * 1024 * 1024,
    )))
}
fn check(source: &str, success: bool) {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let opts = KVMap::new();
    let root = base.logical_root(&opts);
    let result = base.check_source_files(&[source.as_bytes()], &opts, limits());
    if success {
        result
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"))
            .into_complete()
            .unwrap();
    } else {
        assert!(result.is_err(), "{source}");
    }
    assert_eq!(root, base.logical_root(&opts));
}
#[test]
fn simplify_hypotheses_in_both_directions_and_over_nested_occurrences() {
    check(
        "theorem forward (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by simp only [h] at hx; exact hx",
        true,
    );
    check(
        "theorem backward (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by simp only [← h] at hy; exact hy",
        true,
    );
    check(
        "theorem nested (f : Nat -> Nat) (h : forall n : Nat, f n = n) (P : Nat -> Prop) (hx : P (f (f 2))) : P 2 := by simp only [h] at hx; exact hx",
        true,
    );
}
#[test]
fn selected_definitions_and_quantified_rules_simplify_hypotheses() {
    check(
        "def wrap (n : Nat) : Nat := n\ntheorem unfold (P : Nat -> Prop) (n : Nat) (hx : P (wrap (wrap n))) : P n := by simp only [wrap] at hx; exact hx",
        true,
    );
    check(
        "def wrap (n : Nat) : Nat := n\ntheorem unfold (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P (wrap x)) : P y := by simp only [wrap, h] at hx; exact hx",
        true,
    );
    check(
        "theorem many (f : Nat -> Nat) (h : forall n : Nat, f n = n) (P : Nat -> Prop) (p : P (f 1)) (q : P (f 2)) : P 2 := by simp only [h] at p q; exact q",
        true,
    );
}
#[test]
fn simplification_can_use_only_selected_side_condition_evidence() {
    check(
        "theorem selected (P : Prop) (p : P) (x y : Nat) (h : P -> x = y) (Q : Nat -> Prop) (hx : Q x) : Q y := by simp only [h, p] at hx; exact hx",
        true,
    );
    check(
        "theorem unselected (P : Prop) (p : P) (x y : Nat) (h : P -> x = y) (Q : Nat -> Prop) (hx : Q x) : Q y := by simp only [h] at hx; exact hx",
        false,
    );
}
#[test]
fn introduced_let_and_dependent_hypotheses_keep_valid_scopes() {
    check(
        "theorem introed (P : Nat -> Prop) (x y : Nat) (h : x = y) : P x -> P y := by intro hx; have p := hx; simp only [h] at p; exact p",
        true,
    );
    check(
        "theorem dependent (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) (Q : P x -> Prop) (q : Q hx) : Q hx := by simp only [h] at hx; exact q",
        true,
    );
    check(
        "def castValue (A B : Type) (h : A = B) (x : A) : B := by simp only [h] at x; exact x",
        true,
    );
}
#[test]
fn cycles_unknown_locations_and_failed_alternatives_are_atomic() {
    check(
        "theorem recover (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by\n try (simp only [h, ← h] at hx)\n exact hx",
        true,
    );
    check(
        "theorem cycle (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by simp only [h, ← h] at hx; exact hx",
        false,
    );
    check(
        "theorem unknown (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by simp only [h] at hx missing; exact hx",
        false,
    );
    check(
        "theorem unchanged (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by simp only [] at hx; exact hx",
        false,
    );
    check(
        "theorem noOld (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P x := by simp only [h] at hx; assumption",
        false,
    );
}

#[test]
fn hypothesis_premise_resource_stops_remain_nonanswers_even_inside_try() {
    let base = Engine::with_source_seed(limits().admission)
        .unwrap()
        .into_complete()
        .unwrap();
    let options = KVMap::new();
    let root = base.logical_root(&options);
    for tactic in ["simp only [h] at hx", "try (simp only [h] at hx)"] {
        let source = format!(
            "theorem bounded (P : Nat -> Prop) (x y : Nat) (h : (1 <<< 18446744073709551616) = 0 -> x = y) (hx : P x) : P y := by\n  {tactic}\n  exact hx"
        );
        let error = base
            .check_source_files(&[source.as_bytes()], &options, limits())
            .unwrap_err();
        assert_eq!(error.disposition(), ("inconclusive", false, 3), "{error}");
        assert_eq!(root, base.logical_root(&options));
    }
}
