//! Whole-context simplification must produce closed, kernel-checked terms.
#![forbid(unsafe_code)]

use fln_core::outcome::Outcome;
use fln_elab::{check_definition_source, seed::source_seed_declarations};
use fln_env::{
    environment::{DeclarationBudget, DeclarationCommitted, Environment},
    pmap::CollisionBudget,
};
use fln_kernel::{
    Declaration,
    capability::{Published, admit},
    council::{Council, CouncilOutcome, convene},
    verdict::{Budget, Verdict},
};

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn environment() -> Environment {
    let mut env = Environment::new();
    for declaration in source_seed_declarations() {
        let Outcome::Complete(admitted) = admit(&env, declaration, budget()) else {
            panic!("seed nonanswer");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed rejected");
        };
        env = match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("seed publication {other:?}"),
        };
    }
    env
}

fn accepted(source: &str) {
    let result = check_definition_source(source.as_bytes(), &environment(), budget())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    assert!(
        matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}\n{:?}",
        result.outcome
    );
    let Declaration::Thm(proof) = result.declaration else {
        panic!("expected an actual theorem");
    };
    assert!(!proof.value.has_expr_mvar());
    assert!(!proof.value.has_level_mvar());
    assert!(!proof.value.has_fvar());
}

fn refused(source: &str) {
    if let Ok(result) = check_definition_source(source.as_bytes(), &environment(), budget()) {
        assert!(
            !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "unexpected theorem: {source}"
        );
    }
}

#[test]
fn simp_all_selects_local_proofs_with_and_without_defaults() {
    for tactic in [
        "simp_all",
        "simp_all only",
        "simp_all only []",
        "simp_all only [*, *]",
    ] {
        accepted(&format!("theorem t (P : Prop) (h : P) : P := by {tactic}"));
    }
    accepted("theorem t : 2 + 3 = 5 := by simp_all only");
}

#[test]
fn simp_all_revisits_earlier_hypotheses_after_later_equalities_change() {
    accepted(
        "theorem t (P : Nat -> Prop) (f : Nat -> Nat) (x y z : Nat) (hp : P (f y)) (he : f x = z) (hxy : x = y) : P z := by simp_all only",
    );
}

#[test]
fn simp_all_reaches_the_same_result_with_reordered_hypotheses() {
    accepted(
        "theorem t (P : Nat -> Prop) (f : Nat -> Nat) (x y z : Nat) (hxy : x = y) (he : f x = z) (hp : P (f y)) : P z := by simp_all only",
    );
}

#[test]
fn simp_all_preserves_explicit_evidence_and_uses_checked_transports() {
    accepted(
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by simp_all only [h]",
    );
    accepted(
        "theorem t.{u} (A : Sort u) (P : A -> Prop) (x y : A) (h : x = y) (hx : P x) : P y := by simp_all only",
    );
}

#[test]
fn simp_all_handles_local_proof_bindings_and_introduced_contexts() {
    accepted("theorem t (P : Prop) : P -> P := by intro h; simp_all only");
    accepted("theorem t (P : Prop) (h : P) : P := by have hp : P := h; simp_all only");
}

#[test]
fn failed_simp_all_alternative_restores_context_and_pending_transports() {
    accepted(
        "theorem t (P : Nat -> Prop) (Q : Prop) (x y : Nat) (h : x = y) (hx : P x) (hq : Q) : Q := by\n try (simp_all only [h]; fail)\n rewrite [h] at hx\n exact hq",
    );
}

#[test]
fn simp_all_does_not_assume_a_missing_conditional_premise() {
    refused(
        "theorem t (P : Nat -> Prop) (Q : Prop) (x y : Nat) (h : Q -> x = y) (hx : P x) : P y := by simp_all only",
    );
}

#[test]
fn simp_all_does_not_accept_false_or_unfinished_proofs() {
    for source in [
        "theorem t : 1 = 2 := by simp_all only",
        "theorem t (P Q : Prop) (h : P) : Q := by simp_all only",
        "theorem t : 0 = 0 := by simp_all only [missing]",
        "theorem t (x y : Nat) (h : x = y) (k : y = x) : x = x := by simp_all only [h, k]",
    ] {
        refused(source);
    }
}

#[test]
fn simp_custom_dischargers_prove_conditional_premises_in_the_local_context() {
    for discharger in [
        "(discharger := exact h)",
        "(disch := assumption)",
        "(discharger := first | fail | exact h)",
        "(discharger := simp only [h])",
    ] {
        accepted(&format!(
            "theorem t (P : Prop) (h : P) (a b : Nat) (rule : P -> a = b) : a = b := by simp {discharger} only [rule]"
        ));
    }
}

#[test]
fn simp_custom_dischargers_run_composed_tactics_and_close_every_goal() {
    accepted(
        "theorem t (P Q : Prop) (hp : P) (hq : Q) (a b : Nat) (rule : P ∧ Q -> a = b) : a = b := by simp (discharger := constructor <;> assumption) only [rule]",
    );
    accepted(
        "theorem t (P : Prop) (a b : Nat) (rule : (P -> P) -> a = b) : a = b := by simp (discharger := intro hp; exact hp) only [rule]",
    );
    accepted(
        "theorem t (a b : Nat) (rule : a = a -> a = b) : a = b := by simp (discharger := rfl) only [rule]",
    );
    refused(
        "theorem t (P Q : Prop) (hp : P) (a b : Nat) (rule : P ∧ Q -> a = b) : a = b := by simp (discharger := constructor; exact hp) only [rule]",
    );
}

#[test]
fn simp_custom_dischargers_are_shared_by_hypotheses_and_simpa() {
    accepted(
        "theorem t (P : Prop) (Q : Nat -> Prop) (h : P) (a b : Nat) (rule : P -> a = b) (ha : Q a) : Q b := by simp (discharger := exact h) only [rule] at ha; exact ha",
    );
    accepted(
        "theorem t (P : Prop) (Q : Nat -> Prop) (h : P) (a b : Nat) (rule : P -> a = b) (ha : Q a) : Q b := by simpa (discharger := exact h) only [rule] using ha",
    );
    accepted(
        "theorem t (P : Prop) (h : P) (a b : Nat) (rule : P -> a = b) : a = b := by\n conv => lhs; simp (discharger := exact h) only [rule]\n rfl",
    );
    accepted(
        "theorem t (P : Nat -> Prop) (h : ∀ n : Nat, P n) (f : Nat -> Nat) (rule : ∀ n : Nat, P n -> f n = n) : ∀ n : Nat, f n = n := by simp (discharger := apply h) only [rule]",
    );
}

#[test]
fn a_failing_custom_discharger_replaces_default_discharge_and_restores_state() {
    // The selected proof normally discharges the condition, but a custom
    // procedure owns that decision, even when it leaves the goal unchanged.
    accepted(
        "theorem t (P : Prop) (h : P) (a b : Nat) (rule : P -> a = b) : a = b := by simp only [rule, h]",
    );
    for tactic in ["fail", "skip", "exact 0"] {
        refused(&format!(
            "theorem t (P : Prop) (h : P) (a b : Nat) (rule : P -> a = b) : a = b := by simp (discharger := {tactic}) only [rule, h]"
        ));
    }
    accepted(
        "theorem t (P : Prop) (h : P) (a b : Nat) (rule : P -> a = b) : a = b := by\n try simp (discharger := clear h; fail) only [rule]\n exact rule h",
    );
    accepted(
        "theorem t (P : Prop) (h : P) (a b : Nat) (rule : P -> a = b) : a = b := by\n try simp (discharger := have temporary : P := h; fail) only [rule]\n simp (discharger := exact h) only [rule]",
    );
}

#[test]
fn custom_dischargers_do_not_invent_premises_or_change_simp_all_and_dsimp() {
    refused(
        "theorem t (P Q : Prop) (h : Q) (a b : Nat) (rule : P -> a = b) : a = b := by simp (discharger := exact h) only [rule]",
    );
    refused(
        "theorem t (P : Prop) (a b : Nat) (rule : P -> a = b) : a = b := by simp (discharger := assumption) only [rule]",
    );
    refused(
        "theorem t (a b : Nat) (rule : Nat -> a = b) : a = b := by simp (discharger := exact 0) only [rule]",
    );
    for tactic in ["simp_all", "dsimp"] {
        refused(&format!(
            "theorem t (P : Prop) (h : P) : P := by {tactic} (discharger := exact h) only; exact h"
        ));
    }
}
