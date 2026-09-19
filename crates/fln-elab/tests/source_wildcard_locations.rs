//! Native parser -> elaborator -> K1 regression cells for wildcard locations.
//! Acceptance must contain a closed theorem; parsing alone is not evidence.
#![forbid(unsafe_code)]

use fln_core::{name::Name, outcome::Outcome};
use fln_elab::{
    check_definition_source,
    instances::{register_class, register_instance},
    seed::source_seed_declarations,
};
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
    // Declarations and instance metadata are separate immutable inputs. The
    // seed helper supplies checked declarations, not their source registrations.
    env = register_class(&env, &Name::from_components(["Decidable"])).unwrap();
    for name in ["instDecidableTrue", "instDecidableFalse"] {
        env = register_instance(&env, &Name::from_components([name]), 1000).unwrap();
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
fn wildcard_rewrite_skips_unrelated_locations_and_preserves_its_evidence() {
    for source in [
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by rw [h] at *; exact hx",
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by rw [h] at *; exact hy",
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P x := by rewrite [← h] at *; exact hy",
    ] {
        accepted(source);
    }
}

#[test]
fn wildcard_rules_are_ordered_and_quantified_arguments_are_fresh_per_location() {
    accepted(
        "theorem t (P : Nat -> Prop) (x y z : Nat) (h : x = y) (k : y = z) (hx : P x) : P z := by rw [h, k] at *; exact hx",
    );
    accepted(
        "theorem t (f : Nat -> Nat) (P Q : Nat -> Prop) (x y : Nat) (h : ∀ n : Nat, f n = n) (hx : P (f x)) (hy : Q (f y)) : P x ∧ Q y := by rewrite [h] at *; constructor; exact hx; exact hy",
    );
}

#[test]
fn wildcard_simp_uses_checked_hypothesis_transports_and_the_target() {
    for source in [
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by simp only [h] at *; exact hx",
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by simp only [*] at *",
        "theorem t : 2 + 3 = 5 := by simp only [] at *",
    ] {
        accepted(source);
    }
}

#[test]
fn escaped_star_is_a_named_location_and_named_locations_remain_strict() {
    accepted(
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) («*» : P x) : P y := by rw [h] at «*»; exact «*»",
    );
    refused(
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) (hy : P y) : P y := by rw [h] at hy; exact hy",
    );
}

#[test]
fn wildcard_rewriting_retains_missing_premises_and_requires_a_real_match() {
    for source in [
        "theorem t (P : Nat -> Prop) (Q : Prop) (x y : Nat) (h : Q -> x = y) (hx : P x) : P y := by rewrite [h] at *; exact hx",
        "theorem t (x y : Nat) (h : x = y) : 0 = 0 := by rw [h] at *; rfl",
        "theorem t : 0 = 0 := by rw [missing] at *; rfl",
        "theorem t (x y : Nat) (h : x = y) : 1 = 2 := by rw [h] at *; rfl",
    ] {
        refused(source);
    }
}

#[test]
fn decide_closes_polymorphic_contexts_without_accepting_false_propositions() {
    accepted(
        "theorem t.{u} (A : Sort u) (x : A) : (fun (_ : A) => True) x := by decide",
    );
    refused(
        "theorem t.{u} (A : Sort u) (x : A) : (fun (_ : A) => False) x := by decide",
    );
}

#[test]
fn failed_wildcard_prefix_restores_hypotheses_and_deferred_closures() {
    accepted(
        "theorem t (P : Nat -> Prop) (x y : Nat) (h : x = y) (hx : P x) : P y := by\n try (rewrite [h, h] at *)\n rewrite [h] at *\n exact hx",
    );
}

#[test]
fn wildcard_conditional_rewrite_exposes_a_solvable_real_premise() {
    accepted(
        "theorem t (P : Nat -> Prop) (Q : Prop) (x y : Nat) (h : Q -> x = y) (hq : Q) (hx : P x) : P y := by rewrite [h] at *; exact hx; exact hq",
    );
}
