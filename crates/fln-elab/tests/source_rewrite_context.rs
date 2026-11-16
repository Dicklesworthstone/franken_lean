//! Source-level transport controls for rewriting in dependent proof contexts.
#![forbid(unsafe_code)]

use fln_core::{name::Name, outcome::Outcome};
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
            panic!("seed admission did not complete");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed was rejected");
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
            other => panic!("seed publication: {other:?}"),
        };
    }
    env
}

#[test]
fn rewriting_transports_predicates_and_quantified_goals_without_open_terms() {
    let env = environment();
    for source in [
        "theorem transport {A : Type} (x y : A) (h : x = y) (P : A -> Prop) (p : P x) : P y := by rw [<- h]; exact p",
        "theorem quantified {A : Type} (x y : A) (h : x = y) (P : A -> A -> Prop) (p : forall z : A, P x z) : forall z : A, P y z := by rw [<- h]; exact p",
    ] {
        let result = check_definition_source(source.as_bytes(), &env, budget())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        assert!(
            matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}\n{:?}",
            result.outcome
        );
        let Declaration::Thm(theorem) = result.declaration else {
            panic!("expected a checked theorem");
        };
        assert!(!theorem.value.has_fvar());
        assert!(!theorem.value.has_expr_mvar());
        assert!(!theorem.value.has_level_mvar());
        assert!(!theorem.value.has_loose_bvars());
    }
}

#[test]
fn rewriting_cannot_forge_a_predicate_or_discard_an_unsolved_goal() {
    let env = environment();
    for source in [
        "theorem forge {A : Type} (x y : A) (h : x = y) (P : A -> Prop) : P y := by rw [<- h]",
        "theorem forge {A : Type} (x y : A) (h : x = y) (P Q : A -> Prop) (p : P x) : Q y := by rw [<- h]; exact p",
    ] {
        if let Ok(result) = check_definition_source(source.as_bytes(), &env, budget()) {
            assert!(
                !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "forged theorem accepted: {source}"
            );
        }
    }
}

#[test]
fn native_conv_transports_work_without_named_prelude_helpers() {
    let env = environment();
    for helper in ["congrArg", "Eq.symm", "Eq.trans", "Eq.mp", "Eq.mpr", "id"] {
        assert!(
            !env.contains(&Name::from_components(helper.split('.'))),
            "the fixture must exercise equality induction without {helper}"
        );
    }
    for source in [
        "theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (p : P y) : P x := by\n conv => rw [h]\n exact p",
        "theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (p : P x) : P y := by\n conv at p => rw [h]\n exact p",
        "theorem transport (P : Nat -> Prop) (x y : Nat) (h : x = y) (p : P x) : P y := by\n conv => rw [<- h]\n exact p",
        "theorem transport (P : Nat -> Prop) (x y z : Nat) (h : x = y) (k : y = z) (p : P z) : P x := by\n conv => rw [h, k]\n exact p",
        "theorem transport (P : Nat -> Prop) (x y z : Nat) (h : x = y) (k : y = z) (p : P z) : P x := by\n conv => simp only [h, k]\n exact p",
        "theorem transport.{u} (A : Sort u) (P : A -> Prop) (x y : A) (h : x = y) (p : P y) : P x := by\n conv => rw [h]\n exact p",
        "def transport (A B : Type) (h : A = B) (a : A) : B := by\n conv => rw [<- h]\n exact a",
        "def changed : Nat := by\n conv => change (fun T : Type => T) Nat\n exact 0",
    ] {
        let result = check_definition_source(source.as_bytes(), &env, budget())
            .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
        assert!(
            matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}\n{:?}",
            result.outcome
        );
        let value = match result.declaration {
            Declaration::Thm(theorem) => theorem.value,
            Declaration::Defn(definition) => definition.value,
            other => panic!("expected a checked theorem or definition: {other:?}"),
        };
        assert!(!value.has_fvar(), "{source}");
        assert!(!value.has_expr_mvar(), "{source}");
        assert!(!value.has_level_mvar(), "{source}");
        assert!(!value.has_loose_bvars(), "{source}");
    }
}

#[test]
fn native_conv_transports_still_require_evidence_and_a_finished_proof() {
    let env = environment();
    for source in [
        "theorem forge (P Q : Prop) (p : P) : Q := by\n conv => change P\n exact p",
        "theorem forge (P : Nat -> Prop) (x y : Nat) (h : x = y) : P y := by\n conv => rw [<- h]",
        "theorem forge (P Q : Prop) (p : P) : Q := by\n conv => rw [p]\n exact p",
        "def forge (A B : Type) (a : A) : B := by\n conv => change A\n exact a",
    ] {
        if let Ok(result) = check_definition_source(source.as_bytes(), &env, budget()) {
            assert!(
                !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "forged conversion accepted: {source}"
            );
        }
    }
}
