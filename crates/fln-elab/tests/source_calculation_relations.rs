//! Written calculation steps and transports pass through ordinary K1 admission.
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
    let checked = check_definition_source(source.as_bytes(), &environment(), budget())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    assert!(
        matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}\n{:?}",
        checked.outcome
    );
    let value = match &checked.declaration {
        Declaration::Thm(value) => &value.value,
        Declaration::Defn(value) => &value.value,
        other => panic!("unexpected source declaration: {other:?}"),
    };
    assert!(!value.has_expr_mvar());
    assert!(!value.has_level_mvar());
    assert!(!value.has_fvar());
    assert!(!value.has_loose_bvars());
}

fn refused(source: &str) {
    if let Ok(checked) = check_definition_source(source.as_bytes(), &environment(), budget()) {
        assert!(
            !matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "accepted invalid calculation: {source}"
        );
    }
}

#[test]
fn a_single_step_can_be_any_binary_relation() {
    accepted(
        "theorem retain (R : Nat -> Bool -> Prop) (a : Nat) (b : Bool) (h : R a b) : R a b := calc\n  R a b := h",
    );
}

#[test]
fn equality_transports_the_right_endpoint_of_a_heterogeneous_relation() {
    accepted(
        "theorem right (R : Nat -> Bool -> Prop) (a : Nat) (b c : Bool) (h : R a b) (e : b = c) : R a c := calc\n  R a b := h\n  _ = c := e",
    );
}

#[test]
fn equality_transports_the_left_endpoint_without_a_symmetry_axiom() {
    accepted(
        "theorem left (R : Nat -> Bool -> Prop) (a b : Nat) (c : Bool) (e : a = b) (h : R b c) : R a c := calc\n  a = b := e\n  R _ c := h",
    );
}

#[test]
fn both_transports_compose_and_retain_the_original_equality_path() {
    accepted(
        "theorem both (R : Nat -> Bool -> Prop) (a b : Nat) (c d : Bool) (e : a = b) (h : R b c) (f : c = d) : R a d := calc\n  a = b := e\n  R _ c := h\n  _ = d := f",
    );
    accepted(
        "theorem equality (a b c : Nat) (h : a = b) (k : b = c) : a = c := calc\n  a = b := h\n  _ = c := k",
    );
}

#[test]
fn transport_preserves_type_valued_relations_and_their_universe() {
    accepted(
        "def right (R : Nat -> Bool -> Type) (a : Nat) (b c : Bool) (h : R a b) (e : b = c) : R a c := calc\n  R a b := h\n  _ = c := e",
    );
    accepted(
        "def left (R : Nat -> Bool -> Type) (a b : Nat) (c : Bool) (e : a = b) (h : R b c) : R a c := calc\n  a = b := e\n  R _ c := h",
    );
}

#[test]
fn wrong_midpoints_proofs_and_final_endpoints_never_create_success() {
    for source in [
        "theorem bad (R : Nat -> Nat -> Prop) (a b c : Nat) (h : R a b) (e : a = c) : R a c := calc\n  R a b := h\n  a = c := e",
        "theorem bad (R : Nat -> Nat -> Prop) (a b c : Nat) (h : R a b) (e : b = c) : R a c := calc\n  R a b := e\n  _ = c := e",
        "theorem bad (R : Nat -> Nat -> Prop) (a b c : Nat) (h : R a b) (e : b = c) : R c a := calc\n  R a b := h\n  _ = c := e",
        "theorem bad (R : Nat -> Nat -> Prop) (a b c : Nat) (h : R a b) (k : R b c) : R a c := calc\n  R a b := h\n  R _ c := k",
    ] {
        refused(source);
    }
}

#[test]
fn even_an_erasing_relation_cannot_hide_a_disconnected_written_step() {
    refused(
        "theorem bad (P : Prop) (p : P) (a b c : Nat) (e : a = c) : P := let R := fun (x y : Nat) => P; calc\n  R a b := p\n  a = c := e",
    );
}
