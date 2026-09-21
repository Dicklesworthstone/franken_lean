//! Named match equations are scoped minor premises, never assumed facts.
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
fn env() -> Environment {
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
fn accepted(source: &str) -> Declaration {
    let result = check_definition_source(source.as_bytes(), &env(), budget())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    assert!(
        matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}\n{:?}",
        result.outcome
    );
    let value = match &result.declaration {
        Declaration::Thm(value) => &value.value,
        Declaration::Defn(value) => &value.value,
        _ => panic!("source declaration"),
    };
    assert!(!value.has_fvar());
    assert!(!value.has_expr_mvar());
    assert!(!value.has_level_mvar());
    assert!(!value.has_loose_bvars());
    result.declaration
}
fn refused(source: &str) {
    if let Ok(result) = check_definition_source(source.as_bytes(), &env(), budget()) {
        assert!(
            !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}"
        );
    }
}

#[test]
fn branch_handlers_receive_equalities_with_the_original_discriminant() {
    accepted(
        "def use (n : Nat) (z : n = Nat.zero -> Nat) (s : (k : Nat) -> n = Nat.succ k -> Nat) : Nat := match h : n with | Nat.zero => z h | Nat.succ k => s k h",
    );
    accepted(
        "theorem prove (n : Nat) (P : Prop) (z : n = Nat.zero -> P) (s : (k : Nat) -> n = Nat.succ k -> P) : P := match h : n with | Nat.zero => z h | Nat.succ k => s k h",
    );
}

#[test]
fn computed_discriminants_are_generalized_without_selecting_a_branch() {
    accepted(
        "def use (n : Nat) (z : Nat.succ n = Nat.zero -> Nat) (s : (k : Nat) -> Nat.succ n = Nat.succ k -> Nat) : Nat := match h : Nat.succ n with | Nat.zero => z h | Nat.succ k => s k h",
    );
    accepted(
        "theorem same (n : Nat) : Nat.succ n = Nat.succ n := match h : Nat.succ n with | Nat.zero => rfl | Nat.succ k => rfl",
    );
}

#[test]
fn dependent_results_and_anonymous_evidence_remain_checked() {
    accepted(
        "theorem same (n : Nat) : n = n := match h : n with | Nat.zero => rfl | Nat.succ k => rfl",
    );
    accepted("def pred (n : Nat) : Nat := match _ : n with | Nat.zero => 0 | Nat.succ k => k");
}

#[test]
fn equation_binders_shadow_locally_and_restore_outer_names() {
    accepted(
        "def outer (h n : Nat) : Nat := let k : Nat := match h : n with | Nat.zero => 0 | Nat.succ k => k; h",
    );
    refused(
        "def leak (n : Nat) : Nat := let k : Nat := match h : n with | Nat.zero => 0 | Nat.succ k => k; h",
    );
}

#[test]
fn invalid_evidence_and_unselected_branches_cannot_be_erased() {
    for source in [
        "theorem bad : 0 = 1 := match h : Nat.zero with | Nat.zero => h | Nat.succ k => rfl",
        "def bad : Nat := match h : Nat.zero with | Nat.zero => 0 | Nat.succ k => h",
        "def bad : Nat := match h : Nat.succ 0 with | Nat.zero => h | Nat.succ k => k",
        "def missing (n : Nat) : Nat := match h : n with | Nat.zero => 0",
        "def wrong (n m : Nat) (z : m = Nat.zero -> Nat) : Nat := match h : n with | Nat.zero => z h | Nat.succ k => k",
    ] {
        refused(source);
    }
}

#[test]
fn unsupported_matrix_annotations_are_not_silently_dropped() {
    refused("def f (n : Nat) : Nat := match h : n with | Nat.zero => 0 | _ => 1");
    refused("def f (n m : Nat) : Nat := match h : n, m with | Nat.zero, Nat.zero => 0 | _, _ => 1");
}
