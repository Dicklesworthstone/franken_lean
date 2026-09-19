//! Source assertions produce checked terms, including discarded bad witnesses.
#![forbid(unsafe_code)]
use fln_core::{expr::ExprNode, outcome::Outcome};
use fln_elab::check_definition_source;
use fln_kernel::{
    Declaration,
    verdict::{Budget, Verdict},
};

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn accepted(source: &str) -> Declaration {
    let env = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    let checked = check_definition_source(source.as_bytes(), &env, budget())
        .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
    assert!(
        matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}\n{:?}",
        checked.outcome
    );
    let value = match &checked.declaration {
        Declaration::Thm(d) => &d.value,
        Declaration::Defn(d) => &d.value,
        _ => panic!("checked source declaration"),
    };
    assert!(
        !value.has_fvar()
            && !value.has_expr_mvar()
            && !value.has_level_mvar()
            && !value.has_loose_bvars()
    );
    checked.declaration
}
fn refused(source: &str) {
    let env = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    if let Ok(checked) = check_definition_source(source.as_bytes(), &env, budget()) {
        assert!(
            !matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "accepted bad source: {source}"
        );
    }
}
#[test]
fn named_and_inferred_assertions_construct_checked_local_evidence() {
    accepted("theorem relay (P : Prop) (p : P) : P := have h : P := p; h");
    accepted("theorem relay (P : Prop) (p : P) : P := have h := p; h");
    accepted("theorem relay (P : Prop) (p : P) : P := have h : P := (by exact p); h");
    accepted("theorem relay (P : Prop) (p : P) : P := have h : P := p; have q : P := h; q");
}
#[test]
fn anonymous_assertions_and_shadowing_are_lexical_not_recursive() {
    accepted("theorem relay (P : Prop) (p : P) : P := have : P := p; this");
    accepted("theorem relay (P : Prop) (p : P) : P := have := p; this");
    accepted(
        "theorem relay (P Q : Prop) (p : P) (q : Q) : Q := have : P := p; have : Q := q; this",
    );
    accepted("theorem relay (P : Prop) (h : P) : P := have h : P := h; h");
    refused("theorem circular (P : Prop) : P := have h : P := h; h");
}
#[test]
fn show_supports_terms_proofs_and_expected_lambda_domains() {
    accepted("def zero : Nat := show Nat from 0");
    accepted("theorem relay (P : Prop) (p : P) : P := show P from p");
    accepted("theorem relay (P : Prop) (p : P) : P := show P by exact p");
    accepted("theorem relay (P : Prop) (p : P) : P := show P from by exact p");
    accepted("theorem identity (P : Prop) : P -> P := show P -> P from fun h => h");
    accepted("theorem identity (P : Prop) : P -> P := show P -> P by intro h; exact h");
}
#[test]
fn assertions_nest_in_applications_values_and_continuations() {
    accepted(
        "theorem relay (P : Prop) (f : P -> P) (p : P) : P := f (have h : P := p; show P from h)",
    );
    accepted(
        "theorem relay (P : Prop) (p : P) : P := have h : P := have q : P := p; q; show P from h",
    );
    accepted("def value : Nat := let n := have h : Nat := 7; h; n");
}
#[test]
fn unused_invalid_assertions_still_cross_kernel_checking() {
    for source in [
        "def bad (P : Prop) : Nat := have h : P := 0; 7",
        "def bad (P : Prop) : Nat := let unused := show P from 0; 7",
        "def bad : Nat := show Prop from 0",
    ] {
        let env = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
        let checked = check_definition_source(source.as_bytes(), &env, budget())
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert!(
            matches!(checked.outcome, Outcome::Complete(Verdict::Rejected { .. })),
            "{source}\n{:?}",
            checked.outcome
        );
    }
}
#[test]
fn have_retains_the_nondependent_let_marker() {
    let Declaration::Defn(d) = accepted("def value : Nat := have n : Nat := 7; n") else {
        panic!("definition")
    };
    assert!(matches!(
        d.value.node(),
        ExprNode::LetE { non_dep: true, .. }
    ));
    let Declaration::Defn(d) = accepted("def value : Nat := let n : Nat := 7; n") else {
        panic!("definition")
    };
    assert!(matches!(
        d.value.node(),
        ExprNode::LetE { non_dep: false, .. }
    ));
}

use fln_elab::seed::source_seed_declarations;
use fln_env::{
    environment::{DeclarationBudget, DeclarationCommitted, Environment},
    pmap::CollisionBudget,
};
use fln_kernel::{
    capability::{Published, admit},
    council::{Council, CouncilOutcome, convene},
};
fn full_env() -> Environment {
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

#[test]
fn have_is_opaque_to_reflexivity_but_let_is_reducible() {
    let env = full_env();
    let source = "theorem reducible : 0 = 0 := let n : Nat := 0; have h : n = 0 := (by rfl); h";
    let good = check_definition_source(source.as_bytes(), &env, budget()).unwrap();
    assert!(
        matches!(good.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{:?}",
        good.outcome
    );
    let source = "theorem opaque : 0 = 0 := have n : Nat := 0; have h : n = 0 := (by rfl); rfl";
    fln_parse::parse_definition(source.as_bytes()).expect("well-formed opacity regression");
    let bad = check_definition_source(source.as_bytes(), &env, budget());
    assert!(bad.is_err(), "opaque local unfolded during elaboration");
}

#[test]
fn explicitly_shown_equations_are_usable_as_rewrite_evidence() {
    let env = full_env();
    for source in [
        "theorem rewrite (a b : Nat) (h : a = b) : b = a := by rw [show a = b from h]",
        "theorem rewrite (a b : Nat) (h : a = b) : b = a := have h' := show a = b from h; by rw [h']",
    ] {
        let checked = check_definition_source(source.as_bytes(), &env, budget())
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert!(
            matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}\n{:?}",
            checked.outcome
        );
    }
}

#[test]
fn opaque_scopes_preserve_arithmetic_and_transactional_alternatives() {
    let env = full_env();
    for source in [
        "theorem arithmetic : 2 + 3 = 5 := have n : Nat := 7; by rfl",
        "theorem rollback (P : Prop) (p : P) : P := by first | exact (have n : Nat := 0; show Nat from 0) | exact p",
        "theorem opaque_branch : 0 = 0 := have n : Nat := 0; by first | exact (show n = 0 from rfl) | rfl",
    ] {
        let checked = check_definition_source(source.as_bytes(), &env, budget())
            .unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert!(
            matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}\n{:?}",
            checked.outcome
        );
    }
}

#[test]
fn suffices_checks_the_subgoal_before_using_it_in_the_continuation() {
    for source in [
        "theorem chain (P Q : Prop) (f : P -> Q) (p : P) : Q := suffices h : P from f h; p",
        "theorem chain (P Q : Prop) (f : P -> Q) (p : P) : Q := suffices P from f this; p",
        "theorem chain (P : Prop) (p : P) : P := suffices h : P from (by exact h); p",
        "theorem chain (P : Prop) (p : P) : P := suffices h : P from h; by exact p",
        "theorem chain (P : Prop) (p : P) : P := suffices h : P -> P from h p; fun x => x",
        "theorem chain (P : Prop) (h : P) : P := suffices h : P from h; h",
        "def chain (f : Nat -> Nat) : Nat := suffices n : Nat from f n; 7",
    ] {
        accepted(source);
    }
}
#[test]
fn suffices_composes_with_nested_assertions_lets_and_show() {
    for source in [
        "theorem chain (P : Prop) (p : P) : P := suffices P from this; suffices P from this; p",
        "theorem chain (P : Prop) (p : P) : P := suffices h : P from have q : P := h; show P from q; p",
        "theorem chain (P : Prop) (p : P) : P := have h : P := suffices P from this; p; h",
        "def chain : Nat := let n := suffices h : Nat from h; 7; n",
    ] {
        accepted(source);
    }
}
#[test]
fn suffices_never_proves_its_own_subgoal_or_discards_bad_evidence() {
    for source in [
        "theorem circular (P : Prop) : P := suffices h : P from h; h",
        "theorem circular (P : Prop) : P := suffices P from this; this",
        "def bad (P : Prop) : Nat := suffices h : P from 7; 0",
        "theorem bad (P : Prop) (p : P) : P := suffices h : P from 0; p",
    ] {
        refused(source);
    }
}
