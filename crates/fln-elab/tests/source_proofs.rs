//! Real source proof scripts construct terms checked by the ordinary kernel.
#![forbid(unsafe_code)]
use fln_core::expr::ExprNode;
use fln_core::outcome::Outcome;
use fln_elab::{DefinitionFrontendError, check_definition_source};
use fln_env::environment::Environment;
use fln_kernel::{
    Declaration,
    verdict::{Budget, RejectClass, Verdict},
};

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn env() -> Environment {
    fln_elab::seed::bootstrap_nat_environment(budget()).unwrap()
}
fn accepted(source: &str) -> Declaration {
    let result = check_definition_source(source.as_bytes(), &env(), budget())
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"));
    assert!(
        matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}\n{:?}",
        result.outcome
    );
    match &result.declaration {
        Declaration::Thm(value) => {
            assert!(!value.value.has_fvar());
            assert!(!value.value.has_expr_mvar());
            assert!(!value.value.has_level_mvar());
            assert!(!value.value.has_loose_bvars());
        }
        Declaration::Defn(value) => {
            assert!(!value.value.has_fvar());
            assert!(!value.value.has_expr_mvar());
        }
        _ => panic!("source declaration kind"),
    }
    result.declaration
}
#[test]
fn theorem_intro_exact_builds_a_real_proof_not_an_axiom() {
    let declaration = accepted("theorem identity (P : Prop) : P -> P := by intro h; exact h");
    let Declaration::Thm(proof) = declaration else {
        panic!("theorem expected");
    };
    let ExprNode::Lam { body, .. } = proof.value.node() else {
        panic!("P binder");
    };
    let ExprNode::Lam { body, .. } = body.node() else {
        panic!("h binder");
    };
    assert!(matches!(body.node(), ExprNode::BVar { idx: 0 }));
}
#[test]
fn direct_proof_terms_use_theorem_admission_too() {
    accepted("theorem identity (P : Prop) (h : P) : P := h");
    accepted("theorem identity (P : Prop) : P -> P := fun h => h");
}
#[test]
fn intro_and_assumption_handle_shadowing_and_anonymous_binders() {
    accepted("theorem first (P Q : Prop) : P -> Q -> P := by intro h q; assumption");
    accepted("theorem first (P Q : Prop) : P -> Q -> P := by intro _ _; assumption");
    accepted("theorem first (P Q : Prop) : P -> Q -> P := by intro; intro; assumption");
    accepted("theorem first (P Q : Prop) : P -> Q -> P := by intro h h; assumption");
}
#[test]
fn apply_creates_subgoals_closed_by_following_tactics() {
    accepted("theorem mp (P Q : Prop) (f : P -> Q) (h : P) : Q := by apply f; exact h");
    accepted(
        "theorem two (P Q R : Prop) (f : P -> Q -> R) (p : P) (q : Q) : R := by apply f; assumption; assumption",
    );
}
#[test]
fn nested_apply_preserves_introduced_local_scopes() {
    accepted(
        "theorem compose (P Q R : Prop) (f : P -> Q) (g : Q -> R) : P -> R := by intro p; apply g; apply f; exact p",
    );
    accepted(
        "theorem higher (P Q R : Prop) (f : (P -> Q) -> R) (q : Q) : R := by apply f; intro p; exact q",
    );
}
#[test]
fn dependent_apply_infers_parameters_from_the_goal() {
    accepted("theorem relay {P : Prop} (h : P) : P := by exact h");
}
#[test]
fn by_terms_can_be_higher_order_arguments() {
    accepted("theorem higher (P Q : Prop) (f : (P -> P) -> Q) : Q := f (by intro h; exact h)");
}
#[test]
fn multiline_scripts_preserve_comments_crlf_and_source_bytes() {
    let source = b"theorem id (P : Prop) : P -> P := by\r\n  -- keep the hypothesis\r\n  intro h\r\n  exact h\r\n";
    let parsed = fln_parse::parse_definition(source).unwrap();
    assert_eq!(parsed.reconstruct_original(), source);
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source
            .iter()
            .copied()
            .filter(|b| *b != b'\r')
            .collect::<Vec<_>>()
    );
    accepted(std::str::from_utf8(source).unwrap());
}
#[test]
fn incomplete_or_extra_tactics_do_not_create_success() {
    for source in [
        "theorem missing (P : Prop) : P := by intro h",
        "theorem missing (P : Prop) : P -> P := by intro h",
        "theorem missing (P Q : Prop) (f : P -> Q) : Q := by apply f",
        "theorem missing (P : Prop) : P := by assumption",
        "theorem extra (P : Prop) (h : P) : P := by exact h; assumption",
        "theorem extra (P : Prop) (h : P) : P := by exact _",
    ] {
        assert!(
            check_definition_source(source.as_bytes(), &env(), budget()).is_err(),
            "{source}"
        );
    }
}
#[test]
fn incorrect_proofs_and_nonprop_theorems_are_rejected_by_k1() {
    for (source, class) in [
        (
            "theorem bad (P : Prop) : P := by exact 0",
            RejectClass::DefinitionTypeMismatch,
        ),
        (
            "theorem bad : Nat := by exact 0",
            RejectClass::TheoremNotProp,
        ),
    ] {
        let result = check_definition_source(source.as_bytes(), &env(), budget()).unwrap();
        assert!(
            matches!(result.outcome, Outcome::Complete(Verdict::Rejected { class: actual, .. }) if actual == class),
            "{:?}",
            result.outcome
        );
    }
}
#[test]
fn unsupported_tactics_and_nested_by_are_not_reinterpreted() {
    for source in [
        "theorem bad (P : Prop) : P := by sorry",
        "theorem bad (P : Prop) : P := by exact (by assumption)",
    ] {
        assert!(matches!(
            check_definition_source(source.as_bytes(), &env(), budget()),
            Err(DefinitionFrontendError::Parse(_))
        ));
    }
    assert!(fln_parse::parse_nat_definition(b"theorem bad : Nat := 0").is_err());
}
#[test]
fn definitions_can_use_the_same_proof_state_machine() {
    accepted("def identity : Nat -> Nat := by intro n; exact n");
}
