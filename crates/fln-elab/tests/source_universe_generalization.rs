//! Kernel-admitted universe quantification must preserve declaration boundaries.
#![forbid(unsafe_code)]

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::check_definition_source;
use fln_env::constants::DefinitionVal;
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};

fn checked(source: &str) -> DefinitionVal {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    let result = check_definition_source(source.as_bytes(), &env, budget).unwrap();
    assert!(
        matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}: {:?}",
        result.outcome
    );
    let Declaration::Defn(value) = result.declaration else {
        panic!("expected a definition")
    };
    assert!(!value.base.type_.has_expr_mvar(), "{source}");
    assert!(!value.base.type_.has_level_mvar(), "{source}");
    assert!(!value.value.has_expr_mvar(), "{source}");
    assert!(!value.value.has_level_mvar(), "{source}");
    value
}

#[test]
fn explicit_universe_parameters_survive_identity_admission() {
    let value = checked("def universeId.{u} (A : Sort u) (x : A) : A := x");
    assert_eq!(value.base.level_params, vec![Name::from_components(["u"])]);
}

#[test]
fn inferred_named_universes_remain_rigid_not_defaulted() {
    let value = checked("def inferredUniverseId (A : Sort u) (x : A) : A := x");
    assert_eq!(value.base.level_params, vec![Name::from_components(["u"])]);
}

#[test]
fn monomorphic_definitions_do_not_gain_vacuous_universes() {
    let value = checked("def concreteType : Type := Nat");
    assert!(value.base.level_params.is_empty());
    assert_eq!(value.base.type_, Expr::sort(Level::one()));
}

#[test]
fn unification_cannot_assign_a_rigid_named_universe() {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    let source = "def invalidUniverse.{u} : Sort u := Nat";
    if let Ok(result) = check_definition_source(source.as_bytes(), &env, budget) {
        assert!(
            !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "a rigid universe must not be solved to the universe of Nat"
        );
    }
}

#[test]
fn anonymous_header_universe_is_generalized_after_the_body() {
    let value = checked("def anonymousId (A : Sort _) (x : A) : A := x");
    assert_eq!(value.base.level_params.len(), 1);
}

#[test]
fn body_constraints_solve_header_universes_before_generalization() {
    let value = checked("def concreteHole : Sort _ := Nat");
    assert!(value.base.level_params.is_empty());
    assert_eq!(value.base.type_, Expr::sort(Level::one()));
}

#[test]
fn a_body_only_universe_hole_becomes_a_parameter() {
    let value = checked("def anonymousSort := Sort _");
    assert_eq!(value.base.level_params.len(), 1);
}

#[test]
fn independently_inferred_domains_keep_distinct_universes() {
    let value = checked("def first (A : Sort _) (B : Sort _) (x : A) (y : B) : A := x");
    assert_eq!(value.base.level_params.len(), 2);
    let again = checked("def first (A : Sort _) (B : Sort _) (x : A) (y : B) : A := x");
    assert_eq!(value, again);
}

#[test]
fn type_universes_and_unused_parameter_domains_are_preserved() {
    for source in [
        "def typeId (A : Type _) (x : A) : A := x",
        "def ignored (A : Sort _) : Nat := 7",
    ] {
        assert_eq!(checked(source).base.level_params.len(), 1, "{source}");
    }
}

#[test]
fn generated_names_do_not_capture_explicit_parameters() {
    let value = checked("def collision.{u_1} (A : Sort u_1) (B : Sort _) (x : B) : B := x");
    assert_eq!(
        value.base.level_params,
        vec![
            Name::from_components(["u_1"]),
            Name::from_components(["u_2"])
        ]
    );
}

#[test]
fn theorem_universes_are_generalized_without_replacing_proofs_by_axioms() {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    for source in [
        "theorem keep (A : Sort _) (P : A -> Prop) (x : A) (h : P x) : P x := h",
        "theorem keep (A : Sort _) (P : A -> Prop) (x : A) (h : P x) : P x := by exact h",
    ] {
        let result = check_definition_source(source.as_bytes(), &env, budget).unwrap();
        assert!(
            matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}: {:?}",
            result.outcome
        );
        let Declaration::Thm(value) = result.declaration else {
            panic!("theorem admission must retain its checked proof")
        };
        assert_eq!(value.base.level_params.len(), 1, "{source}");
        assert!(!value.value.has_expr_mvar(), "{source}");
        assert!(!value.value.has_level_mvar(), "{source}");
        assert!(!value.base.type_.has_level_mvar(), "{source}");
    }
}

fn publish(env: &Environment, declaration: Declaration, budget: Budget) -> Environment {
    let Outcome::Complete(admitted) = admit(env, declaration, budget) else {
        panic!("admission nonanswer")
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("declaration not accepted")
    };
    let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) = checked
        .publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        )
    else {
        panic!("declaration not published")
    };
    result.environment
}

#[test]
fn published_generalized_declarations_can_be_reused_at_distinct_universes() {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    let env = publish(
        &env,
        Declaration::Defn(checked("def anonymousId (A : Sort _) (x : A) : A := x")),
        budget,
    );
    for source in [
        "def atNat : Nat := anonymousId Nat 7",
        "def atType : Type := anonymousId (Type) Nat",
        "def identityAlias := anonymousId",
        "def atExplicitLevel : Nat := anonymousId.{1} Nat 7",
    ] {
        let result = check_definition_source(source.as_bytes(), &env, budget)
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert!(
            matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}: {:?}",
            result.outcome
        );
        let Declaration::Defn(value) = result.declaration else {
            panic!("definition")
        };
        assert!(!value.value.has_level_mvar(), "{source}");
        assert!(!value.base.type_.has_level_mvar(), "{source}");
        assert_eq!(
            value.base.level_params.len(),
            usize::from(source.contains("identityAlias")),
            "{source}"
        );
    }
}

#[test]
fn generalization_does_not_admit_term_holes_or_erased_invalid_annotations() {
    let budget = Budget::for_stack_bytes(2 * 1024 * 1024);
    let env = fln_elab::seed::bootstrap_nat_environment(budget).unwrap();
    for source in [
        "def missing (A : Sort _) (x : A) : A := _",
        "def header (A : Sort _) (x : _) : Nat := 7",
        "def invalid (A : Sort _) : Nat := let wrong : Prop := Nat; 7",
        "def invalid (A : Sort _) : Nat := let wrong := (Nat : Prop); 7",
    ] {
        if let Ok(result) = check_definition_source(source.as_bytes(), &env, budget) {
            assert!(
                !matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
                "{source}"
            );
        }
    }
}
