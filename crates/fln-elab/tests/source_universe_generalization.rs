//! Kernel-admitted universe quantification must preserve declaration boundaries.
#![forbid(unsafe_code)]

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::check_definition_source;
use fln_env::constants::DefinitionVal;
use fln_kernel::Declaration;
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
