//! Real parser and elaborator coverage for provisional native term goals.
#![forbid(unsafe_code)]

use fln_core::expr::{Expr, Literal, NatLit};
use fln_core::name::Name;
use fln_elab::source::inspect::{self, ObservationKind, ObservedGoal, SourceObservation};
use fln_elab::source::scope::SourceScope;
use fln_kernel::verdict::Budget;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}

fn inspect_at(source: &str, offset: usize) -> Option<SourceObservation> {
    let environment = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    let position = parsed
        .source_view()
        .from_original(fln_parse::BytePos(offset))
        .unwrap();
    inspect::declaration(
        parsed.syntax(),
        &environment,
        budget(),
        &SourceScope::default(),
        position.0,
        ObservationKind::TermGoal,
    )
    .unwrap()
}

fn goal_at(source: &str, selected: &str) -> ObservedGoal {
    let offset = source.rfind(selected).unwrap();
    let Some(SourceObservation::Goals { range, mut goals }) = inspect_at(source, offset) else {
        panic!("expected a term goal at {selected:?}");
    };
    assert_eq!(range, offset..offset + selected.len());
    assert_eq!(goals.len(), 1);
    goals.pop().unwrap()
}

fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}

#[test]
fn hole_has_the_declared_type_without_a_synthetic_proof() {
    let source = "def pending : Nat := _";
    let goal = goal_at(source, "_");
    assert_eq!(goal.target, nat());
    assert!(goal.locals.decls().is_empty());
    let environment = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    assert!(fln_elab::check_definition_source(source.as_bytes(), &environment, budget()).is_err());
}

#[test]
fn application_argument_uses_the_function_domain() {
    let goal = goal_at("def pending (f : Nat → Nat) : Nat := f _", "_");
    assert_eq!(goal.target, nat());
    assert!(goal.locals.find_by_user_name(&name("f")).is_some());
}

#[test]
fn dependent_argument_retains_its_actual_local_type() {
    let source = "def pending (A : Type) (f : A → A) (x : A) : A := f _";
    let goal = goal_at(source, "_");
    let a = goal.locals.find_by_user_name(&name("A")).unwrap();
    let x = goal.locals.find_by_user_name(&name("x")).unwrap();
    assert_eq!(goal.target, Expr::fvar(a.id.clone()));
    assert_eq!(x.type_, goal.target);
}

#[test]
fn lambda_body_retains_the_opened_binder() {
    let goal = goal_at("def pending : Nat → Nat := fun x => _", "_");
    let x = goal.locals.find_by_user_name(&name("x")).unwrap();
    assert_eq!(x.type_, nat());
    assert_eq!(goal.target, nat());
}

#[test]
fn local_definition_value_is_retained_in_the_goal_context() {
    let goal = goal_at("def pending : Nat := let x : Nat := 7; _", "_");
    let x = goal.locals.find_by_user_name(&name("x")).unwrap();
    assert_eq!(x.type_, nat());
    assert_eq!(x.value, Some(Expr::lit(Literal::Nat(NatLit::from_u64(7)))));
    assert_eq!(goal.target, nat());
}

#[test]
fn inference_only_literal_uses_the_pins_inferred_type_fallback() {
    let goal = goal_at("def inferred := 31", "31");
    assert_eq!(goal.target, nat());
    assert!(goal.locals.decls().is_empty());
}

#[test]
fn inference_only_dependent_local_retains_its_type() {
    let goal = goal_at("def inferred (A : Type) (x : A) := x", "x");
    let a = goal.locals.find_by_user_name(&name("A")).unwrap();
    assert_eq!(goal.target, Expr::fvar(a.id.clone()));
}

#[test]
fn a_completed_term_still_has_one_term_goal() {
    let goal = goal_at("def completed (x : Nat) : Nat := x", "x");
    assert_eq!(goal.target, nat());
    assert_eq!(goal.locals.find_by_user_name(&name("x")).unwrap().type_, nat());
}

#[test]
fn repeated_node_kinds_do_not_capture_an_earlier_source_site() {
    let goal = goal_at("def repeated : Nat := let earlier : Nat := 3; 3", "3");
    assert_eq!(goal.target, nat());
    assert!(goal.locals.find_by_user_name(&name("earlier")).is_some());
}

#[test]
fn by_term_exposes_its_expected_goal_before_a_failing_tactic() {
    let source = "def pending (x : Nat) : Nat := by exact notDefined";
    let goal = goal_at(source, "by exact notDefined");
    assert_eq!(goal.target, nat());
    assert!(goal.locals.find_by_user_name(&name("x")).is_some());
    let environment = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    assert!(fln_elab::check_definition_source(source.as_bytes(), &environment, budget()).is_err());
}

#[test]
fn inspection_stop_cannot_be_swallowed_by_a_backtracking_tactic() {
    let source = "def pending : Nat := by first | exact _ | exact 7";
    assert_eq!(goal_at(source, "_").target, nat());
}

#[test]
fn unavailable_term_info_is_not_fabricated_after_an_elaboration_failure() {
    for source in [
        "def pending : Nat := notDefined",
        "def pending : Nat := let x : Nat := notDefined; _",
    ] {
        let environment = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
        let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
        let offset = source.rfind('_').unwrap_or_else(|| source.find("notDefined").unwrap());
        assert!(
            inspect::declaration(
                parsed.syntax(),
                &environment,
                budget(),
                &SourceScope::default(),
                offset,
                ObservationKind::TermGoal,
            )
            .is_err()
        );
    }
}

#[test]
fn declaration_names_and_positions_outside_terms_have_no_term_goal() {
    let source = "def pending : Nat := 7";
    assert!(inspect_at(source, source.find("pending").unwrap()).is_none());
    assert!(inspect_at(source, source.len()).is_none());
}
