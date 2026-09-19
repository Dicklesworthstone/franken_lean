//! Structured assignment inference through the real native worklist and K1.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::ConstraintKind;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::mvar::MetavarKind;
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::{Budget, Verdict};
use std::cell::Cell;

fn name(text: &str) -> Name {
    Name::from_components([text])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}
fn numeral(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn bvar(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(name("x"), domain, body, BinderInfo::Default)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(name("x"), domain, body, BinderInfo::Default)
}
fn identity() -> Expr {
    lam(nat(), bvar(0))
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn transaction() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        41,
    )
}
fn goal(txn: &mut ElabTxn, text: &str, type_: Expr) -> MVarId {
    let id = MVarId(name(text));
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        type_,
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    id
}
fn local(txn: &mut ElabTxn, text: &str, type_: Expr) -> Expr {
    let id = FVarId(name(text));
    txn.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn holes(txn: &mut ElabTxn, universe: Level) -> (MVarId, MVarId) {
    let type_ = goal(txn, "inferredType", Expr::sort(universe));
    let value = goal(txn, "inferredValue", Expr::mvar(type_.clone()));
    (type_, value)
}
fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = actual.budget.heartbeats_consumed;
    assert_eq!(actual, &expected);
}
fn assert_kernel_veto(error: UnificationError) {
    assert!(
        matches!(error, UnificationError::AssignmentCheck { outcome, .. }
        if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })))
    );
}

#[test]
fn a_lambda_determines_its_missing_type_in_both_orientations() {
    for reversed in [false, true] {
        let mut txn = transaction();
        let (type_, value) = holes(&mut txn, Level::one());
        let before = txn.clone();
        let (left, right) = (Expr::mvar(value.clone()), identity());
        let (left, right) = if reversed { (right, left) } else { (left, right) };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.kernel_checks, 2);
        assert!(report.residual_metavariables.is_empty());
        txn.unify(&Expr::mvar(type_), &pi(nat(), nat()), budget()).unwrap();
        assert_eq!(txn.mvars.get_assigned_expr(&value), Some(&identity()));
        assert_eq!(txn.env, before.env);
        assert_eq!(txn.lctx, before.lctx);
    }
}

#[test]
fn lambda_binder_styles_survive_in_the_inferred_telescope() {
    for style in [BinderInfo::Default, BinderInfo::Implicit, BinderInfo::StrictImplicit] {
        let mut txn = transaction();
        let (type_, value) = holes(&mut txn, Level::one());
        let candidate = Expr::lam(name("shadowed"), nat(), bvar(0), style);
        txn.unify(&Expr::mvar(value), &candidate, budget()).unwrap();
        let ExprNode::ForallE { binder_info, .. } =
            txn.mvars.get_assigned_expr(&type_).unwrap().node()
        else {
            panic!("the inferred lambda type must be a Pi");
        };
        assert_eq!(*binder_info, style);
    }
}

#[test]
fn dependent_lambdas_rebind_domains_and_results_without_capture() {
    let mut txn = transaction();
    let u = Level::param(name("u"));
    let identity_level = Level::imax(u.clone().succ().unwrap(), u.clone()).unwrap();
    let (type_, value) = holes(&mut txn, identity_level);
    let candidate = lam(Expr::sort(u.clone()), lam(bvar(0), bvar(0)));
    let expected = pi(Expr::sort(u), pi(bvar(0), bvar(1)));
    let report = txn.unify(&Expr::mvar(value), &candidate, budget()).unwrap();
    assert_eq!(report.kernel_checks, 2);
    assert!(report.residual_metavariables.is_empty());
    txn.unify(&Expr::mvar(type_.clone()), &expected, budget()).unwrap();
    let inferred = txn.mvars.get_assigned_expr(&type_).unwrap();
    assert!(!inferred.has_fvar());
    assert!(!inferred.has_loose_bvars());
    assert!(txn.lctx.is_empty());
}

#[test]
fn an_inferred_function_type_also_determines_its_missing_universe() {
    let mut txn = transaction();
    let u = LMVarId(name("typeUniverse"));
    let (_, value) = holes(&mut txn, Level::mvar(u.clone()));
    let report = txn.unify(&Expr::mvar(value), &identity(), budget()).unwrap();
    assert_eq!(report.kernel_checks, 2);
    assert_eq!(report.universe_assignments, vec![u.clone()]);
    assert_eq!(txn.universes.instantiate(&Level::mvar(u)).unwrap(), Level::one());
}

#[test]
fn dependent_pi_types_preserve_symbolic_imax_universes() {
    let mut txn = transaction();
    let u = Level::param(name("u"));
    let v = Level::param(name("v"));
    let a = local(&mut txn, "A", Expr::sort(u.clone()));
    let family = local(&mut txn, "Family", pi(a.clone(), Expr::sort(v.clone())));
    let product_level = Level::imax(u, v).unwrap();
    let (type_, value) = holes(&mut txn, product_level.clone().succ().unwrap());
    let candidate = pi(a, Expr::app(family, bvar(0)));
    txn.unify(&Expr::mvar(value), &candidate, budget()).unwrap();
    txn.unify(&Expr::mvar(type_), &Expr::sort(product_level), budget()).unwrap();
}

#[test]
fn quantified_propositions_stay_in_prop_instead_of_max_universes() {
    let mut txn = transaction();
    let (type_, value) = holes(&mut txn, Level::one());
    // forall (P : Prop), P -> P : Prop, not Type.
    let proposition = pi(Expr::sort(Level::zero()), pi(bvar(0), bvar(1)));
    txn.unify(&Expr::mvar(value), &proposition, budget()).unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&type_), Some(&Expr::sort(Level::zero())));
}

#[test]
fn a_let_bound_type_is_substituted_out_of_a_nested_lambda_telescope() {
    let mut txn = transaction();
    let (type_, value) = holes(&mut txn, Level::one());
    let candidate = lam(
        nat(),
        Expr::let_e(
            name("A"),
            Expr::sort(Level::one()),
            nat(),
            lam(bvar(0), bvar(0)),
            false,
        ),
    );
    let before = txn.lctx.clone();
    txn.unify(&Expr::mvar(value), &candidate, budget()).unwrap();
    txn.unify(&Expr::mvar(type_.clone()), &pi(nat(), pi(nat(), nat())), budget()).unwrap();
    assert!(!txn.mvars.get_assigned_expr(&type_).unwrap().has_fvar());
    assert_eq!(txn.lctx, before);
}

#[test]
fn computed_applications_inside_lambdas_supply_their_dependent_result_type() {
    let mut txn = transaction();
    let (type_, value) = holes(&mut txn, Level::one());
    let polymorphic_identity = lam(Expr::sort(Level::one()), lam(bvar(0), bvar(0)));
    let body = Expr::app(Expr::app(polymorphic_identity, nat()), bvar(0));
    txn.unify(&Expr::mvar(value), &lam(nat(), body), budget()).unwrap();
    txn.unify(&Expr::mvar(type_), &pi(nat(), nat()), budget()).unwrap();
}

#[test]
fn fresh_inference_locals_do_not_capture_existing_user_identities() {
    let mut txn = transaction();
    let id = FVarId(Name::from_components(["_fln_unify_local", "0"]));
    txn.lctx.add_param(id.clone(), name("A"), Expr::sort(Level::one()), BinderInfo::Default);
    let a = Expr::fvar(id);
    let x = local(&mut txn, "known", a.clone());
    let (type_, value) = holes(&mut txn, Level::one());
    let before = txn.lctx.clone();
    txn.unify(&Expr::mvar(value), &lam(nat(), x), budget()).unwrap();
    txn.unify(&Expr::mvar(type_), &pi(nat(), a), budget()).unwrap();
    assert_eq!(txn.lctx, before);
}

#[test]
fn inferring_a_lambda_type_does_not_solve_its_residual_value_hole() {
    let mut txn = transaction();
    let residual = goal(&mut txn, "body", nat());
    let (type_, value) = holes(&mut txn, Level::one());
    let candidate = lam(nat(), Expr::mvar(residual.clone()));
    let report = txn.unify(&Expr::mvar(value), &candidate, budget()).unwrap();
    assert!(report.residual_metavariables.contains(&residual));
    assert!(!txn.mvars.is_assigned(&residual));
    txn.unify(&Expr::mvar(type_), &pi(nat(), nat()), budget()).unwrap();
    txn.unify(&Expr::mvar(residual), &numeral(12), budget()).unwrap();
}

#[test]
fn application_type_hints_cannot_hide_invalid_arguments_from_k1() {
    let mut txn = transaction();
    let op = local(&mut txn, "op", pi(nat(), nat()));
    let (_, value) = holes(&mut txn, Level::one());
    let candidate = lam(nat(), Expr::app(op, Expr::sort(Level::zero())));
    let before = txn.clone();
    assert_kernel_veto(txn.unify(&Expr::mvar(value), &candidate, budget()).unwrap_err());
    unchanged(&txn, &before);
}

#[test]
fn a_let_annotation_mismatch_is_not_erased_by_inferred_type_substitution() {
    let mut txn = transaction();
    let (_, value) = holes(&mut txn, Level::one());
    let candidate = lam(
        nat(),
        Expr::let_e(name("bad"), nat(), Expr::sort(Level::zero()), bvar(0), false),
    );
    let before = txn.clone();
    assert_kernel_veto(txn.unify(&Expr::mvar(value), &candidate, budget()).unwrap_err());
    unchanged(&txn, &before);
}

#[test]
fn an_unavailable_application_hint_does_not_invent_a_function_type() {
    let mut txn = transaction();
    let (_, value) = holes(&mut txn, Level::one());
    let candidate = lam(nat(), Expr::app(numeral(0), numeral(1)));
    let before = txn.clone();
    assert!(txn.unify(&Expr::mvar(value), &candidate, budget()).is_err());
    unchanged(&txn, &before);
}

#[test]
fn inferred_type_holes_respect_opaque_and_depth_policies() {
    for (kind, depth) in [(MetavarKind::SyntheticOpaque, 0), (MetavarKind::Natural, 1)] {
        let mut txn = transaction();
        let type_ = MVarId(name("restricted"));
        txn.mvars.declare(type_.clone(), name("restricted"), Expr::sort(Level::one()),
            txn.lctx.clone(), kind, depth, None);
        let value = goal(&mut txn, "value", Expr::mvar(type_));
        let before = txn.clone();
        assert!(matches!(txn.unify(&Expr::mvar(value), &identity(), budget()),
            Err(UnificationError::Deferred(_))));
        unchanged(&txn, &before);
    }
}

#[test]
fn inferred_types_cannot_capture_locals_outside_the_type_holes_scope() {
    let mut txn = transaction();
    let type_ = goal(&mut txn, "earlyType", Expr::sort(Level::one()));
    let a = local(&mut txn, "laterType", Expr::sort(Level::one()));
    let value = goal(&mut txn, "value", Expr::mvar(type_));
    let candidate = lam(a, bvar(0));
    let before = txn.clone();
    assert!(matches!(txn.unify(&Expr::mvar(value), &candidate, budget()),
        Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn cancellation_at_entry_during_inference_and_at_publication_is_atomic() {
    let mut base = transaction();
    let (_, value) = holes(&mut base, Level::one());
    let equations = [(Expr::mvar(value), identity())];
    let polls = Cell::new(0usize);
    base.clone().unify_many_with(&equations, budget(), &|| {
        polls.set(polls.get() + 1);
        false
    }).unwrap();
    let total = polls.get();
    assert!(total > 2);
    for stop in [0, total / 2, total - 1] {
        let mut txn = base.clone();
        let polls = Cell::new(0usize);
        assert!(matches!(txn.unify_many_with(&equations, budget(), &|| {
            let current = polls.get();
            polls.set(current + 1);
            current >= stop
        }), Err(UnificationError::Cancelled)));
        unchanged(&txn, &base);
    }
}

#[test]
fn assignment_exhaustion_keeps_neither_the_lambda_nor_its_inferred_type() {
    let mut txn = transaction();
    let (_, value) = holes(&mut txn, Level::one());
    let before = txn.clone();
    let mut limited = budget();
    limited.max_assignments = 1;
    assert!(matches!(txn.unify(&Expr::mvar(value.clone()), &identity(), limited),
        Err(UnificationError::AssignmentLimit { limit: 1 })));
    unchanged(&txn, &before);
    txn.unify(&Expr::mvar(value), &identity(), budget()).unwrap();
}

#[test]
fn queue_solving_reports_awakened_typing_obligations_instead_of_solving_them() {
    let mut txn = transaction();
    let (type_, value) = holes(&mut txn, Level::one());
    let typing = txn.postpone(ConstraintKind::HasType {
        expr: Expr::mvar(value.clone()), expected_type: Expr::mvar(type_),
    }, 0);
    let equation = txn.postpone(ConstraintKind::DefEq {
        lhs: Expr::mvar(value), rhs: identity(),
    }, 0);
    let report = txn.solve_defeq_constraints_with(&[equation], budget(), &|| false).unwrap();
    assert_eq!(report.solved, vec![equation]);
    assert_eq!(report.unification.awakened.len(), 1);
    assert_eq!(report.unification.awakened[0].id, typing);
    assert!(matches!(&report.unification.awakened[0].kind, ConstraintKind::HasType { .. }));
}

#[test]
fn deep_structured_candidates_stop_under_explicit_resource_limits() {
    let mut txn = transaction();
    let (_, value) = holes(&mut txn, Level::one());
    let mut candidate = numeral(0);
    for _ in 0..512 {
        candidate = lam(nat(), candidate);
    }
    let before = txn.clone();
    let mut limited = budget();
    limited.max_visited_nodes = 5_000;
    limited.max_steps = 10_000;
    assert!(matches!(txn.unify(&Expr::mvar(value), &candidate, limited),
        Err(UnificationError::NodeLimit { .. } | UnificationError::StepLimit { .. }
            | UnificationError::HeartbeatLimit)));
    unchanged(&txn, &before);
}

#[test]
fn an_inferred_type_cannot_raise_a_declared_prop_universe() {
    let mut txn = transaction();
    let (_, value) = holes(&mut txn, Level::zero());
    let before = txn.clone();
    assert_kernel_veto(txn.unify(&Expr::mvar(value), &identity(), budget()).unwrap_err());
    unchanged(&txn, &before);
}

#[test]
fn dependent_let_results_refer_to_the_original_outer_binder() {
    let mut txn = transaction();
    let family = local(&mut txn, "Family", pi(nat(), Expr::sort(Level::one())));
    let produce = local(&mut txn, "produce", pi(nat(), Expr::app(family.clone(), bvar(0))));
    let (type_, value) = holes(&mut txn, Level::one());
    let candidate = lam(nat(), Expr::let_e(
        name("y"), nat(), bvar(0), Expr::app(produce, bvar(0)), false,
    ));
    let expected = pi(nat(), Expr::app(family, bvar(0)));
    txn.unify(&Expr::mvar(value), &candidate, budget()).unwrap();
    txn.unify(&Expr::mvar(type_), &expected, budget()).unwrap();
}

#[test]
fn an_invalid_lambda_domain_is_not_authenticated_by_a_pi_type_hint() {
    let mut txn = transaction();
    let (_, value) = holes(&mut txn, Level::one());
    let candidate = lam(numeral(0), bvar(0));
    let before = txn.clone();
    assert_kernel_veto(txn.unify(&Expr::mvar(value), &candidate, budget()).unwrap_err());
    unchanged(&txn, &before);
}
