//! Delayed type hints re-enter the ordinary transactional equation worklist.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
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
fn lam(body: Expr) -> Expr {
    Expr::lam(name("x"), nat(), body, BinderInfo::Default)
}
fn function_type() -> Expr {
    pi(nat(), nat())
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn transaction() -> ElabTxn {
    ElabTxn::new(bootstrap_nat_environment(budget().kernel).unwrap(), KVMap::new(), 47)
}
fn goal(txn: &mut ElabTxn, text: &str, type_: Expr) -> MVarId {
    let id = MVarId(name(text));
    txn.mvars.declare(id.clone(), name(text), type_, txn.lctx.clone(),
        MetavarKind::Natural, 0, None);
    id
}
fn local(txn: &mut ElabTxn, text: &str, type_: Expr) -> Expr {
    let id = FVarId(name(text));
    txn.lctx.add_param(id.clone(), name(text), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = actual.budget.heartbeats_consumed;
    assert_eq!(actual, &expected);
}

type Equations = Vec<(Expr, Expr)>;

fn delayed_application(invalid: bool) -> (ElabTxn, MVarId, MVarId, Equations) {
    let mut txn = transaction();
    let function_type_hole = goal(&mut txn, "functionType", Expr::sort(Level::one()));
    let op = local(&mut txn, "op", Expr::mvar(function_type_hole.clone()));
    let result_type = goal(&mut txn, "resultType", Expr::sort(Level::one()));
    let value = goal(&mut txn, "value", Expr::mvar(result_type.clone()));
    let argument = if invalid { Expr::sort(Level::zero()) } else { bvar(0) };
    let candidate = lam(Expr::app(op, argument));
    let equations = vec![
        (Expr::mvar(value), candidate),
        (Expr::mvar(function_type_hole.clone()), function_type()),
    ];
    (txn, result_type, function_type_hole, equations)
}

#[test]
fn a_later_function_type_revives_an_earlier_unavailable_assignment_hint() {
    for reverse_order in [false, true] {
        for reverse_sides in [false, true] {
            let (mut txn, result_type, _, mut equations) = delayed_application(false);
            if reverse_order { equations.reverse(); }
            if reverse_sides {
                for (left, right) in &mut equations { std::mem::swap(left, right); }
            }
            let env = txn.env.clone();
            let locals = txn.lctx.clone();
            let report = txn.unify_many_with(&equations, budget(), &|| false).unwrap();
            assert_eq!(report.expression_assignments.len(), 3);
            assert_eq!(report.kernel_checks, 3);
            assert!(report.residual_metavariables.is_empty());
            txn.unify(&Expr::mvar(result_type), &function_type(), budget()).unwrap();
            assert_eq!(txn.env, env);
            assert_eq!(txn.lctx, locals);
        }
    }
}

#[test]
fn newly_inferred_types_unlock_further_hints_across_multiple_generations() {
    for order in [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
        let mut txn = transaction();
        let f = goal(&mut txn, "functionType", Expr::sort(Level::one()));
        let op = local(&mut txn, "op", Expr::mvar(f.clone()));
        let t1 = goal(&mut txn, "typeOne", Expr::sort(Level::one()));
        let v1 = goal(&mut txn, "valueOne", Expr::mvar(t1.clone()));
        let consumer = local(&mut txn, "consumer", Expr::mvar(t1.clone()));
        let t2 = goal(&mut txn, "typeTwo", Expr::sort(Level::one()));
        let v2 = goal(&mut txn, "valueTwo", Expr::mvar(t2.clone()));
        let equations = [
            (Expr::mvar(v2), lam(Expr::app(consumer, bvar(0)))),
            (Expr::mvar(v1), lam(Expr::app(op, bvar(0)))),
            (Expr::mvar(f), function_type()),
        ];
        let selected: Vec<_> = order.into_iter().map(|i| equations[i].clone()).collect();
        let report = txn.unify_many_with(&selected, budget(), &|| false).unwrap();
        assert_eq!(report.kernel_checks, 5);
        assert!(report.residual_metavariables.is_empty());
        txn.unify(&Expr::mvar(t1), &function_type(), budget()).unwrap();
        txn.unify(&Expr::mvar(t2), &function_type(), budget()).unwrap();
    }
}

#[test]
fn a_later_sort_enables_previously_blocked_pi_formation() {
    let mut txn = transaction();
    let s = goal(&mut txn, "sort", Expr::sort(Level::one().succ().unwrap()));
    let a = local(&mut txn, "A", Expr::mvar(s.clone()));
    let t = goal(&mut txn, "type", Expr::sort(Level::one().succ().unwrap()));
    let value = goal(&mut txn, "value", Expr::mvar(t.clone()));
    let equations = [
        (Expr::mvar(value), pi(a.clone(), a)),
        (Expr::mvar(s), Expr::sort(Level::one())),
    ];
    let report = txn.unify_many_with(&equations, budget(), &|| false).unwrap();
    assert_eq!(report.kernel_checks, 3);
    assert_eq!(txn.mvars.get_assigned_expr(&t), Some(&Expr::sort(Level::one())));
}

#[test]
fn an_unavailable_hint_at_a_fixed_generation_defers_instead_of_spinning() {
    let (mut txn, _, _, equations) = delayed_application(false);
    let before = txn.clone();
    let error = txn.unify_many_with(&equations[..1], budget(), &|| false).unwrap_err();
    assert!(matches!(error, UnificationError::Deferred(_)));
    unchanged(&txn, &before);
    txn.unify_many_with(&equations, budget(), &|| false).unwrap();
}

#[test]
fn delayed_hint_recovery_still_submits_original_bad_arguments_to_k1() {
    let (mut txn, _, _, equations) = delayed_application(true);
    let before = txn.clone();
    let error = txn.unify_many_with(&equations, budget(), &|| false).unwrap_err();
    assert!(matches!(error, UnificationError::AssignmentCheck { outcome, .. }
        if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. }))));
    unchanged(&txn, &before);
}

#[test]
fn revisiting_typing_keeps_an_unrelated_postponed_equation_live() {
    let (mut txn, _, _, mut equations) = delayed_application(false);
    let h = goal(&mut txn, "h", function_type());
    equations.insert(0, (Expr::app(Expr::mvar(h.clone()), numeral(0)), numeral(1)));
    equations.push((Expr::mvar(h), lam(bvar(0))));
    let before = txn.clone();
    assert!(matches!(txn.unify_many_with(&equations, budget(), &|| false),
        Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn delayed_inference_exhaustion_restores_selected_and_unselected_queue_rows() {
    let (mut txn, type_, _, equations) = delayed_application(false);
    let extra = txn.postpone(ConstraintKind::HasType {
        expr: numeral(5), expected_type: Expr::mvar(type_),
    }, 0);
    let ids: Vec<_> = equations.into_iter()
        .map(|(lhs, rhs)| txn.postpone(ConstraintKind::DefEq { lhs, rhs }, 0)).collect();
    let before = txn.clone();
    let mut limited = budget();
    limited.max_assignments = 2;
    assert!(txn.solve_defeq_constraints_with(&ids, limited, &|| false).is_err());
    unchanged(&txn, &before);
    let report = txn.solve_defeq_constraints_with(&ids, budget(), &|| false).unwrap();
    assert_eq!(report.solved, ids);
    assert!(report.unification.awakened.iter().any(|row| row.id == extra));
}

#[test]
fn delayed_typing_obeys_cancellation_through_the_final_publication_poll() {
    let (base, _, _, equations) = delayed_application(false);
    let polls = Cell::new(0usize);
    base.clone().unify_many_with(&equations, budget(), &|| {
        polls.set(polls.get() + 1);
        false
    }).unwrap();
    let total = polls.get();
    assert!(total > 2);
    for stop in [0, total / 3, total / 2, total - 1] {
        let mut txn = base.clone();
        let polls = Cell::new(0usize);
        assert!(matches!(txn.unify_many_with(&equations, budget(), &|| {
            let at = polls.get();
            polls.set(at + 1);
            at >= stop
        }), Err(UnificationError::Cancelled)));
        unchanged(&txn, &base);
    }
}

#[test]
fn a_late_type_hint_cannot_assign_an_opaque_expected_type() {
    let mut txn = transaction();
    let f = goal(&mut txn, "functionType", Expr::sort(Level::one()));
    let op = local(&mut txn, "op", Expr::mvar(f.clone()));
    let t = MVarId(name("opaqueType"));
    txn.mvars.declare(t.clone(), name("opaqueType"), Expr::sort(Level::one()),
        txn.lctx.clone(), MetavarKind::SyntheticOpaque, 0, None);
    let value = goal(&mut txn, "value", Expr::mvar(t));
    let equations = [
        (Expr::mvar(value), lam(Expr::app(op, bvar(0)))),
        (Expr::mvar(f), function_type()),
    ];
    let before = txn.clone();
    assert!(matches!(txn.unify_many_with(&equations, budget(), &|| false),
        Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn repeated_runs_reconstruct_identical_assignments_without_publishing_declarations() {
    let (base, _, _, equations) = delayed_application(false);
    let mut first = base.clone();
    let first_report = first.unify_many_with(&equations, budget(), &|| false).unwrap();
    for _ in 0..3 {
        let mut next = base.clone();
        let report = next.unify_many_with(&equations, budget(), &|| false).unwrap();
        assert_eq!(next.mvars, first.mvars);
        assert_eq!(next.universes, first.universes);
        assert_eq!(next.constraints, first.constraints);
        assert_eq!(report.expression_assignments, first_report.expression_assignments);
        assert_eq!(next.env, base.env);
    }
}
