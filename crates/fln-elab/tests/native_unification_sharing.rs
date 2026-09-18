//! Production unification over shared syntax, with deterministic work ceilings.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::mvar::MetavarKind;
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::Budget;
use std::cell::Cell;

fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn name(text: &str) -> Name {
    Name::from_components([text])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}
fn numeral(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}
fn transaction() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        0,
    )
}
fn hole(txn: &mut ElabTxn, ordinal: u64, type_: Expr) -> MVarId {
    let id = MVarId(Name::num(name("shared"), ordinal));
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
fn shared_transaction() -> ElabTxn {
    let mut txn = transaction();
    let mut type_ = nat();
    for _ in 0..64 {
        type_ = Expr::forall_e(Name::anonymous(), nat(), type_, BinderInfo::Default);
    }
    for ordinal in 0..64 {
        hole(&mut txn, ordinal, type_.clone());
    }
    txn
}
fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    assert_eq!(actual.env, before.env);
    assert_eq!(actual.mvars, before.mvars);
    assert_eq!(actual.universes, before.universes);
    assert_eq!(actual.constraints, before.constraints);
    assert_eq!(actual.lctx, before.lctx);
}

#[test]
fn shared_declaration_telescopes_fit_a_linear_work_ceiling() {
    let mut txn = shared_transaction();
    let before = txn.clone();
    let mut limits = budget();
    // Rewalking every shared telescope uses over 8,000 visits before solving
    // even this reflexive equation. The ceiling is a work bound, not a timer.
    limits.max_visited_nodes = 1_000;
    limits.max_steps = 2_000;
    let report = txn.unify(&nat(), &nat(), limits).unwrap();
    assert!(report.visited_nodes < 1_000, "{report:?}");
    assert!(report.unifier_steps < 2_000, "{report:?}");
    assert!(report.expression_assignments.is_empty());
    assert!(report.universe_assignments.is_empty());
    assert_eq!(report.kernel_checks, 0);
    unchanged(&txn, &before);
}

#[test]
fn syntax_fact_reuse_does_not_freeze_a_metavariable_interpretation() {
    for reverse in [false, true] {
        let mut txn = shared_transaction();
        let function_type = Expr::forall_e(name("x"), nat(), nat(), BinderInfo::Default);
        let id = hole(&mut txn, 64, function_type);
        let application = Expr::app(Expr::mvar(id.clone()), numeral(0));
        let value = Expr::lam(name("x"), nat(), numeral(7), BinderInfo::Default);
        let equation = if reverse {
            (numeral(7), application.clone())
        } else {
            (application.clone(), numeral(7))
        };
        let report = txn
            .unify_many_with(
                &[equation, (Expr::mvar(id.clone()), value.clone())],
                budget(),
                &|| false,
            )
            .unwrap();
        assert_eq!(report.expression_assignments, vec![id.clone()]);
        assert_eq!(report.kernel_checks, 1);
        assert_eq!(txn.mvars.get_assigned_expr(&id), Some(&value));
        assert!(application.has_expr_mvar(), "input syntax is immutable");
        assert!(!txn.instantiate_expr(&application).unwrap().has_expr_mvar());
    }
}

#[test]
fn warm_syntax_scans_still_obey_cancellation_and_atomic_publication() {
    let mut base = shared_transaction();
    let id = hole(&mut base, 64, nat());
    let equations = [(Expr::mvar(id), numeral(37))];
    let calls = Cell::new(0);
    base.clone()
        .unify_many_with(&equations, budget(), &|| {
            calls.set(calls.get() + 1);
            false
        })
        .unwrap();
    for cut in [0, calls.get() / 2, calls.get() - 1] {
        let mut txn = base.clone();
        let ticks = Cell::new(0);
        assert!(matches!(
            txn.unify_many_with(&equations, budget(), &|| {
                let current = ticks.get();
                ticks.set(current + 1);
                current == cut
            }),
            Err(UnificationError::Cancelled)
        ));
        unchanged(&txn, &base);
        if cut != 0 {
            assert!(txn.budget.heartbeats_consumed > base.budget.heartbeats_consumed);
        }
        txn.unify_many_with(&equations, budget(), &|| false)
            .unwrap();
    }
}

#[test]
fn a_new_batch_cannot_inherit_a_warm_cache_or_refund_failed_work() {
    let mut txn = shared_transaction();
    let first = txn.unify(&nat(), &nat(), budget()).unwrap();
    let second = txn.unify(&nat(), &nat(), budget()).unwrap();
    assert_eq!(first.unifier_steps, second.unifier_steps);
    assert_eq!(first.visited_nodes, second.visited_nodes);
    let before = txn.clone();
    let mut small = budget();
    small.max_steps = 8;
    assert!(matches!(
        txn.unify(&nat(), &Expr::sort(Level::one()), small),
        Err(UnificationError::StepLimit { limit: 8 })
    ));
    unchanged(&txn, &before);
    assert_eq!(
        txn.budget.heartbeats_consumed - before.budget.heartbeats_consumed,
        8
    );
}
