//! Queued work retains its lexical meaning after the caller leaves that scope.
#![forbid(unsafe_code)]
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::constraint::{ConstraintId, ConstraintKind, ConstraintSolveError};
use fln_elab::mvar::MetavarKind;
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::Budget;
use std::cell::Cell;
fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn lit(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn txn() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        131,
    )
}
fn local(tx: &mut ElabTxn, s: &str, ty: Expr) -> Expr {
    let id = FVarId(name(s));
    tx.lctx
        .add_param(id.clone(), id.0.clone(), ty, BinderInfo::Default);
    Expr::fvar(id)
}
fn let_local(tx: &mut ElabTxn, s: &str, value: Expr) -> Expr {
    let id = FVarId(name(s));
    tx.lctx.add_let(id.clone(), id.0.clone(), nat(), value);
    Expr::fvar(id)
}
fn hole(tx: &mut ElabTxn, s: &str, ty: Expr) -> MVarId {
    let id = MVarId(name(s));
    tx.mvars.declare(
        id.clone(),
        id.0.clone(),
        ty,
        tx.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    id
}
fn typed(tx: &mut ElabTxn, expr: Expr, expected_type: Expr) -> ConstraintId {
    tx.postpone(
        ConstraintKind::HasType {
            expr,
            expected_type,
        },
        0,
    )
}
fn equal(tx: &mut ElabTxn, lhs: Expr, rhs: Expr) -> ConstraintId {
    tx.postpone(ConstraintKind::DefEq { lhs, rhs }, 0)
}
fn unchanged(tx: &ElabTxn, before: &ElabTxn) {
    let mut before = before.clone();
    before.budget.heartbeats_consumed = tx.budget.heartbeats_consumed;
    assert_eq!(tx, &before);
}
#[test]
fn typing_survives_leaving_the_original_local_context() {
    let mut tx = txn();
    let x = local(&mut tx, "x", nat());
    let id = typed(&mut tx, x, nat());
    tx.lctx.truncate(0);
    let report = tx
        .solve_constraints_with(&[id], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![id]);
    assert_eq!(report.unification.kernel_checks, 1);
    assert!(tx.lctx.is_empty());
}
#[test]
fn sibling_contexts_with_reused_local_ids_are_not_conflated() {
    for reverse in [false, true] {
        let mut tx = txn();
        let x = local(&mut tx, "x", nat());
        let first = typed(&mut tx, x, nat());
        tx.lctx.truncate(0);
        let x = local(&mut tx, "x", Expr::sort(Level::one()));
        let second = typed(&mut tx, x, Expr::sort(Level::one()));
        tx.lctx.truncate(0);
        let mut selected = vec![first, second, first];
        if reverse {
            selected.reverse();
        }
        let report = tx
            .solve_constraints_with(&selected, budget(), &|| false)
            .unwrap();
        assert_eq!(report.solved, vec![first, second]);
        assert_eq!(report.unification.kernel_checks, 2);
        assert!(tx.lctx.is_empty());
    }
}
#[test]
fn defeq_uses_each_retained_let_value_not_the_latest_ambient_value() {
    let mut tx = txn();
    let x = let_local(&mut tx, "x", lit(7));
    let first = equal(&mut tx, x, lit(7));
    tx.lctx.truncate(0);
    let x = let_local(&mut tx, "x", lit(8));
    let second = equal(&mut tx, x, lit(8));
    tx.lctx.truncate(0);
    let_local(&mut tx, "x", lit(99));
    let ambient = tx.lctx.clone();
    tx.solve_defeq_constraints_with(&[second, first], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.lctx, ambient);
}
#[test]
fn delayed_telescope_is_retained_after_its_parameters_leave_scope() {
    let mut tx = txn();
    let fun_ty = Expr::forall_e(name("n"), nat(), nat(), BinderInfo::Default);
    let f = hole(&mut tx, "f", fun_ty);
    let x = local(&mut tx, "x", nat());
    let id = tx.postpone(
        ConstraintKind::DelayedAssign {
            mvar: f.clone(),
            fvars: vec![FVarId(name("x"))],
            val: x,
        },
        0,
    );
    tx.lctx.truncate(0);
    tx.solve_constraints_with(&[id], budget(), &|| false)
        .unwrap();
    let identity = Expr::lam(
        name("n"),
        nat(),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    tx.unify(&Expr::mvar(f), &identity, budget()).unwrap();
    assert!(tx.lctx.is_empty());
}
#[test]
fn mixed_rows_infer_a_shared_type_without_rebinding_sibling_locals() {
    let mut tx = txn();
    let ty = hole(&mut tx, "type", Expr::sort(Level::one()));
    let x = local(&mut tx, "x", Expr::mvar(ty.clone()));
    let first = typed(&mut tx, x, nat());
    tx.lctx.truncate(0);
    let x = let_local(&mut tx, "x", lit(3));
    let second = equal(&mut tx, x, lit(3));
    tx.lctx.truncate(0);
    tx.solve_constraints_with(&[second, first], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.mvars.get_assigned_expr(&ty), Some(&nat()));
    assert!(tx.lctx.is_empty());
}
#[test]
fn dependent_local_types_and_let_values_survive_the_scope_exit() {
    let mut tx = txn();
    let a = local(&mut tx, "A", Expr::sort(Level::one()));
    let x = local(&mut tx, "x", a.clone());
    let z = FVarId(name("z"));
    tx.lctx.add_let(z.clone(), z.0.clone(), a.clone(), x);
    let id = typed(&mut tx, Expr::fvar(z), a);
    tx.lctx.truncate(0);
    let before = tx.env.clone();
    tx.solve_constraints_with(&[id], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.env, before);
    assert!(tx.lctx.is_empty());
}
#[test]
fn a_new_ambient_context_cannot_rescue_an_invalid_original_typing() {
    let mut tx = txn();
    let x = local(&mut tx, "x", nat());
    let id = typed(&mut tx, x, Expr::sort(Level::one()));
    tx.lctx.truncate(0);
    local(&mut tx, "x", Expr::sort(Level::one()));
    let before = tx.clone();
    assert!(
        tx.solve_constraints_with(&[id], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
}
#[test]
fn invalid_original_delayed_argument_is_not_retyped_by_the_caller() {
    let mut tx = txn();
    let f = hole(
        &mut tx,
        "f",
        Expr::forall_e(name("n"), nat(), nat(), BinderInfo::Default),
    );
    local(&mut tx, "x", Expr::sort(Level::one()));
    let id = tx.postpone(
        ConstraintKind::DelayedAssign {
            mvar: f,
            fvars: vec![FVarId(name("x"))],
            val: lit(1),
        },
        0,
    );
    tx.lctx.truncate(0);
    local(&mut tx, "x", nat());
    let before = tx.clone();
    assert!(
        tx.solve_constraints_with(&[id], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
}
#[test]
fn scoped_cancellation_and_node_limits_keep_every_original_row() {
    let mut initial = txn();
    let x = local(&mut initial, "x", nat());
    let id = typed(&mut initial, x, nat());
    initial.lctx.truncate(0);
    let calls = Cell::new(0usize);
    let report = initial
        .clone()
        .solve_constraints_with(&[id], budget(), &|| {
            calls.set(calls.get() + 1);
            false
        })
        .unwrap();
    let total = calls.get();
    for stop in [0, total / 2, total - 1] {
        let mut tx = initial.clone();
        let calls = Cell::new(0);
        assert!(matches!(
            tx.solve_constraints_with(&[id], budget(), &|| {
                let n = calls.get();
                calls.set(n + 1);
                n >= stop
            }),
            Err(ConstraintSolveError::Unification(
                UnificationError::Cancelled
            ))
        ));
        unchanged(&tx, &initial);
    }
    let mut tx = initial.clone();
    let mut limited = budget();
    limited.max_visited_nodes = report.unification.visited_nodes - 1;
    assert!(matches!(
        tx.solve_constraints_with(&[id], limited, &|| false),
        Err(ConstraintSolveError::Unification(
            UnificationError::NodeLimit { .. }
        ))
    ));
    unchanged(&tx, &initial);
    tx.solve_constraints_with(&[id], budget(), &|| false)
        .unwrap();
}
#[test]
fn legacy_unscoped_queue_rows_keep_the_explicit_caller_context_contract() {
    let mut tx = txn();
    let x = local(&mut tx, "x", nat());
    let kind = ConstraintKind::HasType {
        expr: x,
        expected_type: nat(),
    };
    let id = tx.constraints.enqueue_inferred(kind, &tx.mvars, 0);
    let locals = tx.lctx.clone();
    tx.lctx.truncate(0);
    assert!(
        tx.solve_constraints_with(&[id], budget(), &|| false)
            .is_err()
    );
    tx.lctx = locals;
    tx.solve_constraints_with(&[id], budget(), &|| false)
        .unwrap();
}

#[test]
fn assigning_a_hidden_value_type_wakes_its_typing_obligation() {
    let mut tx = txn();
    let ty = hole(&mut tx, "type", Expr::sort(Level::one()));
    let value = hole(&mut tx, "value", Expr::mvar(ty.clone()));
    let id = typed(&mut tx, Expr::mvar(value.clone()), nat());
    let readers = &tx.constraints.constraints()[&id].reads_mvars;
    assert!(readers.contains(&ty));
    assert!(readers.contains(&value));
    let report = tx.unify(&Expr::mvar(ty), &nat(), budget()).unwrap();
    assert_eq!(report.awakened.len(), 1);
    assert_eq!(report.awakened[0].id, id);
    assert!(!tx.mvars.is_assigned(&value));
}
