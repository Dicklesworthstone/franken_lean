//! Proof conversion through the native solver, with K1 validating both inputs.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_elab::mvar::MetavarKind;
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::Budget;

fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn prop() -> Expr {
    Expr::sort(Level::zero())
}
fn bv(n: u32) -> Expr {
    Expr::bvar(n).unwrap()
}
fn pi(a: Expr, b: Expr) -> Expr {
    Expr::forall_e(name("x"), a, b, BinderInfo::Default)
}
fn lam(a: Expr, b: Expr) -> Expr {
    Expr::lam(name("x"), a, b, BinderInfo::Default)
}
fn num(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn budget() -> UnificationBudget {
    let mut b = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    b.transparency = UnificationTransparency::None;
    b
}
fn txn() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        47,
    )
}
fn local(tx: &mut ElabTxn, s: &str, ty: Expr) -> Expr {
    let id = FVarId(name(s));
    tx.lctx
        .add_param(id.clone(), name(s), ty, BinderInfo::Default);
    Expr::fvar(id)
}
fn hole(tx: &mut ElabTxn, s: &str, ty: Expr, kind: MetavarKind) -> MVarId {
    let id = MVarId(name(s));
    tx.mvars
        .declare(id.clone(), name(s), ty, tx.lctx.clone(), kind, 0, None);
    id
}
fn proofs() -> (ElabTxn, Expr, Expr, Expr) {
    let mut tx = txn();
    let p = local(&mut tx, "P", prop());
    let h = local(&mut tx, "h", p.clone());
    let k = local(&mut tx, "k", p.clone());
    (tx, p, h, k)
}
fn unchanged(tx: &ElabTxn, before: &ElabTxn) {
    assert_eq!(tx.env, before.env);
    assert_eq!(tx.lctx, before.lctx);
    assert_eq!(tx.mvars, before.mvars);
    assert_eq!(tx.universes, before.universes);
    assert_eq!(tx.constraints, before.constraints);
    assert_eq!(tx.seed, before.seed);
    assert_eq!(tx.options, before.options);
}

#[test]
fn distinct_local_proofs_compare_in_both_directions_without_assignment() {
    let (mut tx, _, h, k) = proofs();
    let before = tx.clone();
    for (a, b) in [(&h, &k), (&k, &h)] {
        let report = tx.unify(a, b, budget()).unwrap();
        assert_eq!(report.kernel_checks, 1);
        assert!(report.expression_assignments.is_empty());
        assert!(report.residual_metavariables.is_empty());
        unchanged(&tx, &before);
    }
}

#[test]
fn different_propositions_and_ordinary_data_are_not_proof_irrelevant() {
    let (mut tx, _, h, _) = proofs();
    let q = local(&mut tx, "Q", prop());
    let k = local(&mut tx, "q_proof", q.clone());
    let a = local(&mut tx, "A", Expr::sort(Level::one()));
    let x = local(&mut tx, "x", a.clone());
    let y = local(&mut tx, "y", a);
    let before = tx.clone();
    for (a, b) in [(h, k), (x, y), (num(1), num(2))] {
        assert!(matches!(
            tx.unify(&a, &b, budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&tx, &before);
    }
}

#[test]
fn propositions_themselves_are_not_equated() {
    let (mut tx, p, _, _) = proofs();
    let q = local(&mut tx, "Q", prop());
    let before = tx.clone();
    assert!(tx.unify(&p, &q, budget()).is_err());
    unchanged(&tx, &before);
}

#[test]
fn proof_arguments_do_not_force_rigid_application_heads_to_match() {
    let (mut tx, p, h, k) = proofs();
    let consume = local(&mut tx, "consume", pi(p, nat()));
    let left = Expr::app(consume.clone(), h);
    let right = Expr::app(consume, k);
    let before = tx.clone();
    tx.unify(&left, &right, budget()).unwrap();
    unchanged(&tx, &before);
}

#[test]
fn applications_of_distinct_proof_producers_are_interchangeable() {
    let (mut tx, p, _, _) = proofs();
    let f = local(&mut tx, "f", pi(nat(), p.clone()));
    let g = local(&mut tx, "g", pi(nat(), p));
    let before = tx.clone();
    tx.unify(&Expr::app(f, num(3)), &Expr::app(g, num(9)), budget())
        .unwrap();
    unchanged(&tx, &before);
}

#[test]
fn impredicative_proof_functions_and_lambda_proofs_compare() {
    let (mut tx, p, h, _) = proofs();
    let f = local(&mut tx, "f", pi(nat(), p.clone()));
    let g = local(&mut tx, "g", pi(nat(), p));
    let before = tx.clone();
    tx.unify(&f, &g, budget()).unwrap();
    tx.unify(&lam(nat(), h), &g, budget()).unwrap();
    unchanged(&tx, &before);
}

#[test]
fn proof_comparison_under_binders_preserves_the_exact_local_context() {
    let mut tx = txn();
    let left = lam(prop(), lam(bv(0), lam(bv(1), bv(1))));
    let right = lam(prop(), lam(bv(0), lam(bv(1), bv(0))));
    let before = tx.clone();
    tx.unify(&left, &right, budget()).unwrap();
    unchanged(&tx, &before);
}

#[test]
fn malformed_proof_applications_cannot_hide_ill_typed_arguments() {
    let (mut tx, p, h, _) = proofs();
    let f = local(&mut tx, "f", pi(nat(), p));
    let before = tx.clone();
    assert!(tx.unify(&Expr::app(f, prop()), &h, budget()).is_err());
    unchanged(&tx, &before);
}

#[test]
fn unresolved_opaque_proof_arguments_remain_obligations() {
    let (mut tx, p, h, _) = proofs();
    let f = local(&mut tx, "f", pi(p.clone(), p.clone()));
    let goal = hole(&mut tx, "proof_goal", p, MetavarKind::SyntheticOpaque);
    let before = tx.clone();
    assert!(
        tx.unify(&Expr::app(f, Expr::mvar(goal.clone())), &h, budget())
            .is_err()
    );
    assert!(!tx.mvars.is_assigned(&goal));
    unchanged(&tx, &before);
}

#[test]
fn later_assignments_reawaken_proof_comparison() {
    let (mut tx, p, h, _) = proofs();
    let f = local(&mut tx, "f", pi(p.clone(), p.clone()));
    let goal = hole(&mut tx, "proof_goal", p, MetavarKind::Natural);
    let report = tx
        .unify_many_with(
            &[
                (Expr::app(f, Expr::mvar(goal.clone())), h.clone()),
                (Expr::mvar(goal.clone()), h.clone()),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(tx.mvars.get_assigned_expr(&goal), Some(&h));
    assert_eq!(report.expression_assignments, vec![goal]);
    assert_eq!(report.kernel_checks, 2);
}

#[test]
fn unknown_prop_type_universes_are_not_defaulted_by_proof_comparison() {
    let mut tx = txn();
    let u = LMVarId(name("unknown_sort"));
    let p = local(&mut tx, "P", Expr::sort(Level::mvar(u.clone())));
    let h = local(&mut tx, "h", p.clone());
    let k = local(&mut tx, "k", p);
    let before = tx.clone();
    assert!(tx.unify(&h, &k, budget()).is_err());
    unchanged(&tx, &before);
    tx.unify_many_with(
        &[(h, k), (Expr::sort(Level::mvar(u)), prop())],
        budget(),
        &|| false,
    )
    .unwrap();
}

#[test]
fn let_contexts_are_closed_without_changing_transparency() {
    let (mut tx, p, h, k) = proofs();
    let alias = FVarId(name("alias"));
    tx.lctx.add_let(alias.clone(), name("alias"), p, h);
    let before = tx.clone();
    let mut b = budget();
    b.zeta_delta = false;
    tx.unify(&Expr::fvar(alias), &k, b).unwrap();
    unchanged(&tx, &before);
}

#[test]
fn a_later_mismatch_rolls_back_proof_driven_batches() {
    let (mut tx, _, h, k) = proofs();
    let goal = hole(&mut tx, "n", nat(), MetavarKind::Natural);
    let before = tx.clone();
    assert!(
        tx.unify_many_with(
            &[(Expr::mvar(goal), num(7)), (h, k), (num(1), num(2)),],
            budget(),
            &|| false
        )
        .is_err()
    );
    unchanged(&tx, &before);
    assert!(tx.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn kernel_resource_stops_are_not_boolean_conversion_results() {
    let (mut tx, _, h, k) = proofs();
    let before = tx.clone();
    let mut b = budget();
    b.kernel = b.kernel.narrowed(0, b.kernel.depth);
    let error = tx.unify(&h, &k, b).unwrap_err();
    assert!(
        matches!(error, UnificationError::ConversionCheck { outcome }
        if matches!(*outcome, Outcome::Inconclusive(_)))
    );
    unchanged(&tx, &before);
}

#[test]
fn cancellation_at_the_publication_barrier_keeps_proof_batches_atomic() {
    use std::cell::Cell;
    let (mut original, _, h, k) = proofs();
    let goal = hole(&mut original, "n", nat(), MetavarKind::Natural);
    let equations = [(Expr::mvar(goal), num(7)), (h, k)];
    let polls = Cell::new(0);
    let mut control = original.clone();
    control
        .unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let last = polls.get();
    let calls = Cell::new(0);
    let mut tx = original.clone();
    let result = tx.unify_many_with(&equations, budget(), &|| {
        calls.set(calls.get() + 1);
        calls.get() == last
    });
    assert!(matches!(result, Err(UnificationError::Cancelled)));
    unchanged(&tx, &original);
    assert!(tx.budget.heartbeats_consumed > original.budget.heartbeats_consumed);
}
