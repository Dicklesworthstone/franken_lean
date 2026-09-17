//! Function eta conversion must participate in native constraint solving, not
//! merely in final declaration checking. All assignments still pass K1.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, MVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
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
fn bvar(n: u32) -> Expr {
    Expr::bvar(n).unwrap()
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(name("x"), domain, body, BinderInfo::Default)
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(name("x"), domain, body, BinderInfo::Default)
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn txn() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        31,
    )
}
fn local(txn: &mut ElabTxn, s: &str, ty: Expr) -> Expr {
    let id = FVarId(name(s));
    txn.lctx
        .add_param(id.clone(), id.0.clone(), ty, BinderInfo::Default);
    Expr::fvar(id)
}
fn hole(txn: &mut ElabTxn, s: &str, ty: Expr) -> MVarId {
    let id = MVarId(name(s));
    txn.mvars.declare(
        id.clone(),
        name(s),
        ty,
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    id
}
fn unchanged(txn: &ElabTxn, before: &ElabTxn) {
    assert_eq!(txn.env, before.env);
    assert_eq!(txn.lctx, before.lctx);
    assert_eq!(txn.mvars, before.mvars);
    assert_eq!(txn.universes, before.universes);
    assert_eq!(txn.constraints, before.constraints);
    assert_eq!(txn.seed, before.seed);
    assert_eq!(txn.options, before.options);
}

#[test]
fn eta_works_in_both_directions_without_publishing_fresh_locals() {
    let mut tx = txn();
    let f = local(&mut tx, "f", pi(nat(), nat()));
    let expanded = lam(nat(), Expr::app(f.clone(), bvar(0)));
    let before = tx.clone();
    for (left, right) in [(&f, &expanded), (&expanded, &f)] {
        let report = tx.unify(left, right, budget()).unwrap();
        assert!(report.expression_assignments.is_empty());
        assert!(report.universe_assignments.is_empty());
        unchanged(&tx, &before);
    }
}

#[test]
fn eta_opens_dependent_domains_in_the_current_binder_scope() {
    let mut tx = txn();
    let f = local(
        &mut tx,
        "f",
        pi(Expr::sort(Level::one()), pi(bvar(0), bvar(1))),
    );
    let expanded = lam(
        Expr::sort(Level::one()),
        lam(bvar(0), Expr::app(Expr::app(f.clone(), bvar(1)), bvar(0))),
    );
    let before = tx.clone();
    tx.unify(&expanded, &f, budget()).unwrap();
    tx.unify(&f, &expanded, budget()).unwrap();
    unchanged(&tx, &before);
}

#[test]
fn eta_synthesizes_a_checked_pattern_assignment() {
    let mut tx = txn();
    let f = local(&mut tx, "f", pi(nat(), nat()));
    let m = hole(&mut tx, "function", pi(nat(), nat()));
    let expanded = lam(nat(), Expr::app(Expr::mvar(m.clone()), bvar(0)));
    let before = tx.clone();
    let report = tx.unify(&expanded, &f, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![m.clone()]);
    assert_eq!(report.kernel_checks, 1);
    let assignment = tx.mvars.get_assigned_expr(&m).unwrap().clone();
    assert!(!assignment.has_loose_bvars());
    tx.unify(&assignment, &f, budget()).unwrap();
    assert_eq!(tx.env, before.env);
    assert_eq!(tx.lctx, before.lctx);
}

#[test]
fn eta_does_not_capture_an_existing_generated_name() {
    let mut tx = txn();
    let id = FVarId(Name::from_components(["_fln_unify_local", "0"]));
    tx.lctx
        .add_param(id.clone(), name("outer"), nat(), BinderInfo::Default);
    let outer = Expr::fvar(id);
    let f = local(&mut tx, "f", pi(nat(), pi(nat(), nat())));
    let partial = Expr::app(f, outer);
    let expanded = lam(nat(), Expr::app(partial.clone(), bvar(0)));
    let before = tx.clone();
    tx.unify(&expanded, &partial, budget()).unwrap();
    unchanged(&tx, &before);
}

#[test]
fn eta_mismatches_are_deferred_and_batch_assignments_roll_back() {
    let mut tx = txn();
    let f = local(&mut tx, "f", pi(nat(), nat()));
    let g = local(&mut tx, "g", pi(nat(), nat()));
    let m = hole(&mut tx, "function", pi(nat(), nat()));
    let expanded = lam(nat(), Expr::app(f.clone(), bvar(0)));
    let before = tx.clone();
    let result = tx.unify_many_with(&[(Expr::mvar(m), f), (expanded, g)], budget(), &|| false);
    assert!(
        matches!(result, Err(UnificationError::Deferred(_))),
        "{result:?}"
    );
    unchanged(&tx, &before);
}

#[test]
fn eta_cannot_assign_a_body_hole_to_an_escaping_binder() {
    let mut tx = txn();
    let m = hole(&mut tx, "outside", nat());
    let expanded = lam(nat(), Expr::mvar(m));
    let identity = lam(nat(), bvar(0));
    let before = tx.clone();
    assert!(tx.unify(&expanded, &identity, budget()).is_err());
    unchanged(&tx, &before);
}

#[test]
fn eta_respects_cancellation_and_shared_step_limits() {
    let mut tx = txn();
    let f = local(&mut tx, "f", pi(nat(), nat()));
    let expanded = lam(nat(), Expr::app(f.clone(), bvar(0)));
    let before = tx.clone();
    let calls = std::cell::Cell::new(0);
    let result = tx.unify_many_with(&[(expanded.clone(), f.clone())], budget(), &|| {
        let n = calls.get() + 1;
        calls.set(n);
        n > 20
    });
    assert!(
        matches!(result, Err(UnificationError::Cancelled)),
        "{result:?}"
    );
    unchanged(&tx, &before);
    let mut limited = budget();
    limited.max_steps = 20;
    assert!(matches!(
        tx.unify(&expanded, &f, limited),
        Err(UnificationError::StepLimit { .. })
    ));
    unchanged(&tx, &before);
}

#[test]
fn eta_does_not_erase_lambda_domain_mismatches() {
    let mut tx = txn();
    let before = tx.clone();
    let natural_identity = lam(nat(), bvar(0));
    let type_identity = lam(Expr::sort(Level::one()), bvar(0));
    assert!(
        tx.unify(&natural_identity, &type_identity, budget())
            .is_err()
    );
    unchanged(&tx, &before);
}

#[test]
fn eta_assignments_keep_the_kernel_type_veto() {
    let mut tx = txn();
    let f = local(&mut tx, "f", pi(nat(), nat()));
    let m = hole(&mut tx, "wrong_result", pi(nat(), Expr::sort(Level::one())));
    let expanded = lam(nat(), Expr::app(Expr::mvar(m), bvar(0)));
    let before = tx.clone();
    let result = tx.unify(&expanded, &f, budget());
    assert!(
        matches!(result, Err(UnificationError::AssignmentCheck { .. })),
        "{result:?}"
    );
    unchanged(&tx, &before);
}
