//! Assignment typing may infer necessary universe equations; validation itself
//! must not guess or capture universes, and residual values stay unassigned.
#![forbid(unsafe_code)]
use fln_core::expr::{Expr, MVarId};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::unify::{UnificationBudget, UnificationDeferred, UnificationError};
use fln_elab::mvar::MetavarKind;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::Budget;
fn n(s: &str) -> Name {
    Name::from_components([s])
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn txn() -> ElabTxn {
    ElabTxn::new(
        fln_elab::seed::bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        17,
    )
}
fn hole(txn: &mut ElabTxn, name: &str, type_: Expr, kind: MetavarKind) -> MVarId {
    let id = MVarId(n(name));
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        type_,
        txn.lctx.clone(),
        kind,
        0,
        None,
    );
    id
}
#[test]
fn an_alias_can_be_checked_universally_before_its_universe_is_known() {
    let mut txn = txn();
    let u = LMVarId(n("u"));
    let sort = Expr::sort(Level::mvar(u.clone()));
    let a = hole(&mut txn, "a", sort.clone(), MetavarKind::Natural);
    let b = hole(&mut txn, "b", sort.clone(), MetavarKind::Natural);
    let report = txn
        .unify(&Expr::mvar(a.clone()), &Expr::mvar(b.clone()), budget())
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(report.residual_metavariables, vec![b.clone()]);
    assert_eq!(
        txn.mvars.get_assigned_expr(&a),
        Some(&Expr::mvar(b.clone()))
    );
    assert!(!txn.mvars.is_assigned(&b));
    assert!(txn.universes.is_empty());
    // The same alias subsequently specializes at a higher universe.
    txn.unify_many_with(
        &[
            (sort, Expr::sort(Level::one().succ().unwrap())),
            (Expr::mvar(b), Expr::sort(Level::one())),
        ],
        budget(),
        &|| false,
    )
    .unwrap();
    assert_eq!(
        txn.instantiate_expr(&Expr::mvar(a)).unwrap(),
        Expr::sort(Level::one())
    );
}
#[test]
fn alias_typing_reports_its_necessary_universe_equation() {
    let mut txn = txn();
    let u = LMVarId(n("u"));
    let v = LMVarId(n("v"));
    let a = hole(
        &mut txn,
        "a",
        Expr::sort(Level::mvar(u.clone())),
        MetavarKind::Natural,
    );
    let b = hole(
        &mut txn,
        "b",
        Expr::sort(Level::mvar(v.clone())),
        MetavarKind::Natural,
    );
    let report = txn
        .unify(&Expr::mvar(a), &Expr::mvar(b.clone()), budget())
        .unwrap();
    assert_eq!(report.universe_assignments, vec![u.clone()]);
    assert_eq!(
        txn.universes.instantiate(&Level::mvar(u)).unwrap(),
        Level::mvar(v)
    );
    assert_eq!(report.residual_metavariables, vec![b.clone()]);
    assert!(!txn.mvars.is_assigned(&b));
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn generalization_cannot_capture_an_existing_universe_parameter() {
    let mut txn = txn();
    let collision = Name::num(n("_fln_residual_universe"), 0);
    // The assigned hole's type is closed, so this exercises validation-only
    // generalization, not assignment-generated inference of a necessary u = p.
    let a = hole(
        &mut txn,
        "a",
        Expr::sort(Level::param(collision)),
        MetavarKind::Natural,
    );
    let b = hole(
        &mut txn,
        "b",
        Expr::sort(Level::mvar(LMVarId(n("u")))),
        MetavarKind::Natural,
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&Expr::mvar(a), &Expr::mvar(b), budget()),
        Err(UnificationError::Deferred(
            UnificationDeferred::UnresolvedAssignmentType(_)
        ))
    ));
    assert_eq!(txn.mvars, before.mvars);
    assert!(txn.universes.is_empty());
}

#[test]
fn universally_checked_aliases_do_not_solve_opaque_residuals() {
    let mut txn = txn();
    let sort = Expr::sort(Level::mvar(LMVarId(n("u"))));
    let a = hole(&mut txn, "a", sort.clone(), MetavarKind::Natural);
    let b = hole(&mut txn, "b", sort, MetavarKind::SyntheticOpaque);
    let report = txn
        .unify(&Expr::mvar(a.clone()), &Expr::mvar(b.clone()), budget())
        .unwrap();
    assert_eq!(report.residual_metavariables, vec![b.clone()]);
    assert_eq!(
        txn.mvars.get_assigned_expr(&a),
        Some(&Expr::mvar(b.clone()))
    );
    assert!(!txn.mvars.is_assigned(&b));
    assert!(txn.universes.is_empty());
}
#[test]
fn generalization_budget_and_cancellation_fail_atomically() {
    for cancel in [false, true] {
        let mut txn = txn();
        let sort = Expr::sort(Level::mvar(LMVarId(n("u"))));
        let a = hole(&mut txn, "a", sort.clone(), MetavarKind::Natural);
        let b = hole(&mut txn, "b", sort, MetavarKind::Natural);
        let before = txn.clone();
        let mut budget = budget();
        if !cancel {
            budget.max_visited_nodes = 2;
        }
        assert!(
            txn.unify_many_with(&[(Expr::mvar(a), Expr::mvar(b))], budget, &|| cancel)
                .is_err()
        );
        assert_eq!(txn.mvars, before.mvars);
        assert_eq!(txn.universes, before.universes);
        assert_eq!(txn.constraints, before.constraints);
    }
}
