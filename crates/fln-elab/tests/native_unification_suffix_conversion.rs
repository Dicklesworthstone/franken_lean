//! Function-head recovery must establish suffix conversion without solving it.
//! These tests exercise the real transactional unifier and its K1 assignment guard.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::mvar::MetavarKind;
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::Budget;
use std::cell::Cell;

fn name(text: &str) -> Name {
    Name::from_components([text])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}
fn numeral(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(name("x"), domain, body, BinderInfo::Default)
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn transaction() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        17,
    )
}
fn local(txn: &mut ElabTxn, text: &str, type_: Expr) -> Expr {
    let id = FVarId(name(text));
    txn.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn hole(txn: &mut ElabTxn, text: &str, type_: Expr, kind: MetavarKind) -> MVarId {
    let id = MVarId(name(text));
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
fn beta(value: Expr) -> Expr {
    Expr::app(
        Expr::lam(
            name("x"),
            nat(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
        value,
    )
}
fn zeta(value: Expr) -> Expr {
    Expr::let_e(name("x"), nat(), value, Expr::bvar(0).unwrap(), false)
}
fn assert_unchanged(txn: &ElabTxn, before: &ElabTxn) {
    assert_eq!(txn.mvars, before.mvars);
    assert_eq!(txn.universes, before.universes);
    assert_eq!(txn.constraints, before.constraints);
    assert_eq!(txn.lctx, before.lctx);
    assert_eq!(txn.env, before.env);
    assert_eq!(txn.options, before.options);
    assert_eq!(txn.seed, before.seed);
}

#[test]
fn recovers_head_through_nested_beta_zeta_and_metadata_in_either_orientation() {
    for reverse in [false, true] {
        let mut txn = transaction();
        let h = local(&mut txn, "h", pi(nat(), nat()));
        let g = local(&mut txn, "g", pi(nat(), nat()));
        let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
        let left_arg = Expr::app(
            h.clone(),
            Expr::mdata(KVMap::new(), beta(zeta(numeral(7)))),
        );
        let right_arg = Expr::app(h, numeral(7));
        let left = Expr::app(Expr::mvar(f.clone()), left_arg);
        let right = Expr::app(g.clone(), right_arg);
        let before_env = txn.env.clone();
        let report = if reverse {
            txn.unify(&right, &left, budget())
        } else {
            txn.unify(&left, &right, budget())
        }
        .unwrap();
        assert_eq!(report.expression_assignments, vec![f.clone()]);
        assert!(report.kernel_checks > 0);
        assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
        assert_eq!(txn.env, before_env);
    }
}

#[test]
fn recovers_the_complete_partial_head_and_preserves_suffix_order() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let g = local(&mut txn, "g", pi(nat(), pi(nat(), pi(nat(), nat()))));
    let f = hole(&mut txn, "f", pi(nat(), pi(nat(), nat())), MetavarKind::Natural);
    let left = Expr::app(
        Expr::app(
            Expr::mvar(f.clone()),
            Expr::app(h.clone(), beta(numeral(1))),
        ),
        Expr::app(h.clone(), zeta(numeral(2))),
    );
    let prefix = Expr::app(g, numeral(9));
    let right = Expr::app(
        Expr::app(prefix.clone(), Expr::app(h.clone(), numeral(1))),
        Expr::app(h, numeral(2)),
    );
    txn.unify(&left, &right, budget()).unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&prefix));
}

#[test]
fn unequal_nested_arguments_do_not_select_a_head() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let g = local(&mut txn, "g", pi(nat(), nat()));
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    let left = Expr::app(Expr::mvar(f), Expr::app(h.clone(), beta(numeral(7))));
    let right = Expr::app(g, Expr::app(h, numeral(8)));
    let before = txn.clone();
    assert!(txn.unify(&left, &right, budget()).is_err());
    assert_unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn recovery_does_not_assign_an_argument_hole_to_make_a_suffix_equal() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let g = local(&mut txn, "g", pi(nat(), nat()));
    let argument = hole(&mut txn, "argument", nat(), MetavarKind::Natural);
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    let left = Expr::app(Expr::mvar(f), Expr::app(h.clone(), Expr::mvar(argument)));
    let right = Expr::app(g, Expr::app(h, numeral(7)));
    let before = txn.clone();
    assert!(txn.unify(&left, &right, budget()).is_err());
    assert_unchanged(&txn, &before);
}

#[test]
fn a_recovered_head_cannot_escape_the_metavariables_original_scope() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    // Unlike the positive cases, g is deliberately NOT in f's declaration context.
    let g = local(&mut txn, "g", pi(nat(), nat()));
    let left = Expr::app(Expr::mvar(f), Expr::app(h.clone(), beta(numeral(7))));
    let right = Expr::app(g, Expr::app(h, numeral(7)));
    let before = txn.clone();
    assert!(txn.unify(&left, &right, budget()).is_err());
    assert_unchanged(&txn, &before);
}

#[test]
fn a_convertible_suffix_does_not_bypass_assignment_typing() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let wrong = local(&mut txn, "wrong", pi(nat(), Expr::sort(Level::one())));
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    let left = Expr::app(Expr::mvar(f), Expr::app(h.clone(), beta(numeral(7))));
    let right = Expr::app(wrong, Expr::app(h, numeral(7)));
    let before = txn.clone();
    assert!(txn.unify(&left, &right, budget()).is_err());
    assert_unchanged(&txn, &before);
}

#[test]
fn synthetic_opaque_heads_remain_unassigned() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let g = local(&mut txn, "g", pi(nat(), nat()));
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::SyntheticOpaque);
    let left = Expr::app(Expr::mvar(f), Expr::app(h.clone(), beta(numeral(7))));
    let right = Expr::app(g, Expr::app(h, numeral(7)));
    let before = txn.clone();
    assert!(txn.unify(&left, &right, budget()).is_err());
    assert_unchanged(&txn, &before);
}

#[test]
fn cancelled_recovery_retains_the_original_transaction() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let g = local(&mut txn, "g", pi(nat(), nat()));
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    let mut left_arg = beta(numeral(7));
    let mut right_arg = numeral(7);
    for _ in 0..64 {
        left_arg = Expr::app(h.clone(), left_arg);
        right_arg = Expr::app(h.clone(), right_arg);
    }
    let left = Expr::app(Expr::mvar(f), left_arg);
    let right = Expr::app(g, right_arg);
    let before = txn.clone();
    let calls = Cell::new(0_u64);
    let error = txn
        .unify_many_with(&[(left, right)], budget(), &|| {
            calls.set(calls.get() + 1);
            calls.get() >= 100
        })
        .unwrap_err();
    assert_eq!(error, UnificationError::Cancelled);
    assert_unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}
