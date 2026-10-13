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
        let left_arg = Expr::app(h.clone(), Expr::mdata(KVMap::new(), beta(zeta(numeral(7)))));
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
    let f = hole(
        &mut txn,
        "f",
        pi(nat(), pi(nat(), nat())),
        MetavarKind::Natural,
    );
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
    let f = hole(
        &mut txn,
        "f",
        pi(nat(), nat()),
        MetavarKind::SyntheticOpaque,
    );
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

#[test]
fn recovers_a_head_when_lambda_arguments_reduce_below_the_binder() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let function_type = pi(nat(), nat());
    let g = local(&mut txn, "g", pi(function_type.clone(), nat()));
    let f = hole(
        &mut txn,
        "f",
        pi(function_type, nat()),
        MetavarKind::Natural,
    );
    let left_arg = Expr::lam(
        name("x"),
        nat(),
        Expr::app(h.clone(), beta(Expr::bvar(0).unwrap())),
        BinderInfo::Default,
    );
    let right_arg = Expr::lam(
        name("renamed"),
        nat(),
        Expr::app(h, Expr::bvar(0).unwrap()),
        BinderInfo::Default,
    );
    let report = txn
        .unify(
            &Expr::app(Expr::mvar(f.clone()), left_arg),
            &Expr::app(g.clone(), right_arg),
            budget(),
        )
        .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
    assert_eq!(report.expression_assignments, vec![f]);
    assert!(report.kernel_checks > 0);
}

#[test]
fn dependent_nested_binders_share_fresh_locals_without_capture() {
    let mut txn = transaction();
    let family = local(&mut txn, "family", pi(nat(), Expr::sort(Level::one())));
    // (n : Nat) -> family n -> family n
    let dependent = pi(
        nat(),
        pi(
            Expr::app(family.clone(), Expr::bvar(0).unwrap()),
            Expr::app(family.clone(), Expr::bvar(1).unwrap()),
        ),
    );
    let g = local(&mut txn, "g", pi(dependent.clone(), nat()));
    let f = hole(&mut txn, "f", pi(dependent, nat()), MetavarKind::Natural);
    let left_inner = Expr::let_e(
        name("copy"),
        Expr::app(family.clone(), Expr::bvar(1).unwrap()),
        Expr::bvar(0).unwrap(),
        Expr::bvar(0).unwrap(),
        false,
    );
    let argument = |body| {
        Expr::lam(
            name("n"),
            nat(),
            Expr::lam(
                name("x"),
                Expr::app(family.clone(), Expr::bvar(0).unwrap()),
                body,
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        )
    };
    txn.unify(
        &Expr::app(Expr::mvar(f.clone()), argument(left_inner)),
        &Expr::app(g.clone(), argument(Expr::bvar(0).unwrap())),
        budget(),
    )
    .unwrap();
    let assignment = txn.mvars.get_assigned_expr(&f).unwrap();
    assert_eq!(assignment, &g);
    assert!(!assignment.has_loose_bvars());
}

#[test]
fn dependent_pi_arguments_are_compared_under_their_binder() {
    let mut txn = transaction();
    let family = local(&mut txn, "family", pi(nat(), Expr::sort(Level::one())));
    let g = local(&mut txn, "g", pi(Expr::sort(Level::one()), nat()));
    let f = hole(
        &mut txn,
        "f",
        pi(Expr::sort(Level::one()), nat()),
        MetavarKind::Natural,
    );
    let left_arg = pi(
        nat(),
        Expr::app(family.clone(), beta(Expr::bvar(0).unwrap())),
    );
    let right_arg = pi(nat(), Expr::app(family, Expr::bvar(0).unwrap()));
    txn.unify(
        &Expr::app(Expr::mvar(f.clone()), left_arg),
        &Expr::app(g.clone(), right_arg),
        budget(),
    )
    .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
}

#[test]
fn suffix_universe_identities_do_not_create_universe_assignments() {
    let mut txn = transaction();
    let u = Level::param(name("u"));
    let argument_type = Expr::sort(u.clone().succ().unwrap());
    let g = local(&mut txn, "g", pi(argument_type.clone(), nat()));
    let f = hole(
        &mut txn,
        "f",
        pi(argument_type, nat()),
        MetavarKind::Natural,
    );
    let left_arg = Expr::sort(Level::max(u.clone(), Level::zero()).unwrap());
    let right_arg = Expr::sort(u);
    assert_ne!(
        left_arg, right_arg,
        "the fixture must require level normalization"
    );
    let before_universes = txn.universes.clone();
    let report = txn
        .unify(
            &Expr::app(Expr::mvar(f.clone()), left_arg),
            &Expr::app(g.clone(), right_arg),
            budget(),
        )
        .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
    assert!(report.universe_assignments.is_empty());
    assert_eq!(txn.universes, before_universes);
}

#[test]
fn nested_suffix_reduction_respects_the_local_let_policy() {
    for unfold in [false, true] {
        let mut txn = transaction();
        let value = FVarId(name("value"));
        txn.lctx
            .add_let(value.clone(), value.0.clone(), nat(), numeral(7));
        let h = local(&mut txn, "h", pi(nat(), nat()));
        let g = local(&mut txn, "g", pi(nat(), nat()));
        let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
        let left = Expr::app(
            Expr::mvar(f.clone()),
            Expr::app(h.clone(), Expr::fvar(value)),
        );
        let right = Expr::app(g.clone(), Expr::app(h, numeral(7)));
        let before = txn.clone();
        let mut limits = budget();
        limits.zeta_delta = unfold;
        let result = txn.unify(&left, &right, limits);
        if unfold {
            result.unwrap();
            assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
        } else {
            assert!(result.is_err());
            assert_unchanged(&txn, &before);
        }
    }
}

#[test]
fn convertible_suffixes_still_respect_the_assignment_limit() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let g = local(&mut txn, "g", pi(nat(), nat()));
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    let left = Expr::app(Expr::mvar(f), Expr::app(h.clone(), beta(numeral(7))));
    let right = Expr::app(g, Expr::app(h, numeral(7)));
    let before = txn.clone();
    let mut limits = budget();
    limits.max_assignments = 0;
    assert_eq!(
        txn.unify(&left, &right, limits).unwrap_err(),
        UnificationError::AssignmentLimit { limit: 0 },
    );
    assert_unchanged(&txn, &before);
}

#[test]
fn equal_lambda_bodies_do_not_hide_unequal_domains() {
    let mut txn = transaction();
    let g = local(
        &mut txn,
        "g",
        pi(pi(Expr::sort(Level::one()), nat()), nat()),
    );
    let f = hole(
        &mut txn,
        "f",
        pi(pi(nat(), nat()), nat()),
        MetavarKind::Natural,
    );
    let left_arg = Expr::lam(name("unused"), nat(), beta(numeral(7)), BinderInfo::Default);
    let right_arg = Expr::lam(
        name("unused"),
        Expr::sort(Level::one()),
        numeral(7),
        BinderInfo::Default,
    );
    let before = txn.clone();
    assert!(
        txn.unify(
            &Expr::app(Expr::mvar(f), left_arg),
            &Expr::app(g, right_arg),
            budget(),
        )
        .is_err()
    );
    assert_unchanged(&txn, &before);
}
