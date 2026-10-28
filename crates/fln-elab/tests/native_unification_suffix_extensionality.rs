//! Eta and proof-irrelevant suffixes must not turn head recovery into hole solving.
//! Real transactional solver, native reduction and K1 checks; no mocked judgments.
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

fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(name("parameter"), domain, body, BinderInfo::Default)
}
fn prop() -> Expr {
    Expr::sort(Level::zero())
}
fn wrapped_equation(
    txn: &mut ElabTxn,
    domain: Expr,
    left: Expr,
    right: Expr,
) -> (MVarId, Expr, Expr, Expr) {
    // The wrapper makes the suffix a rigid application rather than a local
    // Miller argument, so ordinary abstraction cannot solve a different head.
    let wrap = local(txn, "wrap", pi(domain, nat()));
    let g = local(txn, "g", pi(nat(), nat()));
    let f = hole(txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    let lhs = Expr::app(Expr::mvar(f.clone()), Expr::app(wrap.clone(), left));
    let rhs = Expr::app(g.clone(), Expr::app(wrap, right));
    (f, g, lhs, rhs)
}

#[test]
fn eta_suffixes_recover_the_same_head_in_all_orientations() {
    for expanded_left in [false, true] {
        for reverse in [false, true] {
            let mut txn = transaction();
            let h = local(&mut txn, "h", pi(nat(), nat()));
            let expanded = lam(nat(), Expr::app(h.clone(), beta(Expr::bvar(0).unwrap())));
            let (a, b) = if expanded_left {
                (expanded, h)
            } else {
                (h, expanded)
            };
            let (f, g, lhs, rhs) = wrapped_equation(&mut txn, pi(nat(), nat()), a, b);
            let report = if reverse {
                txn.unify(&rhs, &lhs, budget())
            } else {
                txn.unify(&lhs, &rhs, budget())
            }
            .unwrap();
            assert_eq!(report.expression_assignments, vec![f.clone()]);
            assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
            assert!(report.kernel_checks > 0);
        }
    }
}

#[test]
fn eta_suffixes_open_dependent_telescopes_without_capture() {
    let mut txn = transaction();
    let family = local(&mut txn, "family", pi(nat(), Expr::sort(Level::one())));
    let domain = pi(
        nat(),
        pi(
            Expr::app(family.clone(), Expr::bvar(0).unwrap()),
            Expr::app(family.clone(), Expr::bvar(1).unwrap()),
        ),
    );
    let h = local(&mut txn, "h", domain.clone());
    let expanded = lam(
        nat(),
        lam(
            Expr::app(family, Expr::bvar(0).unwrap()),
            Expr::app(
                Expr::app(h.clone(), Expr::bvar(1).unwrap()),
                Expr::bvar(0).unwrap(),
            ),
        ),
    );
    let (f, g, lhs, rhs) = wrapped_equation(&mut txn, domain, expanded, h);
    txn.unify(&lhs, &rhs, budget()).unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
    assert!(!txn.mvars.get_assigned_expr(&f).unwrap().has_loose_bvars());
}

/// Head recovery never solves an argument function hole, but the pin's first-order
/// approximation, which runs first, unifies `wrap (fun x => h x)` with `wrap ?argument`
/// (vendored `Lean/Meta/ExprDefEq.lean:1172-1212`) and so assigns `?argument`.
#[test]
fn first_order_approximation_solves_an_argument_function_hole() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let argument = hole(&mut txn, "argument", pi(nat(), nat()), MetavarKind::Natural);
    let expanded = lam(nat(), Expr::app(h, Expr::bvar(0).unwrap()));
    let (f, g, lhs, rhs) = wrapped_equation(
        &mut txn,
        pi(nat(), nat()),
        expanded,
        Expr::mvar(argument.clone()),
    );
    txn.unify(&lhs, &rhs, budget()).unwrap();
    assert!(txn.mvars.is_assigned(&argument));
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
}

/// On a deliberately ill-typed pair (h expects Type, not Nat), the pin's first-order
/// approximation runs before head recovery's domain check is reached, and its `etaEq` compares
/// `fun x => h x` with `h` structurally, as the pin's `isDefEq` does on input it assumes
/// well-typed. The only assignment it publishes, `?f := g`, is well-typed and K1-checked.
#[test]
fn first_order_approximation_publishes_only_a_checked_head_on_ill_typed_eta() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(Expr::sort(Level::one()), nat()));
    let expanded = lam(nat(), Expr::app(h.clone(), Expr::bvar(0).unwrap()));
    let (f, g, lhs, rhs) = wrapped_equation(&mut txn, pi(nat(), nat()), expanded, h);
    let report = txn.unify(&lhs, &rhs, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![f.clone()]);
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
    assert!(report.kernel_checks > 0);
}

#[test]
fn distinct_proofs_convert_only_when_proof_irrelevance_is_enabled() {
    for enabled in [false, true] {
        for reverse in [false, true] {
            let mut txn = transaction();
            let p = local(&mut txn, "P", prop());
            let first = local(&mut txn, "first", p.clone());
            let second = local(&mut txn, "second", p.clone());
            let (f, g, lhs, rhs) = wrapped_equation(&mut txn, p, first, second);
            let before = txn.clone();
            let mut limits = budget();
            limits.proof_irrelevance = enabled;
            let result = if reverse {
                txn.unify(&rhs, &lhs, limits)
            } else {
                txn.unify(&lhs, &rhs, limits)
            };
            if enabled {
                let report = result.unwrap();
                assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
                assert_eq!(report.expression_assignments, vec![f]);
                assert!(
                    report.kernel_checks >= 2,
                    "proof conversion plus assignment must be checked"
                );
            } else {
                assert!(result.is_err());
                assert_unchanged(&txn, &before);
            }
        }
    }
}

#[test]
fn proof_conversion_does_not_erase_an_unsolved_proof() {
    for kind in [MetavarKind::Natural, MetavarKind::SyntheticOpaque] {
        let mut txn = transaction();
        let p = local(&mut txn, "P", prop());
        let first = hole(&mut txn, "proof", p.clone(), kind);
        let second = local(&mut txn, "second", p.clone());
        let (_, _, lhs, rhs) = wrapped_equation(&mut txn, p, Expr::mvar(first), second);
        let before = txn.clone();
        assert!(txn.unify(&lhs, &rhs, budget()).is_err());
        assert_unchanged(&txn, &before);
    }
}

#[test]
fn proof_conversion_retains_its_type_equation_at_the_callers_policy() {
    for unfold in [false, true] {
        let mut txn = transaction();
        let p = local(&mut txn, "P", prop());
        let alias = FVarId(name("Alias"));
        txn.lctx
            .add_let(alias.clone(), alias.0.clone(), prop(), p.clone());
        let first = local(&mut txn, "first", p.clone());
        let second = local(&mut txn, "second", Expr::fvar(alias));
        let (f, g, lhs, rhs) = wrapped_equation(&mut txn, p, first, second);
        let before = txn.clone();
        let mut limits = budget();
        limits.zeta_delta = unfold;
        let result = txn.unify(&lhs, &rhs, limits);
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
fn a_proof_type_hint_cannot_hide_an_ill_typed_application() {
    let mut txn = transaction();
    let p = local(&mut txn, "P", prop());
    let first = local(&mut txn, "first", p.clone());
    let constructor = local(&mut txn, "constructor", pi(nat(), p.clone()));
    let invalid = Expr::app(constructor, Expr::sort(Level::one()));
    let (_, _, lhs, rhs) = wrapped_equation(&mut txn, p, first, invalid);
    let before = txn.clone();
    assert!(txn.unify(&lhs, &rhs, budget()).is_err());
    assert_unchanged(&txn, &before);
}

#[test]
fn ordinary_data_is_not_proof_irrelevant() {
    let mut txn = transaction();
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let (_, _, lhs, rhs) = wrapped_equation(&mut txn, nat(), x, y);
    let before = txn.clone();
    assert!(txn.unify(&lhs, &rhs, budget()).is_err());
    assert_unchanged(&txn, &before);
}

#[test]
fn a_stopped_proof_guard_is_not_a_conversion_rejection() {
    let mut txn = transaction();
    let p = local(&mut txn, "P", prop());
    let first = local(&mut txn, "first", p.clone());
    let second = local(&mut txn, "second", p.clone());
    let (_, _, lhs, rhs) = wrapped_equation(&mut txn, p, first, second);
    let before = txn.clone();
    let mut limits = budget();
    limits.kernel.steps = 0;
    let error = txn.unify(&lhs, &rhs, limits).unwrap_err();
    assert!(
        matches!(error, UnificationError::ConversionCheck { outcome }
        if !matches!(*outcome, fln_core::outcome::Outcome::Complete(_)))
    );
    assert_unchanged(&txn, &before);
}

#[test]
fn cancellation_at_conversion_and_publication_boundaries_is_atomic() {
    let mut base = transaction();
    let h = local(&mut base, "h", pi(nat(), nat()));
    let expanded = lam(nat(), Expr::app(h.clone(), zeta(Expr::bvar(0).unwrap())));
    let (_, _, lhs, rhs) = wrapped_equation(&mut base, pi(nat(), nat()), expanded, h);
    let calls = Cell::new(0_usize);
    base.clone()
        .unify_many_with(&[(lhs.clone(), rhs.clone())], budget(), &|| {
            calls.set(calls.get() + 1);
            false
        })
        .unwrap();
    let total = calls.get();
    assert!(total > 4);
    for stop in [1, total / 4, total / 2, 3 * total / 4, total] {
        let mut txn = base.clone();
        let calls = Cell::new(0_usize);
        let error = txn
            .unify_many_with(&[(lhs.clone(), rhs.clone())], budget(), &|| {
                calls.set(calls.get() + 1);
                calls.get() >= stop
            })
            .unwrap_err();
        assert_eq!(error, UnificationError::Cancelled);
        assert_unchanged(&txn, &base);
    }
    base.unify(&lhs, &rhs, budget()).unwrap();
}

#[test]
fn unequal_function_bodies_cannot_be_erased_by_eta() {
    let mut txn = transaction();
    let first = lam(nat(), numeral(1));
    let second = lam(nat(), numeral(2));
    let (_, _, lhs, rhs) = wrapped_equation(&mut txn, pi(nat(), nat()), first, second);
    let before = txn.clone();
    assert!(txn.unify(&lhs, &rhs, budget()).is_err());
    assert_unchanged(&txn, &before);
}

#[test]
fn eta_does_not_treat_data_as_a_function() {
    let mut txn = transaction();
    let h = local(&mut txn, "h", pi(nat(), nat()));
    let expanded = lam(nat(), Expr::app(h, Expr::bvar(0).unwrap()));
    let (_, _, lhs, rhs) = wrapped_equation(&mut txn, pi(nat(), nat()), expanded, numeral(7));
    let before = txn.clone();
    assert!(txn.unify(&lhs, &rhs, budget()).is_err());
    assert_unchanged(&txn, &before);
}
