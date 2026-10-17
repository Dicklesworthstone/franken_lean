//! Telescope closure through real checked assignments and atomic failures.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
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

fn numeral(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}

fn transaction() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        29,
    )
}

fn hole(txn: &mut ElabTxn, text: &str, type_: Expr) -> MVarId {
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

fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = actual.budget.heartbeats_consumed;
    assert_eq!(actual, &expected);
}

#[test]
fn dependent_captured_let_fields_are_checked_and_remain_convertible() {
    for reverse in [false, true] {
        let mut txn = transaction();
        let a = FVarId(name("type"));
        let x = FVarId(name("value"));
        let alias = FVarId(name("alias"));
        let y = FVarId(name("copied"));
        txn.lctx.add_param(
            a.clone(),
            name("same"),
            Expr::sort(Level::one()),
            BinderInfo::Implicit,
        );
        txn.lctx.add_param(
            x.clone(),
            name("same"),
            Expr::fvar(a.clone()),
            BinderInfo::StrictImplicit,
        );
        txn.lctx.add_let(
            alias.clone(),
            name("same"),
            Expr::sort(Level::one()),
            Expr::fvar(a.clone()),
        );
        txn.lctx.add_let(
            y.clone(),
            name("same"),
            Expr::fvar(alias.clone()),
            Expr::fvar(x.clone()),
        );
        let type_ = Expr::forall_e(
            name("same"),
            Expr::fvar(alias.clone()),
            Expr::fvar(a),
            BinderInfo::InstImplicit,
        );
        let value = Expr::lam(
            name("same"),
            Expr::fvar(alias),
            Expr::fvar(y),
            BinderInfo::InstImplicit,
        );
        let goal = hole(&mut txn, "result", type_);
        let before_lctx = txn.lctx.clone();
        let before_env = txn.env.clone();
        let equation = (Expr::mvar(goal.clone()), value.clone());
        let report = if reverse {
            txn.unify(&equation.1, &equation.0, budget())
        } else {
            txn.unify(&equation.0, &equation.1, budget())
        }
        .unwrap();
        assert_eq!(report.kernel_checks, 2);
        assert!(report.residual_metavariables.is_empty());
        assert_eq!(txn.mvars.get_assigned_expr(&goal), Some(&value));
        // Both dependent let fields must still reduce to the captured argument.
        txn.unify(
            &Expr::app(Expr::mvar(goal), Expr::fvar(x.clone())),
            &Expr::fvar(x),
            budget(),
        )
        .unwrap();
        assert_eq!(txn.lctx, before_lctx);
        assert_eq!(txn.env, before_env);
    }
}

#[test]
fn unused_invalid_captured_fields_are_rejected_without_publishing() {
    for is_let in [false, true] {
        for invalid in [false, true] {
            let mut txn = transaction();
            let x = FVarId(name("x"));
            txn.lctx
                .add_param(x.clone(), name("same"), nat(), BinderInfo::Default);
            let unused = FVarId(name("unused"));
            if is_let {
                let value = if invalid {
                    Expr::sort(Level::one())
                } else {
                    Expr::fvar(x)
                };
                txn.lctx.add_let(unused, name("same"), nat(), value);
            } else {
                let type_ = if invalid { numeral(0) } else { nat() };
                txn.lctx
                    .add_param(unused, name("same"), type_, BinderInfo::Default);
            }
            // The candidate never mentions the malformed field. It must still
            // be checked as part of the captured LocalContext.
            let goal = hole(&mut txn, "result", nat());
            let before = txn.clone();
            let result = txn.unify(&Expr::mvar(goal.clone()), &numeral(7), budget());
            if invalid {
                assert!(
                    matches!(result, Err(UnificationError::AssignmentCheck { outcome, .. })
                        if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. }))),
                );
                unchanged(&txn, &before);
                assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed,);
                assert!(!txn.mvars.is_assigned(&goal));
            } else {
                assert_eq!(result.unwrap().kernel_checks, 2);
                assert_eq!(txn.mvars.get_assigned_expr(&goal), Some(&numeral(7)));
                assert_eq!(txn.lctx, before.lctx);
                assert_eq!(txn.env, before.env);
            }
        }
    }
}

#[test]
fn checked_large_context_assignments_obey_work_limits_and_atomic_cancellation() {
    const LOCALS: u64 = 64;
    let mut base = transaction();
    for index in 0..LOCALS {
        base.lctx.add_param(
            FVarId(Name::num(name("local"), index)),
            name("same"),
            nat(),
            BinderInfo::Default,
        );
    }
    let value = Expr::fvar(FVarId(Name::num(name("local"), 0)));
    let goal = hole(&mut base, "result", nat());
    let equations = [(Expr::mvar(goal.clone()), value.clone())];
    let mut limits = budget();
    // This ceiling includes captured-context validation and both real K1
    // checks. No context is pruned merely because its fields are unused.
    limits.max_steps = 20_000;
    limits.max_visited_nodes = 10_000;
    let polls = Cell::new(0_u64);
    let mut successful = base.clone();
    let report = successful
        .unify_many_with(&equations, limits, &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    assert_eq!(report.kernel_checks, 2);
    assert_eq!(report.expression_assignments, vec![goal.clone()]);
    assert!(report.residual_metavariables.is_empty());
    assert_eq!(successful.mvars.get_assigned_expr(&goal), Some(&value));
    assert_eq!(successful.lctx, base.lctx);
    assert_eq!(successful.env, base.env);
    assert_eq!(successful.lctx.len(), LOCALS as usize);
    assert!(report.unifier_steps <= 20_000, "{report:?}");
    assert!(report.visited_nodes <= 10_000, "{report:?}");

    for stop in [0, polls.get() / 2, polls.get() - 1] {
        let mut txn = base.clone();
        let calls = Cell::new(0_u64);
        assert!(matches!(
            txn.unify_many_with(&equations, limits, &|| {
                let current = calls.get();
                calls.set(current + 1);
                current >= stop
            }),
            Err(UnificationError::Cancelled),
        ));
        unchanged(&txn, &base);
        if stop != 0 {
            assert!(txn.budget.heartbeats_consumed > base.budget.heartbeats_consumed);
        }
        txn.unify_many_with(&equations, limits, &|| false).unwrap();
        assert_eq!(txn.mvars.get_assigned_expr(&goal), Some(&value));
    }

    for node_bound in [false, true] {
        let mut txn = base.clone();
        let mut limited = limits;
        if node_bound {
            limited.max_visited_nodes = report.visited_nodes - 1;
        } else {
            limited.max_steps = report.unifier_steps - 1;
        }
        let error = txn
            .unify_many_with(&equations, limited, &|| false)
            .unwrap_err();
        assert!(matches!(
            error,
            UnificationError::NodeLimit { .. } | UnificationError::StepLimit { .. },
        ));
        unchanged(&txn, &base);
        assert!(txn.budget.heartbeats_consumed > base.budget.heartbeats_consumed);
        txn.unify_many_with(&equations, limits, &|| false).unwrap();
        assert_eq!(txn.mvars.get_assigned_expr(&goal), Some(&value));
    }
}
