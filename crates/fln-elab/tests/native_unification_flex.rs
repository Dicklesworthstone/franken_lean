//! Regression coverage for postponed higher-order application equations.
//! These tests use the native elaborator and its ordinary K1 assignment checks.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::ConstraintKind;
use fln_elab::constraint::unify::{UnificationBudget, UnificationDeferred, UnificationError};
use fln_elab::mvar::{MetavarError, MetavarKind};
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
fn function_type() -> Expr {
    Expr::forall_e(name("x"), nat(), nat(), BinderInfo::Default)
}
fn constant(value: u64) -> Expr {
    Expr::lam(name("x"), nat(), numeral(value), BinderInfo::Default)
}
fn identity() -> Expr {
    Expr::lam(name("x"), nat(), Expr::bvar(0).unwrap(), BinderInfo::Default)
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
fn goal(txn: &mut ElabTxn, text: &str, type_: Expr) -> MVarId {
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
fn local(txn: &mut ElabTxn, text: &str, type_: Expr) -> Expr {
    let id = FVarId(name(text));
    txn.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn assert_semantics_unchanged(actual: &ElabTxn, before: &ElabTxn) {
    // Work accounting alone is allowed to advance on a failed attempt.
    let mut accounted_before = before.clone();
    accounted_before.budget.heartbeats_consumed = actual.budget.heartbeats_consumed;
    assert_eq!(actual, &accounted_before);
}

type EquationBatch = Vec<(Expr, Expr)>;

fn distinct_heads() -> (ElabTxn, MVarId, MVarId, EquationBatch) {
    let mut txn = transaction();
    let f = goal(&mut txn, "f", function_type());
    let g = goal(&mut txn, "g", function_type());
    let equations = vec![
        (
            Expr::app(Expr::mvar(f.clone()), numeral(0)),
            Expr::app(Expr::mvar(g.clone()), numeral(1)),
        ),
        (Expr::mvar(f.clone()), constant(7)),
        (Expr::mvar(g.clone()), constant(7)),
    ];
    (txn, f, g, equations)
}

#[test]
fn same_head_occurs_candidate_waits_for_a_later_function_assignment() {
    // Both context orders matter: a captured y reaches the occurs check,
    // whereas a y outside the declaration context first fails scope checking.
    for captured in [false, true] {
        for reverse_order in [false, true] {
            for reverse_sides in [false, true] {
                let mut txn = transaction();
                let early = (!captured).then(|| goal(&mut txn, "f", function_type()));
                let x = local(&mut txn, "x", nat());
                let y = local(&mut txn, "y", nat());
                let f = early.unwrap_or_else(|| goal(&mut txn, "f", function_type()));
                let left = Expr::app(Expr::mvar(f.clone()), x);
                let right = Expr::app(Expr::mvar(f.clone()), y);
                let equation = if reverse_sides {
                    (right, left)
                } else {
                    (left, right)
                };
                let mut equations = vec![equation, (Expr::mvar(f.clone()), constant(9))];
                if reverse_order {
                    equations.reverse();
                }
                let env = txn.env.clone();
                let report = txn
                    .unify_many_with(&equations, budget(), &|| false)
                    .unwrap();
                assert_eq!(report.expression_assignments, vec![f.clone()]);
                assert_eq!(report.kernel_checks, 1);
                assert!(report.residual_metavariables.is_empty());
                assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&constant(9)));
                assert_eq!(txn.env, env);
            }
        }
    }
}

#[test]
fn distinct_flexible_heads_do_not_force_distinct_arguments_equal() {
    for order in [
        [0, 1, 2],
        [0, 2, 1],
        [1, 0, 2],
        [1, 2, 0],
        [2, 0, 1],
        [2, 1, 0],
    ] {
        for reverse_sides in [false, true] {
            let (mut txn, f, g, equations) = distinct_heads();
            let selected: Vec<_> = order
                .into_iter()
                .map(|index| {
                    let (left, right) = equations[index].clone();
                    if reverse_sides {
                        (right, left)
                    } else {
                        (left, right)
                    }
                })
                .collect();
            let env = txn.env.clone();
            let report = txn
                .unify_many_with(&selected, budget(), &|| false)
                .unwrap();
            assert_eq!(report.expression_assignments.len(), 2);
            assert_eq!(report.kernel_checks, 2);
            assert!(report.residual_metavariables.is_empty());
            assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&constant(7)));
            assert_eq!(txn.mvars.get_assigned_expr(&g), Some(&constant(7)));
            assert_eq!(txn.env, env);
        }
    }
}

#[test]
fn a_flexible_head_is_not_prematurely_assigned_the_rigid_head() {
    for reverse_order in [false, true] {
        for reverse_sides in [false, true] {
            let mut txn = transaction();
            let f = goal(&mut txn, "f", function_type());
            let n = goal(&mut txn, "n", nat());
            let left = Expr::app(Expr::mvar(f.clone()), numeral(0));
            let right = Expr::app(
                Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new()),
                Expr::mvar(n.clone()),
            );
            let equation = if reverse_sides {
                (right, left)
            } else {
                (left, right)
            };
            let mut equations = vec![equation, (Expr::mvar(f.clone()), constant(4))];
            if reverse_order {
                equations.reverse();
            }
            let report = txn
                .unify_many_with(&equations, budget(), &|| false)
                .unwrap();
            assert_eq!(report.kernel_checks, 2);
            assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&constant(4)));
            assert_eq!(txn.mvars.get_assigned_expr(&n), Some(&numeral(3)));
        }
    }
}

#[test]
fn a_blocked_flexible_equation_is_not_a_success_or_a_committed_alias() {
    let (mut txn, _, _, equations) = distinct_heads();
    let unrelated = goal(&mut txn, "unrelated", nat());
    let before = txn.clone();
    let attempt = [equations[0].clone(), (Expr::mvar(unrelated), numeral(5))];
    assert!(matches!(
        txn.unify_many_with(&attempt, budget(), &|| false),
        Err(UnificationError::Deferred(_))
    ));
    assert_semantics_unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
    // Retrying the actual equations after a failed attempt is safe.
    txn.unify_many_with(&equations, budget(), &|| false)
        .unwrap();
}

#[test]
fn same_head_without_a_solution_stays_deferred() {
    let mut txn = transaction();
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let f = goal(&mut txn, "f", function_type());
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f.clone()), x),
            &Expr::app(Expr::mvar(f), y),
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn an_incompatible_later_function_does_not_erase_the_postponed_equation() {
    let mut txn = transaction();
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let f = goal(&mut txn, "f", function_type());
    let before = txn.clone();
    let equations = [
        (
            Expr::app(Expr::mvar(f.clone()), x),
            Expr::app(Expr::mvar(f.clone()), y),
        ),
        (Expr::mvar(f), identity()),
    ];
    assert!(matches!(
        txn.unify_many_with(&equations, budget(), &|| false),
        Err(UnificationError::Deferred(_))
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn queued_flexible_equations_retry_without_losing_queue_authority() {
    let (mut txn, f, g, equations) = distinct_heads();
    let ids: Vec<_> = equations
        .into_iter()
        .map(|(lhs, rhs)| txn.postpone(ConstraintKind::DefEq { lhs, rhs }, 0))
        .collect();
    let report = txn
        .solve_defeq_constraints_with(&[ids[2], ids[0], ids[1], ids[0]], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, ids);
    assert_eq!(report.unification.kernel_checks, 2);
    assert!(txn.constraints.constraints().is_empty());
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&constant(7)));
    assert_eq!(txn.mvars.get_assigned_expr(&g), Some(&constant(7)));
}

#[test]
fn kernel_rejection_rolls_back_the_entire_recovered_batch() {
    let (mut txn, _, _, mut equations) = distinct_heads();
    let bad = goal(&mut txn, "bad", nat());
    equations.push((Expr::mvar(bad.clone()), Expr::sort(Level::zero())));
    let before = txn.clone();
    match txn
        .unify_many_with(&equations, budget(), &|| false)
        .unwrap_err()
    {
        UnificationError::AssignmentCheck { id, outcome } => {
            assert_eq!(id, bad);
            assert!(matches!(
                *outcome,
                Outcome::Complete(Verdict::Rejected { .. })
            ));
        }
        other => panic!("expected the ordinary K1 veto, got {other:?}"),
    }
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn cancellation_including_the_final_poll_publishes_no_recovered_assignments() {
    let (base, _, _, equations) = distinct_heads();
    let polls = Cell::new(0usize);
    base.clone()
        .unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let total = polls.get();
    assert!(total > 2);
    for stop in [0, total / 2, total - 1] {
        let mut txn = base.clone();
        let polls = Cell::new(0usize);
        assert!(matches!(
            txn.unify_many_with(&equations, budget(), &|| {
                let current = polls.get();
                polls.set(current + 1);
                current >= stop
            }),
            Err(UnificationError::Cancelled)
        ));
        assert_semantics_unchanged(&txn, &base);
    }
}

#[test]
fn an_assignment_limit_does_not_publish_the_first_function() {
    let (mut txn, _, _, equations) = distinct_heads();
    let before = txn.clone();
    let mut limited = budget();
    limited.max_assignments = 1;
    assert!(matches!(
        txn.unify_many_with(&equations, limited, &|| false),
        Err(UnificationError::AssignmentLimit { limit: 1 })
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn bare_occurs_checks_and_opaque_hole_policy_are_not_weakened() {
    let mut txn = transaction();
    let n = goal(&mut txn, "n", nat());
    let before = txn.clone();
    let cyclic = Expr::app(
        Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new()),
        Expr::mvar(n.clone()),
    );
    assert!(matches!(
        txn.unify(&Expr::mvar(n), &cyclic, budget()),
        Err(UnificationError::Metavariable(
            MetavarError::OccursCheckFailed { .. }
        ))
    ));
    assert_semantics_unchanged(&txn, &before);

    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let f = MVarId(name("opaque"));
    txn.mvars.declare(
        f.clone(),
        f.0.clone(),
        function_type(),
        txn.lctx.clone(),
        MetavarKind::SyntheticOpaque,
        0,
        None,
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f.clone()), x),
            &Expr::app(Expr::mvar(f), y),
            budget(),
        ),
        Err(UnificationError::Deferred(
            UnificationDeferred::OpaqueMetavariable(_)
        ))
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn rigid_congruence_and_valid_miller_patterns_still_assign() {
    let mut txn = transaction();
    let n = goal(&mut txn, "n", nat());
    let rigid = local(&mut txn, "rigid", function_type());
    txn.unify(
        &Expr::app(rigid.clone(), Expr::mvar(n.clone())),
        &Expr::app(rigid, numeral(8)),
        budget(),
    )
    .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&n), Some(&numeral(8)));

    let f = goal(&mut txn, "pattern", function_type());
    let x = local(&mut txn, "argument", nat());
    let report = txn
        .unify(&Expr::app(Expr::mvar(f.clone()), x.clone()), &x, budget())
        .unwrap();
    assert_eq!(report.expression_assignments, vec![f]);
    assert_eq!(report.kernel_checks, 1);
    assert!(report.residual_metavariables.is_empty());
}

#[test]
fn unresolved_function_eta_remains_available_without_assigning_the_head() {
    for reverse_sides in [false, true] {
        let mut txn = transaction();
        let f = goal(
            &mut txn,
            "curried",
            Expr::forall_e(name("n"), nat(), function_type(), BinderInfo::Default),
        );
        let left = Expr::app(Expr::mvar(f), numeral(0));
        let right = Expr::lam(
            name("x"),
            nat(),
            Expr::app(left.clone(), Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        let (left, right) = if reverse_sides {
            (right, left)
        } else {
            (left, right)
        };
        let before = txn.clone();
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert!(report.expression_assignments.is_empty());
        assert_semantics_unchanged(&txn, &before);
    }
}
