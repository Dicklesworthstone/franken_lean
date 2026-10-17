//! Dependency-closed intersections must preserve typing, scope and rollback.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::ConstraintKind;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::mvar::MetavarKind;
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::Budget;
use std::cell::Cell;

fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}
fn number(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
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
fn app(head: Expr, args: &[Expr]) -> Expr {
    args.iter().cloned().fold(head, Expr::app)
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
fn hole(txn: &mut ElabTxn, s: &str, type_: Expr) -> MVarId {
    let id = MVarId(name(s));
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
fn local(txn: &mut ElabTxn, s: &str, type_: Expr) -> Expr {
    let id = FVarId(name(s));
    txn.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn unchanged(txn: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = txn.budget.heartbeats_consumed;
    assert_eq!(txn, &expected);
}

/// ?f A a p = ?g a B b q. Only a is shared, but its type A is not in
/// the parents' common captured context. The private p/q (and B/b) prevent
/// ordinary assignment in either direction from bypassing the pruning rung.
/// Returning A instead of Nat makes the result itself escape after pruning.
fn equation(dependent_result: bool) -> (ElabTxn, MVarId, MVarId, Expr, Expr) {
    let mut txn = transaction();
    let result = if dependent_result { bvar(2) } else { nat() };
    let f = hole(
        &mut txn,
        "f",
        pi(Expr::sort(Level::one()), pi(bvar(0), pi(nat(), result))),
    );
    let a_type = local(&mut txn, "A", Expr::sort(Level::one()));
    let result = if dependent_result {
        a_type.clone()
    } else {
        nat()
    };
    let g = hole(
        &mut txn,
        "g",
        pi(
            a_type.clone(),
            pi(Expr::sort(Level::one()), pi(bvar(0), pi(nat(), result))),
        ),
    );
    let a = local(&mut txn, "a", a_type.clone());
    let b_type = local(&mut txn, "B", Expr::sort(Level::one()));
    let b = local(&mut txn, "b", b_type.clone());
    let p = local(&mut txn, "p", nat());
    let q = local(&mut txn, "q", nat());
    let left = app(Expr::mvar(f.clone()), &[a_type, a.clone(), p]);
    let right = app(Expr::mvar(g.clone()), &[a, b_type, b, q]);
    (txn, f, g, left, right)
}

#[test]
fn an_unavailable_argument_domain_no_longer_blocks_a_closed_solution() {
    for reverse in [false, true] {
        let (mut txn, f, g, left, right) = equation(false);
        let before_env = txn.env.clone();
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.expression_assignments.len(), 2);
        assert!(report.expression_assignments.contains(&f));
        assert!(report.expression_assignments.contains(&g));
        assert!(report.kernel_checks >= 2);
        assert_eq!(report.residual_metavariables.len(), 1);
        assert_eq!(txn.mvars.len(), 3);
        let residual = report.residual_metavariables[0].clone();
        let declaration = txn.mvars.get_decl(&residual).unwrap();
        assert_eq!(declaration.type_, nat());
        assert!(declaration.lctx.is_empty());
        assert!(!txn.mvars.is_assigned(&residual));
        for id in [&f, &g] {
            let value = txn.mvars.get_assigned_expr(id).unwrap();
            assert!(!value.has_loose_bvars());
            assert!(value.has_expr_mvar());
        }
        assert!(!txn.mvars.get_assigned_expr(&f).unwrap().has_fvar());
        assert_eq!(txn.env, before_env);
        // The fresh hole is a real obligation, not an assumed Nat inhabitant.
        txn.unify(&Expr::mvar(residual), &number(37), budget())
            .unwrap();
        txn.unify(&left, &number(37), budget()).unwrap();
        txn.unify(&right, &number(37), budget()).unwrap();
        assert_eq!(txn.env, before_env);
    }
}

#[test]
fn an_escaping_result_still_defers_without_creating_a_residual() {
    for reverse in [false, true] {
        let (mut txn, _, _, left, right) = equation(true);
        let before = txn.clone();
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        assert!(matches!(
            txn.unify(&left, &right, budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn dropping_an_argument_cannot_hide_an_ill_typed_original_spine() {
    // f A x = f B x is not well typed when x : A and A/B are distinct
    // local types. A constant assignment would otherwise erase the evidence.
    for reverse in [false, true] {
        let mut txn = transaction();
        let f = hole(
            &mut txn,
            "f",
            pi(Expr::sort(Level::one()), pi(bvar(0), nat())),
        );
        let a = local(&mut txn, "A", Expr::sort(Level::one()));
        let b = local(&mut txn, "B", Expr::sort(Level::one()));
        let x = local(&mut txn, "x", a.clone());
        let left = app(Expr::mvar(f.clone()), &[a, x.clone()]);
        let right = app(Expr::mvar(f), &[b, x]);
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&left, &right, budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn dependency_cascades_drop_together_but_independent_arguments_survive() {
    for reverse in [false, true] {
        let mut txn = transaction();
        // f : (T : Type) -> (P : T -> Type) -> (x : T) -> P x -> Nat -> Nat -> Nat
        let f = hole(
            &mut txn,
            "f",
            pi(
                Expr::sort(Level::one()),
                pi(
                    pi(bvar(0), Expr::sort(Level::one())),
                    pi(
                        bvar(1),
                        pi(Expr::app(bvar(1), bvar(0)), pi(nat(), pi(nat(), nat()))),
                    ),
                ),
            ),
        );
        let a = local(&mut txn, "A", Expr::sort(Level::one()));
        let family = local(&mut txn, "P", pi(a.clone(), Expr::sort(Level::one())));
        // g captures A/P, whereas f captures neither.
        let g = hole(
            &mut txn,
            "g",
            pi(
                a.clone(),
                pi(
                    Expr::app(family.clone(), bvar(0)),
                    pi(
                        Expr::sort(Level::one()),
                        pi(bvar(0), pi(nat(), pi(nat(), nat()))),
                    ),
                ),
            ),
        );
        let x = local(&mut txn, "x", a.clone());
        let y = local(&mut txn, "y", Expr::app(family.clone(), x.clone()));
        let b_type = local(&mut txn, "B", Expr::sort(Level::one()));
        let b = local(&mut txn, "b", b_type.clone());
        let n = local(&mut txn, "n", nat());
        let p = local(&mut txn, "p", nat());
        let q = local(&mut txn, "q", nat());
        let left = app(
            Expr::mvar(f),
            &[a, family, x.clone(), y.clone(), n.clone(), p],
        );
        let right = app(Expr::mvar(g), &[x, y, b_type, b, n.clone(), q]);
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        let declaration = txn.mvars.get_decl(&residual).unwrap();
        assert_eq!(
            declaration.type_,
            Expr::forall_e(name("n"), nat(), nat(), BinderInfo::Default)
        );
        assert!(declaration.lctx.is_empty());
        assert!(!txn.mvars.is_assigned(&residual));
        txn.unify(&Expr::mvar(residual), &lam(nat(), bvar(0)), budget())
            .unwrap();
        txn.unify(&left, &n, budget()).unwrap();
        txn.unify(&right, &n, budget()).unwrap();
    }
}

#[test]
fn queued_typing_obligations_wake_without_hiding_the_new_residual() {
    let (mut txn, f, _, lhs, rhs) = equation(false);
    let type_ = txn.mvars.get_decl(&f).unwrap().type_.clone();
    let selected = txn.postpone(ConstraintKind::DefEq { lhs, rhs }, 0);
    let waiting = txn.postpone(
        ConstraintKind::HasType {
            expr: Expr::mvar(f),
            expected_type: type_,
        },
        0,
    );
    let report = txn
        .solve_defeq_constraints_with(&[selected], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![selected]);
    assert_eq!(report.unification.residual_metavariables.len(), 1);
    assert!(
        report
            .unification
            .awakened
            .iter()
            .any(|row| row.id == waiting)
    );
    assert!(
        !txn.mvars
            .is_assigned(&report.unification.residual_metavariables[0])
    );
}

#[test]
fn both_assignments_and_the_residual_roll_back_at_resource_stops() {
    let (base, _, _, left, right) = equation(false);
    let report = base.clone().unify(&left, &right, budget()).unwrap();
    assert!(report.unifier_steps > 1 && report.visited_nodes > 1);
    for limit in 0..3 {
        let mut txn = base.clone();
        let mut limits = budget();
        match limit {
            0 => limits.max_assignments = 1,
            1 => limits.max_steps = report.unifier_steps - 1,
            _ => limits.max_visited_nodes = report.visited_nodes - 1,
        }
        let error = txn.unify(&left, &right, limits).unwrap_err();
        match limit {
            0 => assert!(matches!(
                error,
                UnificationError::AssignmentLimit { limit: 1 }
            )),
            1 => assert!(matches!(error, UnificationError::StepLimit { .. })),
            _ => assert!(matches!(error, UnificationError::NodeLimit { .. })),
        }
        unchanged(&txn, &base);
        txn.unify(&left, &right, budget()).unwrap();
    }
}

#[test]
fn late_cancellation_leaks_neither_pruned_assignments_nor_queue_wakeups() {
    let (mut base, f, _, left, right) = equation(false);
    let type_ = base.mvars.get_decl(&f).unwrap().type_.clone();
    base.postpone(
        ConstraintKind::HasType {
            expr: Expr::mvar(f),
            expected_type: type_,
        },
        0,
    );
    let equations = [(left, right)];
    let polls = Cell::new(0usize);
    base.clone()
        .unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let total = polls.get();
    assert!(total > 1);
    for stop in [0, total / 2, total - 1] {
        let mut txn = base.clone();
        let calls = Cell::new(0usize);
        assert!(matches!(
            txn.unify_many_with(&equations, budget(), &|| {
                let n = calls.get();
                calls.set(n + 1);
                n >= stop
            }),
            Err(UnificationError::Cancelled)
        ));
        unchanged(&txn, &base);
    }
}

#[test]
fn kernel_nonanswers_cannot_publish_the_pruned_solution() {
    let (mut txn, _, _, left, right) = equation(false);
    let before = txn.clone();
    let mut limits = budget();
    limits.kernel = limits.kernel.narrowed(0, limits.kernel.depth);
    match txn.unify(&left, &right, limits).unwrap_err() {
        UnificationError::AssignmentCheck { outcome, .. } => {
            assert!(matches!(*outcome, Outcome::Inconclusive(_)));
        }
        other => panic!("expected a typed K1 stop, got {other:?}"),
    }
    unchanged(&txn, &before);
    txn.unify(&left, &right, budget()).unwrap();
}

#[test]
fn private_argument_type_errors_cannot_disappear_with_the_shared_argument() {
    for reverse in [false, true] {
        let (mut txn, _, g, left, _) = equation(false);
        let var = |s| Expr::fvar(FVarId(name(s)));
        // g's last argument requires Nat, but r has type A. Its position is
        // private, so checking only the shared a would miss this malformed use.
        let bad = local(&mut txn, "r", var("A"));
        let right = app(Expr::mvar(g), &[var("a"), var("B"), var("b"), bad]);
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&left, &right, budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn retained_domains_can_depend_on_the_common_captured_context() {
    for reverse in [false, true] {
        let mut txn = transaction();
        let shared_type = local(&mut txn, "C", Expr::sort(Level::one()));
        let common = txn.lctx.clone();
        let f = hole(
            &mut txn,
            "f",
            pi(
                Expr::sort(Level::one()),
                pi(bvar(0), pi(shared_type.clone(), pi(nat(), nat()))),
            ),
        );
        let a_type = local(&mut txn, "A", Expr::sort(Level::one()));
        let g = hole(
            &mut txn,
            "g",
            pi(
                a_type.clone(),
                pi(
                    shared_type.clone(),
                    pi(Expr::sort(Level::one()), pi(bvar(0), pi(nat(), nat()))),
                ),
            ),
        );
        let a = local(&mut txn, "a", a_type.clone());
        let x = local(&mut txn, "x", shared_type.clone());
        let b_type = local(&mut txn, "B", Expr::sort(Level::one()));
        let b = local(&mut txn, "b", b_type.clone());
        let p = local(&mut txn, "p", nat());
        let q = local(&mut txn, "q", nat());
        let left = app(Expr::mvar(f), &[a_type, a.clone(), x.clone(), p]);
        let right = app(Expr::mvar(g), &[a, x, b_type, b, q]);
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        let declaration = txn.mvars.get_decl(&residual).unwrap();
        assert_eq!(declaration.type_, pi(shared_type.clone(), nat()));
        assert_eq!(declaration.lctx, common);
        txn.unify(
            &Expr::mvar(residual),
            &lam(shared_type, number(7)),
            budget(),
        )
        .unwrap();
        txn.unify(&left, &number(7), budget()).unwrap();
        txn.unify(&right, &number(7), budget()).unwrap();
    }
}

#[test]
fn propositional_residuals_remain_obligations_not_fabricated_proofs() {
    for reverse in [false, true] {
        let mut txn = transaction();
        let proposition = local(&mut txn, "P", Expr::sort(Level::zero()));
        let common = txn.lctx.clone();
        let before_env = txn.env.clone();
        let f = hole(
            &mut txn,
            "f",
            pi(
                Expr::sort(Level::one()),
                pi(bvar(0), pi(nat(), proposition.clone())),
            ),
        );
        let a_type = local(&mut txn, "A", Expr::sort(Level::one()));
        let g = hole(
            &mut txn,
            "g",
            pi(
                a_type.clone(),
                pi(
                    Expr::sort(Level::one()),
                    pi(bvar(0), pi(nat(), proposition.clone())),
                ),
            ),
        );
        let a = local(&mut txn, "a", a_type.clone());
        let b_type = local(&mut txn, "B", Expr::sort(Level::one()));
        let b = local(&mut txn, "b", b_type.clone());
        let p = local(&mut txn, "p", nat());
        let q = local(&mut txn, "q", nat());
        let left = app(Expr::mvar(f), &[a_type, a.clone(), p]);
        let right = app(Expr::mvar(g), &[a, b_type, b, q]);
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        // Exercise pruning, not the separate proof-irrelevance rung.
        let mut limits = budget();
        limits.proof_irrelevance = false;
        let report = txn.unify(&left, &right, limits).unwrap();
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        let declaration = txn.mvars.get_decl(&residual).unwrap();
        assert_eq!(declaration.type_, proposition);
        assert_eq!(declaration.lctx, common);
        assert!(!txn.mvars.is_assigned(&residual));
        let before_bad_proof = txn.clone();
        assert!(
            txn.unify(&Expr::mvar(residual), &number(0), budget())
                .is_err()
        );
        unchanged(&txn, &before_bad_proof);
        assert_eq!(txn.env, before_env);
    }
}
