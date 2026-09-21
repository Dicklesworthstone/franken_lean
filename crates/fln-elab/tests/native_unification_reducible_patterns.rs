//! Reducible higher-order patterns through the public transactional unifier.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
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
fn beta(type_: Expr, value: Expr) -> Expr {
    Expr::app(lam(type_, bvar(0)), value)
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
fn hole(txn: &mut ElabTxn, s: &str, type_: Expr, kind: MetavarKind) -> MVarId {
    let id = MVarId(name(s));
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
fn identity_equation() -> (ElabTxn, MVarId, Expr, Expr) {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    let x = local(&mut txn, "x", nat());
    let left = Expr::app(Expr::mvar(f.clone()), beta(nat(), x.clone()));
    (txn, f, left, x)
}

#[test]
fn beta_arguments_infer_a_kernel_checked_function_in_both_orientations() {
    for reverse in [false, true] {
        let (mut txn, f, left, right) = identity_equation();
        let environment = txn.env.clone();
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.expression_assignments, vec![f.clone()]);
        assert_eq!(report.kernel_checks, 1);
        assert!(report.residual_metavariables.is_empty());
        assert!(!txn.mvars.get_assigned_expr(&f).unwrap().has_fvar());
        txn.unify(&Expr::app(Expr::mvar(f), number(37)), &number(37), budget())
            .unwrap();
        assert_eq!(txn.env, environment);
    }
}

#[test]
fn normalized_reflexivity_does_not_assign_an_unknown_function() {
    let (mut txn, f, left, x) = identity_equation();
    let before = txn.clone();
    let report = txn
        .unify(&left, &Expr::app(Expr::mvar(f.clone()), x), budget())
        .unwrap();
    assert!(report.expression_assignments.is_empty());
    assert!(report.residual_metavariables.is_empty());
    assert_eq!(report.kernel_checks, 0);
    assert!(!txn.mvars.is_assigned(&f));
    unchanged(&txn, &before);
}

#[test]
fn local_let_arguments_obey_the_callers_zeta_delta_policy() {
    for unfold in [false, true] {
        let mut txn = transaction();
        let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
        let x = local(&mut txn, "x", nat());
        let alias = FVarId(name("alias"));
        txn.lctx
            .add_let(alias.clone(), alias.0.clone(), nat(), x.clone());
        let before = txn.clone();
        let mut limits = budget();
        limits.zeta_delta = unfold;
        let result = txn.unify(
            &Expr::app(Expr::mvar(f.clone()), Expr::fvar(alias)),
            &x,
            limits,
        );
        if unfold {
            let report = result.unwrap();
            assert_eq!(report.kernel_checks, 1);
            txn.unify(&Expr::app(Expr::mvar(f), number(8)), &number(8), budget())
                .unwrap();
        } else {
            assert!(matches!(result, Err(UnificationError::Deferred(_))));
            unchanged(&txn, &before);
        }
    }
}

#[test]
fn dependent_pattern_domains_use_the_normalized_arguments() {
    let mut txn = transaction();
    let f = hole(
        &mut txn,
        "f",
        pi(Expr::sort(Level::one()), pi(bvar(0), bvar(1))),
        MetavarKind::Natural,
    );
    let a = local(&mut txn, "A", Expr::sort(Level::one()));
    let x = local(&mut txn, "x", a.clone());
    let left = app(
        Expr::mvar(f.clone()),
        &[
            beta(Expr::sort(Level::one()), a.clone()),
            beta(a, x.clone()),
        ],
    );
    let report = txn.unify(&left, &x, budget()).unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert!(report.residual_metavariables.is_empty());
    txn.unify(
        &app(Expr::mvar(f), &[nat(), number(19)]),
        &number(19),
        budget(),
    )
    .unwrap();
}

#[test]
fn argument_order_is_preserved_when_rebuilding_the_spine() {
    let mut txn = transaction();
    let f = hole(
        &mut txn,
        "f",
        pi(nat(), pi(nat(), nat())),
        MetavarKind::Natural,
    );
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let report = txn
        .unify(
            &app(
                Expr::mvar(f.clone()),
                &[beta(nat(), x), beta(nat(), y.clone())],
            ),
            &y,
            budget(),
        )
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    txn.unify(
        &app(Expr::mvar(f), &[number(7), number(9)]),
        &number(9),
        budget(),
    )
    .unwrap();
}

#[test]
fn normalization_does_not_turn_duplicate_arguments_into_a_pattern() {
    let mut txn = transaction();
    let f = hole(
        &mut txn,
        "f",
        pi(nat(), pi(nat(), nat())),
        MetavarKind::Natural,
    );
    let x = local(&mut txn, "x", nat());
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &app(Expr::mvar(f), &[beta(nat(), x.clone()), x.clone()]),
            &x,
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn irreducible_nonlocal_arguments_still_defer() {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f), beta(nat(), number(7))),
            &number(7),
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn normalization_does_not_bypass_opaque_holes_or_local_scope() {
    for opaque in [false, true] {
        let mut txn = transaction();
        let kind = if opaque {
            MetavarKind::SyntheticOpaque
        } else {
            MetavarKind::Natural
        };
        let f = hole(&mut txn, "f", pi(nat(), nat()), kind);
        let x = local(&mut txn, "x", nat());
        let y = local(&mut txn, "y", nat());
        let before = txn.clone();
        let right = if opaque { x.clone() } else { y };
        assert!(matches!(
            txn.unify(&Expr::app(Expr::mvar(f), beta(nat(), x)), &right, budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn an_ill_typed_candidate_is_never_published() {
    let (mut txn, _, left, _) = identity_equation();
    let before = txn.clone();
    assert!(
        txn.unify(&left, &Expr::sort(Level::zero()), budget())
            .is_err()
    );
    unchanged(&txn, &before);
}

#[test]
fn normalization_work_is_bounded_and_failure_rolls_back() {
    let (txn, _, left, right) = identity_equation();
    let report = txn.clone().unify(&left, &right, budget()).unwrap();
    for cutoff in [0, 1, report.unifier_steps / 2, report.unifier_steps - 1] {
        let mut work = txn.clone();
        let mut limits = budget();
        limits.max_steps = cutoff;
        assert!(matches!(
            work.unify(&left, &right, limits),
            Err(UnificationError::StepLimit { .. })
        ));
        unchanged(&work, &txn);
    }
    let mut work = txn.clone();
    let mut limits = budget();
    limits.max_visited_nodes = report.visited_nodes - 1;
    assert!(matches!(
        work.unify(&left, &right, limits),
        Err(UnificationError::NodeLimit { .. })
    ));
    unchanged(&work, &txn);
}

#[test]
fn cancellation_never_publishes_a_partially_normalized_assignment() {
    let (txn, _, left, right) = identity_equation();
    let report = txn.clone().unify(&left, &right, budget()).unwrap();
    for cutoff in [1, report.unifier_steps / 2, report.unifier_steps] {
        let mut work = txn.clone();
        let calls = Cell::new(0_u64);
        let cancelled = || {
            calls.set(calls.get() + 1);
            calls.get() >= cutoff
        };
        assert!(matches!(
            work.unify_many_with(&[(left.clone(), right.clone())], budget(), &cancelled),
            Err(UnificationError::Cancelled)
        ));
        unchanged(&work, &txn);
    }
}

#[test]
fn a_late_batch_failure_rolls_back_earlier_normalized_assignments() {
    let (mut txn, _, left, right) = identity_equation();
    let before = txn.clone();
    assert!(
        txn.unify_many_with(&[(left, right), (number(0), number(1))], budget(), &|| {
            false
        },)
            .is_err()
    );
    unchanged(&txn, &before);
}

#[test]
fn successful_existing_patterns_get_first_choice_before_let_unfolding() {
    let mut txn = transaction();
    let f = hole(
        &mut txn,
        "f",
        pi(nat(), pi(nat(), nat())),
        MetavarKind::Natural,
    );
    let x = local(&mut txn, "x", nat());
    let alias = FVarId(name("alias"));
    txn.lctx
        .add_let(alias.clone(), alias.0.clone(), nat(), x.clone());
    // Raw x/alias are distinct and the existing first projection is well-typed.
    // Eager argument normalization would collapse them to x/x and regress this.
    let report = txn
        .unify(
            &app(Expr::mvar(f.clone()), &[x.clone(), Expr::fvar(alias)]),
            &x,
            budget(),
        )
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    txn.unify(
        &app(Expr::mvar(f), &[number(7), number(9)]),
        &number(7),
        budget(),
    )
    .unwrap();
}

fn pruning_equation() -> (ElabTxn, MVarId, Expr, Expr) {
    let mut txn = transaction();
    let f = hole(
        &mut txn,
        "f",
        pi(nat(), pi(nat(), nat())),
        MetavarKind::Natural,
    );
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let z = local(&mut txn, "z", nat());
    let left = app(Expr::mvar(f.clone()), &[beta(nat(), x.clone()), y]);
    let right = app(Expr::mvar(f.clone()), &[x, beta(nat(), z)]);
    (txn, f, left, right)
}

#[test]
fn normalized_same_head_pruning_replays_the_original_equation() {
    for reverse in [false, true] {
        let (mut txn, f, left, right) = pruning_equation();
        let environment = txn.env.clone();
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.expression_assignments, vec![f.clone()]);
        assert_eq!(report.kernel_checks, 1);
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        assert!(!txn.mvars.is_assigned(&residual));
        assert!(txn.mvars.get_decl(&residual).unwrap().lctx.is_empty());
        // The residual is a real outstanding obligation, not an assumed result.
        txn.unify(&Expr::mvar(residual), &lam(nat(), bvar(0)), budget())
            .unwrap();
        txn.unify(&left, &right, budget()).unwrap();
        txn.unify(
            &app(Expr::mvar(f), &[number(23), number(91)]),
            &number(23),
            budget(),
        )
        .unwrap();
        assert_eq!(txn.env, environment);
    }
}

fn distinct_pruning_equation() -> (ElabTxn, MVarId, MVarId, Expr, Expr) {
    let mut txn = transaction();
    let type_ = pi(nat(), pi(nat(), nat()));
    let f = hole(&mut txn, "f", type_.clone(), MetavarKind::Natural);
    let g = hole(&mut txn, "g", type_, MetavarKind::Natural);
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let z = local(&mut txn, "z", nat());
    let left = app(Expr::mvar(f.clone()), &[beta(nat(), x.clone()), y]);
    let right = app(Expr::mvar(g.clone()), &[beta(nat(), z), x]);
    (txn, f, g, left, right)
}

#[test]
fn distinct_heads_share_the_normalized_intersection_in_each_argument_order() {
    for reverse in [false, true] {
        let (mut txn, f, g, left, right) = distinct_pruning_equation();
        let environment = txn.env.clone();
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.kernel_checks, 2);
        assert_eq!(report.expression_assignments.len(), 2);
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        assert!(!txn.mvars.is_assigned(&residual));
        assert!(txn.mvars.get_decl(&residual).unwrap().lctx.is_empty());
        txn.unify(&Expr::mvar(residual), &lam(nat(), bvar(0)), budget())
            .unwrap();
        txn.unify(
            &app(Expr::mvar(f), &[number(7), number(9)]),
            &number(7),
            budget(),
        )
        .unwrap();
        txn.unify(
            &app(Expr::mvar(g), &[number(9), number(7)]),
            &number(7),
            budget(),
        )
        .unwrap();
        txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(txn.env, environment);
    }
}

#[test]
fn normalized_dependent_pruning_does_not_invent_an_inhabitant() {
    let mut txn = transaction();
    let f = hole(
        &mut txn,
        "f",
        pi(Expr::sort(Level::one()), pi(bvar(0), bvar(1))),
        MetavarKind::Natural,
    );
    let a = local(&mut txn, "A", Expr::sort(Level::one()));
    let x = local(&mut txn, "x", a.clone());
    let y = local(&mut txn, "y", a.clone());
    let report = txn
        .unify(
            &app(
                Expr::mvar(f.clone()),
                &[
                    beta(Expr::sort(Level::one()), a.clone()),
                    beta(a.clone(), x),
                ],
            ),
            &app(Expr::mvar(f), &[a, y]),
            budget(),
        )
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(report.residual_metavariables.len(), 1);
    let residual = report.residual_metavariables[0].clone();
    assert!(!txn.mvars.is_assigned(&residual));
    let declaration = txn.mvars.get_decl(&residual).unwrap();
    let ExprNode::ForallE {
        binder_type, body, ..
    } = declaration.type_.node()
    else {
        panic!("expected an explicitly quantified dependent obligation");
    };
    assert_eq!(binder_type, &Expr::sort(Level::one()));
    assert_eq!(body, &bvar(0));
    let before = txn.clone();
    assert!(
        txn.unify(
            &Expr::mvar(residual),
            &lam(Expr::sort(Level::one()), number(0)),
            budget(),
        )
        .is_err()
    );
    unchanged(&txn, &before);
}

#[test]
fn normalization_never_assumes_an_unknown_function_is_injective() {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()), MetavarKind::Natural);
    let a = hole(&mut txn, "a", nat(), MetavarKind::Natural);
    let b = hole(&mut txn, "b", nat(), MetavarKind::Natural);
    let left = Expr::app(Expr::mvar(f.clone()), beta(nat(), Expr::mvar(a.clone())));
    let right = Expr::app(Expr::mvar(f.clone()), Expr::mvar(b.clone()));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&left, &right, budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
    let report = txn
        .unify_many_with(
            &[
                (left, right),
                (Expr::mvar(f.clone()), lam(nat(), number(0))),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.expression_assignments, vec![f]);
    assert!(!txn.mvars.is_assigned(&a));
    assert!(!txn.mvars.is_assigned(&b));
}

#[test]
fn pruning_assignment_limits_do_not_leak_a_shared_residual() {
    let (mut txn, _, _, left, right) = distinct_pruning_equation();
    let before = txn.clone();
    let mut limits = budget();
    limits.max_assignments = 1;
    assert!(matches!(
        txn.unify(&left, &right, limits),
        Err(UnificationError::AssignmentLimit { .. })
    ));
    unchanged(&txn, &before);
}

#[test]
fn a_late_failure_discards_the_residual_and_both_parent_assignments() {
    let (mut txn, _, _, left, right) = distinct_pruning_equation();
    let before = txn.clone();
    assert!(
        txn.unify_many_with(&[(left, right), (number(0), number(1))], budget(), &|| {
            false
        },)
            .is_err()
    );
    unchanged(&txn, &before);
}
