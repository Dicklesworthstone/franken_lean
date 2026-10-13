//! Captured-context higher-order pruning uses the real transaction and K1.
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
fn equation() -> (ElabTxn, MVarId, Expr, Expr) {
    let mut txn = transaction();
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let z = local(&mut txn, "z", nat());
    let f = hole(&mut txn, "f", pi(nat(), pi(nat(), nat())));
    let left = app(Expr::mvar(f.clone()), &[x.clone(), y]);
    let right = app(Expr::mvar(f.clone()), &[x, z]);
    (txn, f, left, right)
}

#[test]
fn captured_argument_pruning_retains_formal_positions_not_captured_values() {
    for reverse in [false, true] {
        let (mut txn, f, left, right) = equation();
        let before = txn.clone();
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.expression_assignments, vec![f.clone()]);
        assert!(report.kernel_checks >= 2);
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        let declaration = txn.mvars.get_decl(&residual).unwrap();
        assert_eq!(declaration.type_, pi(nat(), nat()));
        assert_eq!(declaration.lctx, before.lctx);
        assert!(!txn.mvars.is_assigned(&residual));
        assert_eq!(txn.mvars.len(), before.mvars.len() + 1);
        assert_eq!(txn.env, before.env);
        assert_eq!(txn.lctx, before.lctx);
        txn.unify(&Expr::mvar(residual), &lam(nat(), bvar(0)), budget())
            .unwrap();
        // A fresh argument must be returned, not the captured local named x.
        txn.unify(
            &app(Expr::mvar(f), &[number(23), number(71)]),
            &number(23),
            budget(),
        )
        .unwrap();
    }
}

#[test]
fn a_captured_and_a_later_argument_can_be_pruned_to_one_obligation() {
    let mut txn = transaction();
    let x = local(&mut txn, "x", nat());
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let captured_context = txn.lctx.clone();
    let y = local(&mut txn, "y", nat());
    let left = Expr::app(Expr::mvar(f.clone()), x);
    let right = Expr::app(Expr::mvar(f), y);
    let report = txn.unify(&left, &right, budget()).unwrap();
    assert_eq!(report.residual_metavariables.len(), 1);
    let residual = report.residual_metavariables[0].clone();
    let declaration = txn.mvars.get_decl(&residual).unwrap();
    assert_eq!(declaration.type_, nat());
    assert_eq!(declaration.lctx, captured_context);
    txn.unify(&Expr::mvar(residual), &number(37), budget())
        .unwrap();
    txn.unify(&left, &number(37), budget()).unwrap();
    txn.unify(&right, &number(37), budget()).unwrap();
}

#[test]
fn independent_captured_types_remain_available_to_the_residual() {
    let mut txn = transaction();
    let a = local(&mut txn, "A", Expr::sort(Level::one()));
    let x = local(&mut txn, "x", a.clone());
    let y = local(&mut txn, "y", a.clone());
    let f = hole(&mut txn, "f", pi(a.clone(), a.clone()));
    let before = txn.clone();
    let report = txn
        .unify(
            &Expr::app(Expr::mvar(f.clone()), x.clone()),
            &Expr::app(Expr::mvar(f.clone()), y.clone()),
            budget(),
        )
        .unwrap();
    assert_eq!(report.residual_metavariables.len(), 1);
    let residual = report.residual_metavariables[0].clone();
    let declaration = txn.mvars.get_decl(&residual).unwrap();
    assert_eq!(declaration.type_, a);
    assert_eq!(declaration.lctx, before.lctx);
    // Captures stay accessible as captures: h := x gives a constant function.
    txn.unify(&Expr::mvar(residual), &x, budget()).unwrap();
    txn.unify(&Expr::app(Expr::mvar(f), y), &x, budget())
        .unwrap();
    assert_eq!(txn.env, before.env);
}

#[test]
fn dependent_formal_parameters_work_when_the_signature_does_not_capture_them() {
    let mut txn = transaction();
    let a = local(&mut txn, "A", Expr::sort(Level::one()));
    let x = local(&mut txn, "x", a.clone());
    let y = local(&mut txn, "y", a.clone());
    let f = hole(
        &mut txn,
        "f",
        pi(Expr::sort(Level::one()), pi(bvar(0), bvar(1))),
    );
    let report = txn
        .unify(
            &app(Expr::mvar(f.clone()), &[a.clone(), x]),
            &app(Expr::mvar(f), &[a, y]),
            budget(),
        )
        .unwrap();
    assert!(report.kernel_checks >= 2);
    assert_eq!(report.residual_metavariables.len(), 1);
    let residual = &report.residual_metavariables[0];
    let ExprNode::ForallE {
        binder_type, body, ..
    } = txn.mvars.get_decl(residual).unwrap().type_.node()
    else {
        panic!("the shared type argument must remain a formal parameter");
    };
    assert_eq!(binder_type, &Expr::sort(Level::one()));
    assert_eq!(body, &bvar(0));
    // This type need not be inhabited. The solver must not invent its value.
    assert!(!txn.mvars.is_assigned(residual));
}

#[test]
fn different_heads_keep_only_their_common_captured_context() {
    for reverse in [false, true] {
        let mut txn = transaction();
        let g = hole(&mut txn, "g", pi(nat(), nat()));
        let x = local(&mut txn, "x", nat());
        let f = hole(&mut txn, "f", pi(nat(), nat()));
        let y = local(&mut txn, "y", nat());
        let left = Expr::app(Expr::mvar(f.clone()), x);
        let right = Expr::app(Expr::mvar(g.clone()), y);
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let before_env = txn.env.clone();
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert!(report.expression_assignments.contains(&f));
        assert!(report.expression_assignments.contains(&g));
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        let declaration = txn.mvars.get_decl(&residual).unwrap();
        assert!(declaration.lctx.is_empty());
        assert_eq!(declaration.type_, nat());
        txn.unify(&Expr::mvar(residual), &number(17), budget())
            .unwrap();
        txn.unify(&left, &number(17), budget()).unwrap();
        txn.unify(&right, &number(17), budget()).unwrap();
        assert_eq!(txn.env, before_env);
    }
}

#[test]
fn a_direct_captured_result_dependency_is_not_rebound_as_a_formal() {
    let mut txn = transaction();
    let predicate = local(&mut txn, "P", pi(nat(), Expr::sort(Level::one())));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let f = hole(&mut txn, "f", pi(nat(), Expr::app(predicate, x.clone())));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f.clone()), x),
            &Expr::app(Expr::mvar(f), y),
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn a_local_alias_cannot_hide_a_captured_signature_dependency() {
    let mut txn = transaction();
    let predicate = local(&mut txn, "P", pi(nat(), Expr::sort(Level::one())));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let alias = FVarId(name("R"));
    txn.lctx.add_let(
        alias.clone(),
        alias.0.clone(),
        Expr::sort(Level::one()),
        Expr::app(predicate, x.clone()),
    );
    let f = hole(&mut txn, "f", pi(nat(), Expr::fvar(alias)));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f.clone()), x),
            &Expr::app(Expr::mvar(f), y),
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn unresolved_signature_holes_do_not_gain_an_assumed_capture_policy() {
    let mut txn = transaction();
    let ty = hole(&mut txn, "T", Expr::sort(Level::one()));
    let x = local(&mut txn, "x", Expr::mvar(ty.clone()));
    let y = local(&mut txn, "y", Expr::mvar(ty.clone()));
    let f = hole(&mut txn, "f", pi(Expr::mvar(ty.clone()), nat()));
    let left = Expr::app(Expr::mvar(f.clone()), x);
    let right = Expr::app(Expr::mvar(f), y);
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&left, &right, budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
    txn.unify(&Expr::mvar(ty), &nat(), budget()).unwrap();
    let report = txn.unify(&left, &right, budget()).unwrap();
    assert_eq!(report.residual_metavariables.len(), 1);
    assert!(!txn.mvars.is_assigned(&report.residual_metavariables[0]));
}

#[test]
fn pruning_cannot_erase_ill_typed_captured_arguments() {
    for reverse in [false, true] {
        let mut txn = transaction();
        let x = local(&mut txn, "x", Expr::sort(Level::one()));
        let y = local(&mut txn, "y", Expr::sort(Level::one()));
        let f = hole(&mut txn, "f", pi(nat(), nat()));
        let left = Expr::app(Expr::mvar(f.clone()), x);
        let right = Expr::app(Expr::mvar(f), y);
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
fn a_propositional_residual_remains_an_unproved_obligation() {
    let mut txn = transaction();
    let proposition = local(&mut txn, "P", Expr::sort(Level::zero()));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let f = hole(&mut txn, "f", pi(nat(), proposition.clone()));
    let mut limits = budget();
    // Exercise pruning, not the separate proof-irrelevance conversion shortcut.
    limits.proof_irrelevance = false;
    let report = txn
        .unify(
            &Expr::app(Expr::mvar(f.clone()), x),
            &Expr::app(Expr::mvar(f), y),
            limits,
        )
        .unwrap();
    assert_eq!(report.residual_metavariables.len(), 1);
    let residual = report.residual_metavariables[0].clone();
    assert_eq!(txn.mvars.get_decl(&residual).unwrap().type_, proposition);
    assert!(!txn.mvars.is_assigned(&residual));
    let before = txn.clone();
    assert!(
        txn.unify(&Expr::mvar(residual), &number(0), limits)
            .is_err()
    );
    unchanged(&txn, &before);
}

#[test]
fn cancellation_at_every_captured_pruning_checkpoint_is_atomic() {
    let (initial, _, left, right) = equation();
    let mut count = initial.clone();
    let polls = Cell::new(0);
    count
        .unify_many_with(&[(left.clone(), right.clone())], budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    assert!(polls.get() > 0);
    for stop_at in 1..=polls.get() {
        let mut txn = initial.clone();
        let before = txn.clone();
        let current = Cell::new(0);
        let result = txn.unify_many_with(&[(left.clone(), right.clone())], budget(), &|| {
            current.set(current.get() + 1);
            current.get() == stop_at
        });
        assert!(
            matches!(result, Err(UnificationError::Cancelled)),
            "checkpoint {stop_at}"
        );
        unchanged(&txn, &before);
    }
}

#[test]
fn exhausted_captured_pruning_budgets_do_not_publish_residuals() {
    let (initial, _, left, right) = equation();
    let mut measured = initial.clone();
    let report = measured.unify(&left, &right, budget()).unwrap();
    let mut work = budget();
    work.max_steps = report.unifier_steps.saturating_sub(1);
    let mut nodes = budget();
    nodes.max_visited_nodes = report.visited_nodes.saturating_sub(1);
    let mut assignments = budget();
    assignments.max_assignments = 0;
    for limits in [work, nodes, assignments] {
        let mut txn = initial.clone();
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&left, &right, limits),
            Err(UnificationError::StepLimit { .. }
                | UnificationError::NodeLimit { .. }
                | UnificationError::AssignmentLimit { .. })
        ));
        unchanged(&txn, &before);
        assert!(txn.unify(&left, &right, budget()).is_ok());
    }
}

#[test]
fn an_equal_identifier_does_not_license_a_rebound_captured_local() {
    let mut txn = transaction();
    let x = local(&mut txn, "x", nat());
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    // The type is intentionally unchanged: original-spine typing alone would
    // not detect that this is no longer the parent's exact lexical binding.
    txn.lctx = fln_elab::lctx::LocalContext::new();
    txn.lctx.add_param(
        FVarId(name("x")),
        name("rebound_x"),
        nat(),
        BinderInfo::Default,
    );
    let y = local(&mut txn, "y", nat());
    let before = txn.clone();
    let outcome = txn.unify(
        &Expr::app(Expr::mvar(f.clone()), x),
        &Expr::app(Expr::mvar(f), y),
        budget(),
    );
    assert!(matches!(outcome, Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn completed_type_assignments_cannot_hide_captured_dependencies() {
    let mut txn = transaction();
    let predicate = local(&mut txn, "P", pi(nat(), Expr::sort(Level::one())));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let ty = hole(&mut txn, "T", Expr::sort(Level::one()));
    let f = hole(&mut txn, "f", pi(nat(), Expr::mvar(ty.clone())));
    txn.unify(&Expr::mvar(ty), &Expr::app(predicate, x.clone()), budget())
        .unwrap();
    let before = txn.clone();
    let outcome = txn.unify(
        &Expr::app(Expr::mvar(f.clone()), x),
        &Expr::app(Expr::mvar(f), y),
        budget(),
    );
    assert!(matches!(outcome, Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}
