//! Native higher-order pattern pruning, not an oracle or a mock solver.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::ConstraintKind;
use fln_elab::constraint::unify::{UnificationBudget, UnificationDeferred, UnificationError};
use fln_elab::mvar::MetavarKind;
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::Budget;
use std::cell::Cell;

fn name(s: &str) -> Name { Name::from_components([s]) }
fn nat() -> Expr { Expr::const_(name("Nat"), Vec::new()) }
fn number(n: u64) -> Expr { Expr::lit(Literal::Nat(NatLit::from_u64(n))) }
fn bvar(n: u32) -> Expr { Expr::bvar(n).unwrap() }
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
    ElabTxn::new(bootstrap_nat_environment(budget().kernel).unwrap(), KVMap::new(), 17)
}
fn hole(txn: &mut ElabTxn, s: &str, type_: Expr, kind: MetavarKind, depth: u32) -> MVarId {
    let id = MVarId(name(s));
    txn.mvars.declare(id.clone(), id.0.clone(), type_, txn.lctx.clone(), kind, depth, None);
    id
}
fn natural(txn: &mut ElabTxn, s: &str, type_: Expr) -> MVarId {
    hole(txn, s, type_, MetavarKind::Natural, 0)
}
fn local(txn: &mut ElabTxn, s: &str, type_: Expr) -> Expr {
    let id = FVarId(name(s));
    txn.lctx.add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn unchanged(txn: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = txn.budget.heartbeats_consumed;
    assert_eq!(txn, &expected);
}
fn equation() -> (ElabTxn, MVarId, Expr, Expr) {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(nat(), pi(nat(), nat())));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let z = local(&mut txn, "z", nat());
    let left = app(Expr::mvar(f.clone()), &[x.clone(), y]);
    let right = app(Expr::mvar(f.clone()), &[x, z]);
    (txn, f, left, right)
}

#[test]
fn same_head_keeps_only_agreeing_positions_and_reports_the_typed_residual() {
    for reverse in [false, true] {
        let (mut txn, f, left, right) = equation();
        let before_env = txn.env.clone();
        let (left, right) = if reverse { (right, left) } else { (left, right) };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.expression_assignments, vec![f.clone()]);
        assert_eq!(report.kernel_checks, 1);
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        let declaration = txn.mvars.get_decl(&residual).unwrap();
        assert_eq!(declaration.type_, pi(nat(), nat()));
        assert!(declaration.lctx.is_empty());
        assert!(!txn.mvars.is_assigned(&residual));
        assert_eq!(txn.mvars.len(), 2);
        assert!(!txn.mvars.get_assigned_expr(&f).unwrap().has_fvar());
        assert_eq!(txn.env, before_env);
        // A later batch solves the residual, not a silently assumed result.
        txn.unify(&Expr::mvar(residual), &lam(nat(), bvar(0)), budget()).unwrap();
        txn.unify(&app(Expr::mvar(f), &[number(7), number(99)]), &number(7), budget()).unwrap();
        assert_eq!(txn.env, before_env);
    }
}

#[test]
fn middle_positions_survive_a_nontrivial_permutation() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(nat(), pi(nat(), pi(nat(), nat()))));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let z = local(&mut txn, "z", nat());
    let report = txn.unify(
        &app(Expr::mvar(f.clone()), &[x.clone(), y.clone(), z.clone()]),
        &app(Expr::mvar(f.clone()), &[z, y, x]), budget(),
    ).unwrap();
    let residual = report.residual_metavariables[0].clone();
    txn.unify(&Expr::mvar(residual), &lam(nat(), bvar(0)), budget()).unwrap();
    txn.unify(&app(Expr::mvar(f), &[number(1), number(2), number(3)]), &number(2), budget()).unwrap();
}

#[test]
fn dependent_results_keep_their_type_parameter_without_inventing_an_inhabitant() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(Expr::sort(Level::one()), pi(bvar(0), bvar(1))));
    let a = local(&mut txn, "A", Expr::sort(Level::one()));
    let x = local(&mut txn, "x", a.clone());
    let y = local(&mut txn, "y", a.clone());
    let report = txn.unify(
        &app(Expr::mvar(f.clone()), &[a.clone(), x]),
        &app(Expr::mvar(f), &[a, y]), budget(),
    ).unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(report.residual_metavariables.len(), 1);
    let id = &report.residual_metavariables[0];
    let ExprNode::ForallE { binder_type, body, .. } = txn.mvars.get_decl(id).unwrap().type_.node() else {
        panic!("expected a retained dependent telescope");
    };
    assert_eq!(binder_type, &Expr::sort(Level::one()));
    assert_eq!(body, &bvar(0));
    assert!(!txn.mvars.is_assigned(id));
}

#[test]
fn pruning_works_below_binders_opened_by_the_equation_worklist() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(nat(), nat()));
    let left = lam(nat(), lam(nat(), Expr::app(Expr::mvar(f.clone()), bvar(1))));
    let right = lam(nat(), lam(nat(), Expr::app(Expr::mvar(f.clone()), bvar(0))));
    let report = txn.unify(&left, &right, budget()).unwrap();
    assert_eq!(report.residual_metavariables.len(), 1);
    let id = &report.residual_metavariables[0];
    assert_eq!(txn.mvars.get_decl(id).unwrap().type_, nat());
    assert!(txn.lctx.is_empty());
    assert!(!txn.mvars.get_assigned_expr(&f).unwrap().has_fvar());
}

#[test]
fn ordinary_batch_assignments_take_precedence_over_residual_creation() {
    let (mut txn, f, left, right) = equation();
    let value = lam(nat(), lam(nat(), number(11)));
    let report = txn.unify_many_with(
        &[(left, right), (Expr::mvar(f.clone()), value)], budget(), &|| false,
    ).unwrap();
    assert_eq!(report.expression_assignments, vec![f]);
    assert!(report.residual_metavariables.is_empty());
    assert_eq!(txn.mvars.len(), 1);
}

#[test]
fn dependent_domain_and_result_escapes_defer_without_creating_holes() {
    for dependent_result in [false, true] {
        let mut txn = transaction();
        let type_ = if dependent_result {
            pi(Expr::sort(Level::one()), bvar(0))
        } else {
            pi(Expr::sort(Level::one()), pi(bvar(0), nat()))
        };
        let f = natural(&mut txn, "f", type_);
        let a = local(&mut txn, "A", Expr::sort(Level::one()));
        let b = local(&mut txn, "B", Expr::sort(Level::one()));
        let x = local(&mut txn, "x", a.clone());
        let mut left = Expr::app(Expr::mvar(f.clone()), a);
        let mut right = Expr::app(Expr::mvar(f), b);
        if !dependent_result {
            left = Expr::app(left, x.clone());
            right = Expr::app(right, x);
        }
        let before = txn.clone();
        assert!(matches!(txn.unify(&left, &right, budget()), Err(UnificationError::Deferred(_))));
        unchanged(&txn, &before);
    }
}

#[test]
fn captured_arguments_and_opaque_or_deeper_holes_remain_deferred() {
    for case in 0..3 {
        let mut txn = transaction();
        let early_x = (case == 0).then(|| local(&mut txn, "x", nat()));
        let kind = if case == 1 { MetavarKind::SyntheticOpaque } else { MetavarKind::Natural };
        let depth = if case == 2 { 1 } else { 0 };
        let f = hole(&mut txn, "f", pi(nat(), nat()), kind, depth);
        let x = early_x.unwrap_or_else(|| local(&mut txn, "x", nat()));
        let y = local(&mut txn, "y", nat());
        let before = txn.clone();
        assert!(matches!(txn.unify(
            &Expr::app(Expr::mvar(f.clone()), x),
            &Expr::app(Expr::mvar(f), y), budget(),
        ), Err(UnificationError::Deferred(_))));
        unchanged(&txn, &before);
    }
}

#[test]
fn repeated_and_nonlocal_arguments_do_not_enter_the_pattern_fragment() {
    for repeat in [false, true] {
        let mut txn = transaction();
        let f = natural(&mut txn, "f", pi(nat(), pi(nat(), nat())));
        let x = local(&mut txn, "x", nat());
        let y = local(&mut txn, "y", nat());
        let left_args = if repeat { vec![x.clone(), x.clone()] } else { vec![x.clone(), number(0)] };
        let right_args = if repeat { vec![y.clone(), y] } else { vec![x, number(1)] };
        let before = txn.clone();
        assert!(matches!(txn.unify(
            &app(Expr::mvar(f.clone()), &left_args),
            &app(Expr::mvar(f), &right_args), budget(),
        ), Err(UnificationError::Deferred(_))));
        unchanged(&txn, &before);
    }
}

#[test]
fn queued_obligations_retain_residuals_instead_of_misreporting_complete_proofs() {
    let (mut txn, f, lhs, rhs) = equation();
    let selected = txn.postpone(ConstraintKind::DefEq { lhs, rhs }, 0);
    let waiting = txn.postpone(ConstraintKind::HasType { expr: Expr::mvar(f), expected_type: pi(nat(), pi(nat(), nat())) }, 0);
    let report = txn.solve_defeq_constraints_with(&[selected, selected], budget(), &|| false).unwrap();
    assert_eq!(report.solved, vec![selected]);
    assert_eq!(report.unification.residual_metavariables.len(), 1);
    assert_eq!(report.unification.awakened.len(), 1);
    assert_eq!(report.unification.awakened[0].id, waiting);
    assert!(matches!(report.unification.awakened[0].kind, ConstraintKind::HasType { .. }));
}

#[test]
fn generated_identity_cannot_capture_unknown_queue_or_expression_holes() {
    for in_queue in [false, true] {
        let (mut txn, _, left, right) = equation();
        let unknown = MVarId(Name::from_components(["_fln_unify_pruned", "0"]));
        let mut equations = vec![(left, right)];
        if in_queue {
            txn.postpone(ConstraintKind::SynthInstance { class: nat(), mvar: unknown.clone() }, 0);
        } else {
            // A reflexive unknown is still an existing identity, even though
            // the ordinary syntactic fast path need not inspect its declaration.
            equations.push((Expr::mvar(unknown.clone()), Expr::mvar(unknown.clone())));
        }
        let report = txn.unify_many_with(&equations, budget(), &|| false).unwrap();
        assert_eq!(report.residual_metavariables.len(), 1);
        assert_ne!(report.residual_metavariables[0], unknown);
        assert!(!txn.mvars.is_declared(&unknown));
    }
}

#[test]
fn resource_and_cancellation_stops_publish_neither_assignment_nor_residual() {
    let (base, _, left, right) = equation();
    let equations = vec![(left, right)];
    let polls = Cell::new(0usize);
    base.clone().unify_many_with(&equations, budget(), &|| {
        polls.set(polls.get() + 1);
        false
    }).unwrap();
    let total = polls.get();
    for stop in [0, total / 2, total - 1] {
        let mut txn = base.clone();
        let calls = Cell::new(0usize);
        assert!(matches!(txn.unify_many_with(&equations, budget(), &|| {
            let n = calls.get();
            calls.set(n + 1);
            n >= stop
        }), Err(UnificationError::Cancelled)));
        unchanged(&txn, &base);
    }
    let mut txn = base.clone();
    let mut limits = budget();
    limits.max_assignments = 0;
    assert!(matches!(txn.unify_many_with(&equations, limits, &|| false), Err(UnificationError::AssignmentLimit { limit: 0 })));
    unchanged(&txn, &base);
    txn.unify_many_with(&equations, budget(), &|| false).unwrap();
}

#[test]
fn the_kernel_can_stop_residual_validation_without_publishing_any_state() {
    let (mut txn, _, left, right) = equation();
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
fn a_late_unsolved_equation_rolls_back_pruning_and_can_be_retried() {
    let (mut txn, _, left, right) = equation();
    let before = txn.clone();
    assert!(matches!(txn.unify_many_with(
        &[(left.clone(), right.clone()), (number(0), number(1))], budget(), &|| false,
    ), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
    txn.unify(&left, &right, budget()).unwrap();
}

#[test]
fn a_residual_assignment_remains_a_lambda_with_no_escaped_binders() {
    let (mut txn, f, left, right) = equation();
    txn.unify(&left, &right, budget()).unwrap();
    let assignment = txn.mvars.get_assigned_expr(&f).unwrap();
    assert!(matches!(assignment.node(), ExprNode::Lam { .. }));
    assert!(!assignment.has_fvar());
    assert!(!assignment.has_loose_bvars());
    assert!(assignment.has_expr_mvar());
}


#[test]
fn late_native_step_and_node_stops_roll_back_the_created_residual() {
    let (base, _, left, right) = equation();
    let report = base.clone().unify(&left, &right, budget()).unwrap();
    assert!(report.unifier_steps > 1 && report.visited_nodes > 1);
    let mut txn = base.clone();
    let mut limits = budget();
    limits.max_steps = report.unifier_steps - 1;
    assert!(matches!(txn.unify(&left, &right, limits),
        Err(UnificationError::StepLimit { .. })
    ));
    unchanged(&txn, &base);
    let mut txn = base.clone();
    let mut limits = budget();
    limits.max_visited_nodes = report.visited_nodes - 1;
    assert!(matches!(txn.unify(&left, &right, limits),
        Err(UnificationError::NodeLimit { .. })
    ));
    unchanged(&txn, &base);
    txn.unify(&left, &right, budget()).unwrap();
}


#[test]
fn a_retained_dependent_binder_keeps_its_domain_and_can_be_solved_later() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(Expr::sort(Level::one()), pi(bvar(0), pi(nat(), bvar(2)))));
    let a = local(&mut txn, "A", Expr::sort(Level::one()));
    let x = local(&mut txn, "x", a.clone());
    let n = local(&mut txn, "n", nat());
    let m = local(&mut txn, "m", nat());
    let report = txn.unify(
        &app(Expr::mvar(f.clone()), &[a.clone(), x.clone(), n]),
        &app(Expr::mvar(f.clone()), &[a, x, m]), budget(),
    ).unwrap();
    assert_eq!(report.residual_metavariables.len(), 1);
    let residual = report.residual_metavariables[0].clone();
    let value = lam(Expr::sort(Level::one()), lam(bvar(0), bvar(0)));
    txn.unify(&Expr::mvar(residual), &value, budget()).unwrap();
    txn.unify(&app(Expr::mvar(f), &[nat(), number(5), number(99)]), &number(5), budget()).unwrap();
}

fn curried(arity: usize) -> Expr {
    (0..arity).fold(nat(), |body, _| pi(nat(), body))
}
fn distinct_equation() -> (ElabTxn, MVarId, MVarId, Expr, Expr) {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", curried(2));
    let g = natural(&mut txn, "g", curried(2));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let z = local(&mut txn, "z", nat());
    let left = app(Expr::mvar(f.clone()), &[x, y.clone()]);
    let right = app(Expr::mvar(g.clone()), &[y, z]);
    (txn, f, g, left, right)
}

#[test]
fn distinct_heads_share_one_typed_residual_and_check_both_assignments() {
    for reverse in [false, true] {
        let (mut txn, f, g, left, right) = distinct_equation();
        let env = txn.env.clone();
        let (left, right) = if reverse { (right, left) } else { (left, right) };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.kernel_checks, 2);
        assert_eq!(report.expression_assignments.len(), 2);
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        assert!(!txn.mvars.is_assigned(&residual));
        assert_eq!(txn.mvars.len(), 3);
        txn.unify(&Expr::mvar(residual), &lam(nat(), bvar(0)), budget()).unwrap();
        txn.unify(&app(Expr::mvar(f), &[number(4), number(5)]), &number(5), budget()).unwrap();
        txn.unify(&app(Expr::mvar(g), &[number(5), number(6)]), &number(5), budget()).unwrap();
        assert_eq!(txn.env, env);
    }
}

#[test]
fn distinct_arities_and_permuted_intersections_rebind_each_function_separately() {
    for reverse in [false, true] {
        let mut txn = transaction();
        let f = natural(&mut txn, "f", curried(4));
        let g = natural(&mut txn, "g", curried(3));
        let x = local(&mut txn, "x", nat());
        let y = local(&mut txn, "y", nat());
        let z = local(&mut txn, "z", nat());
        let w = local(&mut txn, "w", nat());
        let v = local(&mut txn, "v", nat());
        let left = app(Expr::mvar(f.clone()), &[x.clone(), y, z.clone(), w]);
        let right = app(Expr::mvar(g.clone()), &[z, x, v]);
        let (left, right) = if reverse { (right, left) } else { (left, right) };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.kernel_checks, 2);
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        txn.unify(&Expr::mvar(residual), &lam(nat(), lam(nat(), bvar(1))), budget()).unwrap();
        let expected = if reverse { number(12) } else { number(10) };
        txn.unify(&app(Expr::mvar(f), &[number(10), number(11), number(12), number(13)]), &expected, budget()).unwrap();
        txn.unify(&app(Expr::mvar(g), &[number(12), number(10), number(14)]), &expected, budget()).unwrap();
    }
}

#[test]
fn disjoint_arguments_leave_a_shared_unsolved_value_not_a_guessed_constant() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", curried(1));
    let g = natural(&mut txn, "g", curried(1));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let report = txn.unify(
        &Expr::app(Expr::mvar(f.clone()), x),
        &Expr::app(Expr::mvar(g.clone()), y), budget(),
    ).unwrap();
    let residual = report.residual_metavariables[0].clone();
    assert_eq!(txn.mvars.get_decl(&residual).unwrap().type_, nat());
    assert!(!txn.mvars.is_assigned(&residual));
    txn.unify(&Expr::mvar(residual), &number(29), budget()).unwrap();
    txn.unify(&Expr::app(Expr::mvar(f), number(7)), &number(29), budget()).unwrap();
    txn.unify(&Expr::app(Expr::mvar(g), number(9)), &number(29), budget()).unwrap();
}

#[test]
fn subsequent_equations_can_prune_the_shared_residual_again() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", curried(2));
    let g = natural(&mut txn, "g", curried(2));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let z = local(&mut txn, "z", nat());
    let report = txn.unify_many_with(&[
        (app(Expr::mvar(f.clone()), &[x.clone(), y.clone()]), app(Expr::mvar(g.clone()), &[y.clone(), z.clone()])),
        (app(Expr::mvar(f.clone()), &[x.clone(), z]), app(Expr::mvar(g.clone()), &[y, x])),
    ], budget(), &|| false).unwrap();
    assert_eq!(report.expression_assignments.len(), 3);
    assert_eq!(report.kernel_checks, 3);
    assert_eq!(report.residual_metavariables.len(), 1);
    let residual = report.residual_metavariables[0].clone();
    assert_eq!(txn.mvars.get_decl(&residual).unwrap().type_, nat());
    txn.unify(&Expr::mvar(residual), &number(13), budget()).unwrap();
    txn.unify(&app(Expr::mvar(f), &[number(1), number(2)]), &number(13), budget()).unwrap();
    txn.unify(&app(Expr::mvar(g), &[number(3), number(4)]), &number(13), budget()).unwrap();
}

#[test]
fn different_captured_contexts_are_not_silently_merged() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", curried(1));
    local(&mut txn, "capture", nat());
    let g = natural(&mut txn, "g", curried(1));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let before = txn.clone();
    assert!(matches!(txn.unify(
        &Expr::app(Expr::mvar(f), x), &Expr::app(Expr::mvar(g), y), budget(),
    ), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn the_assignment_limit_covers_both_sides_before_creating_the_shared_hole() {
    let (mut txn, _, _, left, right) = distinct_equation();
    let before = txn.clone();
    let mut limits = budget();
    limits.max_assignments = 1;
    assert!(matches!(txn.unify(&left, &right, limits), Err(UnificationError::AssignmentLimit { limit: 1 })));
    unchanged(&txn, &before);
    txn.unify(&left, &right, budget()).unwrap();
}

#[test]
fn a_kernel_veto_on_the_second_assignment_cannot_publish_the_first_one() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", curried(1));
    let g = natural(&mut txn, "g", pi(Expr::const_(name("UnknownDomain"), Vec::new()), nat()));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let before = txn.clone();
    let error = txn.unify(
        &Expr::app(Expr::mvar(f), x), &Expr::app(Expr::mvar(g.clone()), y), budget(),
    ).unwrap_err();
    assert!(matches!(error,
        UnificationError::Deferred(UnificationDeferred::UnresolvedAssignmentType(id)) if id == g
    ));
    unchanged(&txn, &before);
}

#[test]
fn an_opaque_second_head_cannot_become_a_shared_natural_hole() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", curried(1));
    let g = hole(&mut txn, "g", curried(1), MetavarKind::SyntheticOpaque, 0);
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let before = txn.clone();
    assert!(matches!(txn.unify(
        &Expr::app(Expr::mvar(f), x), &Expr::app(Expr::mvar(g), y), budget(),
    ), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn identical_inputs_generate_identical_residual_identities_and_assignments() {
    let mut snapshots = Vec::new();
    for _ in 0..8 {
        let (mut txn, _, _, left, right) = distinct_equation();
        let report = txn.unify(&left, &right, budget()).unwrap();
        snapshots.push((txn.mvars, report.expression_assignments, report.residual_metavariables));
    }
    assert!(snapshots.windows(2).all(|pair| pair[0] == pair[1]));
}

#[test]
fn shared_residual_depth_preserves_the_stricter_parent_scope() {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", curried(2), MetavarKind::Natural, 1);
    let g = natural(&mut txn, "g", curried(2));
    let x = local(&mut txn, "x", nat());
    let y = local(&mut txn, "y", nat());
    let z = local(&mut txn, "z", nat());
    let mut limits = budget();
    limits.max_metavar_depth = 1;
    let report = txn.unify(
        &app(Expr::mvar(f), &[x, y.clone()]),
        &app(Expr::mvar(g), &[y, z]), limits,
    ).unwrap();
    let residual = report.residual_metavariables[0].clone();
    assert_eq!(txn.mvars.get_decl(&residual).unwrap().depth, 1);
    let before = txn.clone();
    assert!(matches!(txn.unify(&Expr::mvar(residual.clone()), &lam(nat(), bvar(0)), budget()),
        Err(UnificationError::Deferred(UnificationDeferred::MetavariableDepth(_)))
    ));
    unchanged(&txn, &before);
    txn.unify(&Expr::mvar(residual), &lam(nat(), bvar(0)), limits).unwrap();
}

#[test]
fn distinct_heads_retain_a_dependent_result_parameter_in_the_shared_telescope() {
    let mut txn = transaction();
    let type_ = pi(Expr::sort(Level::one()), pi(bvar(0), pi(nat(), bvar(2))));
    let f = natural(&mut txn, "f", type_.clone());
    let g = natural(&mut txn, "g", type_);
    let a = local(&mut txn, "A", Expr::sort(Level::one()));
    let x = local(&mut txn, "x", a.clone());
    let y = local(&mut txn, "y", a.clone());
    let n = local(&mut txn, "n", nat());
    let m = local(&mut txn, "m", nat());
    let report = txn.unify(
        &app(Expr::mvar(f), &[a.clone(), x, n]),
        &app(Expr::mvar(g), &[a, y, m]), budget(),
    ).unwrap();
    assert_eq!(report.kernel_checks, 2);
    assert_eq!(report.residual_metavariables.len(), 1);
    let residual = &report.residual_metavariables[0];
    let ExprNode::ForallE { binder_type, body, .. } = txn.mvars.get_decl(residual).unwrap().type_.node() else {
        panic!("expected a shared dependent telescope");
    };
    assert_eq!(binder_type, &Expr::sort(Level::one()));
    assert_eq!(body, &bvar(0));
    assert!(!txn.mvars.is_assigned(residual));
}
