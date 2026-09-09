//! Executable tests of the native solver, not a mock unification model.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
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
fn numeral(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn bvar(n: u32) -> Expr {
    Expr::bvar(n).unwrap()
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(name("x"), domain, body, BinderInfo::Default)
}
fn identity() -> Expr {
    Expr::lam(name("x"), nat(), bvar(0), BinderInfo::Default)
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
fn goal(txn: &mut ElabTxn, text: &str, type_: Expr, kind: MetavarKind, depth: u32) -> MVarId {
    let id = MVarId(name(text));
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        type_,
        txn.lctx.clone(),
        kind,
        depth,
        None,
    );
    id
}
fn natural(txn: &mut ElabTxn, text: &str, type_: Expr) -> MVarId {
    goal(txn, text, type_, MetavarKind::Natural, 0)
}
fn local(txn: &mut ElabTxn, text: &str, type_: Expr) -> Expr {
    let id = FVarId(name(text));
    txn.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn assert_semantics_unchanged(actual: &ElabTxn, before: &ElabTxn) {
    assert_eq!(actual.mvars, before.mvars);
    assert_eq!(actual.universes, before.universes);
    assert_eq!(actual.constraints, before.constraints);
    assert_eq!(actual.lctx, before.lctx);
    assert_eq!(actual.env, before.env);
    assert_eq!(actual.options, before.options);
    assert_eq!(actual.seed, before.seed);
}

#[test]
fn ground_assignment_is_checked_without_publishing_a_declaration() {
    let mut txn = transaction();
    let id = natural(&mut txn, "n", nat());
    let env = txn.env.clone();
    let report = txn
        .unify(&Expr::mvar(id.clone()), &numeral(37), budget())
        .unwrap();
    assert_eq!(report.expression_assignments, vec![id.clone()]);
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(txn.mvars.get_assigned_expr(&id), Some(&numeral(37)));
    assert_eq!(txn.env, env);
}

#[test]
fn wrong_typed_assignment_is_vetoed_by_the_real_kernel() {
    let mut txn = transaction();
    let id = natural(&mut txn, "n", nat());
    let before = txn.clone();
    let error = txn
        .unify(
            &Expr::mvar(id.clone()),
            &Expr::sort(Level::zero()),
            budget(),
        )
        .unwrap_err();
    match error {
        UnificationError::AssignmentCheck { id: found, outcome } => {
            assert_eq!(found, id);
            assert!(matches!(
                *outcome,
                Outcome::Complete(Verdict::Rejected { .. })
            ));
        }
        other => panic!("expected a real K1 rejection, got {other:?}"),
    }
    assert_semantics_unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn a_distinct_local_pattern_synthesizes_a_lambda() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(nat(), nat()));
    let x = local(&mut txn, "argument", nat());
    let report = txn
        .unify(&Expr::app(Expr::mvar(f.clone()), x.clone()), &x, budget())
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    let assignment = txn.mvars.get_assigned_expr(&f).unwrap();
    let ExprNode::Lam {
        body, binder_type, ..
    } = assignment.node()
    else {
        panic!("expected lambda");
    };
    assert_eq!(body, &bvar(0));
    assert_eq!(binder_type, &nat());
    assert!(!assignment.has_fvar());
}

#[test]
fn dependent_pattern_rebinds_later_domains_capture_avoidantly() {
    let mut txn = transaction();
    let f = natural(
        &mut txn,
        "dependent",
        pi(Expr::sort(Level::one()), pi(bvar(0), bvar(1))),
    );
    let a = local(&mut txn, "A", Expr::sort(Level::one()));
    let x = local(&mut txn, "x", a.clone());
    let lhs = Expr::app(Expr::app(Expr::mvar(f.clone()), a), x.clone());
    let report = txn.unify(&lhs, &x, budget()).unwrap();
    assert_eq!(report.kernel_checks, 1);
    let assignment = txn.mvars.get_assigned_expr(&f).unwrap();
    let ExprNode::Lam { body, .. } = assignment.node() else {
        panic!("expected outer lambda");
    };
    let ExprNode::Lam {
        binder_type, body, ..
    } = body.node()
    else {
        panic!("expected inner lambda");
    };
    assert_eq!(binder_type, &bvar(0));
    assert_eq!(body, &bvar(0));
    assert!(!assignment.has_fvar());
}

#[test]
fn lambda_comparison_opens_both_bodies_with_the_same_fresh_local() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(nat(), nat()));
    let lhs = Expr::lam(
        name("left"),
        nat(),
        Expr::app(Expr::mvar(f.clone()), bvar(0)),
        BinderInfo::Default,
    );
    let rhs = Expr::lam(name("right"), nat(), bvar(0), BinderInfo::Default);
    txn.unify(&lhs, &rhs, budget()).unwrap();
    assert!(matches!(
        txn.mvars.get_assigned_expr(&f).unwrap().node(),
        ExprNode::Lam { .. }
    ));
}

#[test]
fn beta_zeta_and_metadata_are_reduced_natively() {
    let mut txn = transaction();
    let applied = Expr::app(identity(), numeral(9));
    let let_term = Expr::let_e(name("n"), nat(), applied, bvar(0), false);
    let term = Expr::mdata(KVMap::new(), let_term);
    let report = txn.unify(&term, &numeral(9), budget()).unwrap();
    assert!(report.expression_assignments.is_empty());
    assert_eq!(report.kernel_checks, 0);
}

#[test]
fn a_later_assignment_unblocks_an_earlier_nonpattern_equation() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(nat(), nat()));
    let equations = [
        (Expr::app(Expr::mvar(f.clone()), numeral(5)), numeral(5)),
        (Expr::mvar(f.clone()), identity()),
    ];
    txn.unify_many_with(&equations, budget(), &|| false)
        .unwrap();
    assert!(txn.mvars.is_assigned(&f));
}

#[test]
fn later_equations_resolve_earlier_assignment_typing_dependencies() {
    let mut txn = transaction();
    let type_hole = natural(&mut txn, "type", Expr::sort(Level::one()));
    let value_hole = natural(&mut txn, "value", Expr::mvar(type_hole.clone()));
    let report = txn
        .unify_many_with(
            &[
                (Expr::mvar(value_hole.clone()), numeral(12)),
                (Expr::mvar(type_hole.clone()), nat()),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.kernel_checks, 2);
    assert!(txn.mvars.is_assigned(&type_hole));
    assert!(txn.mvars.is_assigned(&value_hole));
}

#[test]
fn unresolved_assignment_typing_does_not_become_success() {
    let mut txn = transaction();
    let type_hole = natural(&mut txn, "type", Expr::sort(Level::one()));
    let value_hole = natural(&mut txn, "value", Expr::mvar(type_hole));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&Expr::mvar(value_hole), &numeral(1), budget()),
        Err(UnificationError::Deferred(
            UnificationDeferred::UnresolvedAssignmentType(_)
        ))
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn assignment_checks_close_over_the_metavariables_own_local_context() {
    let mut txn = transaction();
    let x = local(&mut txn, "x", nat());
    let id = natural(&mut txn, "n", nat());
    txn.unify(&Expr::mvar(id.clone()), &x, budget()).unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&id), Some(&x));
}

#[test]
fn a_newer_local_cannot_escape_into_an_older_goal() {
    let mut txn = transaction();
    let id = natural(&mut txn, "n", nat());
    let x = local(&mut txn, "later", nat());
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&Expr::mvar(id), &x, budget()),
        Err(UnificationError::Deferred(
            UnificationDeferred::EscapingLocal(_)
        ))
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn separately_allocated_reflexive_flexible_applications_do_not_fail_occurs_check() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(nat(), nat()));
    let x = local(&mut txn, "x", nat());
    let lhs = Expr::app(Expr::mvar(f.clone()), x.clone());
    let rhs = Expr::app(Expr::mvar(f.clone()), x);
    let report = txn.unify(&lhs, &rhs, budget()).unwrap();
    assert!(report.expression_assignments.is_empty());
    assert!(!txn.mvars.is_assigned(&f));
}

#[test]
fn a_genuine_occurs_cycle_is_refused_without_mutation() {
    let mut txn = transaction();
    let id = natural(&mut txn, "n", nat());
    let rhs = Expr::app(
        Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new()),
        Expr::mvar(id.clone()),
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&Expr::mvar(id), &rhs, budget()),
        Err(UnificationError::Metavariable(
            MetavarError::OccursCheckFailed { .. }
        ))
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn opaque_and_deeper_metavariables_are_not_assigned() {
    for (kind, depth) in [(MetavarKind::SyntheticOpaque, 0), (MetavarKind::Natural, 1)] {
        let mut txn = transaction();
        let id = goal(&mut txn, "n", nat(), kind, depth);
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&Expr::mvar(id), &numeral(1), budget()),
            Err(UnificationError::Deferred(_))
        ));
        assert_semantics_unchanged(&txn, &before);
    }
}

#[test]
fn repeated_pattern_arguments_are_deferred() {
    let mut txn = transaction();
    let f = natural(&mut txn, "f", pi(nat(), pi(nat(), nat())));
    let x = local(&mut txn, "x", nat());
    let lhs = Expr::app(Expr::app(Expr::mvar(f.clone()), x.clone()), x.clone());
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&lhs, &x, budget()),
        Err(UnificationError::Deferred(UnificationDeferred::NotAPattern))
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn universe_assignment_solves_a_sort_equation() {
    let mut txn = transaction();
    let u = LMVarId(name("u"));
    let report = txn
        .unify(
            &Expr::sort(Level::mvar(u.clone())),
            &Expr::sort(Level::one()),
            budget(),
        )
        .unwrap();
    assert_eq!(report.universe_assignments, vec![u.clone()]);
    assert_eq!(txn.universes.get_assignment(&u), Some(&Level::one()));
}

#[test]
fn cyclic_universe_equations_defer_instead_of_constructing_a_cycle() {
    let mut txn = transaction();
    let u = LMVarId(name("u"));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::sort(Level::mvar(u.clone())),
            &Expr::sort(Level::mvar(u).succ().unwrap()),
            budget()
        ),
        Err(UnificationError::Deferred(
            UnificationDeferred::CyclicUniverse(_)
        ))
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn rigid_failure_rolls_back_prior_assignments_and_constraint_extraction() {
    let mut txn = transaction();
    let id = natural(&mut txn, "n", nat());
    txn.postpone(
        ConstraintKind::HasType {
            expr: Expr::mvar(id.clone()),
            expected_type: nat(),
        },
        0,
    );
    let before = txn.clone();
    assert!(
        txn.unify_many_with(
            &[(Expr::mvar(id), numeral(7)), (numeral(1), numeral(2))],
            budget(),
            &|| false
        )
        .is_err()
    );
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn successful_assignments_return_wakeups_in_stable_identity_order() {
    let mut txn = transaction();
    let a = natural(&mut txn, "a", nat());
    let b = natural(&mut txn, "b", nat());
    let first = txn.postpone(
        ConstraintKind::HasType {
            expr: Expr::mvar(b.clone()),
            expected_type: nat(),
        },
        0,
    );
    let second = txn.postpone(
        ConstraintKind::HasType {
            expr: Expr::mvar(a.clone()),
            expected_type: nat(),
        },
        0,
    );
    let report = txn
        .unify_many_with(
            &[(Expr::mvar(a), numeral(1)), (Expr::mvar(b), numeral(2))],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(
        report.awakened.iter().map(|row| row.id).collect::<Vec<_>>(),
        vec![first, second]
    );
    assert!(txn.constraints.is_empty());
}

#[test]
fn cancellation_at_the_final_publication_boundary_is_atomic() {
    let mut original = transaction();
    let id = natural(&mut original, "n", nat());
    let equations = [(Expr::mvar(id), numeral(8))];
    let mut control = original.clone();
    let count = Cell::new(0_usize);
    control
        .unify_many_with(&equations, budget(), &|| {
            count.set(count.get() + 1);
            false
        })
        .unwrap();
    let limit = count.get();
    let count = Cell::new(0_usize);
    let before = original.clone();
    let result = original.unify_many_with(&equations, budget(), &|| {
        count.set(count.get() + 1);
        count.get() == limit
    });
    assert!(matches!(result, Err(UnificationError::Cancelled)));
    assert_semantics_unchanged(&original, &before);
}

#[test]
fn zero_resource_budgets_do_not_publish_assignments() {
    for dimension in 0..3 {
        let mut txn = transaction();
        let id = natural(&mut txn, "n", nat());
        let before = txn.clone();
        let mut limits = budget();
        match dimension {
            0 => limits.max_steps = 0,
            1 => limits.max_visited_nodes = 0,
            _ => limits.max_assignments = 0,
        }
        assert!(txn.unify(&Expr::mvar(id), &numeral(1), limits).is_err());
        assert_semantics_unchanged(&txn, &before);
    }
}

#[test]
fn shared_reflexive_dags_are_not_expanded_as_trees() {
    let mut txn = transaction();
    let id = natural(&mut txn, "n", nat());
    let build = || {
        let mut expr = Expr::mvar(id.clone());
        for _ in 0..60 {
            expr = Expr::app(expr.clone(), expr);
        }
        expr
    };
    let mut limits = budget();
    limits.max_steps = 2000;
    let report = txn.unify(&build(), &build(), limits).unwrap();
    assert!(report.unifier_steps < 1000);
    assert!(!txn.mvars.is_assigned(&id));
}

#[test]
fn alpha_names_are_not_semantic_equation_content() {
    let mut txn = transaction();
    let lhs = Expr::lam(name("first"), nat(), bvar(0), BinderInfo::Default);
    let rhs = Expr::lam(name("second"), nat(), bvar(0), BinderInfo::Implicit);
    assert!(txn.unify(&lhs, &rhs, budget()).is_ok());
}

#[test]
fn loose_bound_variables_are_not_interpreted_as_locals() {
    let mut txn = transaction();
    assert!(matches!(
        txn.unify(&bvar(0), &bvar(0), budget()),
        Err(UnificationError::LooseBoundVariable)
    ));
}

#[test]
fn elementary_universe_identities_are_solved_without_assigning_parameters() {
    let a = Level::param(name("a"));
    let b = Level::param(name("b")).succ().unwrap();
    let pairs = [
        (Level::max(Level::zero(), a.clone()).unwrap(), a.clone()),
        (Level::max(a.clone(), Level::zero()).unwrap(), a.clone()),
        (Level::max(a.clone(), a.clone()).unwrap(), a.clone()),
        (
            Level::imax(a.clone(), Level::zero()).unwrap(),
            Level::zero(),
        ),
        (Level::imax(Level::zero(), a.clone()).unwrap(), a.clone()),
        (Level::imax(a.clone(), a.clone()).unwrap(), a.clone()),
        (
            Level::imax(a.clone(), b.clone()).unwrap(),
            Level::max(a, b).unwrap(),
        ),
    ];
    for (left, right) in pairs {
        let mut txn = transaction();
        let report = txn
            .unify(&Expr::sort(left), &Expr::sort(right), budget())
            .unwrap();
        assert!(report.universe_assignments.is_empty());
        assert!(txn.universes.is_empty());
    }
}

#[test]
fn function_universes_propagate_into_a_later_type_assignment() {
    let mut txn = transaction();
    let u = LMVarId(name("function_universe"));
    let function = pi(nat(), nat());
    let ty = natural(
        &mut txn,
        "function_type",
        Expr::sort(Level::mvar(u.clone())),
    );
    let report = txn
        .unify_many_with(
            &[
                (
                    Expr::sort(Level::mvar(u.clone())),
                    Expr::sort(Level::imax(Level::one(), Level::one()).unwrap()),
                ),
                (Expr::mvar(ty.clone()), function.clone()),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(
        txn.universes.instantiate(&Level::mvar(u)).unwrap(),
        Level::one()
    );
    assert_eq!(txn.instantiate_expr(&Expr::mvar(ty)).unwrap(), function);
}

#[test]
fn symbolic_imax_is_not_replaced_by_max_without_a_positive_right_side() {
    let mut txn = transaction();
    let a = Level::param(name("a"));
    let b = Level::param(name("b"));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::sort(Level::imax(a.clone(), b.clone()).unwrap()),
            &Expr::sort(Level::max(a, b).unwrap()),
            budget()
        ),
        Err(UnificationError::Deferred(_))
    ));
    assert_semantics_unchanged(&txn, &before);
}

#[test]
fn universe_simplification_stays_inside_the_unifier_work_budget() {
    let mut txn = transaction();
    let before = txn.clone();
    let mut limits = budget();
    limits.max_steps = 1;
    assert!(matches!(
        txn.unify(
            &Expr::sort(Level::imax(Level::one(), Level::one()).unwrap()),
            &Expr::sort(Level::one()),
            limits
        ),
        Err(UnificationError::StepLimit { .. })
    ));
    assert_semantics_unchanged(&txn, &before);
}
