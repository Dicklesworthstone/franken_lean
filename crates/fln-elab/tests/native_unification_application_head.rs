//! Public-transaction controls for the bounded application-head approximation.
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
fn succ() -> Expr {
    Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new())
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
        23,
    )
}
fn hole_at(
    txn: &mut ElabTxn,
    s: &str,
    type_: Expr,
    kind: MetavarKind,
    depth: u32,
) -> MVarId {
    let id = MVarId(name(s));
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
fn hole(txn: &mut ElabTxn, s: &str, type_: Expr) -> MVarId {
    hole_at(txn, s, type_, MetavarKind::Natural, 0)
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
fn successor_equation() -> (ElabTxn, MVarId, Expr, Expr) {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let left = Expr::app(Expr::mvar(f.clone()), number(7));
    let right = Expr::app(succ(), number(7));
    (txn, f, left, right)
}

#[test]
fn recovers_a_checked_constructor_head_in_both_orientations() {
    for reverse in [false, true] {
        for n in 0..8 {
            let mut txn = transaction();
            let f = hole(&mut txn, "f", pi(nat(), nat()));
            let left = Expr::app(Expr::mvar(f.clone()), number(n));
            let right = Expr::app(succ(), number(n));
            let env = txn.env.clone();
            let (left, right) = if reverse { (right, left) } else { (left, right) };
            let report = txn.unify(&left, &right, budget()).unwrap();
            assert_eq!(report.expression_assignments, vec![f.clone()]);
            assert_eq!(report.kernel_checks, 1);
            assert!(report.residual_metavariables.is_empty());
            assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&succ()));
            txn.unify(&Expr::app(Expr::mvar(f), number(91)), &number(92), budget())
                .unwrap();
            assert_eq!(txn.env, env);
        }
    }
}

#[test]
fn recovers_a_type_constructor_applied_to_a_nonlocal_type() {
    let mut txn = transaction();
    let type_ = Expr::sort(Level::one());
    let c = local(&mut txn, "C", pi(type_.clone(), type_.clone()));
    let f = hole(&mut txn, "F", pi(type_.clone(), type_));
    let report = txn
        .unify(
            &Expr::app(Expr::mvar(f.clone()), nat()),
            &Expr::app(c.clone(), nat()),
            budget(),
        )
        .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&c));
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn preserves_the_entire_partially_applied_prefix() {
    let mut txn = transaction();
    let g = local(&mut txn, "g", pi(nat(), pi(nat(), nat())));
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let candidate = Expr::app(g, number(3));
    let report = txn
        .unify(
            &Expr::app(Expr::mvar(f.clone()), number(7)),
            &Expr::app(candidate.clone(), number(7)),
            budget(),
        )
        .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&candidate));
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn dependent_prefix_parameters_are_not_dropped() {
    let mut txn = transaction();
    let g = local(
        &mut txn,
        "g",
        pi(Expr::sort(Level::one()), pi(bvar(0), bvar(1))),
    );
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let candidate = Expr::app(g, nat());
    let report = txn
        .unify(
            &Expr::app(Expr::mvar(f.clone()), number(13)),
            &Expr::app(candidate.clone(), number(13)),
            budget(),
        )
        .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&candidate));
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn repeated_rigid_arguments_are_valid_for_head_recovery() {
    let mut txn = transaction();
    let g = local(&mut txn, "g", pi(nat(), pi(nat(), nat())));
    let f = hole(&mut txn, "f", pi(nat(), pi(nat(), nat())));
    let args = [number(7), number(7)];
    let report = txn
        .unify(&app(Expr::mvar(f.clone()), &args), &app(g.clone(), &args), budget())
        .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&g));
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn argument_order_and_arity_must_match() {
    for mismatch in [0, 1, 2] {
        let mut txn = transaction();
        let g = local(&mut txn, "g", pi(nat(), pi(nat(), nat())));
        let f = hole(&mut txn, "f", pi(nat(), pi(nat(), nat())));
        let left = app(Expr::mvar(f), &[number(7), number(9)]);
        let args = match mismatch {
            0 => vec![number(9), number(7)],
            1 => vec![number(7)],
            _ => vec![number(7), number(10)],
        };
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&left, &app(g, &args), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn reduces_a_matching_suffix_before_recovering_the_head() {
    let (mut txn, f, left, _) = successor_equation();
    let report = txn
        .unify(&left, &Expr::app(succ(), beta(nat(), number(7))), budget())
        .unwrap();
    assert_eq!(report.expression_assignments, vec![f]);
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn local_let_suffix_conversion_obeys_zeta_delta() {
    for unfold in [false, true] {
        let (mut txn, f, left, _) = successor_equation();
        let alias = FVarId(name("alias"));
        txn.lctx.add_let(alias.clone(), alias.0.clone(), nat(), number(7));
        let right = Expr::app(succ(), Expr::fvar(alias));
        let before = txn.clone();
        let mut limits = budget();
        limits.zeta_delta = unfold;
        let result = txn.unify(&left, &right, limits);
        if unfold {
            assert_eq!(result.unwrap().expression_assignments, vec![f]);
        } else {
            assert!(matches!(result, Err(UnificationError::Deferred(_))));
            unchanged(&txn, &before);
        }
    }
}

#[test]
fn ordinary_pattern_assignments_retain_priority() {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let x = local(&mut txn, "x", nat());
    txn.unify(
        &Expr::app(Expr::mvar(f.clone()), x.clone()),
        &Expr::app(succ(), x),
        budget(),
    )
    .unwrap();
    assert!(matches!(txn.mvars.get_assigned_expr(&f).unwrap().node(), ExprNode::Lam { .. }));
}

#[test]
fn later_ordinary_constraints_preempt_the_head_approximation() {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let answer = Expr::app(succ(), number(7));
    let chosen = lam(nat(), answer.clone());
    txn.unify_many_with(
        &[
            (Expr::app(Expr::mvar(f.clone()), number(7)), answer.clone()),
            (Expr::app(Expr::mvar(f.clone()), number(8)), answer),
            (Expr::mvar(f.clone()), chosen.clone()),
        ],
        budget(),
        &|| false,
    )
    .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&chosen));
}

#[test]
fn candidate_type_holes_are_inferred_in_the_same_batch() {
    let mut txn = transaction();
    let type_id = hole(&mut txn, "T", Expr::sort(Level::one()));
    let f = hole(&mut txn, "f", Expr::mvar(type_id.clone()));
    let report = txn
        .unify(
            &Expr::app(Expr::mvar(f.clone()), number(7)),
            &Expr::app(succ(), number(7)),
            budget(),
        )
        .unwrap();
    assert!(report.expression_assignments.contains(&f));
    assert!(report.expression_assignments.contains(&type_id));
    assert_eq!(report.kernel_checks, 2);
    assert!(report.residual_metavariables.is_empty());
    txn.unify(&Expr::mvar(type_id), &pi(nat(), nat()), budget()).unwrap();
}

#[test]
fn a_candidate_with_the_wrong_function_type_is_not_published() {
    let mut txn = transaction();
    let g = local(&mut txn, "g", pi(nat(), Expr::sort(Level::one())));
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f), number(7)),
            &Expr::app(g, number(7)),
            budget(),
        ),
        Err(UnificationError::AssignmentCheck { .. })
    ));
    unchanged(&txn, &before);
}

#[test]
fn a_private_function_cannot_escape_into_an_older_hole() {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let g = local(&mut txn, "g", pi(nat(), nat()));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f), number(7)),
            &Expr::app(g, number(7)),
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn opaque_and_deeper_holes_keep_their_assignment_barriers() {
    for (kind, depth) in [(MetavarKind::SyntheticOpaque, 0), (MetavarKind::Natural, 1)] {
        let mut txn = transaction();
        let f = hole_at(&mut txn, "f", pi(nat(), nat()), kind, depth);
        let left = Expr::app(Expr::mvar(f.clone()), number(7));
        let right = Expr::app(succ(), number(7));
        let before = txn.clone();
        assert!(matches!(txn.unify(&left, &right, budget()), Err(UnificationError::Deferred(_))));
        unchanged(&txn, &before);
        if kind == MetavarKind::Natural {
            let mut limits = budget();
            limits.max_metavar_depth = 1;
            assert_eq!(txn.unify(&left, &right, limits).unwrap().expression_assignments, vec![f]);
        }
    }
}

#[test]
fn undeclared_heads_are_not_silently_created() {
    let mut txn = transaction();
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(MVarId(name("missing"))), number(7)),
            &Expr::app(succ(), number(7)),
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn cyclic_prefix_candidates_are_postponed_without_mutation() {
    let mut txn = transaction();
    let function = pi(nat(), nat());
    let k = local(&mut txn, "k", pi(function.clone(), function.clone()));
    let f = hole(&mut txn, "f", function);
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f.clone()), number(7)),
            &app(k, &[Expr::mvar(f), number(7)]),
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn an_unknown_function_is_not_assumed_injective() {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let a = hole(&mut txn, "a", nat());
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f.clone()), Expr::mvar(a)),
            &Expr::app(Expr::mvar(f), number(7)),
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn mismatched_suffix_holes_are_not_assigned_to_force_an_alignment() {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let a = hole(&mut txn, "a", nat());
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &Expr::app(Expr::mvar(f), Expr::mvar(a)),
            &Expr::app(succ(), number(7)),
            budget(),
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn an_unsolved_later_equation_rolls_back_the_recovered_head() {
    let (mut txn, f, left, right) = successor_equation();
    let before = txn.clone();
    assert!(matches!(
        txn.unify_many_with(&[(left, right), (number(0), number(1))], budget(), &|| false),
        Err(UnificationError::Deferred(_))
    ));
    assert!(!txn.mvars.is_assigned(&f));
    unchanged(&txn, &before);
}

#[test]
fn all_native_resource_gates_preserve_transactional_state() {
    for gate in 0..3 {
        let (mut txn, _, left, right) = successor_equation();
        let before = txn.clone();
        let mut limits = budget();
        match gate {
            0 => limits.max_steps = 0,
            1 => limits.max_visited_nodes = 0,
            _ => limits.max_assignments = 0,
        }
        let result = txn.unify(&left, &right, limits);
        match gate {
            0 => assert!(matches!(result, Err(UnificationError::StepLimit { .. }))),
            1 => assert!(matches!(result, Err(UnificationError::NodeLimit { .. }))),
            _ => assert!(matches!(result, Err(UnificationError::AssignmentLimit { .. }))),
        }
        unchanged(&txn, &before);
    }
}

#[test]
fn cancellation_including_the_final_publication_check_rolls_back() {
    let (mut probe, _, left, right) = successor_equation();
    let calls = Cell::new(0_u64);
    probe
        .unify_many_with(&[(left, right)], budget(), &|| {
            calls.set(calls.get() + 1);
            false
        })
        .unwrap();
    let total = calls.get();
    for stop in [1, total / 2, total] {
        let (mut txn, _, left, right) = successor_equation();
        let before = txn.clone();
        let calls = Cell::new(0_u64);
        assert!(matches!(
            txn.unify_many_with(&[(left, right)], budget(), &|| {
                calls.set(calls.get() + 1);
                calls.get() == stop
            }),
            Err(UnificationError::Cancelled)
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn identical_suffix_holes_remain_unsolved_after_head_recovery() {
    let mut txn = transaction();
    let f = hole(&mut txn, "f", pi(nat(), nat()));
    let a = hole(&mut txn, "a", nat());
    let argument = Expr::mvar(a.clone());
    let report = txn
        .unify(
            &Expr::app(Expr::mvar(f.clone()), argument.clone()),
            &Expr::app(succ(), argument),
            budget(),
        )
        .unwrap();
    assert_eq!(report.expression_assignments, vec![f.clone()]);
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&succ()));
    assert!(!txn.mvars.is_assigned(&a));
    // This report inventories conditional assignment checks, not every hole
    // in the input. The unresolved argument is not part of f's assigned value.
    assert!(report.residual_metavariables.is_empty());
    assert_eq!(report.kernel_checks, 1);
}
