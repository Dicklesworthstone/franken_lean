//! Fresh pruning obligations cannot adopt identities hidden elsewhere in the store.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, MVarId};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::unify::UnificationBudget;
use fln_elab::lctx::LocalContext;
use fln_elab::mvar::{AssignmentJustification, MetavarKind};
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::Budget;

fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}
fn pi(body: Expr) -> Expr {
    Expr::forall_e(name("x"), nat(), body, BinderInfo::Default)
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn declare(txn: &mut ElabTxn, s: &str, type_: Expr, locals: LocalContext) -> MVarId {
    let id = MVarId(name(s));
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        type_,
        locals,
        MetavarKind::Natural,
        0,
        None,
    );
    id
}
fn equation() -> (ElabTxn, Expr, Expr) {
    let mut txn = ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        31,
    );
    let f = declare(&mut txn, "f", pi(pi(nat())), LocalContext::new());
    let mut args = Vec::new();
    for s in ["x", "y", "z"] {
        let id = FVarId(name(s));
        txn.lctx
            .add_param(id.clone(), id.0.clone(), nat(), BinderInfo::Default);
        args.push(Expr::fvar(id));
    }
    let head = Expr::app(Expr::mvar(f), args[0].clone());
    (
        txn,
        Expr::app(head.clone(), args[1].clone()),
        Expr::app(head, args[2].clone()),
    )
}
fn reserved(n: usize) -> MVarId {
    MVarId(Name::from_components(["_fln_unify_pruned", &n.to_string()]))
}

#[test]
fn unrelated_declaration_type_identities_stay_undeclared() {
    let (mut txn, left, right) = equation();
    let unknown = reserved(0);
    let other = declare(
        &mut txn,
        "other",
        Expr::mvar(unknown.clone()),
        LocalContext::new(),
    );
    let before = txn.mvars.get_decl(&other).unwrap().clone();
    let report = txn.unify(&left, &right, budget()).unwrap();
    assert_eq!(report.residual_metavariables.len(), 1);
    assert_ne!(report.residual_metavariables[0], unknown);
    assert!(!txn.mvars.is_declared(&unknown));
    assert_eq!(txn.mvars.get_decl(&other), Some(&before));
}

#[test]
fn unrelated_assignment_identities_stay_undeclared() {
    let (mut txn, left, right) = equation();
    let unknown = reserved(0);
    let other = declare(&mut txn, "other", nat(), LocalContext::new());
    txn.assign_mvar(
        other.clone(),
        Expr::mvar(unknown.clone()),
        AssignmentJustification::UserGiven,
    )
    .unwrap();
    let before = txn.mvars.get_assignment(&other).unwrap().clone();
    let report = txn.unify(&left, &right, budget()).unwrap();
    assert_ne!(report.residual_metavariables[0], unknown);
    assert!(!txn.mvars.is_declared(&unknown));
    assert_eq!(txn.mvars.get_assignment(&other), Some(&before));
}

#[test]
fn unrelated_captured_local_types_and_values_keep_their_identities() {
    for in_value in [false, true] {
        let (mut txn, left, right) = equation();
        let unknown = reserved(0);
        let id = FVarId(name("captured"));
        let mut locals = LocalContext::new();
        if in_value {
            locals.add_let(id.clone(), id.0.clone(), nat(), Expr::mvar(unknown.clone()));
        } else {
            locals.add_param(
                id.clone(),
                id.0.clone(),
                Expr::mvar(unknown.clone()),
                BinderInfo::Default,
            );
        }
        let other = declare(&mut txn, "other", nat(), locals);
        let before = txn.mvars.get_decl(&other).unwrap().clone();
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_ne!(
            report.residual_metavariables[0], unknown,
            "in_value={in_value}"
        );
        assert!(!txn.mvars.is_declared(&unknown));
        assert_eq!(txn.mvars.get_decl(&other), Some(&before));
    }
}

#[test]
fn queued_saved_context_is_reserved_independently_of_observed_reads() {
    use fln_elab::constraint::ConstraintKind;
    use std::collections::HashSet;

    for inferred_reads in [false, true] {
        let (mut txn, left, right) = equation();
        let unknown = reserved(0);
        let id = FVarId(name("saved"));
        let mut saved = LocalContext::new();
        saved.add_let(id.clone(), id.0.clone(), nat(), Expr::mvar(unknown.clone()));
        let waiting = txn.constraints.enqueue_scoped(
            ConstraintKind::HasType {
                expr: Expr::const_(Name::from_components(["Nat", "zero"]), Vec::new()),
                expected_type: nat(),
            },
            &txn.mvars,
            &saved,
            0,
        );
        if !inferred_reads {
            // A resumer may replace its observed read signature. That index is
            // not an inventory of identities present in its retained syntax.
            assert!(txn.constraints.update_reads(waiting, HashSet::new()));
        }
        let before = txn.constraints.clone();
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_ne!(report.residual_metavariables[0], unknown);
        assert!(!txn.mvars.is_declared(&unknown));
        assert_eq!(txn.constraints, before);
    }
}

#[test]
fn multiple_hidden_ids_are_skipped_independently_of_insertion_order() {
    for reverse in [false, true] {
        let (mut txn, left, right) = equation();
        let mut ordinals: Vec<_> = (0..8).collect();
        if reverse {
            ordinals.reverse();
        }
        for index in ordinals {
            declare(
                &mut txn,
                &format!("other{index}"),
                Expr::mvar(reserved(index)),
                LocalContext::new(),
            );
        }
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.residual_metavariables, vec![reserved(8)]);
        for index in 0..8 {
            assert!(!txn.mvars.is_declared(&reserved(index)));
        }
    }
}

#[test]
fn shared_hidden_expression_dags_are_not_expanded_as_trees() {
    let (mut txn, left, right) = equation();
    let unknown = reserved(0);
    let mut dag = Expr::mvar(unknown.clone());
    for _ in 0..32 {
        dag = Expr::app(dag.clone(), dag);
    }
    declare(&mut txn, "unrelated", dag, LocalContext::new());
    let mut limits = budget();
    limits.max_visited_nodes = 20_000;
    let report = txn.unify(&left, &right, limits).unwrap();
    assert_eq!(report.residual_metavariables, vec![reserved(1)]);
    assert!(!txn.mvars.is_declared(&unknown));
}

#[test]
fn large_closed_subgraphs_do_not_consume_identity_walk_budget() {
    let mut costs = Vec::new();
    for depth in [1, 1024] {
        let (mut txn, left, right) = equation();
        let mut closed = nat();
        for _ in 0..depth {
            closed = Expr::app(closed.clone(), closed);
        }
        declare(&mut txn, "unrelated", closed, LocalContext::new());
        let report = txn.unify(&left, &right, budget()).unwrap();
        costs.push((report.unifier_steps, report.visited_nodes));
    }
    assert_eq!(costs[0], costs[1]);
}

#[test]
fn inventory_exhaustion_and_cancellation_leave_no_residual_or_assignment() {
    use fln_elab::constraint::unify::UnificationError;
    use std::cell::Cell;

    let (mut base, left, right) = equation();
    for index in 0..64 {
        declare(
            &mut base,
            &format!("other{index}"),
            Expr::mvar(reserved(index)),
            LocalContext::new(),
        );
    }
    let polls = Cell::new(0usize);
    let report = base
        .clone()
        .unify_many_with(&[(left.clone(), right.clone())], budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    for stop in [polls.get() / 2, polls.get() - 1] {
        let mut txn = base.clone();
        let calls = Cell::new(0usize);
        assert!(matches!(
            txn.unify_many_with(&[(left.clone(), right.clone())], budget(), &|| {
                let count = calls.get();
                calls.set(count + 1);
                count >= stop
            }),
            Err(UnificationError::Cancelled)
        ));
        let mut before = base.clone();
        before.budget.heartbeats_consumed = txn.budget.heartbeats_consumed;
        assert_eq!(txn, before);
    }
    for nodes in [false, true] {
        let mut txn = base.clone();
        let mut limits = budget();
        if nodes {
            limits.max_visited_nodes = report.visited_nodes - 1;
        } else {
            limits.max_steps = report.unifier_steps - 1;
        }
        let error = txn.unify(&left, &right, limits).unwrap_err();
        assert!(matches!(
            error,
            UnificationError::NodeLimit { .. } | UnificationError::StepLimit { .. }
        ));
        let mut before = base.clone();
        before.budget.heartbeats_consumed = txn.budget.heartbeats_consumed;
        assert_eq!(txn, before);
        txn.unify(&left, &right, budget()).unwrap();
    }
}
