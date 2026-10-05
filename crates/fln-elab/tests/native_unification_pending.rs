//! The `synthPending` rung of native unification (bead `fln-pv1`): a batch at a
//! fixed point blocked on an opaque hole asks the hole's owner, and an answer is
//! an ordinary assignment, validated by K1 with the rest of the batch.
//!
//! The owners here are test doubles standing in for the elaborator's instance
//! search; the elaborator path itself is exercised end to end by
//! `crates/fln/tests/source_pending_instances.rs`.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{
    PendingAnswer, PendingSynthesis, UnificationBudget, UnificationDeferred, UnificationError,
};
use fln_elab::mvar::MetavarKind;
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::{Budget, Verdict};

fn name(text: &str) -> Name {
    Name::from_components([text])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), Vec::new())
}
fn numeral(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn transaction() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        41,
    )
}
fn hole(txn: &mut ElabTxn, text: &str, kind: MetavarKind) -> MVarId {
    let id = MVarId(name(text));
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        nat(),
        txn.lctx.clone(),
        kind,
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

/// Records every request, in order, and answers with `answer`.
struct Owner<F> {
    asked: Vec<MVarId>,
    answer: F,
}

impl<F: FnMut(&ElabTxn, &MVarId) -> PendingAnswer> PendingSynthesis for Owner<F> {
    fn synthesize(&mut self, state: &ElabTxn, goal: &MVarId, _spent: u64) -> PendingAnswer {
        self.asked.push(goal.clone());
        (self.answer)(state, goal)
    }
}

fn owner<F: FnMut(&ElabTxn, &MVarId) -> PendingAnswer>(answer: F) -> Owner<F> {
    Owner {
        asked: Vec::new(),
        answer,
    }
}

fn declined() -> PendingAnswer {
    PendingAnswer {
        result: Ok(None),
        spent: 0,
    }
}

#[test]
fn a_stuck_hole_is_synthesized_from_the_batchs_own_progress_and_the_batch_completes() {
    let mut txn = transaction();
    let input = hole(&mut txn, "input", MetavarKind::Natural);
    let instance = hole(&mut txn, "instance", MetavarKind::SyntheticOpaque);
    let equations = [
        (Expr::mvar(input.clone()), numeral(5)),
        (Expr::mvar(instance.clone()), Expr::mvar(input.clone())),
    ];

    // Control: without an owner the opaque hole blocks the whole batch, and
    // the first-order progress `?input := 5` is not kept.
    let before = txn.clone();
    let mut control = txn.clone();
    assert_eq!(
        control
            .unify_many_with(&equations, budget(), &|| false)
            .unwrap_err(),
        UnificationError::Deferred(UnificationDeferred::OpaqueMetavariable(instance.clone()))
    );
    unchanged(&control, &before);

    // The owner sees the batch's unchecked working assignment of `?input`.
    let watched = input.clone();
    let mut synthesis = owner(move |state: &ElabTxn, _goal: &MVarId| PendingAnswer {
        result: Ok(state
            .mvars
            .get_assigned_expr(&watched)
            .map(|value| (value.clone(), name("Pending")))),
        spent: 0,
    });
    let report = txn
        .unify_many_with_pending(&equations, budget(), &|| false, &mut synthesis)
        .unwrap();
    assert_eq!(synthesis.asked, vec![instance.clone()]);
    assert_eq!(
        report.expression_assignments,
        vec![input.clone(), instance.clone()]
    );
    assert_eq!(txn.mvars.get_assigned_expr(&input), Some(&numeral(5)));
    assert_eq!(txn.mvars.get_assigned_expr(&instance), Some(&numeral(5)));
    // Both assignments crossed K1, the owner's answer included.
    assert_eq!(report.kernel_checks, 2);
}

#[test]
fn an_ill_typed_answer_is_vetoed_by_k1_and_publishes_nothing() {
    let mut txn = transaction();
    let instance = hole(&mut txn, "instance", MetavarKind::SyntheticOpaque);
    let successor = Expr::const_(Name::from_components(["Nat", "succ"]), Vec::new());
    // `?instance : Nat` against `Nat.succ : Nat → Nat`: the equation is
    // syntactically satisfied by the bad answer, so only K1 can refuse it.
    let equations = [(Expr::mvar(instance.clone()), successor.clone())];
    let before = txn.clone();
    let mut synthesis = owner(move |_: &ElabTxn, _: &MVarId| PendingAnswer {
        result: Ok(Some((successor.clone(), name("Pending")))),
        spent: 0,
    });
    let error = txn
        .unify_many_with_pending(&equations, budget(), &|| false, &mut synthesis)
        .unwrap_err();
    assert!(
        matches!(&error, UnificationError::AssignmentCheck { id, outcome }
            if id == &instance && matches!(**outcome, Outcome::Complete(Verdict::Rejected { .. }))),
        "{error:?}"
    );
    unchanged(&txn, &before);
}

#[test]
fn an_answer_escaping_the_holes_context_is_declined_not_published() {
    let mut txn = transaction();
    let instance = hole(&mut txn, "instance", MetavarKind::SyntheticOpaque);
    // A local the hole was declared outside of.
    let outside = FVarId(name("outside"));
    txn.lctx.add_param(
        outside.clone(),
        outside.0.clone(),
        nat(),
        BinderInfo::Default,
    );
    let equations = [(Expr::mvar(instance.clone()), numeral(3))];
    let before = txn.clone();
    let mut synthesis = owner(move |_: &ElabTxn, _: &MVarId| PendingAnswer {
        result: Ok(Some((Expr::fvar(outside.clone()), name("Pending")))),
        spent: 0,
    });
    assert_eq!(
        txn.unify_many_with_pending(&equations, budget(), &|| false, &mut synthesis)
            .unwrap_err(),
        UnificationError::Deferred(UnificationDeferred::OpaqueMetavariable(instance.clone()))
    );
    assert_eq!(synthesis.asked, vec![instance]);
    unchanged(&txn, &before);
}

#[test]
fn an_owners_nonanswer_ends_the_batch_typed_and_its_work_is_charged() {
    let mut txn = transaction();
    let instance = hole(&mut txn, "instance", MetavarKind::SyntheticOpaque);
    let equations = [(Expr::mvar(instance.clone()), numeral(3))];
    let before = txn.clone();

    let stopped = |spent: u64| {
        move |_: &ElabTxn, _: &MVarId| PendingAnswer {
            result: Err(UnificationError::HeartbeatLimit),
            spent,
        }
    };
    // The same deterministic batch, stopped at no cost, fixes the solver's
    // own share of the heartbeats.
    let mut free = txn.clone();
    assert_eq!(
        free.unify_many_with_pending(&equations, budget(), &|| false, &mut owner(stopped(0)))
            .unwrap_err(),
        UnificationError::HeartbeatLimit
    );
    let solver_share = free.budget.heartbeats_consumed - before.budget.heartbeats_consumed;

    assert_eq!(
        txn.unify_many_with_pending(&equations, budget(), &|| false, &mut owner(stopped(1000)))
            .unwrap_err(),
        UnificationError::HeartbeatLimit
    );
    unchanged(&txn, &before);
    assert_eq!(
        txn.budget.heartbeats_consumed - before.budget.heartbeats_consumed,
        solver_share + 1000
    );
}

#[test]
fn declined_holes_are_asked_once_per_assignment_generation_in_occurrence_order() {
    let mut txn = transaction();
    let first = hole(&mut txn, "first", MetavarKind::SyntheticOpaque);
    let second = hole(&mut txn, "second", MetavarKind::SyntheticOpaque);
    let equations = [
        (Expr::mvar(second.clone()), numeral(4)),
        (Expr::mvar(first.clone()), numeral(3)),
    ];
    let before = txn.clone();
    let mut synthesis = owner(|_: &ElabTxn, _: &MVarId| declined());
    assert_eq!(
        txn.unify_many_with_pending(&equations, budget(), &|| false, &mut synthesis)
            .unwrap_err(),
        UnificationError::Deferred(UnificationDeferred::OpaqueMetavariable(second.clone()))
    );
    assert_eq!(synthesis.asked, vec![second, first]);
    unchanged(&txn, &before);
}
