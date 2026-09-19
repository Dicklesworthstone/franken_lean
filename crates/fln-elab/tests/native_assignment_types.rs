//! Assignment-generated type constraints through the real native solver.
#![forbid(unsafe_code)]
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::ConstraintKind;
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
fn numeral(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(name("x"), domain, body, BinderInfo::Default)
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn transaction() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        19,
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
fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = actual.budget.heartbeats_consumed;
    assert_eq!(actual, &expected);
}
fn pair() -> (ElabTxn, MVarId, MVarId) {
    let mut txn = transaction();
    let a = goal(&mut txn, "A", Expr::sort(Level::one()));
    let x = goal(&mut txn, "value", Expr::mvar(a.clone()));
    (txn, a, x)
}

#[test]
fn a_literal_assignment_infers_its_missing_type_in_both_orientations() {
    for reverse in [false, true] {
        let (mut txn, a, x) = pair();
        let env = txn.env.clone();
        let (left, right) = (Expr::mvar(x.clone()), numeral(7));
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(txn.mvars.get_assigned_expr(&a), Some(&nat()));
        assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&numeral(7)));
        assert_eq!(report.kernel_checks, 2);
        assert!(report.residual_metavariables.is_empty());
        assert_eq!(txn.env, env);
    }
}

#[test]
fn inferred_types_propagate_their_universe_without_defaulting() {
    let mut txn = transaction();
    let u = LMVarId(name("u"));
    let a = goal(&mut txn, "A", Expr::sort(Level::mvar(u.clone())));
    let x = goal(&mut txn, "value", Expr::mvar(a.clone()));
    let report = txn.unify(&Expr::mvar(x), &numeral(3), budget()).unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&a), Some(&nat()));
    assert_eq!(
        txn.universes.instantiate(&Level::mvar(u.clone())).unwrap(),
        Level::one()
    );
    assert_eq!(report.universe_assignments, vec![u]);
    assert_eq!(report.kernel_checks, 2);
}

#[test]
fn a_neutral_value_infers_dependent_type_indices() {
    let mut txn = transaction();
    let family = local(&mut txn, "Family", pi(nat(), Expr::sort(Level::one())));
    let value_type = Expr::app(family.clone(), numeral(5));
    let value = local(&mut txn, "known", value_type);
    let index = goal(&mut txn, "index", nat());
    let expected = Expr::app(family, Expr::mvar(index.clone()));
    let x = goal(&mut txn, "value", expected);
    let report = txn.unify(&Expr::mvar(x), &value, budget()).unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&index), Some(&numeral(5)));
    assert_eq!(report.kernel_checks, 2);
}

#[test]
fn applied_patterns_infer_a_dependent_result_type_family() {
    let mut txn = transaction();
    let family = goal(&mut txn, "Family", pi(nat(), Expr::sort(Level::one())));
    let f = goal(
        &mut txn,
        "function",
        pi(
            nat(),
            Expr::app(Expr::mvar(family.clone()), Expr::bvar(0).unwrap()),
        ),
    );
    let x = local(&mut txn, "argument", nat());
    let report = txn
        .unify(&Expr::app(Expr::mvar(f.clone()), x.clone()), &x, budget())
        .unwrap();
    let family_value = Expr::lam(name("n"), nat(), nat(), BinderInfo::Default);
    // Binder names are not part of conversion; check both assignments through
    // the normal unifier instead of asserting the fresh binder's spelling.
    txn.unify(&Expr::mvar(family), &family_value, budget())
        .unwrap();
    let identity = Expr::lam(
        name("n"),
        nat(),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    txn.unify(&Expr::mvar(f), &identity, budget()).unwrap();
    assert_eq!(report.kernel_checks, 2);
    assert!(report.residual_metavariables.is_empty());
}

#[test]
fn neutral_application_type_hints_do_not_skip_argument_checking() {
    for invalid in [false, true] {
        let mut txn = transaction();
        let op = local(&mut txn, "op", pi(nat(), nat()));
        let a = goal(&mut txn, "A", Expr::sort(Level::one()));
        let x = goal(&mut txn, "value", Expr::mvar(a.clone()));
        let argument = if invalid {
            Expr::sort(Level::zero())
        } else {
            numeral(7)
        };
        let value = Expr::app(op, argument);
        let before = txn.clone();
        let outcome = txn.unify(&Expr::mvar(x), &value, budget());
        if invalid {
            assert!(
                matches!(outcome, Err(UnificationError::AssignmentCheck { outcome, .. })
                if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })))
            );
            unchanged(&txn, &before);
        } else {
            assert_eq!(outcome.unwrap().kernel_checks, 2);
            assert_eq!(txn.mvars.get_assigned_expr(&a), Some(&nat()));
        }
    }
}

#[test]
fn sort_assignments_infer_successor_universes_not_cumulativity() {
    let mut txn = transaction();
    let a = goal(
        &mut txn,
        "A",
        Expr::sort(Level::succ(Level::one()).unwrap()),
    );
    let x = goal(&mut txn, "value", Expr::mvar(a.clone()));
    let report = txn
        .unify(&Expr::mvar(x), &Expr::sort(Level::zero()), budget())
        .unwrap();
    assert_eq!(
        txn.mvars.get_assigned_expr(&a),
        Some(&Expr::sort(Level::one()))
    );
    assert_eq!(report.kernel_checks, 2);
}

#[test]
fn queued_type_inference_does_not_count_awakened_obligations_as_solved() {
    let (mut txn, a, x) = pair();
    let selected = txn.postpone(
        ConstraintKind::DefEq {
            lhs: Expr::mvar(x.clone()),
            rhs: numeral(11),
        },
        0,
    );
    let watcher = txn.postpone(
        ConstraintKind::HasType {
            expr: Expr::mvar(x.clone()),
            expected_type: Expr::mvar(a.clone()),
        },
        0,
    );
    let report = txn
        .solve_defeq_constraints_with(&[selected], budget(), &|| false)
        .unwrap();
    assert_eq!(report.unification.awakened.len(), 1);
    assert_eq!(report.unification.awakened[0].id, watcher);
    assert!(matches!(
        report.unification.awakened[0].kind,
        ConstraintKind::HasType { .. }
    ));
    assert_eq!(report.solved, vec![selected]);
    assert_eq!(report.unification.kernel_checks, 2);
    assert_eq!(txn.mvars.get_assigned_expr(&a), Some(&nat()));
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&numeral(11)));
}

#[test]
fn inference_cannot_assign_opaque_or_deeper_type_holes() {
    for (kind, depth) in [(MetavarKind::SyntheticOpaque, 0), (MetavarKind::Natural, 1)] {
        let mut txn = transaction();
        let a = MVarId(name("A"));
        txn.mvars.declare(
            a.clone(),
            a.0.clone(),
            Expr::sort(Level::one()),
            txn.lctx.clone(),
            kind,
            depth,
            None,
        );
        let x = goal(&mut txn, "value", Expr::mvar(a));
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&Expr::mvar(x), &numeral(7), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn inferred_types_cannot_escape_an_older_metavariable_context() {
    let mut txn = transaction();
    let a = goal(&mut txn, "A", Expr::sort(Level::one()));
    let t = local(&mut txn, "T", Expr::sort(Level::one()));
    let value = local(&mut txn, "known", t);
    let x = goal(&mut txn, "value", Expr::mvar(a));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&Expr::mvar(x), &value, budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn a_later_failure_rolls_back_inferred_types_and_values() {
    let (mut txn, _, x) = pair();
    let before = txn.clone();
    assert!(matches!(
        txn.unify_many_with(
            &[(Expr::mvar(x), numeral(7)), (numeral(0), numeral(1)),],
            budget(),
            &|| false
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > 0);
}

#[test]
fn resource_stops_and_final_cancellation_do_not_publish_inferred_types() {
    let (base, _, x) = pair();
    let equation = [(Expr::mvar(x.clone()), numeral(7))];
    let polls = Cell::new(0usize);
    base.clone()
        .unify_many_with(&equation, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let total = polls.get();
    for stop in [0, total / 2, total - 1] {
        let mut txn = base.clone();
        let polls = Cell::new(0usize);
        assert!(matches!(
            txn.unify_many_with(&equation, budget(), &|| {
                let current = polls.get();
                polls.set(current + 1);
                current >= stop
            }),
            Err(UnificationError::Cancelled)
        ));
        unchanged(&txn, &base);
    }
    let mut txn = base.clone();
    let mut limited = budget();
    limited.max_assignments = 1;
    assert!(matches!(
        txn.unify(&Expr::mvar(x), &numeral(7), limited),
        Err(UnificationError::AssignmentLimit { limit: 1 })
    ));
    unchanged(&txn, &base);
    txn.unify_many_with(&equation, budget(), &|| false).unwrap();
}

#[test]
fn assignment_typing_still_checks_the_sort_of_an_inferred_type() {
    let mut txn = transaction();
    // A : Prop cannot be assigned Nat : Type, even though value : A can
    // syntactically acquire a natural-number value and generate A = Nat.
    let a = goal(&mut txn, "A", Expr::sort(Level::zero()));
    let x = goal(&mut txn, "value", Expr::mvar(a.clone()));
    let before = txn.clone();
    assert!(matches!(txn.unify(&Expr::mvar(x), &numeral(7), budget()),
        Err(UnificationError::AssignmentCheck { id, outcome })
            if id == a && matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. }))));
    unchanged(&txn, &before);
}

#[test]
fn a_closed_type_mismatch_retains_the_real_kernel_rejection() {
    let mut txn = transaction();
    let x = goal(&mut txn, "value", nat());
    let before = txn.clone();
    assert!(
        matches!(txn.unify(&Expr::mvar(x), &Expr::sort(Level::zero()), budget()),
        Err(UnificationError::AssignmentCheck { outcome, .. })
            if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })))
    );
    unchanged(&txn, &before);
}
