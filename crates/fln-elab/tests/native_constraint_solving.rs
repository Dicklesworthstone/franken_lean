//! Real mixed constraint execution: inference is not a typing verdict.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::constraint::{ConstraintId, ConstraintKind, ConstraintSolveError};
use fln_elab::mvar::MetavarKind;
use fln_elab::seed::bootstrap_nat_environment;
use fln_elab::txn::ElabTxn;
use fln_kernel::verdict::{Budget, Verdict};
use std::cell::Cell;

fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn lit(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn pi(a: Expr, b: Expr) -> Expr {
    Expr::forall_e(name("x"), a, b, BinderInfo::Default)
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn txn() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        113,
    )
}
fn hole(tx: &mut ElabTxn, s: &str, ty: Expr, kind: MetavarKind) -> MVarId {
    let id = MVarId(name(s));
    tx.mvars
        .declare(id.clone(), id.0.clone(), ty, tx.lctx.clone(), kind, 0, None);
    id
}
fn local(tx: &mut ElabTxn, s: &str, ty: Expr) -> Expr {
    let id = FVarId(name(s));
    tx.lctx
        .add_param(id.clone(), id.0.clone(), ty, BinderInfo::Default);
    Expr::fvar(id)
}
fn has_type(tx: &mut ElabTxn, expr: Expr, expected_type: Expr) -> ConstraintId {
    tx.postpone(
        ConstraintKind::HasType {
            expr,
            expected_type,
        },
        0,
    )
}
fn defeq(tx: &mut ElabTxn, lhs: Expr, rhs: Expr) -> ConstraintId {
    tx.postpone(ConstraintKind::DefEq { lhs, rhs }, 0)
}
fn unchanged(tx: &ElabTxn, before: &ElabTxn) {
    let mut before = before.clone();
    before.budget.heartbeats_consumed = tx.budget.heartbeats_consumed;
    assert_eq!(tx, &before);
}

#[test]
fn mixed_batches_infer_types_and_publish_only_selected_rows() {
    for reverse in [false, true] {
        let mut tx = txn();
        let ty = hole(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
        let n = hole(&mut tx, "n", nat(), MetavarKind::Natural);
        let typing = has_type(&mut tx, lit(7), Expr::mvar(ty.clone()));
        let equation = defeq(&mut tx, Expr::mvar(n.clone()), lit(4));
        let untouched = has_type(&mut tx, lit(8), nat());
        let mut selected = vec![typing, equation, typing];
        if reverse {
            selected.reverse();
        }
        let env = tx.env.clone();
        let report = tx
            .solve_constraints_with(&selected, budget(), &|| false)
            .unwrap();
        assert_eq!(report.solved, vec![typing, equation]);
        assert_eq!(report.unification.kernel_checks, 3);
        assert_eq!(tx.mvars.get_assigned_expr(&ty), Some(&nat()));
        assert_eq!(tx.mvars.get_assigned_expr(&n), Some(&lit(4)));
        assert_eq!(
            tx.mvars.len(),
            2,
            "typing must not manufacture a temporary goal"
        );
        assert_eq!(tx.constraints.len(), 1);
        assert!(tx.constraints.constraints().contains_key(&untouched));
        assert_eq!(tx.env, env);
    }
}

#[test]
fn a_closed_expected_type_can_infer_an_open_values_declared_type() {
    let mut tx = txn();
    let ty = hole(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
    let value = hole(
        &mut tx,
        "value",
        Expr::mvar(ty.clone()),
        MetavarKind::Natural,
    );
    let row = has_type(&mut tx, Expr::mvar(value.clone()), nat());
    let report = tx
        .solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.mvars.get_assigned_expr(&ty), Some(&nat()));
    assert!(!tx.mvars.is_assigned(&value));
    assert_eq!(report.unification.residual_metavariables, vec![value]);
    assert_eq!(report.unification.kernel_checks, 2);
    assert_eq!(tx.mvars.len(), 2);
}

#[test]
fn checking_a_proof_holes_type_never_solves_the_proof() {
    let mut tx = txn();
    let proposition = local(&mut tx, "P", Expr::sort(Level::zero()));
    let proof = hole(
        &mut tx,
        "proof",
        proposition.clone(),
        MetavarKind::SyntheticOpaque,
    );
    let row = has_type(&mut tx, Expr::mvar(proof.clone()), proposition);
    let before_mvars = tx.mvars.clone();
    let report = tx
        .solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.mvars, before_mvars);
    assert_eq!(report.unification.residual_metavariables, vec![proof]);
    assert!(report.unification.expression_assignments.is_empty());
    assert_eq!(report.unification.kernel_checks, 1);
}

#[test]
fn structured_typing_and_chained_type_discoveries_use_the_same_worklist() {
    for reverse in [false, true] {
        let mut tx = txn();
        let f_type = hole(&mut tx, "F", Expr::sort(Level::one()), MetavarKind::Natural);
        let op = local(&mut tx, "op", Expr::mvar(f_type.clone()));
        let result_type = hole(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
        let value = Expr::lam(
            name("x"),
            nat(),
            Expr::app(op.clone(), Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        );
        let first = has_type(&mut tx, value, Expr::mvar(result_type.clone()));
        let second = has_type(&mut tx, op, pi(nat(), nat()));
        let mut ids = vec![first, second];
        if reverse {
            ids.reverse();
        }
        let report = tx
            .solve_constraints_with(&ids, budget(), &|| false)
            .unwrap();
        assert_eq!(tx.mvars.get_assigned_expr(&f_type), Some(&pi(nat(), nat())));
        assert_eq!(
            tx.mvars.get_assigned_expr(&result_type),
            Some(&pi(nat(), nat()))
        );
        assert!(report.unification.residual_metavariables.is_empty());
        assert_eq!(tx.lctx.len(), 1);
        assert_eq!(report.unification.kernel_checks, 4);
    }
}

#[test]
fn typing_constraints_infer_universes_without_defaulting_other_holes() {
    let mut tx = txn();
    let u = LMVarId(name("u"));
    let row = has_type(
        &mut tx,
        Expr::sort(Level::mvar(u.clone())),
        Expr::sort(Level::one()),
    );
    let report = tx
        .solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(report.unification.universe_assignments, vec![u.clone()]);
    assert_eq!(
        tx.universes.instantiate(&Level::mvar(u)).unwrap(),
        Level::zero()
    );
    assert!(!tx.universes.is_assigned(&LMVarId(name("unrelated"))));
}

#[test]
fn correct_type_hints_cannot_hide_ill_typed_arguments_or_let_annotations() {
    for bad_let in [false, true] {
        let mut tx = txn();
        let op = local(&mut tx, "op", pi(nat(), nat()));
        let invalid = if bad_let {
            Expr::let_e(name("bad"), nat(), Expr::sort(Level::zero()), lit(7), false)
        } else {
            Expr::app(op, Expr::sort(Level::zero()))
        };
        let row = has_type(&mut tx, invalid, nat());
        let n = hole(&mut tx, "n", nat(), MetavarKind::Natural);
        let equation = defeq(&mut tx, Expr::mvar(n), lit(5));
        let before = tx.clone();
        let error = tx
            .solve_constraints_with(&[row, equation], budget(), &|| false)
            .unwrap_err();
        assert!(matches!(error,
            ConstraintSolveError::Unification(UnificationError::ConstraintCheck { id, outcome })
            if id == row && matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. }))
        ));
        unchanged(&tx, &before);
        let correct = has_type(&mut tx, lit(7), nat());
        tx.solve_constraints_with(&[correct, equation], budget(), &|| false)
            .unwrap();
        assert!(tx.constraints.constraints().contains_key(&row));
    }
}

#[test]
fn incompatible_typing_equations_preserve_all_rows_and_assignments() {
    let mut tx = txn();
    let ty = hole(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
    let first = has_type(&mut tx, lit(7), Expr::mvar(ty.clone()));
    let second = has_type(&mut tx, Expr::sort(Level::zero()), Expr::mvar(ty));
    let before = tx.clone();
    assert!(
        tx.solve_constraints_with(&[first, second], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
}

#[test]
fn awakened_typing_and_instance_rows_are_not_reported_solved() {
    let mut tx = txn();
    let ty = hole(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
    let row = has_type(&mut tx, lit(7), Expr::mvar(ty.clone()));
    let other = has_type(&mut tx, lit(8), Expr::mvar(ty.clone()));
    let instance = tx.postpone(
        ConstraintKind::SynthInstance {
            class: Expr::mvar(ty),
            mvar: MVarId(name("out")),
        },
        0,
    );
    let report = tx
        .solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![row]);
    assert_eq!(
        report
            .unification
            .awakened
            .iter()
            .map(|c| c.id)
            .collect::<Vec<_>>(),
        vec![other, instance]
    );
}

#[test]
fn selection_refuses_missing_deep_and_foreign_constraints_before_mutation() {
    let mut tx = txn();
    let row = has_type(&mut tx, lit(7), nat());
    let foreign = tx.postpone(
        ConstraintKind::SynthInstance {
            class: nat(),
            mvar: MVarId(name("x")),
        },
        0,
    );
    let deep = tx.postpone(
        ConstraintKind::HasType {
            expr: lit(7),
            expected_type: nat(),
        },
        1,
    );
    let before = tx.clone();
    assert!(
        matches!(tx.solve_constraints_with(&[row, foreign], budget(), &|| false), Err(ConstraintSolveError::UnsupportedKind(id)) if id == foreign)
    );
    assert!(matches!(
        tx.solve_constraints_with(&[row, deep], budget(), &|| false),
        Err(ConstraintSolveError::Depth { .. })
    ));
    assert!(matches!(
        tx.solve_constraints_with(&[ConstraintId(u64::MAX)], budget(), &|| false),
        Err(ConstraintSolveError::Missing(_))
    ));
    assert!(
        matches!(tx.solve_defeq_constraints_with(&[row], budget(), &|| false), Err(ConstraintSolveError::NotDefEq(id)) if id == row)
    );
    assert_eq!(tx, before);
}

fn inference_batch() -> (ElabTxn, ConstraintId) {
    let mut tx = txn();
    let ty = hole(&mut tx, "T", Expr::sort(Level::one()), MetavarKind::Natural);
    let id = has_type(&mut tx, lit(7), Expr::mvar(ty));
    (tx, id)
}

#[test]
fn cancellation_including_final_publication_restores_the_queue() {
    let (base, row) = inference_batch();
    let polls = Cell::new(0);
    base.clone()
        .solve_constraints_with(&[row], budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    for stop in [0, polls.get() / 2, polls.get() - 1] {
        let mut tx = base.clone();
        let calls = Cell::new(0);
        assert!(matches!(
            tx.solve_constraints_with(&[row], budget(), &|| {
                let now = calls.get();
                calls.set(now + 1);
                now >= stop
            }),
            Err(ConstraintSolveError::Unification(
                UnificationError::Cancelled
            ))
        ));
        unchanged(&tx, &base);
    }
}

#[test]
fn shared_assignment_step_and_node_budgets_cannot_publish_partial_typing() {
    let (base, row) = inference_batch();
    let measured = base
        .clone()
        .solve_constraints_with(&[row], budget(), &|| false)
        .unwrap()
        .unification;
    for limit in 0..3 {
        let mut b = budget();
        match limit {
            0 => b.max_assignments = 0,
            1 => b.max_steps = measured.unifier_steps - 1,
            _ => b.max_visited_nodes = measured.visited_nodes - 1,
        }
        let mut tx = base.clone();
        assert!(tx.solve_constraints_with(&[row], b, &|| false).is_err());
        unchanged(&tx, &base);
    }
}

#[test]
fn a_kernel_nonanswer_is_retained_instead_of_becoming_a_typing_verdict() {
    let mut tx = txn();
    let row = has_type(&mut tx, lit(7), nat());
    let before = tx.clone();
    let mut b = budget();
    b.kernel = b.kernel.narrowed(0, b.kernel.depth);
    assert!(matches!(tx.solve_constraints_with(&[row], b, &|| false),
        Err(ConstraintSolveError::Unification(UnificationError::ConstraintCheck { id, outcome }))
        if id == row && matches!(*outcome, Outcome::Inconclusive(_))
    ));
    unchanged(&tx, &before);
}

#[test]
fn dependent_local_types_and_let_values_are_closed_without_escaping() {
    let mut tx = txn();
    let a = local(&mut tx, "A", Expr::sort(Level::one()));
    let x = local(&mut tx, "x", a.clone());
    let alias = FVarId(name("alias"));
    tx.lctx
        .add_let(alias.clone(), alias.0.clone(), a.clone(), x);
    let row = has_type(&mut tx, Expr::fvar(alias), a);
    let before_locals = tx.lctx.clone();
    let report = tx
        .solve_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(tx.lctx, before_locals);
    assert!(tx.mvars.is_empty());
    assert_eq!(report.unification.kernel_checks, 1);
    let invalid = has_type(&mut tx, Expr::fvar(FVarId(name("not_in_scope"))), nat());
    let before = tx.clone();
    assert!(
        tx.solve_constraints_with(&[invalid], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
}

#[test]
fn unresolved_type_shapes_stop_without_discarding_the_obligation() {
    let mut tx = txn();
    let f_type = hole(
        &mut tx,
        "F",
        Expr::sort(Level::one()),
        MetavarKind::SyntheticOpaque,
    );
    let op = local(&mut tx, "op", Expr::mvar(f_type));
    let row = has_type(&mut tx, Expr::app(op, lit(0)), nat());
    let before = tx.clone();
    assert!(
        tx.solve_constraints_with(&[row], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
}
