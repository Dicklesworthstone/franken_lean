//! Empty-record parameters are constraints, never a reason to erase an open term.
#![forbid(unsafe_code)]
use super::*;
use fln_core::level::LMVarId;

fn parameterized() -> (ElabTxn, MVarId, Expr, Expr) {
    let mut tx = txn();
    let parameter = hole(
        &mut tx,
        "parameter",
        Expr::sort(Level::one()),
        MetavarKind::Natural,
    );
    let a = local(
        &mut tx,
        "a",
        app(constant("Phantom"), [Expr::mvar(parameter.clone())]),
    );
    let b = local(&mut tx, "b", app(constant("Phantom"), [constant("Nat")]));
    (tx, parameter, a, b)
}

#[test]
fn neutral_record_types_infer_parameters_in_both_orientations() {
    for reverse in [false, true] {
        let (mut tx, parameter, a, b) = parameterized();
        let before = tx.clone();
        let (a, b) = if reverse { (b, a) } else { (a, b) };
        let report = tx.unify(&a, &b, budget()).unwrap();
        assert_eq!(report.expression_assignments, vec![parameter.clone()]);
        assert_eq!(
            tx.mvars.get_assigned_expr(&parameter),
            Some(&constant("Nat"))
        );
        assert!(
            report.kernel_checks >= 2,
            "both inhabitants and the assignment must be checked"
        );
        assert!(report.residual_metavariables.is_empty());
        assert_eq!(tx.env, before.env);
        assert_eq!(tx.lctx, before.lctx);
    }
}

#[test]
fn zero_field_universes_are_inferred_not_defaulted() {
    for reverse in [false, true] {
        let mut tx = txn();
        record(
            &mut tx,
            "PolyUnit",
            vec![],
            vec![],
            Level::param(name("u")).succ().unwrap(),
            vec![name("u")],
        );
        let universe = LMVarId(name("unknown"));
        let a = local(
            &mut tx,
            "a",
            Expr::const_(name("PolyUnit"), vec![Level::mvar(universe.clone())]),
        );
        let b = local(
            &mut tx,
            "b",
            Expr::const_(name("PolyUnit"), vec![Level::one()]),
        );
        let (a, b) = if reverse { (b, a) } else { (a, b) };
        let report = tx.unify(&a, &b, budget()).unwrap();
        assert_eq!(report.universe_assignments, vec![universe.clone()]);
        assert_eq!(
            tx.universes.instantiate(&Level::mvar(universe)).unwrap(),
            Level::one()
        );
        assert!(report.expression_assignments.is_empty());
    }
}

#[test]
fn unknown_universes_without_an_equation_remain_unknown() {
    let mut tx = txn();
    record(
        &mut tx,
        "PolyUnit",
        vec![],
        vec![],
        Level::param(name("u")).succ().unwrap(),
        vec![name("u")],
    );
    let universe = Level::mvar(LMVarId(name("unknown")));
    let ty = Expr::const_(name("PolyUnit"), vec![universe]);
    let a = local(&mut tx, "a", ty.clone());
    let b = local(&mut tx, "b", ty);
    let before = tx.clone();
    assert!(tx.unify(&a, &b, budget()).is_err());
    unchanged(&tx, &before);
}

#[test]
fn empty_record_parameters_feed_higher_order_pattern_inference() {
    let mut tx = txn();
    record(
        &mut tx,
        "Tagged",
        vec![binder("tag", constant("Nat"))],
        vec![],
        Level::one(),
        vec![],
    );
    let function = hole(
        &mut tx,
        "function",
        pi(constant("Nat"), constant("Nat")),
        MetavarKind::Natural,
    );
    let x = local(&mut tx, "x", constant("Nat"));
    let a = local(
        &mut tx,
        "a",
        app(
            constant("Tagged"),
            [Expr::app(Expr::mvar(function.clone()), x.clone())],
        ),
    );
    let b = local(&mut tx, "b", app(constant("Tagged"), [x]));
    let report = tx.unify(&a, &b, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![function.clone()]);
    let value = tx.mvars.get_assigned_expr(&function).unwrap().clone();
    tx.unify(&Expr::app(value, number(13)), &number(13), budget())
        .unwrap();
}

#[test]
fn later_equations_reveal_blocked_receiver_types() {
    let mut tx = txn();
    let ty = hole(
        &mut tx,
        "receiver_type",
        Expr::sort(Level::one()),
        MetavarKind::Natural,
    );
    let a = local(&mut tx, "a", Expr::mvar(ty.clone()));
    let b = local(&mut tx, "b", constant("Empty"));
    let report = tx
        .unify_many_with(
            &[(a, b), (Expr::mvar(ty.clone()), constant("Empty"))],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.expression_assignments, vec![ty]);
}

#[test]
fn malformed_original_terms_are_rechecked_after_parameter_inference() {
    let (mut tx, parameter, _, b) = parameterized();
    let f = local(
        &mut tx,
        "f",
        pi(
            constant("Nat"),
            app(constant("Phantom"), [Expr::mvar(parameter)]),
        ),
    );
    let bad = Expr::app(f, constant("Bool.true"));
    let before = tx.clone();
    assert!(tx.unify(&bad, &b, budget()).is_err());
    unchanged(&tx, &before);
}

#[test]
fn type_progress_cannot_discard_opaque_arguments_or_opaque_parameters() {
    for kind in [MetavarKind::Natural, MetavarKind::SyntheticOpaque] {
        let mut tx = txn();
        let parameter = hole(&mut tx, "parameter", Expr::sort(Level::one()), kind);
        let hidden = hole(
            &mut tx,
            "hidden",
            constant("Nat"),
            MetavarKind::SyntheticOpaque,
        );
        let f = local(
            &mut tx,
            "f",
            pi(
                constant("Nat"),
                app(constant("Phantom"), [Expr::mvar(parameter)]),
            ),
        );
        let b = local(&mut tx, "b", app(constant("Phantom"), [constant("Nat")]));
        let before = tx.clone();
        assert!(
            tx.unify(&Expr::app(f, Expr::mvar(hidden)), &b, budget())
                .is_err()
        );
        unchanged(&tx, &before);
    }
}

#[test]
fn inferred_parameters_cannot_capture_newer_locals() {
    let mut tx = txn();
    let parameter = hole(
        &mut tx,
        "parameter",
        Expr::sort(Level::one()),
        MetavarKind::Natural,
    );
    let newer = local(&mut tx, "newer", Expr::sort(Level::one()));
    let a = local(
        &mut tx,
        "a",
        app(constant("Phantom"), [Expr::mvar(parameter)]),
    );
    let b = local(&mut tx, "b", app(constant("Phantom"), [newer]));
    let before = tx.clone();
    assert!(tx.unify(&a, &b, budget()).is_err());
    unchanged(&tx, &before);
}

#[test]
fn later_failure_discards_parameter_inference_without_refunding_work() {
    let (mut tx, _, a, b) = parameterized();
    let before = tx.clone();
    assert!(
        tx.unify_many_with(&[(a, b), (number(0), number(1))], budget(), &|| false)
            .is_err()
    );
    unchanged(&tx, &before);
    assert!(tx.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn kernel_exhaustion_after_type_inference_is_a_nonanswer() {
    let (mut tx, _, a, b) = parameterized();
    let before = tx.clone();
    let mut tiny = budget();
    tiny.kernel = tiny.kernel.narrowed(0, tiny.kernel.depth);
    assert!(
        matches!(tx.unify(&a, &b, tiny), Err(UnificationError::ConversionCheck { outcome }) if matches!(*outcome, Outcome::Inconclusive(_)))
    );
    unchanged(&tx, &before);
}

#[test]
fn cancellation_at_publication_discards_inferred_parameters() {
    use std::cell::Cell;
    let (mut tx, _, a, b) = parameterized();
    let before = tx.clone();
    let polls = Cell::new(0);
    tx.clone()
        .unify_many_with(&[(a.clone(), b.clone())], budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let last = polls.get();
    let calls = Cell::new(0);
    assert!(matches!(
        tx.unify_many_with(&[(a.clone(), b.clone())], budget(), &|| {
            calls.set(calls.get() + 1);
            calls.get() == last
        }),
        Err(UnificationError::Cancelled)
    ));
    unchanged(&tx, &before);
}
