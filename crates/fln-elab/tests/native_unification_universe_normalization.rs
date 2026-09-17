//! Universe conversion through the ordinary transactional solver.
#![forbid(unsafe_code)]
use fln_core::expr::Expr;
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_elab::constraint::unify::{UnificationBudget, UnificationDeferred, UnificationError};
use fln_elab::txn::ElabTxn;
use fln_env::environment::Environment;
use fln_kernel::verdict::Budget;

fn name(text: &str) -> Name { Name::from_components([text]) }
fn p(text: &str) -> Level { Level::param(name(text)) }
fn max(a: Level, b: Level) -> Level { Level::max(a, b).unwrap() }
fn imax(a: Level, b: Level) -> Level { Level::imax(a, b).unwrap() }
fn s(level: Level) -> Level { level.succ().unwrap() }
fn pair(a: Level, b: Level) -> (Expr, Expr) { (Expr::sort(a), Expr::sort(b)) }
fn txn() -> ElabTxn { ElabTxn::new(Environment::new(), KVMap::new(), 71) }
fn budget() -> UnificationBudget { UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024)) }
fn unchanged(a: &ElabTxn, b: &ElabTxn) {
    assert_eq!(a.mvars, b.mvars);
    assert_eq!(a.universes, b.universes);
    assert_eq!(a.constraints, b.constraints);
    assert_eq!(a.env, b.env);
    assert_eq!(a.lctx, b.lctx);
    assert_eq!(a.options, b.options);
    assert_eq!(a.seed, b.seed);
}

#[test]
fn reordered_and_reassociated_maxima_unify_without_assignments() {
    for (left, right) in [
        pair(max(p("u"), p("v")), max(p("v"), p("u"))),
        pair(max(p("u"), max(p("v"), p("w"))), max(max(p("w"), p("u")), p("v"))),
        pair(max(p("u"), max(p("v"), p("u"))), max(p("v"), p("u"))),
    ] {
        let mut tx = txn();
        let before = tx.clone();
        let report = tx.unify(&left, &right, budget()).unwrap();
        assert!(report.universe_assignments.is_empty());
        assert!(report.expression_assignments.is_empty());
        assert_eq!(report.kernel_checks, 0);
        unchanged(&tx, &before);
    }
}

#[test]
fn successors_distribute_and_dominated_offsets_disappear() {
    let mut tx = txn();
    tx.unify_many_with(&[
        pair(s(max(p("u"), p("v"))), max(s(p("v")), s(p("u")))),
        pair(max(p("u"), s(s(p("u")))), s(s(p("u")))),
        pair(max(Level::one(), max(p("u"), s(p("v")))), max(p("u"), s(p("v")))),
    ], budget(), &|| false).unwrap();
}

#[test]
fn imax_uses_definite_positivity_but_does_not_guess_a_guard() {
    let mut tx = txn();
    tx.unify_many_with(&[
        pair(imax(Level::one(), p("u")), p("u")),
        pair(imax(p("u"), max(p("v"), s(p("w")))), max(max(p("w").succ().unwrap(), p("u")), p("v"))),
        pair(s(imax(p("u"), s(p("v")))), max(s(p("u")), s(s(p("v"))))),
    ], budget(), &|| false).unwrap();
    let before = tx.clone();
    let (left, right) = pair(imax(p("u"), p("v")), max(p("u"), p("v")));
    assert!(matches!(tx.unify(&left, &right, budget()), Err(UnificationError::Deferred(_))));
    unchanged(&tx, &before);
}

#[test]
fn a_later_assignment_reopens_an_imax_conversion() {
    let mut tx = txn();
    let id = LMVarId(name("guard"));
    let hole = Level::mvar(id.clone());
    let report = tx.unify_many_with(&[
        pair(imax(p("u"), hole.clone()), max(s(p("v")), p("u"))),
        pair(hole, s(p("v"))),
    ], budget(), &|| false).unwrap();
    assert_eq!(report.universe_assignments, vec![id]);
}

#[test]
fn equivalent_maxima_do_not_force_unrelated_metavariables() {
    let mut tx = txn();
    let id = LMVarId(name("unknown"));
    let hole = Level::mvar(id);
    let before = tx.clone();
    let (a, b) = pair(max(p("u"), hole.clone()), max(hole, p("u")));
    let report = tx.unify(&a, &b, budget()).unwrap();
    assert!(report.universe_assignments.is_empty());
    unchanged(&tx, &before);
}

#[test]
fn cyclic_universe_assignments_are_still_refused() {
    let mut tx = txn();
    let id = LMVarId(name("cycle"));
    let hole = Level::mvar(id);
    let before = tx.clone();
    let (a, b) = pair(hole.clone(), max(s(p("v")), hole));
    assert!(matches!(tx.unify(&a, &b, budget()),
        Err(UnificationError::Deferred(UnificationDeferred::CyclicUniverse(_)))));
    unchanged(&tx, &before);
}

#[test]
fn unequal_explicit_bounds_and_offsets_do_not_unify() {
    for (a, b) in [
        pair(max(s(s(Level::one())), s(p("u"))), s(p("u"))),
        pair(max(p("u"), s(p("v"))), max(p("v"), s(p("u")))),
        pair(s(max(p("u"), p("v"))), max(p("u"), p("v"))),
    ] {
        let mut tx = txn();
        let before = tx.clone();
        assert!(matches!(tx.unify(&a, &b, budget()), Err(UnificationError::Deferred(_))));
        unchanged(&tx, &before);
    }
}

fn large_equations() -> Vec<(Expr, Expr)> {
    let hole = Level::mvar(LMVarId(name("tentative")));
    let mut a = p("u");
    let mut b = p("u");
    for i in 0..40 {
        let next = p(&format!("v{i}"));
        a = max(a, next.clone());
        b = max(next, b);
    }
    vec![pair(hole, Level::one()), pair(a, b)]
}

#[test]
fn normalization_resource_stops_rollback_all_earlier_assignments() {
    let mut initial = txn();
    initial.budget.max_heartbeats = 10_000_000;
    let mut generous = budget();
    generous.max_steps = 5_000_000;
    generous.max_visited_nodes = 3_000_000;
    let equations = large_equations();
    let mut control = initial.clone();
    let report = control.unify_many_with(&equations, generous, &|| false).unwrap();
    let mut stopped = initial.clone();
    let mut limited = generous;
    limited.max_steps = report.unifier_steps - 1;
    assert!(matches!(stopped.unify_many_with(&equations, limited, &|| false),
        Err(UnificationError::StepLimit { .. })));
    unchanged(&stopped, &initial);
    assert!(stopped.budget.heartbeats_consumed > initial.budget.heartbeats_consumed);
    let mut stopped = initial.clone();
    let mut limited = generous;
    limited.max_visited_nodes = report.visited_nodes - 1;
    assert!(matches!(stopped.unify_many_with(&equations, limited, &|| false),
        Err(UnificationError::NodeLimit { .. })));
    unchanged(&stopped, &initial);
}

#[test]
fn final_publication_cancellation_rolls_back_normalized_universes() {
    use std::cell::Cell;
    let mut initial = txn();
    initial.budget.max_heartbeats = 10_000_000;
    let mut generous = budget();
    generous.max_steps = 5_000_000;
    generous.max_visited_nodes = 3_000_000;
    let equations = large_equations();
    let polls = Cell::new(0);
    let mut control = initial.clone();
    control.unify_many_with(&equations, generous, &|| { polls.set(polls.get() + 1); false }).unwrap();
    let stop = polls.get();
    let calls = Cell::new(0);
    let mut cancelled = initial.clone();
    assert!(matches!(cancelled.unify_many_with(&equations, generous, &|| {
        calls.set(calls.get() + 1); calls.get() >= stop
    }), Err(UnificationError::Cancelled)));
    assert_eq!(calls.get(), stop);
    unchanged(&cancelled, &initial);
    assert_eq!(cancelled.budget.heartbeats_consumed, control.budget.heartbeats_consumed);
}

#[test]
fn deeply_shared_max_dags_normalize_without_expansion_or_host_recursion() {
    std::thread::Builder::new().stack_size(128 * 1024).spawn(|| {
        let mut tx = txn();
        let mut left = max(p("u"), p("v"));
        for _ in 0..4_000 { left = max(left.clone(), left); }
        let right = max(p("v"), p("u"));
        let (left, right) = pair(left, right);
        let mut generous = budget();
        generous.max_steps = 5_000_000;
        generous.max_visited_nodes = 3_000_000;
        tx.budget.max_heartbeats = 10_000_000;
        let report = tx.unify(&left, &right, generous).unwrap();
        assert!(report.universe_assignments.is_empty());
    }).unwrap().join().unwrap();
}
