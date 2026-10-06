//! Ground computation must not roll back otherwise solved implicit arguments.
#![forbid(unsafe_code)]

use fln::{Budget, Engine, EngineAdmissionLimits, KVMap, SourceCheckLimits};
use fln_core::expr::{Expr, Literal, MVarId, NatLit};
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_elab::mvar::MetavarKind;
use fln_elab::txn::ElabTxn;
use std::cell::Cell;

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn engine() -> Engine {
    Engine::with_coercion_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap()
}
fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}: {error:?}"))
    .into_complete()
    .expect("both checkers must complete")
    .engine
}
fn numeral(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_components(["Nat", "add"]), vec![]), a),
        b,
    )
}
fn transaction(base: &Engine) -> ElabTxn {
    ElabTxn::new(base.environment().clone(), KVMap::new(), 17)
}
fn budget() -> UnificationBudget {
    let mut budget = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    budget.transparency = UnificationTransparency::SafeDefinitions;
    budget
}
fn hole(txn: &mut ElabTxn, kind: MetavarKind) -> MVarId {
    let id = MVarId(Name::from_components(["conversion_hole"]));
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        Expr::const_(Name::from_components(["Nat"]), vec![]),
        txn.lctx.clone(),
        kind,
        0,
        None,
    );
    id
}
fn unchanged(txn: &ElabTxn, before: &ElabTxn) {
    assert_eq!(txn.mvars, before.mvars);
    assert_eq!(txn.universes, before.universes);
    assert_eq!(txn.constraints, before.constraints);
    assert_eq!(txn.lctx, before.lctx);
    assert_eq!(txn.env, before.env);
    assert_eq!(txn.options, before.options);
    assert_eq!(txn.seed, before.seed);
}

#[test]
fn term_rfl_computes_through_the_ordinary_dual_checker_path() {
    let base = engine();
    for source in [
        "theorem t : Nat.add 2 2 = 4 := rfl",
        "theorem t : 2 + 2 = 4 := rfl",
        "def f (n : Nat) : Nat := n + 1\ntheorem t : f 3 = 4 := rfl",
        "theorem t : Nat.mul 3 7 = 21 := rfl",
        "theorem t : Nat.add (Nat.mul 3 7) 2 = 23 := rfl",
        "theorem t : 2 + 2 = 4 := by rfl",
    ] {
        let result = checked(&base, source);
        assert!(result.environment().contains(&Name::from_components(["t"])));
    }
}

#[test]
fn computed_rfl_preserves_scoped_let_values_and_parameters() {
    let base = engine();
    for source in [
        "theorem t : (let n : Nat := 2; Nat.add n n) = 4 := rfl",
        "theorem t (n : Nat) : (let k : Nat := 2; Nat.add k k) = 4 := rfl",
        "theorem t : (let n : Nat := 2; let n : Nat := n + 1; n + 1) = 4 := rfl",
    ] {
        checked(&base, source);
    }
}

#[test]
fn false_computed_equalities_publish_nothing_and_allow_recovery() {
    let base = engine();
    let root = base.logical_root(&KVMap::new());
    for source in [
        "theorem bad : Nat.add 2 2 = 5 := rfl",
        "theorem bad : Nat.mul 3 7 = 22 := rfl",
        "def prefix : Nat := 7\ntheorem bad : 2 + 2 = 5 := rfl",
        "theorem bad (n : Nat) : Nat.add 2 2 = n := rfl",
        "theorem bad : (let n : Nat := 3; Nat.add n n) = 4 := rfl",
    ] {
        assert!(base.check_source_files(
            &[source.as_bytes()], &KVMap::new(), SourceCheckLimits::new(limits()),
        ).is_err(), "{source}");
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(!base.environment().contains(&Name::from_components(["prefix"])));
        assert!(!base.environment().contains(&Name::from_components(["bad"])));
    }
    checked(&base, "theorem recovery : 2 + 2 = 4 := rfl");
}

#[test]
fn ground_conversion_finishes_a_batch_without_publishing_a_declaration() {
    let base = engine();
    let mut txn = transaction(&base);
    let id = hole(&mut txn, MetavarKind::Natural);
    let env = txn.env.clone();
    let report = txn.unify_many_with(
        &[(Expr::mvar(id.clone()), numeral(7)), (add(numeral(2), numeral(2)), numeral(4))],
        budget(), &|| false,
    ).unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&id), Some(&numeral(7)));
    assert!(report.kernel_checks >= 2, "conversion and assignment must both be checked");
    assert_eq!(txn.env, env);
}

#[test]
fn failed_ground_conversion_rolls_back_an_earlier_assignment() {
    let base = engine();
    let mut txn = transaction(&base);
    let id = hole(&mut txn, MetavarKind::Natural);
    let before = txn.clone();
    assert!(txn.unify_many_with(
        &[(Expr::mvar(id), numeral(7)), (add(numeral(2), numeral(2)), numeral(5))],
        budget(), &|| false,
    ).is_err());
    unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn conversion_does_not_widen_restricted_transparency_or_assign_opaque_holes() {
    let base = engine();
    for transparency in [UnificationTransparency::None, UnificationTransparency::Abbreviations,
        UnificationTransparency::Instances] {
        let mut txn = transaction(&base);
        let before = txn.clone();
        let mut restricted = budget();
        restricted.transparency = transparency;
        assert!(txn.unify(&add(numeral(2), numeral(2)), &numeral(4), restricted).is_err());
        unchanged(&txn, &before);
    }
    let mut txn = transaction(&base);
    let id = hole(&mut txn, MetavarKind::SyntheticOpaque);
    let before = txn.clone();
    assert!(txn.unify(&Expr::mvar(id), &add(numeral(2), numeral(2)), budget()).is_err());
    unchanged(&txn, &before);
}

#[test]
fn kernel_conversion_exhaustion_is_a_typed_nonanswer_and_is_atomic() {
    let base = engine();
    let mut txn = transaction(&base);
    let id = hole(&mut txn, MetavarKind::Natural);
    let before = txn.clone();
    let mut limited = budget();
    limited.kernel = limited.kernel.narrowed(0, limited.kernel.depth);
    let error = txn.unify_many_with(
        &[(Expr::mvar(id), numeral(7)), (add(numeral(2), numeral(2)), numeral(4))],
        limited, &|| false,
    ).unwrap_err();
    assert!(matches!(error, UnificationError::ConversionCheck { outcome }
        if matches!(*outcome, Outcome::Inconclusive(_))));
    unchanged(&txn, &before);
}

#[test]
fn cancellation_at_observed_checkpoints_never_commits_a_partial_batch() {
    let base = engine();
    let mut control = transaction(&base);
    let id = hole(&mut control, MetavarKind::Natural);
    let pairs = [(Expr::mvar(id), numeral(7)), (add(numeral(2), numeral(2)), numeral(4))];
    let initial = control.clone();
    let polls = Cell::new(0_u64);
    control.unify_many_with(&pairs, budget(), &|| { polls.set(polls.get() + 1); false }).unwrap();
    let total = polls.get();
    assert!(total > 2);
    for stop in [1, total / 2, total] {
        let mut txn = initial.clone();
        let polls = Cell::new(0_u64);
        assert!(matches!(txn.unify_many_with(&pairs, budget(), &|| {
            polls.set(polls.get() + 1);
            polls.get() >= stop
        }), Err(UnificationError::Cancelled)), "checkpoint {stop}/{total}");
        unchanged(&txn, &initial);
    }
}
