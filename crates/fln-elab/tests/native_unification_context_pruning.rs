//! Pruning across lexical scopes, through the native solver and K1 checks.
#![forbid(unsafe_code)]
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::ConstraintKind;
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
    Expr::const_(name("Nat"), vec![])
}
fn number(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn pi(a: Expr, b: Expr) -> Expr {
    Expr::forall_e(name("n"), a, b, BinderInfo::Default)
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
fn local(t: &mut ElabTxn, s: &str, type_: Expr) -> Expr {
    let id = FVarId(name(s));
    t.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn hole(t: &mut ElabTxn, s: &str, type_: Expr) -> MVarId {
    let id = MVarId(name(s));
    t.mvars.declare(
        id.clone(),
        id.0.clone(),
        type_,
        t.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    id
}
fn unchanged(t: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = t.budget.heartbeats_consumed;
    assert_eq!(t, &expected);
}
fn nested() -> (ElabTxn, Expr, Expr) {
    let mut t = transaction();
    local(&mut t, "common", nat());
    let f = hole(&mut t, "f", pi(nat(), nat()));
    local(&mut t, "private", nat());
    let g = hole(&mut t, "g", pi(nat(), nat()));
    let x = local(&mut t, "x", nat());
    let y = local(&mut t, "y", nat());
    (t, Expr::app(Expr::mvar(f), x), Expr::app(Expr::mvar(g), y))
}

#[test]
fn nested_contexts_retain_a_dependent_result_and_common_witness() {
    for reverse in [false, true] {
        let mut t = transaction();
        let a = local(&mut t, "A", Expr::sort(Level::one()));
        let witness = local(&mut t, "witness", a.clone());
        let common = t.lctx.clone();
        let f = hole(&mut t, "f", pi(nat(), a.clone()));
        let private = local(&mut t, "private", a.clone());
        let g = hole(&mut t, "g", pi(nat(), a.clone()));
        let x = local(&mut t, "x", nat());
        let y = local(&mut t, "y", nat());
        let pair = (
            Expr::app(Expr::mvar(f.clone()), x),
            Expr::app(Expr::mvar(g.clone()), y),
        );
        let (left, right) = if reverse { (pair.1, pair.0) } else { pair };
        let env = t.env.clone();
        let report = t.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.kernel_checks, 2);
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        let decl = t.mvars.get_decl(&residual).unwrap();
        assert_eq!(decl.lctx, common);
        assert_eq!(decl.type_, a);
        let before = t.clone();
        assert!(
            t.unify(&Expr::mvar(residual.clone()), &private, budget())
                .is_err()
        );
        unchanged(&t, &before);
        t.unify(&Expr::mvar(residual), &witness, budget()).unwrap();
        for id in [f, g] {
            t.unify(&Expr::app(Expr::mvar(id), number(3)), &witness, budget())
                .unwrap();
        }
        assert_eq!(t.env, env);
    }
}

#[test]
fn sibling_contexts_capture_the_common_parent_not_either_private_branch() {
    let mut t = transaction();
    let witness = local(&mut t, "common", nat());
    let parent = t.lctx.clone();
    let left_private = local(&mut t, "left_private", nat());
    let f = hole(&mut t, "f", pi(nat(), nat()));
    let left_context = t.lctx.clone();
    t.lctx = parent.clone();
    let right_private = local(&mut t, "right_private", nat());
    let g = hole(&mut t, "g", pi(nat(), nat()));
    // Both input terms have an ambient interpretation, but assignments retain
    // their own original scopes, not this larger ambient context.
    t.lctx = left_context;
    local(&mut t, "right_private", nat());
    let x = local(&mut t, "x", nat());
    let y = local(&mut t, "y", nat());
    let report = t
        .unify(
            &Expr::app(Expr::mvar(f), x),
            &Expr::app(Expr::mvar(g), y),
            budget(),
        )
        .unwrap();
    assert_eq!(report.kernel_checks, 2);
    let residual = report.residual_metavariables[0].clone();
    assert_eq!(t.mvars.get_decl(&residual).unwrap().lctx, parent);
    for private in [left_private, right_private] {
        let before = t.clone();
        assert!(
            t.unify(&Expr::mvar(residual.clone()), &private, budget())
                .is_err()
        );
        unchanged(&t, &before);
    }
    t.unify(&Expr::mvar(residual), &witness, budget()).unwrap();
}

#[test]
fn common_let_values_survive_without_importing_a_private_let() {
    let mut t = transaction();
    let id = FVarId(name("common"));
    t.lctx.add_let(id.clone(), id.0.clone(), nat(), number(12));
    let common = t.lctx.clone();
    let f = hole(&mut t, "f", pi(nat(), nat()));
    let private = FVarId(name("private"));
    t.lctx
        .add_let(private.clone(), private.0, nat(), number(77));
    let g = hole(&mut t, "g", pi(nat(), nat()));
    let x = local(&mut t, "x", nat());
    let y = local(&mut t, "y", nat());
    let report = t
        .unify(
            &Expr::app(Expr::mvar(f.clone()), x),
            &Expr::app(Expr::mvar(g), y),
            budget(),
        )
        .unwrap();
    let residual = report.residual_metavariables[0].clone();
    assert_eq!(t.mvars.get_decl(&residual).unwrap().lctx, common);
    t.unify(&Expr::mvar(residual), &Expr::fvar(id), budget())
        .unwrap();
    t.unify(&Expr::app(Expr::mvar(f), number(0)), &number(12), budget())
        .unwrap();
}

#[test]
fn a_result_depending_on_a_noncommon_local_cannot_be_retagged() {
    let mut t = transaction();
    let a = local(&mut t, "private_type", Expr::sort(Level::one()));
    let f = hole(&mut t, "f", pi(nat(), a.clone()));
    t.lctx.truncate(0);
    // Deliberately malformed metavariable declaration. Pruning cannot turn it
    // into a well-scoped declaration by inventing a captured type parameter.
    let g = hole(&mut t, "g", pi(nat(), a));
    let x = local(&mut t, "x", nat());
    let y = local(&mut t, "y", nat());
    let before = t.clone();
    assert!(
        t.unify(
            &Expr::app(Expr::mvar(f), x),
            &Expr::app(Expr::mvar(g), y),
            budget()
        )
        .is_err()
    );
    unchanged(&t, &before);
}

#[test]
fn queued_nested_scope_obligations_keep_residual_and_wakeup_authority() {
    let (mut t, left, right) = nested();
    let row = t.postpone(
        ConstraintKind::DefEq {
            lhs: left.clone(),
            rhs: right.clone(),
        },
        0,
    );
    let waiting = t.postpone(
        ConstraintKind::HasType {
            expr: left,
            expected_type: nat(),
        },
        0,
    );
    let report = t
        .solve_defeq_constraints_with(&[row, row], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![row]);
    assert_eq!(report.unification.awakened.len(), 1);
    assert_eq!(report.unification.awakened[0].id, waiting);
    assert!(matches!(
        report.unification.awakened[0].kind,
        ConstraintKind::HasType { .. }
    ));
    let residual = &report.unification.residual_metavariables[0];
    assert!(!t.mvars.is_assigned(residual));
}

#[test]
fn cancellation_and_native_limits_leave_no_cross_scope_assignments() {
    let (base, left, right) = nested();
    let polls = Cell::new(0);
    let report = base
        .clone()
        .unify_many_with(&[(left.clone(), right.clone())], budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    for stop in [0, polls.get() / 2, polls.get() - 1] {
        let mut t = base.clone();
        let count = Cell::new(0);
        assert!(matches!(
            t.unify_many_with(&[(left.clone(), right.clone())], budget(), &|| {
                let n = count.get();
                count.set(n + 1);
                n >= stop
            }),
            Err(UnificationError::Cancelled)
        ));
        unchanged(&t, &base);
    }
    for axis in 0..3 {
        let mut t = base.clone();
        let mut limits = budget();
        match axis {
            0 => limits.max_assignments = 1,
            1 => limits.max_steps = report.unifier_steps - 1,
            _ => limits.max_visited_nodes = report.visited_nodes - 1,
        }
        assert!(t.unify(&left, &right, limits).is_err());
        unchanged(&t, &base);
        t.unify(&left, &right, budget()).unwrap();
    }
}

#[test]
fn kernel_stops_and_late_contradictions_rollback_the_shared_context() {
    let (base, left, right) = nested();
    let mut t = base.clone();
    let mut limits = budget();
    limits.kernel = limits.kernel.narrowed(0, limits.kernel.depth);
    match t.unify(&left, &right, limits).unwrap_err() {
        UnificationError::AssignmentCheck { outcome, .. } => {
            assert!(matches!(*outcome, Outcome::Inconclusive(_)))
        }
        other => panic!("expected a K1 resource stop: {other:?}"),
    }
    unchanged(&t, &base);
    assert!(
        t.unify_many_with(&[(left, right), (number(0), number(1))], budget(), &|| {
            false
        })
        .is_err()
    );
    unchanged(&t, &base);
}
