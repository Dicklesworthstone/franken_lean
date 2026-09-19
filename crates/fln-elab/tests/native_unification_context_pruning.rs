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

#[test]
fn bare_aliases_choose_the_scope_safe_orientation() {
    for reverse in [false, true] {
        let mut t = transaction();
        let witness = local(&mut t, "common", nat());
        let outer = hole(&mut t, "outer", nat());
        local(&mut t, "private", nat());
        let inner = hole(&mut t, "inner", nat());
        let (left, right) = (Expr::mvar(outer.clone()), Expr::mvar(inner.clone()));
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let before = t.clone();
        let report = t.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.expression_assignments, vec![inner.clone()]);
        assert_eq!(report.residual_metavariables, vec![outer.clone()]);
        assert_eq!(report.kernel_checks, 1);
        assert_eq!(t.mvars.len(), before.mvars.len());
        assert!(!t.mvars.is_assigned(&outer));
        assert_eq!(
            t.mvars.get_assigned_expr(&inner),
            Some(&Expr::mvar(outer.clone()))
        );
        assert_eq!(t.env, before.env);
        assert_eq!(t.lctx, before.lctx);
        t.unify(&Expr::mvar(outer), &witness, budget()).unwrap();
        assert_eq!(t.instantiate_expr(&Expr::mvar(inner)).unwrap(), witness);
    }
}

#[test]
fn bare_aliases_respect_metavariable_depth_as_well_as_local_scope() {
    for reverse in [false, true] {
        let mut t = transaction();
        let shallow = hole(&mut t, "shallow", nat());
        let deeper = MVarId(name("deeper"));
        t.mvars.declare(
            deeper.clone(),
            deeper.0.clone(),
            nat(),
            t.lctx.clone(),
            MetavarKind::Natural,
            1,
            None,
        );
        let mut limits = budget();
        limits.max_metavar_depth = 1;
        let (left, right) = (Expr::mvar(shallow.clone()), Expr::mvar(deeper.clone()));
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = t.unify(&left, &right, limits).unwrap();
        assert_eq!(report.expression_assignments, vec![deeper.clone()]);
        assert_eq!(report.residual_metavariables, vec![shallow.clone()]);
        assert!(!t.mvars.is_assigned(&shallow));
        t.unify(&Expr::mvar(shallow), &number(9), limits).unwrap();
        assert_eq!(t.instantiate_expr(&Expr::mvar(deeper)).unwrap(), number(9));
    }
}

#[test]
fn a_dependent_alias_keeps_the_shared_type_and_local_let() {
    let mut t = transaction();
    let a = local(&mut t, "A", Expr::sort(Level::one()));
    let x = local(&mut t, "x", a.clone());
    let let_id = FVarId(name("witness"));
    t.lctx
        .add_let(let_id.clone(), let_id.0.clone(), a.clone(), x.clone());
    let outer = hole(&mut t, "outer", a.clone());
    local(&mut t, "private", a.clone());
    let inner = hole(&mut t, "inner", a);
    let report = t
        .unify(
            &Expr::mvar(outer.clone()),
            &Expr::mvar(inner.clone()),
            budget(),
        )
        .unwrap();
    assert_eq!(report.expression_assignments, vec![inner.clone()]);
    t.unify(&Expr::mvar(outer), &Expr::fvar(let_id), budget())
        .unwrap();
    t.unify(&Expr::mvar(inner), &x, budget()).unwrap();
}

#[test]
fn scope_refusal_can_wait_for_a_later_residual_assignment() {
    for reverse_order in [false, true] {
        let mut t = transaction();
        let op = local(&mut t, "op", pi(nat(), nat()));
        let outer = hole(&mut t, "outer", nat());
        local(&mut t, "private", nat());
        let inner = hole(&mut t, "inner", nat());
        let mut equations = vec![
            (
                Expr::mvar(outer.clone()),
                Expr::app(op.clone(), Expr::mvar(inner.clone())),
            ),
            (Expr::mvar(inner), number(4)),
        ];
        if reverse_order {
            equations.reverse();
        }
        let report = t.unify_many_with(&equations, budget(), &|| false).unwrap();
        assert_eq!(report.kernel_checks, 2);
        assert!(report.residual_metavariables.is_empty());
        t.unify(&Expr::mvar(outer), &Expr::app(op, number(4)), budget())
            .unwrap();
    }
}

#[test]
fn an_opaque_private_residual_cannot_be_aliased_into_an_outer_scope() {
    let mut t = transaction();
    let outer = hole(&mut t, "outer", nat());
    local(&mut t, "private", nat());
    let inner = MVarId(name("opaque"));
    t.mvars.declare(
        inner.clone(),
        inner.0.clone(),
        nat(),
        t.lctx.clone(),
        MetavarKind::SyntheticOpaque,
        0,
        None,
    );
    let before = t.clone();
    assert!(
        t.unify(&Expr::mvar(outer), &Expr::mvar(inner), budget())
            .is_err()
    );
    unchanged(&t, &before);
}

#[test]
fn scope_safe_aliases_still_require_kernel_compatible_types() {
    let mut t = transaction();
    let outer = hole(&mut t, "outer", nat());
    local(&mut t, "private", nat());
    let inner = hole(&mut t, "inner", Expr::sort(Level::one()));
    let before = t.clone();
    assert!(
        t.unify(&Expr::mvar(outer), &Expr::mvar(inner), budget())
            .is_err()
    );
    unchanged(&t, &before);
}

#[test]
fn scope_safe_aliases_preserve_queued_obligation_authority() {
    let mut t = transaction();
    let outer = hole(&mut t, "outer", nat());
    local(&mut t, "private", nat());
    let inner = hole(&mut t, "inner", nat());
    let row = t.postpone(
        ConstraintKind::DefEq {
            lhs: Expr::mvar(outer.clone()),
            rhs: Expr::mvar(inner.clone()),
        },
        0,
    );
    let wait = t.postpone(
        ConstraintKind::HasType {
            expr: Expr::mvar(inner),
            expected_type: nat(),
        },
        0,
    );
    let report = t
        .solve_defeq_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![row]);
    assert_eq!(report.unification.residual_metavariables, vec![outer]);
    assert_eq!(report.unification.awakened.len(), 1);
    assert_eq!(report.unification.awakened[0].id, wait);
    assert!(matches!(
        report.unification.awakened[0].kind,
        ConstraintKind::HasType { .. }
    ));
}

#[test]
fn scope_orientation_cancellation_and_limits_are_failure_atomic() {
    let mut base = transaction();
    let a = hole(&mut base, "a", nat());
    local(&mut base, "private", nat());
    let b = hole(&mut base, "b", nat());
    let equations = [(Expr::mvar(a), Expr::mvar(b))];
    let polls = Cell::new(0);
    let report = base
        .clone()
        .unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    for stop in [0, polls.get() / 2, polls.get() - 1] {
        let mut t = base.clone();
        let current = Cell::new(0);
        assert!(matches!(
            t.unify_many_with(&equations, budget(), &|| {
                let n = current.get();
                current.set(n + 1);
                n >= stop
            }),
            Err(UnificationError::Cancelled)
        ));
        unchanged(&t, &base);
    }
    for kind in 0..3 {
        let mut t = base.clone();
        let mut limits = budget();
        match kind {
            0 => limits.max_assignments = 0,
            1 => limits.max_steps = report.unifier_steps - 1,
            _ => limits.max_visited_nodes = report.visited_nodes - 1,
        }
        assert!(t.unify_many_with(&equations, limits, &|| false).is_err());
        unchanged(&t, &base);
    }
}

fn bare_siblings(type_: Option<Expr>) -> (ElabTxn, MVarId, MVarId, Expr, Expr, Expr) {
    let mut t = transaction();
    let common = local(&mut t, "common", nat());
    let parent = t.lctx.clone();
    let left_private = local(&mut t, "left_private", nat());
    let f = hole(&mut t, "left_hole", type_.clone().unwrap_or_else(nat));
    let left_context = t.lctx.clone();
    t.lctx = parent;
    let right_private = local(&mut t, "right_private", nat());
    let g = hole(&mut t, "right_hole", type_.unwrap_or_else(nat));
    t.lctx = left_context;
    local(&mut t, "right_private", nat());
    (t, f, g, common, left_private, right_private)
}

#[test]
fn bare_sibling_holes_share_only_the_common_lexical_context() {
    for reverse in [false, true] {
        let (mut t, f, g, witness, left_private, right_private) = bare_siblings(None);
        let mut common = t.lctx.clone();
        common.truncate(1);
        let (left, right) = (Expr::mvar(f.clone()), Expr::mvar(g.clone()));
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let before = t.clone();
        let report = t.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.kernel_checks, 2);
        assert_eq!(report.expression_assignments.len(), 2);
        assert_eq!(report.residual_metavariables.len(), 1);
        let residual = report.residual_metavariables[0].clone();
        assert!(!t.mvars.is_assigned(&residual));
        assert_eq!(t.mvars.len(), before.mvars.len() + 1);
        assert_eq!(t.mvars.get_decl(&residual).unwrap().lctx, common);
        for private in [left_private, right_private] {
            let before = t.clone();
            assert!(
                t.unify(&Expr::mvar(residual.clone()), &private, budget())
                    .is_err()
            );
            unchanged(&t, &before);
        }
        t.unify(&Expr::mvar(residual), &witness, budget()).unwrap();
        assert_eq!(t.instantiate_expr(&Expr::mvar(f)).unwrap(), witness);
        assert_eq!(t.instantiate_expr(&Expr::mvar(g)).unwrap(), witness);
        assert_eq!(t.env, before.env);
        assert_eq!(t.lctx, before.lctx);
    }
}

#[test]
fn a_bare_hole_and_an_applied_hole_can_share_a_scope_safe_result() {
    for reverse in [false, true] {
        let mut t = transaction();
        let witness = local(&mut t, "common", nat());
        let parent = t.lctx.clone();
        local(&mut t, "left_private", nat());
        let bare = hole(&mut t, "bare", nat());
        let left_context = t.lctx.clone();
        t.lctx = parent;
        local(&mut t, "right_private", nat());
        let f = hole(&mut t, "f", pi(nat(), nat()));
        t.lctx = left_context;
        local(&mut t, "right_private", nat());
        let x = local(&mut t, "x", nat());
        let pair = (
            Expr::mvar(bare.clone()),
            Expr::app(Expr::mvar(f.clone()), x),
        );
        let (left, right) = if reverse { (pair.1, pair.0) } else { pair };
        let report = t.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.kernel_checks, 2);
        let residual = report.residual_metavariables[0].clone();
        assert_eq!(t.mvars.get_decl(&residual).unwrap().lctx.len(), 1);
        t.unify(&Expr::mvar(residual), &witness, budget()).unwrap();
        t.unify(&Expr::mvar(bare), &witness, budget()).unwrap();
        t.unify(&Expr::app(Expr::mvar(f), number(123)), &witness, budget())
            .unwrap();
    }
}

#[test]
fn bare_dependent_proof_holes_remain_obligations_not_inhabitants() {
    let mut t = transaction();
    let proposition = local(&mut t, "P", Expr::sort(Level::zero()));
    let parent = t.lctx.clone();
    local(&mut t, "left_private", nat());
    let a = hole(&mut t, "a", proposition.clone());
    t.lctx = parent.clone();
    local(&mut t, "right_private", nat());
    let b = hole(&mut t, "b", proposition.clone());
    let report = t
        .unify(&Expr::mvar(a.clone()), &Expr::mvar(b.clone()), budget())
        .unwrap();
    assert_eq!(report.residual_metavariables.len(), 1);
    let residual = report.residual_metavariables[0].clone();
    let declaration = t.mvars.get_decl(&residual).unwrap();
    assert_eq!(declaration.type_, proposition);
    assert_eq!(declaration.lctx, parent);
    assert!(!t.mvars.is_assigned(&residual));
    assert!(t.instantiate_expr(&Expr::mvar(a)).unwrap().has_expr_mvar());
    assert!(t.instantiate_expr(&Expr::mvar(b)).unwrap().has_expr_mvar());
    let before = t.clone();
    assert!(
        t.unify(&Expr::mvar(residual), &number(0), budget())
            .is_err()
    );
    unchanged(&t, &before);
}

#[test]
fn multiple_bare_scope_equations_reuse_the_common_residual() {
    let (mut t, a, b, witness, _, _) = bare_siblings(None);
    t.lctx.truncate(1);
    local(&mut t, "third_private", nat());
    let c = hole(&mut t, "third", nat());
    let report = t
        .unify_many_with(
            &[
                (Expr::mvar(a.clone()), Expr::mvar(b.clone())),
                (Expr::mvar(b.clone()), Expr::mvar(c.clone())),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.kernel_checks, 3);
    assert_eq!(report.residual_metavariables.len(), 1);
    t.unify(
        &Expr::mvar(report.residual_metavariables[0].clone()),
        &witness,
        budget(),
    )
    .unwrap();
    for id in [a, b, c] {
        assert_eq!(t.instantiate_expr(&Expr::mvar(id)).unwrap(), witness);
    }
}

#[test]
fn a_private_dependency_of_the_residual_type_cannot_escape_through_a_bare_hole() {
    let mut t = transaction();
    let private_type = local(&mut t, "private_type", Expr::sort(Level::one()));
    let a = hole(&mut t, "a", private_type.clone());
    t.lctx.truncate(0);
    local(&mut t, "other_private", nat());
    let b = hole(&mut t, "b", private_type);
    let before = t.clone();
    assert!(t.unify(&Expr::mvar(a), &Expr::mvar(b), budget()).is_err());
    unchanged(&t, &before);
}

#[test]
fn malformed_bare_residual_types_remain_subject_to_the_kernel_veto() {
    let (mut t, a, b, _, _, _) = bare_siblings(Some(Expr::app(nat(), number(1))));
    let before = t.clone();
    assert!(t.unify(&Expr::mvar(a), &Expr::mvar(b), budget()).is_err());
    unchanged(&t, &before);
}

#[test]
fn bare_context_pruning_never_publishes_partial_residuals() {
    let (base, a, b, _, _, _) = bare_siblings(None);
    let equations = [(Expr::mvar(a), Expr::mvar(b))];
    let polls = Cell::new(0);
    let report = base
        .clone()
        .unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    for stop in [0, polls.get() / 2, polls.get() - 1] {
        let mut t = base.clone();
        let count = Cell::new(0);
        assert!(matches!(
            t.unify_many_with(&equations, budget(), &|| {
                let n = count.get();
                count.set(n + 1);
                n >= stop
            }),
            Err(UnificationError::Cancelled)
        ));
        unchanged(&t, &base);
    }
    for kind in 0..4 {
        let mut t = base.clone();
        let mut limits = budget();
        match kind {
            0 => limits.max_assignments = 1,
            1 => limits.max_steps = report.unifier_steps - 1,
            2 => limits.max_visited_nodes = report.visited_nodes - 1,
            _ => limits.kernel = limits.kernel.narrowed(0, limits.kernel.depth),
        }
        assert!(t.unify_many_with(&equations, limits, &|| false).is_err());
        unchanged(&t, &base);
    }
}

#[test]
fn a_later_conflict_restores_the_bare_scope_queue_and_all_holes() {
    let (mut t, a, b, _, left_private, _) = bare_siblings(None);
    let row = t.postpone(
        ConstraintKind::DefEq {
            lhs: Expr::mvar(a.clone()),
            rhs: Expr::mvar(b),
        },
        0,
    );
    let conflict = t.postpone(
        ConstraintKind::DefEq {
            lhs: Expr::mvar(a),
            rhs: left_private,
        },
        0,
    );
    let before = t.clone();
    assert!(
        t.solve_defeq_constraints_with(&[row, conflict], budget(), &|| false)
            .is_err()
    );
    unchanged(&t, &before);
    let report = t
        .solve_defeq_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![row]);
    assert_eq!(report.unification.residual_metavariables.len(), 1);
    assert!(report.unification.awakened.iter().any(|c| c.id == conflict));
}
