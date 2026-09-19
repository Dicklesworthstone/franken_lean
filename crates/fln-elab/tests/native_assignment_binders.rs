//! Binder-aware assignment type inference through the ordinary native solver.
#![forbid(unsafe_code)]
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, MVarId, NatLit};
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

fn name(s: &str) -> Name {
    Name::from_components([s])
}
fn nat() -> Expr {
    Expr::const_(name("Nat"), vec![])
}
fn number(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn bvar(i: u32) -> Expr {
    Expr::bvar(i).unwrap()
}
fn pi(a: Expr, b: Expr) -> Expr {
    Expr::forall_e(name("x"), a, b, BinderInfo::Default)
}
fn lam(a: Expr, b: Expr) -> Expr {
    Expr::lam(name("x"), a, b, BinderInfo::Default)
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024))
}
fn transaction() -> ElabTxn {
    ElabTxn::new(
        bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        29,
    )
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
fn local(t: &mut ElabTxn, s: &str, type_: Expr) -> Expr {
    let id = FVarId(name(s));
    t.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn pair(t: &mut ElabTxn) -> (MVarId, MVarId, LMVarId) {
    let u = LMVarId(name("type_universe"));
    let a = hole(t, "type", Expr::sort(Level::mvar(u.clone())));
    let f = hole(t, "value", Expr::mvar(a.clone()));
    (a, f, u)
}
fn unchanged(t: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = t.budget.heartbeats_consumed;
    assert_eq!(t, &expected);
}

#[test]
fn lambda_assignments_infer_function_types_and_their_universes() {
    for reverse in [false, true] {
        let mut t = transaction();
        let (a, f, u) = pair(&mut t);
        let value = lam(nat(), bvar(0));
        let (left, right) = (Expr::mvar(f.clone()), value.clone());
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = t.unify(&left, &right, budget()).unwrap();
        assert_eq!(report.kernel_checks, 2);
        assert!(report.residual_metavariables.is_empty());
        assert_eq!(t.mvars.get_assigned_expr(&f), Some(&value));
        t.unify(&Expr::mvar(a), &pi(nat(), nat()), budget())
            .unwrap();
        assert_eq!(
            t.universes.instantiate(&Level::mvar(u)).unwrap(),
            Level::one()
        );
        assert!(t.lctx.is_empty());
    }
}

#[test]
fn dependent_lambda_telescope_is_closed_capture_avoidantly() {
    let mut t = transaction();
    let (a, f, u) = pair(&mut t);
    let value = lam(Expr::sort(Level::one()), lam(bvar(0), bvar(0)));
    let env = t.env.clone();
    let report = t.unify(&Expr::mvar(f), &value, budget()).unwrap();
    assert_eq!(report.kernel_checks, 2);
    let type_ = t.mvars.get_assigned_expr(&a).unwrap();
    assert!(!type_.has_fvar() && !type_.has_loose_bvars());
    t.unify(
        &Expr::mvar(a),
        &pi(Expr::sort(Level::one()), pi(bvar(0), bvar(1))),
        budget(),
    )
    .unwrap();
    assert_eq!(
        t.universes.instantiate(&Level::mvar(u)).unwrap(),
        Level::succ(Level::one()).unwrap()
    );
    assert_eq!(t.env, env);
}

#[test]
fn pi_type_inference_preserves_prop_impredicativity() {
    for is_prop in [false, true] {
        let mut t = transaction();
        let codomain = if is_prop {
            local(&mut t, "P", Expr::sort(Level::zero()))
        } else {
            nat()
        };
        let (a, f, u) = pair(&mut t);
        // Quantification over types is still Prop when the codomain is Prop.
        let value = pi(Expr::sort(Level::one()), codomain);
        t.unify(&Expr::mvar(f), &value, budget()).unwrap();
        let sort = if is_prop {
            Level::zero()
        } else {
            Level::succ(Level::one()).unwrap()
        };
        assert_eq!(
            t.mvars.get_assigned_expr(&a),
            Some(&Expr::sort(sort.clone()))
        );
        assert_eq!(
            t.universes.instantiate(&Level::mvar(u)).unwrap(),
            Level::succ(sort).unwrap()
        );
    }
}

#[test]
fn parametric_universes_are_retained_in_inferred_pi_sorts() {
    let mut t = transaction();
    let u = Level::param(name("u"));
    let v = Level::param(name("v"));
    let a = local(&mut t, "A", Expr::sort(u.clone()));
    let b = local(&mut t, "B", Expr::sort(v.clone()));
    let (type_hole, value, _) = pair(&mut t);
    t.unify(&Expr::mvar(value), &pi(a, b), budget()).unwrap();
    let expected = Expr::sort(Level::imax(u, v).unwrap());
    t.unify(&Expr::mvar(type_hole), &expected, budget())
        .unwrap();
}

#[test]
fn binder_style_and_shadowed_local_identity_survive_synthesis() {
    for style in [
        BinderInfo::Implicit,
        BinderInfo::StrictImplicit,
        BinderInfo::InstImplicit,
    ] {
        let mut t = transaction();
        let id = FVarId(Name::from_components(["_fln_unify_local", "0"]));
        t.lctx
            .add_param(id.clone(), name("x"), nat(), BinderInfo::Default);
        let captured = Expr::fvar(id);
        let (a, f, _) = pair(&mut t);
        let value = Expr::lam(name("x"), nat(), captured.clone(), style);
        let before = t.lctx.clone();
        t.unify(&Expr::mvar(f.clone()), &value, budget()).unwrap();
        let ExprNode::ForallE {
            binder_info,
            binder_type,
            body,
            ..
        } = t.mvars.get_assigned_expr(&a).unwrap().node()
        else {
            panic!("expected inferred function type");
        };
        assert_eq!(*binder_info, style);
        assert_eq!(binder_type, &nat());
        assert_eq!(body, &nat());
        assert_eq!(t.mvars.get_assigned_expr(&f), Some(&value));
        assert_eq!(t.lctx, before);
        t.unify(&Expr::app(Expr::mvar(f), number(7)), &captured, budget())
            .unwrap();
    }
}

#[test]
fn an_applied_pattern_infers_a_missing_function_valued_result_family() {
    let mut t = transaction();
    let family = hole(&mut t, "Family", pi(nat(), Expr::sort(Level::one())));
    let f = hole(
        &mut t,
        "f",
        pi(nat(), Expr::app(Expr::mvar(family.clone()), bvar(0))),
    );
    let x = local(&mut t, "x", nat());
    let report = t
        .unify(
            &Expr::app(Expr::mvar(f.clone()), x.clone()),
            &lam(nat(), x),
            budget(),
        )
        .unwrap();
    assert_eq!(report.kernel_checks, 2);
    assert!(report.residual_metavariables.is_empty());
    t.unify(&Expr::mvar(family), &lam(nat(), pi(nat(), nat())), budget())
        .unwrap();
    t.unify(
        &Expr::app(Expr::app(Expr::mvar(f), number(3)), number(9)),
        &number(3),
        budget(),
    )
    .unwrap();
}

#[test]
fn invalid_lambda_applications_are_vetoed_after_type_hinting() {
    let mut t = transaction();
    let op = local(&mut t, "op", pi(nat(), nat()));
    let (_, f, _) = pair(&mut t);
    let before = t.clone();
    let value = lam(nat(), Expr::app(op, Expr::sort(Level::zero())));
    let error = t.unify(&Expr::mvar(f), &value, budget()).unwrap_err();
    assert!(
        matches!(error, UnificationError::AssignmentCheck { outcome, .. }
        if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })))
    );
    unchanged(&t, &before);
}

#[test]
fn nested_let_type_hints_do_not_erase_original_value_checks() {
    for invalid in [false, true] {
        let mut t = transaction();
        let (a, f, _) = pair(&mut t);
        let let_value = if invalid {
            Expr::sort(Level::zero())
        } else {
            bvar(0)
        };
        // The let is unused by the result but remains inside the assigned lambda.
        let value = lam(
            nat(),
            Expr::let_e(name("unused"), nat(), let_value, bvar(1), false),
        );
        let before = t.clone();
        let result = t.unify(&Expr::mvar(f.clone()), &value, budget());
        if invalid {
            assert!(
                matches!(result, Err(UnificationError::AssignmentCheck { outcome, .. })
                if matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })))
            );
            unchanged(&t, &before);
        } else {
            assert_eq!(result.unwrap().kernel_checks, 2);
            assert_eq!(t.mvars.get_assigned_expr(&f), Some(&value));
            t.unify(&Expr::mvar(a), &pi(nat(), nat()), budget())
                .unwrap();
        }
    }
}

#[test]
fn dependent_let_domains_close_without_leaking_the_opened_binder() {
    let mut t = transaction();
    let (a, f, _) = pair(&mut t);
    let body = Expr::let_e(
        name("A"),
        Expr::sort(Level::one()),
        nat(),
        lam(bvar(0), bvar(0)),
        false,
    );
    let value = lam(nat(), body);
    t.unify(&Expr::mvar(f), &value, budget()).unwrap();
    t.unify(&Expr::mvar(a), &pi(nat(), pi(nat(), nat())), budget())
        .unwrap();
    assert!(t.lctx.is_empty());
}

#[test]
fn missing_lambda_domains_stay_explicit_until_a_later_solution() {
    let mut t = transaction();
    let domain = hole(&mut t, "domain", Expr::sort(Level::one()));
    let (a, f, _) = pair(&mut t);
    let value = lam(Expr::mvar(domain.clone()), bvar(0));
    let report = t.unify(&Expr::mvar(f.clone()), &value, budget()).unwrap();
    assert!(!t.mvars.is_assigned(&domain));
    assert_eq!(report.residual_metavariables, vec![domain.clone()]);
    t.unify(&Expr::mvar(domain), &nat(), budget()).unwrap();
    t.unify(&Expr::mvar(a), &pi(nat(), nat()), budget())
        .unwrap();
    t.unify(&Expr::app(Expr::mvar(f), number(23)), &number(23), budget())
        .unwrap();
}

#[test]
fn opaque_and_deeper_type_holes_are_not_assigned_by_binder_synthesis() {
    for opaque in [false, true] {
        let mut t = transaction();
        let a = MVarId(name("type"));
        t.mvars.declare(
            a.clone(),
            a.0.clone(),
            Expr::sort(Level::one()),
            t.lctx.clone(),
            if opaque {
                MetavarKind::SyntheticOpaque
            } else {
                MetavarKind::Natural
            },
            if opaque { 0 } else { 1 },
            None,
        );
        let f = hole(&mut t, "f", Expr::mvar(a));
        let before = t.clone();
        assert!(matches!(
            t.unify(&Expr::mvar(f), &lam(nat(), bvar(0)), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&t, &before);
    }
}

#[test]
fn queued_lambda_type_inference_does_not_claim_awakened_typing_obligations() {
    let mut t = transaction();
    let (a, f, _) = pair(&mut t);
    let row = t.postpone(
        ConstraintKind::DefEq {
            lhs: Expr::mvar(f.clone()),
            rhs: lam(nat(), bvar(0)),
        },
        0,
    );
    let waiting = t.postpone(
        ConstraintKind::HasType {
            expr: Expr::mvar(f),
            expected_type: Expr::mvar(a),
        },
        0,
    );
    let report = t
        .solve_defeq_constraints_with(&[row], budget(), &|| false)
        .unwrap();
    assert_eq!(report.solved, vec![row]);
    assert_eq!(report.unification.awakened.len(), 1);
    assert_eq!(report.unification.awakened[0].id, waiting);
    assert!(matches!(
        report.unification.awakened[0].kind,
        ConstraintKind::HasType { .. }
    ));
}

#[test]
fn binder_synthesis_has_bounded_work_and_failure_atomic_publication() {
    let mut base = transaction();
    let (_, f, _) = pair(&mut base);
    let value = lam(Expr::sort(Level::one()), lam(bvar(0), bvar(0)));
    let equations = [(Expr::mvar(f), value)];
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
        let calls = Cell::new(0);
        assert!(matches!(
            t.unify_many_with(&equations, budget(), &|| {
                let n = calls.get();
                calls.set(n + 1);
                n >= stop
            }),
            Err(UnificationError::Cancelled)
        ));
        unchanged(&t, &base);
    }
    for axis in 0..4 {
        let mut t = base.clone();
        let mut limits = budget();
        match axis {
            0 => limits.max_steps = report.unifier_steps - 1,
            1 => limits.max_visited_nodes = report.visited_nodes - 1,
            2 => limits.max_assignments = 1,
            _ => limits.kernel = limits.kernel.narrowed(0, limits.kernel.depth),
        }
        let error = t
            .unify_many_with(&equations, limits, &|| false)
            .unwrap_err();
        if axis == 3 {
            assert!(
                matches!(error, UnificationError::AssignmentCheck { outcome, .. } if matches!(*outcome, Outcome::Inconclusive(_)))
            );
        }
        unchanged(&t, &base);
        t.unify_many_with(&equations, budget(), &|| false).unwrap();
    }
}

#[test]
fn deep_lambda_synthesis_uses_the_same_meter_and_can_stop_before_k1() {
    for depth in [8, 24, 40] {
        let mut t = transaction();
        let (a, f, _) = pair(&mut t);
        let mut value = number(3);
        let mut type_ = nat();
        for _ in 0..depth {
            value = lam(nat(), value);
            type_ = pi(nat(), type_);
        }
        let before = t.clone();
        let mut limited = budget();
        limited.max_steps = 30;
        assert!(t.unify(&Expr::mvar(f.clone()), &value, limited).is_err());
        unchanged(&t, &before);
        let mut limits = budget();
        limits.max_steps = 190_000;
        t.unify(&Expr::mvar(f), &value, limits).unwrap();
        t.unify(&Expr::mvar(a), &type_, budget()).unwrap();
        assert!(t.lctx.is_empty());
    }
}
