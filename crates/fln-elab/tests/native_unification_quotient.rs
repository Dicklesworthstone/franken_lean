//! Quotient computation through the real transaction and K1 assignment barrier.
#![forbid(unsafe_code)]

#[path = "support/quotient.rs"]
mod quotient;

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_elab::mvar::MetavarKind;
use fln_elab::txn::ElabTxn;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn constant(text: &str) -> Expr {
    Expr::const_(name(text), vec![])
}
fn bv(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn numeral(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}
fn lambda(text: &str, domain: Expr, body: Expr) -> Expr {
    Expr::lam(name(text), domain, body, BinderInfo::Default)
}
fn pi(text: &str, domain: Expr, body: Expr) -> Expr {
    Expr::forall_e(name(text), domain, body, BinderInfo::Default)
}
fn eq_at(level: Level, type_: Expr, left: Expr, right: Expr) -> Expr {
    apply(Expr::const_(name("Eq"), vec![level]), [type_, left, right])
}
fn refl_at(level: Level, type_: Expr, term: Expr) -> Expr {
    apply(Expr::const_(name("Eq.refl"), vec![level]), [type_, term])
}
fn relation() -> Expr {
    lambda(
        "a",
        constant("Nat"),
        lambda(
            "b",
            constant("Nat"),
            eq_at(Level::one(), constant("Nat"), bv(1), bv(0)),
        ),
    )
}
fn quotient_type() -> Expr {
    apply(
        Expr::const_(name("Quot"), vec![Level::one()]),
        [constant("Nat"), relation()],
    )
}
fn representative(value: Expr) -> Expr {
    apply(
        Expr::const_(name("Quot.mk"), vec![Level::one()]),
        [constant("Nat"), relation(), value],
    )
}
fn identity() -> Expr {
    lambda("a", constant("Nat"), bv(0))
}
fn identity_respects() -> Expr {
    lambda(
        "a",
        constant("Nat"),
        lambda(
            "b",
            constant("Nat"),
            lambda(
                "h",
                eq_at(Level::one(), constant("Nat"), bv(1), bv(0)),
                bv(0),
            ),
        ),
    )
}
fn lift_with(major: Expr, result_type: Expr, branch: Expr, proof: Expr) -> Expr {
    apply(
        Expr::const_(name("Quot.lift"), vec![Level::one(), Level::one()]),
        [
            constant("Nat"),
            relation(),
            result_type,
            branch,
            proof,
            major,
        ],
    )
}
fn lift(major: Expr) -> Expr {
    lift_with(major, constant("Nat"), identity(), identity_respects())
}
fn induction(major: Expr) -> Expr {
    let motive = lambda(
        "q",
        quotient_type(),
        eq_at(Level::one(), quotient_type(), bv(0), bv(0)),
    );
    let branch = lambda(
        "a",
        constant("Nat"),
        refl_at(Level::one(), quotient_type(), representative(bv(0))),
    );
    apply(
        Expr::const_(name("Quot.ind"), vec![Level::one()]),
        [constant("Nat"), relation(), motive, branch, major],
    )
}
fn budget() -> UnificationBudget {
    let mut budget = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    budget.transparency = UnificationTransparency::None;
    budget
}
/// K1 checks the original (not pre-reduced) expression in the statement and
/// verifies the proposed equation via reflexivity at the expected result.
/// This prevents a malformed fixture from appearing green solely because the
/// elaborator erased an ill-typed branch or proof argument while reducing it.
fn k1_proves_computation(
    txn: &ElabTxn,
    level: Level,
    type_: Expr,
    original: &Expr,
    expected: &Expr,
) {
    let id = name("_quotient_test_computation");
    let candidate = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: id.clone(),
            level_params: vec![],
            type_: eq_at(
                level.clone(),
                type_.clone(),
                original.clone(),
                expected.clone(),
            ),
        },
        value: refl_at(level, type_, expected.clone()),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![id],
    });
    let outcome = check(&txn.env, &candidate, budget().kernel);
    assert!(
        matches!(outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "K1 did not validate the original quotient equation: {outcome:?}"
    );
}

fn publish_block(env: &Environment, declaration: Declaration) -> Environment {
    let admission = admit(env, declaration, budget().kernel);
    let Outcome::Complete(admitted) = admission else {
        panic!("block admission did not complete");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("K1 rejected the quotient test fixture");
    };
    let Outcome::Complete(Published::BlockCommitted(publication)) = checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) else {
        panic!("block publication did not complete");
    };
    publication.environment
}
fn transaction() -> ElabTxn {
    let mut env = Environment::new();
    for declaration in [
        fln_elab::seed::nat_inductive_seed_declaration(),
        fln_elab::seed::bool_seed_declaration(),
        fln_elab::seed::eq_seed_declaration(),
        quotient::quotient_declaration(),
    ] {
        env = publish_block(&env, declaration);
    }
    ElabTxn::new(env, KVMap::new(), 41)
}
fn local(txn: &mut ElabTxn, text: &str, type_: Expr) -> Expr {
    let id = FVarId(name(text));
    txn.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
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
fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    assert_eq!(actual.mvars, before.mvars);
    assert_eq!(actual.universes, before.universes);
    assert_eq!(actual.constraints, before.constraints);
    assert_eq!(actual.env, before.env);
    assert_eq!(actual.lctx, before.lctx);
    assert_eq!(actual.options, before.options);
    assert_eq!(actual.seed, before.seed);
}

#[test]
fn quotient_initialization_requires_eq_and_rejects_forged_types() {
    assert!(matches!(
        check(
            &Environment::new(),
            &quotient::quotient_declaration(),
            budget().kernel
        ),
        Outcome::Complete(Verdict::Rejected { .. })
    ));
    let env = publish_block(&Environment::new(), fln_elab::seed::eq_seed_declaration());
    let Declaration::Quotient(mut rows) = quotient::quotient_declaration() else {
        unreachable!()
    };
    rows[2].base.type_ = Expr::sort(Level::one());
    assert!(matches!(
        check(&env, &Declaration::Quotient(rows), budget().kernel),
        Outcome::Complete(Verdict::Rejected { .. })
    ));
}

#[test]
fn quotient_lift_computes_in_both_orientations_without_delta() {
    for reversed in [false, true] {
        let mut txn = transaction();
        let left = lift(representative(numeral(37)));
        let right = numeral(37);
        k1_proves_computation(&txn, Level::one(), constant("Nat"), &left, &right);
        let before = txn.clone();
        let (left, right) = if reversed {
            (&right, &left)
        } else {
            (&left, &right)
        };
        let report = txn.unify(left, right, budget()).unwrap();
        assert_eq!(report.kernel_checks, 0);
        assert!(report.expression_assignments.is_empty());
        unchanged(&txn, &before);
    }
}

#[test]
fn quotient_induction_computes_a_dependent_proof() {
    let mut txn = transaction();
    let q = representative(numeral(37));
    let expected = refl_at(Level::one(), quotient_type(), q.clone());
    k1_proves_computation(
        &txn,
        Level::zero(),
        eq_at(Level::one(), quotient_type(), q.clone(), q.clone()),
        &induction(q.clone()),
        &expected,
    );
    let report = txn
        .unify(&induction(q.clone()), &expected, budget())
        .unwrap();
    assert_eq!(report.kernel_checks, 0);
    // An independent use of the equation result: assignment is still checked
    // against the dependent proposition by the ordinary K1 barrier.
    let proof = goal(
        &mut txn,
        "proof",
        eq_at(Level::one(), quotient_type(), q.clone(), q.clone()),
    );
    let report = txn
        .unify(&Expr::mvar(proof.clone()), &induction(q), budget())
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(txn.mvars.get_assigned_expr(&proof), Some(&expected));
}

#[test]
fn a_quotient_valued_assignment_is_validated_by_k1() {
    let mut txn = transaction();
    let id = goal(&mut txn, "q", quotient_type());
    let value = representative(numeral(5));
    let report = txn
        .unify(&Expr::mvar(id.clone()), &value, budget())
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(txn.mvars.get_assigned_expr(&id), Some(&value));
}

#[test]
fn a_later_major_assignment_reawakens_quotient_computation() {
    let mut txn = transaction();
    let q = goal(&mut txn, "q", quotient_type());
    let report = txn
        .unify_many_with(
            &[
                (lift(Expr::mvar(q.clone())), numeral(37)),
                (Expr::mvar(q.clone()), representative(numeral(37))),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.expression_assignments, vec![q]);
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn a_later_universe_assignment_reawakens_quotient_computation() {
    let mut txn = transaction();
    let u = LMVarId(name("pending_quotient_universe"));
    let expr = apply(
        Expr::const_(
            name("Quot.lift"),
            vec![Level::mvar(u.clone()), Level::one()],
        ),
        [
            constant("Nat"),
            relation(),
            constant("Nat"),
            identity(),
            identity_respects(),
            representative(numeral(37)),
        ],
    );
    let report = txn
        .unify_many_with(
            &[
                (expr, numeral(37)),
                (Expr::sort(Level::mvar(u.clone())), Expr::sort(Level::one())),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.universe_assignments, vec![u]);
    assert_eq!(report.kernel_checks, 0);
}

#[test]
fn quotient_computation_preserves_trailing_function_arguments() {
    let mut txn = transaction();
    let function_type = pi("a", constant("Nat"), constant("Nat"));
    let branch = lambda("a", constant("Nat"), identity());
    let proof = lambda(
        "a",
        constant("Nat"),
        lambda(
            "b",
            constant("Nat"),
            lambda(
                "h",
                eq_at(Level::one(), constant("Nat"), bv(1), bv(0)),
                refl_at(Level::one(), function_type.clone(), identity()),
            ),
        ),
    );
    let expr = Expr::app(
        lift_with(representative(numeral(5)), function_type, branch, proof),
        numeral(73),
    );
    k1_proves_computation(&txn, Level::one(), constant("Nat"), &expr, &numeral(73));
    txn.unify(&expr, &numeral(73), budget()).unwrap();
}

#[test]
fn lift_preserves_distinct_source_and_result_universes() {
    let mut txn = transaction();
    let universe = Level::one().succ().unwrap();
    let alpha = Expr::sort(Level::one());
    let r = lambda(
        "A",
        alpha.clone(),
        lambda(
            "B",
            alpha.clone(),
            eq_at(universe.clone(), alpha.clone(), bv(1), bv(0)),
        ),
    );
    let q = apply(
        Expr::const_(name("Quot.mk"), vec![universe.clone()]),
        [alpha.clone(), r.clone(), constant("Nat")],
    );
    let f = lambda("A", alpha.clone(), numeral(9));
    let h = lambda(
        "A",
        alpha.clone(),
        lambda(
            "B",
            alpha.clone(),
            lambda(
                "h",
                eq_at(universe.clone(), alpha.clone(), bv(1), bv(0)),
                refl_at(Level::one(), constant("Nat"), numeral(9)),
            ),
        ),
    );
    let expr = apply(
        Expr::const_(name("Quot.lift"), vec![universe, Level::one()]),
        [alpha, r, constant("Nat"), f, h, q],
    );
    k1_proves_computation(&txn, Level::one(), constant("Nat"), &expr, &numeral(9));
    let out = goal(&mut txn, "out", constant("Nat"));
    let report = txn
        .unify(&expr, &Expr::mvar(out.clone()), budget())
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(txn.mvars.get_assigned_expr(&out), Some(&numeral(9)));
}

#[test]
fn quotient_reduction_composes_with_beta_zeta_and_inductive_iota() {
    let mut txn = transaction();
    let choose = apply(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        [
            lambda("b", constant("Bool"), quotient_type()),
            representative(numeral(4)),
            representative(numeral(9)),
            constant("Bool.true"),
        ],
    );
    let id = FVarId(name("chosen_quotient"));
    txn.lctx
        .add_let(id.clone(), id.0.clone(), quotient_type(), choose);
    let major = Expr::app(lambda("q", quotient_type(), bv(0)), Expr::fvar(id));
    txn.unify(&lift(major), &numeral(9), budget()).unwrap();
}

#[test]
fn neutral_quotients_remain_blocked_and_unchanged() {
    let mut txn = transaction();
    let q = local(&mut txn, "q", quotient_type());
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&lift(q), &numeral(37), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn malformed_constructor_arities_and_universes_do_not_reduce() {
    for bad in [
        Expr::const_(name("Quot.mk"), vec![Level::one()]),
        apply(
            Expr::const_(name("Quot.mk"), vec![Level::one()]),
            [constant("Nat"), relation()],
        ),
        Expr::app(representative(numeral(37)), numeral(99)),
        apply(
            Expr::const_(name("Quot.mk"), vec![]),
            [constant("Nat"), relation(), numeral(37)],
        ),
        apply(
            Expr::const_(name("Quot.mk"), vec![Level::zero()]),
            [constant("Nat"), relation(), numeral(37)],
        ),
        apply(
            Expr::const_(name("User.Quot.mk"), vec![Level::one()]),
            [constant("Nat"), relation(), numeral(37)],
        ),
    ] {
        let mut txn = transaction();
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&lift(bad), &numeral(37), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn partial_eliminators_and_wrong_universe_arity_do_not_reduce() {
    for expr in [
        apply(
            Expr::const_(name("Quot.lift"), vec![Level::one(), Level::one()]),
            [
                constant("Nat"),
                relation(),
                constant("Nat"),
                identity(),
                identity_respects(),
            ],
        ),
        apply(
            Expr::const_(name("Quot.lift"), vec![Level::one()]),
            [
                constant("Nat"),
                relation(),
                constant("Nat"),
                identity(),
                identity_respects(),
                representative(numeral(37)),
            ],
        ),
        apply(
            Expr::const_(name("Quot.ind"), vec![Level::one(), Level::one()]),
            [
                constant("Nat"),
                relation(),
                constant("Nat"),
                identity(),
                representative(numeral(37)),
            ],
        ),
    ] {
        let mut txn = transaction();
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&expr, &numeral(37), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn quotient_step_cannot_publish_an_ill_typed_representative() {
    let mut txn = transaction();
    let id = goal(&mut txn, "n", constant("Nat"));
    let before = txn.clone();
    let expr = lift(representative(constant("Bool.true")));
    match txn
        .unify(&Expr::mvar(id.clone()), &expr, budget())
        .unwrap_err()
    {
        UnificationError::AssignmentCheck { id: found, outcome } => {
            assert_eq!(found, id);
            assert!(matches!(
                *outcome,
                Outcome::Complete(Verdict::Rejected { .. })
            ));
        }
        other => panic!("expected the ordinary K1 veto, got {other:?}"),
    }
    unchanged(&txn, &before);
}

#[test]
fn a_later_failure_discards_a_quotient_driven_assignment() {
    let mut txn = transaction();
    let id = goal(&mut txn, "n", constant("Nat"));
    let before = txn.clone();
    assert!(matches!(
        txn.unify_many_with(
            &[
                (lift(representative(Expr::mvar(id))), numeral(37)),
                (lift(representative(numeral(9))), numeral(8)),
            ],
            budget(),
            &|| false
        ),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn quotient_computation_does_not_unfold_closed_local_lets() {
    let mut txn = transaction();
    let id = FVarId(name("q"));
    txn.lctx.add_let(
        id.clone(),
        id.0.clone(),
        quotient_type(),
        representative(numeral(37)),
    );
    let expr = lift(Expr::fvar(id));
    let before = txn.clone();
    let mut closed = budget();
    closed.zeta_delta = false;
    assert!(matches!(
        txn.unify(&expr, &numeral(37), closed),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
    txn.unify(&expr, &numeral(37), budget()).unwrap();
}

#[test]
fn quotient_branches_feed_ordinary_higher_order_pattern_inference() {
    let mut txn = transaction();
    let x = local(&mut txn, "x", constant("Nat"));
    let f = goal(&mut txn, "f", pi("n", constant("Nat"), constant("Nat")));
    let function = Expr::mvar(f.clone());
    let compatibility = pi(
        "a",
        constant("Nat"),
        pi(
            "b",
            constant("Nat"),
            pi(
                "h",
                eq_at(Level::one(), constant("Nat"), bv(1), bv(0)),
                eq_at(
                    Level::one(),
                    constant("Nat"),
                    Expr::app(function.clone(), bv(2)),
                    Expr::app(function.clone(), bv(1)),
                ),
            ),
        ),
    );
    let h = goal(&mut txn, "respectful", compatibility);
    let expr = lift_with(
        representative(x.clone()),
        constant("Nat"),
        function,
        Expr::mvar(h.clone()),
    );
    let report = txn.unify(&expr, &x, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![f.clone()]);
    assert_eq!(report.kernel_checks, 1);
    assert!(
        txn.mvars.get_assigned_expr(&h).is_none(),
        "computation is not a proof of the respectfulness obligation"
    );
    let value = txn.mvars.get_assigned_expr(&f).unwrap().clone();
    txn.unify(&Expr::app(value, numeral(13)), &numeral(13), budget())
        .unwrap();
}

#[test]
fn quotient_driven_assignments_cannot_escape_their_local_scope() {
    let mut txn = transaction();
    let id = goal(&mut txn, "outer", constant("Nat"));
    let inner = local(&mut txn, "inner", constant("Nat"));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&Expr::mvar(id), &lift(representative(inner)), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

fn cancellation_problem(txn: &mut ElabTxn) -> Vec<(Expr, Expr)> {
    let id = goal(txn, "n", constant("Nat"));
    let mut value = numeral(37);
    for _ in 0..40 {
        value = lift(representative(value));
    }
    vec![
        (lift(representative(Expr::mvar(id))), numeral(37)),
        (value, numeral(37)),
    ]
}

#[test]
fn final_barrier_cancellation_discards_quotient_assignments() {
    use std::cell::Cell;
    let mut initial = transaction();
    let equations = cancellation_problem(&mut initial);
    let mut generous = budget();
    generous.max_steps = 5_000_000;
    generous.max_visited_nodes = 3_000_000;
    initial.budget.max_heartbeats = generous.max_steps;
    let polls = Cell::new(0_u64);
    let mut control = initial.clone();
    let report = control
        .unify_many_with(&equations, generous, &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    let stop = polls.get();
    let calls = Cell::new(0_u64);
    let mut cancelled = initial.clone();
    let result = cancelled.unify_many_with(&equations, generous, &|| {
        calls.set(calls.get() + 1);
        calls.get() >= stop
    });
    assert!(matches!(result, Err(UnificationError::Cancelled)));
    assert_eq!(calls.get(), stop);
    unchanged(&cancelled, &initial);
    assert_eq!(
        cancelled.budget.heartbeats_consumed,
        control.budget.heartbeats_consumed
    );
}

#[test]
fn quotient_budget_stops_preserve_assignments_and_keep_spent_work() {
    let mut initial = transaction();
    let equations = cancellation_problem(&mut initial);
    let mut generous = budget();
    generous.max_steps = 5_000_000;
    generous.max_visited_nodes = 3_000_000;
    initial.budget.max_heartbeats = generous.max_steps;
    let mut control = initial.clone();
    let report = control
        .unify_many_with(&equations, generous, &|| false)
        .unwrap();
    let mut limited = generous;
    limited.max_steps = report.unifier_steps - 1;
    let mut stopped = initial.clone();
    assert!(matches!(
        stopped.unify_many_with(&equations, limited, &|| false),
        Err(UnificationError::StepLimit { .. })
    ));
    unchanged(&stopped, &initial);
    assert!(stopped.budget.heartbeats_consumed > initial.budget.heartbeats_consumed);
    limited = generous;
    limited.max_visited_nodes = report.visited_nodes - 1;
    let mut stopped = initial.clone();
    assert!(matches!(
        stopped.unify_many_with(&equations, limited, &|| false),
        Err(UnificationError::NodeLimit { .. })
    ));
    unchanged(&stopped, &initial);
}

#[test]
fn nested_quotient_majors_use_the_shared_heap_continuation_stack() {
    let mut txn = transaction();
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            // The minor returns its representative as a quotient. Each outer
            // eliminator must normalize the preceding quotient-valued eliminator
            // before it can select a constructor; these are genuinely nested majors.
            let mut value = representative(numeral(37));
            let branch = lambda("n", constant("Nat"), representative(bv(0)));
            let compatibility = pi(
                "a",
                constant("Nat"),
                pi(
                    "b",
                    constant("Nat"),
                    pi(
                        "h",
                        eq_at(Level::one(), constant("Nat"), bv(1), bv(0)),
                        eq_at(
                            Level::one(),
                            quotient_type(),
                            representative(bv(2)),
                            representative(bv(1)),
                        ),
                    ),
                ),
            );
            let proof = local(&mut txn, "respectfulness", compatibility);
            for _ in 0..2_000 {
                value = lift_with(value, quotient_type(), branch.clone(), proof.clone());
            }
            let expr = lift(value);
            let mut generous = budget();
            generous.max_steps = 10_000_000;
            generous.max_visited_nodes = 5_000_000;
            generous.kernel = Budget::for_stack_bytes(128 * 1024);
            txn.budget.max_heartbeats = generous.max_steps;
            let report = txn.unify(&expr, &numeral(37), generous).unwrap();
            assert_eq!(report.kernel_checks, 0);
            assert!(report.expression_assignments.is_empty());
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn quotient_spelling_does_not_enable_uninitialized_primitives() {
    let env = publish_block(
        &Environment::new(),
        fln_elab::seed::nat_inductive_seed_declaration(),
    );
    let mut txn = ElabTxn::new(env, KVMap::new(), 41);
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&lift(representative(numeral(37))), &numeral(37), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}
