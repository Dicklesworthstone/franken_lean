//! Native recursor equations through ElabTxn, not a model of the solver.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_elab::mvar::MetavarKind;
use fln_elab::txn::ElabTxn;
use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::Budget;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn constant(text: &str) -> Expr {
    Expr::const_(name(text), Vec::new())
}
fn numeral(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn bvar(n: u32) -> Expr {
    Expr::bvar(n).unwrap()
}
fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(Name::anonymous(), domain, body, BinderInfo::Default)
}
fn apply(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn budget() -> UnificationBudget {
    let mut result = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    // Recursor reduction must not require unfolding ordinary definitions.
    result.transparency = UnificationTransparency::None;
    result
}
fn transaction() -> ElabTxn {
    let mut env = Environment::new();
    for declaration in [
        fln_elab::seed::nat_inductive_seed_declaration(),
        fln_elab::seed::bool_seed_declaration(),
        fln_elab::seed::eq_seed_declaration(),
    ] {
        let Outcome::Complete(admitted) = admit(&env, declaration, budget().kernel) else {
            panic!("seed admission did not complete");
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("seed was rejected");
        };
        let Outcome::Complete(Published::BlockCommitted(publication)) = checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) else {
            panic!("seed publication did not complete");
        };
        env = publication.environment;
    }
    ElabTxn::new(env, KVMap::new(), 17)
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
fn select(major: Expr) -> Expr {
    apply(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        [
            lam(constant("Bool"), constant("Bool")),
            constant("Bool.false"),
            constant("Bool.true"),
            major,
        ],
    )
}
fn nat_rec(major: Expr, zero: Expr, successor: Expr) -> Expr {
    apply(
        Expr::const_(name("Nat.rec"), vec![Level::one()]),
        [
            lam(constant("Nat"), constant("Nat")),
            zero,
            successor,
            major,
        ],
    )
}

#[test]
fn both_bool_rules_compute_with_delta_disabled() {
    for constructor in ["Bool.false", "Bool.true"] {
        let mut txn = transaction();
        let before = txn.clone();
        let value = constant(constructor);
        let report = txn.unify(&select(value.clone()), &value, budget()).unwrap();
        assert!(report.expression_assignments.is_empty());
        assert_eq!(report.kernel_checks, 0);
        unchanged(&txn, &before);
    }
}

#[test]
fn recursive_constructor_fields_feed_the_checked_rule() {
    let mut txn = transaction();
    let input = apply(
        constant("Nat.succ"),
        [apply(constant("Nat.succ"), [constant("Nat.zero")])],
    );
    let step = lam(
        constant("Nat"),
        lam(constant("Nat"), apply(constant("Nat.succ"), [bvar(0)])),
    );
    txn.unify(&nat_rec(input, numeral(0), step), &numeral(2), budget())
        .unwrap();
}

#[test]
fn an_assignment_exposed_by_iota_still_passes_k1() {
    let mut txn = transaction();
    let id = goal(&mut txn, "selected", constant("Bool"));
    let expr = apply(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        [
            lam(constant("Bool"), constant("Bool")),
            constant("Bool.false"),
            Expr::mvar(id.clone()),
            constant("Bool.true"),
        ],
    );
    let env = txn.env.clone();
    let report = txn.unify(&expr, &constant("Bool.true"), budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![id.clone()]);
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(
        txn.mvars.get_assigned_expr(&id),
        Some(&constant("Bool.true"))
    );
    assert_eq!(txn.env, env);
}

#[test]
fn a_later_equation_wakes_a_blocked_recursor_major() {
    let mut txn = transaction();
    let id = goal(&mut txn, "major", constant("Bool"));
    let expr = select(Expr::mvar(id.clone()));
    let report = txn
        .unify_many_with(
            &[
                (expr, constant("Bool.true")),
                (Expr::mvar(id.clone()), constant("Bool.true")),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.expression_assignments, vec![id]);
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn arguments_after_the_major_apply_to_a_function_valued_minor() {
    let mut txn = transaction();
    let function_type = Expr::forall_e(
        Name::anonymous(),
        constant("Nat"),
        constant("Nat"),
        BinderInfo::Default,
    );
    let expr = apply(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        [
            lam(constant("Bool"), function_type),
            lam(constant("Nat"), numeral(0)),
            lam(constant("Nat"), bvar(0)),
            constant("Bool.true"),
            numeral(42),
        ],
    );
    txn.unify(&expr, &numeral(42), budget()).unwrap();
}

#[test]
fn parameterized_indexed_equality_recursor_uses_only_prefix_and_fields() {
    let mut txn = transaction();
    let equality = apply(
        Expr::const_(name("Eq"), vec![Level::one()]),
        [constant("Nat"), numeral(7), bvar(0)],
    );
    let motive = lam(constant("Nat"), lam(equality, constant("Nat")));
    let proof = apply(
        Expr::const_(name("Eq.refl"), vec![Level::one()]),
        [constant("Nat"), numeral(7)],
    );
    let expr = apply(
        Expr::const_(name("Eq.rec"), vec![Level::one(), Level::one()]),
        [
            constant("Nat"),
            numeral(7),
            motive,
            numeral(23),
            numeral(7),
            proof,
        ],
    );
    txn.unify(&expr, &numeral(23), budget()).unwrap();
}

#[test]
fn unsupported_and_malformed_majors_defer_without_publication() {
    let mut txn = transaction();
    let id = FVarId(name("flag"));
    txn.lctx.add_param(
        id.clone(),
        id.0.clone(),
        constant("Bool"),
        BinderInfo::Default,
    );
    for major in [
        Expr::fvar(id),
        constant("Nat.zero"),
        numeral(0),
        Expr::app(constant("Bool.true"), numeral(0)),
        Expr::const_(name("Bool.true"), vec![Level::one()]),
    ] {
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&select(major), &constant("Bool.true"), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
    for expr in [
        Expr::app(
            Expr::const_(name("Bool.rec"), vec![Level::one()]),
            constant("Bool.true"),
        ),
        apply(
            Expr::const_(name("Bool.rec"), Vec::new()),
            [
                lam(constant("Bool"), constant("Bool")),
                constant("Bool.false"),
                constant("Bool.true"),
                constant("Bool.true"),
            ],
        ),
    ] {
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&expr, &constant("Bool.true"), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn local_let_transparency_is_not_widened_by_iota() {
    let mut txn = transaction();
    let id = FVarId(name("flag"));
    txn.lctx.add_let(
        id.clone(),
        id.0.clone(),
        constant("Bool"),
        constant("Bool.true"),
    );
    let expr = select(Expr::fvar(id));
    let before = txn.clone();
    let mut closed = budget();
    closed.zeta_delta = false;
    assert!(matches!(
        txn.unify(&expr, &constant("Bool.true"), closed),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
    txn.unify(&expr, &constant("Bool.true"), budget()).unwrap();
}

#[test]
fn compact_nat_zero_and_recursive_successor_rules_compute() {
    for n in [0, 1, 2, 16] {
        let mut txn = transaction();
        let step = lam(
            constant("Nat"),
            lam(constant("Nat"), apply(constant("Nat.succ"), [bvar(0)])),
        );
        txn.unify(
            &nat_rec(numeral(n), numeral(0), step),
            &numeral(n),
            budget(),
        )
        .unwrap();
    }
}

#[test]
fn a_huge_literal_does_not_force_an_unused_induction_hypothesis() {
    let mut txn = transaction();
    let step = lam(constant("Nat"), lam(constant("Nat"), bvar(1)));
    let expr = nat_rec(numeral(u64::MAX), numeral(0), step);
    let mut bounded = budget();
    bounded.max_steps = 20_000;
    let report = txn.unify(&expr, &numeral(u64::MAX - 1), bounded).unwrap();
    assert!(report.unifier_steps < bounded.max_steps);
    assert!(report.expression_assignments.is_empty());
}

#[test]
fn universe_assignments_reawaken_constructor_compatibility() {
    use fln_core::level::LMVarId;
    let mut txn = transaction();
    let universe = LMVarId(name("pending_universe"));
    let equality = apply(
        Expr::const_(name("Eq"), vec![Level::one()]),
        [constant("Nat"), numeral(7), bvar(0)],
    );
    let proof = apply(
        Expr::const_(name("Eq.refl"), vec![Level::one()]),
        [constant("Nat"), numeral(7)],
    );
    let expr = apply(
        Expr::const_(
            name("Eq.rec"),
            vec![Level::one(), Level::mvar(universe.clone())],
        ),
        [
            constant("Nat"),
            numeral(7),
            lam(constant("Nat"), lam(equality, constant("Nat"))),
            numeral(23),
            numeral(7),
            proof,
        ],
    );
    let report = txn
        .unify_many_with(
            &[
                (expr, numeral(23)),
                (
                    Expr::sort(Level::mvar(universe.clone())),
                    Expr::sort(Level::one()),
                ),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.universe_assignments, vec![universe]);
    assert!(report.expression_assignments.is_empty());
}

#[test]
fn an_ill_typed_selected_assignment_is_still_vetoed_by_k1() {
    use fln_kernel::verdict::Verdict;
    let mut txn = transaction();
    let id = goal(&mut txn, "bad_minor", constant("Nat"));
    let before = txn.clone();
    let expr = apply(
        Expr::const_(name("Bool.rec"), vec![Level::one()]),
        [
            lam(constant("Bool"), constant("Bool")),
            constant("Bool.false"),
            Expr::mvar(id.clone()),
            constant("Bool.true"),
        ],
    );
    match txn
        .unify(&expr, &constant("Bool.true"), budget())
        .unwrap_err()
    {
        UnificationError::AssignmentCheck { id: found, outcome } => {
            assert_eq!(found, id);
            assert!(matches!(
                *outcome,
                Outcome::Complete(Verdict::Rejected { .. })
            ));
        }
        other => panic!("expected K1 veto, got {other:?}"),
    }
    unchanged(&txn, &before);
}

#[test]
fn a_failed_later_recursor_equation_rolls_back_an_earlier_assignment() {
    let mut txn = transaction();
    let id = goal(&mut txn, "tentative", constant("Nat"));
    let before = txn.clone();
    let result = txn.unify_many_with(
        &[
            (Expr::mvar(id), numeral(37)),
            (select(constant("Bool.false")), constant("Bool.true")),
        ],
        budget(),
        &|| false,
    );
    assert!(matches!(result, Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn cancellation_discards_speculative_assignments_but_keeps_spent_work() {
    use std::cell::Cell;
    let mut initial = transaction();
    let id = goal(&mut initial, "tentative", constant("Nat"));
    let mut expr = constant("Bool.true");
    for _ in 0..200 {
        expr = select(expr);
    }
    let equations = [(Expr::mvar(id), numeral(37)), (expr, constant("Bool.true"))];
    let mut generous = budget();
    generous.max_steps = 2_000_000;
    initial.budget.max_heartbeats = generous.max_steps;
    // Count polls on the successful path, then cancel at its final publication
    // barrier, after speculative assignment and K1 validation have occurred.
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
        let next = calls.get() + 1;
        calls.set(next);
        next >= stop
    });
    assert!(matches!(result, Err(UnificationError::Cancelled)));
    assert_eq!(calls.get(), stop);
    unchanged(&cancelled, &initial);
    assert_eq!(
        cancelled.budget.heartbeats_consumed,
        control.budget.heartbeats_consumed
    );
    assert!(cancelled.budget.heartbeats_consumed > initial.budget.heartbeats_consumed);
}

#[test]
fn step_and_node_exhaustion_are_typed_nonanswers_not_partial_success() {
    let mut expr = constant("Bool.true");
    for _ in 0..30 {
        expr = select(expr);
    }
    let initial = transaction();
    let mut control = initial.clone();
    let report = control
        .unify(&expr, &constant("Bool.true"), budget())
        .unwrap();
    let mut limited = budget();
    limited.max_steps = report.unifier_steps - 1;
    let mut txn = initial.clone();
    assert!(matches!(
        txn.unify(&expr, &constant("Bool.true"), limited),
        Err(UnificationError::StepLimit { .. })
    ));
    unchanged(&txn, &initial);
    limited = budget();
    limited.max_visited_nodes = report.visited_nodes - 1;
    let mut txn = initial.clone();
    assert!(matches!(
        txn.unify(&expr, &constant("Bool.true"), limited),
        Err(UnificationError::NodeLimit { .. })
    ));
    unchanged(&txn, &initial);
}

#[test]
fn deeply_nested_majors_use_heap_continuations_on_a_small_stack() {
    let mut txn = transaction();
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(move || {
            let mut expr = constant("Bool.true");
            for _ in 0..10_000 {
                expr = select(expr);
            }
            let mut large = budget();
            large.max_steps = 5_000_000;
            large.max_visited_nodes = 3_000_000;
            large.kernel = Budget::for_stack_bytes(128 * 1024);
            // Keep the inherited transaction cap consistent with this stress
            // test's explicit work limit rather than stopping at the default.
            txn.budget.max_heartbeats = large.max_steps;
            // This closed equation makes no assignment and needs no K1 recursion.
            let report = txn.unify(&expr, &constant("Bool.true"), large).unwrap();
            assert_eq!(report.kernel_checks, 0);
        })
        .unwrap()
        .join()
        .unwrap();
}

fn mutual_transaction() -> ElabTxn {
    use fln_elab::inductive::{ConstructorSpec, InductiveSpec, mutual_inductive_declaration};
    use fln_elab::lctx::LocalDecl;
    use fln_elab::records::RecordBudget;
    let field = |text: &str, family: &str| LocalDecl {
        id: FVarId(name(text)),
        user_name: name(text),
        type_: constant(family),
        value: None,
        binder_info: BinderInfo::Default,
        index: 0,
    };
    let constructor = |text: &str, fields: Vec<LocalDecl>| ConstructorSpec {
        name: name(text),
        fields,
        result_indices: vec![],
    };
    let family = |text: &str, constructors: Vec<ConstructorSpec>| InductiveSpec {
        name: name(text),
        level_params: vec![],
        parameters: vec![],
        indices: vec![],
        constructors,
        result_level: Level::one(),
    };
    let declaration = mutual_inductive_declaration(
        &[
            family(
                "Even",
                vec![
                    constructor("zero", vec![]),
                    constructor("succ", vec![field("odd_child", "Odd")]),
                ],
            ),
            family(
                "Odd",
                vec![constructor("succ", vec![field("even_child", "Even")])],
            ),
        ],
        RecordBudget::default(),
    )
    .unwrap();
    let mut tx = transaction();
    let Outcome::Complete(admitted) = admit(&tx.env, declaration, budget().kernel) else {
        panic!("mutual candidate did not complete admission");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("mutual candidate failed K1 reconstruction");
    };
    let Outcome::Complete(Published::BlockCommitted(publication)) = checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) else {
        panic!("mutual candidate did not publish");
    };
    tx.env = publication.environment;
    tx
}

fn mutual_rec(family: &str, major: Expr, zero: Expr, function_result: bool) -> Expr {
    let result = if function_result {
        Expr::forall_e(
            Name::anonymous(),
            constant("Bool"),
            constant("Bool"),
            BinderInfo::Default,
        )
    } else {
        constant("Bool")
    };
    let odd_result = if function_result {
        lam(constant("Bool"), constant("Bool.false"))
    } else {
        constant("Bool.true")
    };
    apply(
        Expr::const_(name(&format!("{family}.rec")), vec![Level::one()]),
        [
            lam(constant("Even"), result.clone()),
            lam(constant("Odd"), result.clone()),
            zero,
            lam(constant("Odd"), lam(result.clone(), bvar(0))),
            lam(constant("Even"), lam(result, odd_result)),
            major,
        ],
    )
}

fn kernel_bool_conversion(tx: &ElabTxn, left: &Expr, right: &Expr) {
    use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
    use fln_kernel::{Declaration, verdict::Verdict};
    let type_ = apply(
        Expr::const_(name("Eq"), vec![Level::one()]),
        [constant("Bool"), left.clone(), right.clone()],
    );
    let value = apply(
        Expr::const_(name("Eq.refl"), vec![Level::one()]),
        [constant("Bool"), right.clone()],
    );
    let candidate = Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name("mutual_conversion_guard"),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name("mutual_conversion_guard")],
    });
    let outcome = fln_kernel::check(&tx.env, &candidate, budget().kernel);
    assert!(
        matches!(outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{outcome:?}"
    );
}

#[test]
fn mutual_iota_uses_the_selected_family_and_all_ordered_motives_and_minors() {
    let mut tx = mutual_transaction();
    let zero = constant("Even.zero");
    let odd = Expr::app(constant("Odd.succ"), zero.clone());
    let even = Expr::app(constant("Even.succ"), odd.clone());
    for (family, major, expected) in [
        ("Even", zero, "Bool.false"),
        ("Odd", odd, "Bool.true"),
        ("Even", even, "Bool.true"),
    ] {
        let term = mutual_rec(family, major, constant("Bool.false"), false);
        let expected = constant(expected);
        kernel_bool_conversion(&tx, &term, &expected);
        tx.unify(&term, &expected, budget())
            .expect("ordinary mutual iota must agree with K1");
    }
}

#[test]
fn mutual_iota_preserves_applications_after_a_function_valued_major() {
    let mut tx = mutual_transaction();
    let major = Expr::app(
        constant("Even.succ"),
        Expr::app(constant("Odd.succ"), constant("Even.zero")),
    );
    let fold = mutual_rec("Even", major, lam(constant("Bool"), bvar(0)), true);
    let applied = Expr::app(fold, constant("Bool.true"));
    kernel_bool_conversion(&tx, &applied, &constant("Bool.false"));
    tx.unify(&applied, &constant("Bool.false"), budget())
        .expect("mutual iota keeps the result's argument");
}

#[test]
fn mutual_iota_exposes_result_holes_to_checked_assignment() {
    let mut tx = mutual_transaction();
    let id = goal(&mut tx, "mutual_result", constant("Bool"));
    let term = mutual_rec("Even", constant("Even.zero"), Expr::mvar(id.clone()), false);
    let report = tx
        .unify(&term, &constant("Bool.true"), budget())
        .expect("iota exposes the actual result hole");
    assert_eq!(
        tx.mvars.get_assigned_expr(&id),
        Some(&constant("Bool.true"))
    );
    assert_eq!(report.kernel_checks, 1);
}

#[test]
fn mutual_recursor_from_another_family_cannot_reduce_a_sibling_constructor() {
    let mut tx = mutual_transaction();
    let term = mutual_rec("Odd", constant("Even.zero"), constant("Bool.false"), false);
    let before = tx.clone();
    assert!(matches!(
        tx.unify(&term, &constant("Bool.false"), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&tx, &before);
}

#[test]
fn mutual_iota_retries_when_a_later_equation_assigns_the_major() {
    let mut tx = mutual_transaction();
    let id = goal(&mut tx, "mutual_major", constant("Even"));
    let term = mutual_rec(
        "Even",
        Expr::mvar(id.clone()),
        constant("Bool.false"),
        false,
    );
    let report = tx
        .unify_many_with(
            &[
                (term, constant("Bool.false")),
                (Expr::mvar(id.clone()), constant("Even.zero")),
            ],
            budget(),
            &|| false,
        )
        .unwrap();
    assert_eq!(report.expression_assignments, vec![id.clone()]);
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(
        tx.mvars.get_assigned_expr(&id),
        Some(&constant("Even.zero"))
    );
}

#[test]
fn mutual_iota_failure_and_resource_stops_never_publish_selected_assignments() {
    let mut initial = mutual_transaction();
    let id = goal(&mut initial, "selected_minor", constant("Bool"));
    let term = mutual_rec("Even", constant("Even.zero"), Expr::mvar(id.clone()), false);
    let equations = [(term, constant("Bool.true"))];
    let control = initial
        .clone()
        .unify_many_with(&equations, budget(), &|| false)
        .unwrap();
    assert_eq!(control.expression_assignments, vec![id]);
    for bounded in [
        {
            let mut b = budget();
            b.max_steps = 1;
            b
        },
        {
            let mut b = budget();
            b.max_visited_nodes = 1;
            b
        },
        {
            let mut b = budget();
            b.max_assignments = 0;
            b
        },
    ] {
        let mut tx = initial.clone();
        assert!(matches!(
            tx.unify_many_with(&equations, bounded, &|| false),
            Err(UnificationError::StepLimit { .. }
                | UnificationError::NodeLimit { .. }
                | UnificationError::AssignmentLimit { .. })
        ));
        unchanged(&tx, &initial);
    }
    let mut failed = initial.clone();
    let mut batch = equations.to_vec();
    batch.push((
        mutual_rec("Odd", constant("Even.zero"), constant("Bool.false"), false),
        constant("Bool.false"),
    ));
    assert!(matches!(
        failed.unify_many_with(&batch, budget(), &|| false),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&failed, &initial);

    // Cancel at the successful path's publication barrier, after the selected
    // assignment has been built and checked. Spent work survives; state does not.
    let polls = std::cell::Cell::new(0usize);
    initial
        .clone()
        .unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let total = polls.get();
    polls.set(0);
    let mut cancelled = initial.clone();
    assert!(matches!(
        cancelled.unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            polls.get() == total
        }),
        Err(UnificationError::Cancelled)
    ));
    unchanged(&cancelled, &initial);
    assert!(cancelled.budget.heartbeats_consumed > initial.budget.heartbeats_consumed);
}
