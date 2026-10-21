//! Native conversion must evaluate a shared demanded subterm once, not as a tree.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, Literal, NatLit};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{UnificationBudget, UnificationTransparency};
use fln_elab::txn::ElabTxn;
use fln_env::constants::{AxiomVal, ConstantVal};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::Budget;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn constant(s: &str) -> Expr {
    Expr::const_(name(s), Vec::new())
}
fn number(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn pi(a: Expr, b: Expr) -> Expr {
    Expr::forall_e(name("x"), a, b, BinderInfo::Default)
}
fn add(a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(constant("Nat.add"), a), b)
}
fn budget() -> UnificationBudget {
    let mut budget = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    budget.transparency = UnificationTransparency::Default;
    budget
}
fn publish(txn: &mut ElabTxn, declaration: Declaration) {
    let Outcome::Complete(admitted) = admit(&txn.env, declaration, budget().kernel) else {
        panic!("fixture admission stopped")
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture rejected")
    };
    txn.env = match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
            result.environment
        }
        Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
        other => panic!("fixture publication: {other:?}"),
    };
}
fn transaction() -> ElabTxn {
    let mut txn = ElabTxn::new(Environment::new(), KVMap::new(), 71);
    publish(&mut txn, fln_elab::seed::nat_inductive_seed_declaration());
    publish(
        &mut txn,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: name("Nat.add"),
                level_params: Vec::new(),
                type_: pi(constant("Nat"), pi(constant("Nat"), constant("Nat"))),
            },
            is_unsafe: false,
        }),
    );
    txn
}
fn circuit(depth: u32) -> Expr {
    (0..depth).fold(number(1), |term, _| add(term.clone(), term))
}
#[test]
fn shared_arithmetic_demands_complete_without_exponential_reduction() {
    let mut txn = transaction();
    let report = txn.unify(&circuit(32), &number(1 << 32), budget()).unwrap();
    assert!(report.unifier_steps < 10_000, "{report:?}");
    assert!(report.visited_nodes < 10_000, "{report:?}");
    assert!(report.expression_assignments.is_empty());
    assert_eq!(report.kernel_checks, 0);
}

fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = actual.budget.heartbeats_consumed;
    assert_eq!(actual, &expected);
}

#[test]
fn reduction_work_scales_with_the_shared_graph_and_is_query_local() {
    let mut txn = transaction();
    let first = txn.unify(&circuit(16), &number(1 << 16), budget()).unwrap();
    let second = txn.unify(&circuit(32), &number(1 << 32), budget()).unwrap();
    assert!(second.unifier_steps < first.unifier_steps * 3);
    assert!(second.visited_nodes < first.visited_nodes * 3);
    let again = txn.unify(&circuit(32), &number(1 << 32), budget()).unwrap();
    assert_eq!(again.unifier_steps, second.unifier_steps);
    assert_eq!(again.visited_nodes, second.visited_nodes);
}

#[test]
fn different_results_cannot_become_equal_or_publish_an_earlier_assignment() {
    use fln_core::expr::MVarId;
    use fln_elab::constraint::unify::UnificationError;
    use fln_elab::mvar::MetavarKind;
    for reverse in [false, true] {
        let mut txn = transaction();
        let id = MVarId(name("prior"));
        txn.mvars.declare(
            id.clone(),
            id.0.clone(),
            constant("Nat"),
            txn.lctx.clone(),
            MetavarKind::Natural,
            0,
            None,
        );
        let before = txn.clone();
        let (a, b) = (circuit(24), number((1 << 24) + 1));
        let equation = if reverse { (b, a) } else { (a, b) };
        assert!(matches!(
            txn.unify_many_with(&[(Expr::mvar(id), number(7)), equation], budget(), &|| {
                false
            }),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
        assert!(txn.unify(&circuit(24), &number(1 << 24), budget()).is_ok());
    }
}

#[test]
fn every_demand_cancellation_checkpoint_rolls_back_and_can_be_retried() {
    use fln_elab::constraint::unify::UnificationError;
    use std::cell::Cell;
    let initial = transaction();
    let equation = [(circuit(4), number(16))];
    let polls = Cell::new(0);
    initial
        .clone()
        .unify_many_with(&equation, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    for stop in 1..=polls.get() {
        let mut txn = initial.clone();
        let count = Cell::new(0);
        let result = txn.unify_many_with(&equation, budget(), &|| {
            count.set(count.get() + 1);
            count.get() == stop
        });
        assert!(
            matches!(result, Err(UnificationError::Cancelled)),
            "checkpoint {stop}"
        );
        unchanged(&txn, &initial);
    }
    initial
        .clone()
        .unify_many_with(&equation, budget(), &|| false)
        .unwrap();
}

#[test]
fn exact_step_and_node_limits_still_bound_warm_demand_work() {
    use fln_elab::constraint::unify::UnificationError;
    let initial = transaction();
    let expr = circuit(16);
    let value = number(1 << 16);
    let report = initial.clone().unify(&expr, &value, budget()).unwrap();
    let mut steps = budget();
    steps.max_steps = report.unifier_steps;
    assert!(initial.clone().unify(&expr, &value, steps).is_ok());
    steps.max_steps -= 1;
    let mut stopped = initial.clone();
    assert!(matches!(
        stopped.unify(&expr, &value, steps),
        Err(UnificationError::StepLimit { .. })
    ));
    unchanged(&stopped, &initial);
    let mut nodes = budget();
    nodes.max_visited_nodes = report.visited_nodes;
    assert!(initial.clone().unify(&expr, &value, nodes).is_ok());
    nodes.max_visited_nodes -= 1;
    let mut stopped = initial.clone();
    assert!(matches!(
        stopped.unify(&expr, &value, nodes),
        Err(UnificationError::NodeLimit { .. })
    ));
    unchanged(&stopped, &initial);
}

#[test]
fn cached_computation_does_not_widen_other_transparencies() {
    use fln_elab::constraint::unify::UnificationError;
    let mut txn = transaction();
    let expr = circuit(8);
    txn.unify(&expr, &number(256), budget()).unwrap();
    for transparency in [
        UnificationTransparency::None,
        UnificationTransparency::Abbreviations,
        UnificationTransparency::Instances,
    ] {
        let mut limits = budget();
        limits.transparency = transparency;
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&expr, &number(256), limits),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(name("x"), domain, body, BinderInfo::Default)
}
fn apply(head: Expr, args: &[Expr]) -> Expr {
    args.iter().cloned().fold(head, Expr::app)
}
fn recursor(major: Expr, zero: Expr, step: Expr, result_type: Expr) -> Expr {
    use fln_core::level::Level;
    apply(
        Expr::const_(name("Nat.rec"), vec![Level::one()]),
        &[lam(constant("Nat"), result_type), zero, step, major],
    )
}

#[test]
fn demanded_recursor_results_keep_their_trailing_function_arguments() {
    let mut txn = transaction();
    let nat = constant("Nat");
    let function = recursor(
        add(number(1), number(1)),
        lam(nat.clone(), add(Expr::bvar(0).unwrap(), number(3))),
        lam(
            nat.clone(),
            lam(pi(nat.clone(), nat.clone()), Expr::bvar(0).unwrap()),
        ),
        pi(nat.clone(), nat),
    );
    let left = Expr::app(function.clone(), number(7));
    let right = Expr::app(function, number(9));
    txn.unify(&add(left, right), &number(22), budget()).unwrap();
}

#[test]
fn identical_demand_allocations_do_not_cross_rebound_local_contexts() {
    use fln_core::expr::FVarId;
    let id = FVarId(name("major"));
    let nat = constant("Nat");
    let expr = recursor(
        Expr::fvar(id.clone()),
        number(11),
        lam(nat.clone(), lam(nat.clone(), number(22))),
        nat.clone(),
    );
    for (major, expected) in [(0, 11), (1, 22), (0, 11)] {
        let mut txn = transaction();
        txn.lctx
            .add_let(id.clone(), id.0.clone(), nat.clone(), number(major));
        let before = txn.clone();
        txn.unify(&expr, &number(expected), budget()).unwrap();
        unchanged(&txn, &before);
    }
}

#[test]
fn earlier_demand_results_do_not_freeze_later_metavariable_assignments() {
    use fln_core::expr::MVarId;
    use fln_elab::constraint::unify::UnificationError;
    use fln_elab::mvar::MetavarKind;
    let mut txn = transaction();
    let id = MVarId(name("major"));
    let nat = constant("Nat");
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        nat.clone(),
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    let expr = recursor(
        Expr::mvar(id.clone()),
        number(11),
        lam(nat.clone(), lam(nat.clone(), number(22))),
        nat,
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&expr, &number(11), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
    txn.unify(&Expr::mvar(id), &number(0), budget()).unwrap();
    txn.unify(&expr, &number(11), budget()).unwrap();
}

#[test]
fn cached_literals_do_not_confer_constructor_authority_on_a_different_environment() {
    use fln_elab::constraint::unify::UnificationError;
    let expr = circuit(8);
    transaction().unify(&expr, &number(256), budget()).unwrap();
    let mut txn = ElabTxn::new(
        fln_elab::seed::bootstrap_nat_environment(budget().kernel).unwrap(),
        KVMap::new(),
        71,
    );
    publish(
        &mut txn,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: name("Nat.add"),
                level_params: Vec::new(),
                type_: pi(constant("Nat"), pi(constant("Nat"), constant("Nat"))),
            },
            is_unsafe: false,
        }),
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&expr, &number(256), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn structurally_colliding_demands_do_not_share_different_declared_values() {
    use fln_elab::constraint::unify::UnificationError;
    use fln_env::constants::{DefinitionSafety, DefinitionVal, ReducibilityHints};
    let mut txn = transaction();
    let names: Vec<_> = (0..2)
        .map(|index| Name::num_overflowing(name("value"), index))
        .collect();
    for (label, value) in names.iter().zip([7, 9]) {
        publish(
            &mut txn,
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: label.clone(),
                    level_params: vec![],
                    type_: constant("Nat"),
                },
                value: number(value),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![label.clone()],
            }),
        );
    }
    let left = Expr::const_(names[0].clone(), vec![]);
    let right = Expr::const_(names[1].clone(), vec![]);
    assert_eq!(
        left.hash(),
        right.hash(),
        "exercise a real syntax-hash collision"
    );
    assert_ne!(left, right);
    let expression = add(left, right);
    let before = txn.clone();
    txn.unify(&expression, &number(16), budget()).unwrap();
    unchanged(&txn, &before);
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&expression, &number(14), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn separately_rebuilt_recursor_demands_preserve_trailing_function_arguments() {
    let make = |argument| {
        let nat = constant("Nat");
        let function = recursor(
            add(number(1), number(1)),
            lam(nat.clone(), add(Expr::bvar(0).unwrap(), number(3))),
            lam(
                nat.clone(),
                lam(pi(nat.clone(), nat.clone()), Expr::bvar(0).unwrap()),
            ),
            pi(nat.clone(), nat),
        );
        Expr::app(function, number(argument))
    };
    let mut txn = transaction();
    let before = txn.clone();
    // These have equal recursor demands but are not allocation-sharing clones.
    txn.unify(&add(make(7), make(9)), &number(22), budget())
        .unwrap();
    unchanged(&txn, &before);
}

#[test]
fn hidden_local_function_holes_remain_recoverable_only_when_zeta_is_enabled() {
    use fln_core::expr::{FVarId, MVarId};
    use fln_elab::constraint::unify::UnificationError;
    use fln_elab::mvar::MetavarKind;
    let mut initial = transaction();
    let function = pi(constant("Nat"), constant("Nat"));
    publish(
        &mut initial,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: name("rigid"),
                level_params: vec![],
                type_: function.clone(),
            },
            is_unsafe: false,
        }),
    );
    let id = MVarId(name("hidden_function"));
    initial.mvars.declare(
        id.clone(),
        id.0.clone(),
        function.clone(),
        initial.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    let local = FVarId(name("alias"));
    initial.lctx.add_let(
        local.clone(),
        local.0.clone(),
        function,
        Expr::mvar(id.clone()),
    );
    let left = Expr::app(Expr::fvar(local), number(3));
    let right = Expr::app(constant("rigid"), number(3));
    assert!(
        !left.has_expr_mvar(),
        "the hole is hidden behind its local binding"
    );
    let mut blocked = initial.clone();
    let mut limits = budget();
    limits.zeta_delta = false;
    assert!(matches!(
        blocked.unify(&left, &right, limits),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&blocked, &initial);
    let mut permitted = initial.clone();
    permitted.unify(&left, &right, budget()).unwrap();
    assert_eq!(
        permitted.mvars.get_assigned_expr(&id),
        Some(&constant("rigid"))
    );
}
