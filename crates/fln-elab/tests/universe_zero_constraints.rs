//! Forced Prop universes are consequences, not defaulting or max injectivity.
#![forbid(unsafe_code)]

use fln_core::expr::Expr;
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::check_definition_source;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError};
use fln_elab::txn::ElabTxn;
use fln_env::environment::Environment;
use fln_kernel::Declaration;
use fln_kernel::verdict::{Budget, Verdict};
use std::cell::Cell;

fn id(text: &str) -> LMVarId {
    LMVarId(Name::from_components([text]))
}
fn hole(text: &str) -> Level {
    Level::mvar(id(text))
}
fn parameter(text: &str) -> Level {
    Level::param(Name::from_components([text]))
}
fn maximum(a: Level, b: Level) -> Level {
    Level::max(a, b).unwrap()
}
fn imax(a: Level, b: Level) -> Level {
    Level::imax(a, b).unwrap()
}
fn pair(a: Level, b: Level) -> (Expr, Expr) {
    (Expr::sort(a), Expr::sort(b))
}
fn kernel_budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn budget() -> UnificationBudget {
    UnificationBudget::new(kernel_budget())
}
fn txn() -> ElabTxn {
    ElabTxn::new(Environment::new(), KVMap::new(), 97)
}
fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    assert_eq!(actual.universes, before.universes);
    assert_eq!(actual.mvars, before.mvars);
    assert_eq!(actual.constraints, before.constraints);
    assert_eq!(actual.env, before.env);
    assert_eq!(actual.lctx, before.lctx);
    assert_eq!(actual.options, before.options);
    assert_eq!(actual.seed, before.seed);
}
fn zero(tx: &ElabTxn, name: &str) {
    assert_eq!(
        tx.universes.instantiate(&hole(name)).unwrap(),
        Level::zero()
    );
}

#[test]
fn a_zero_maximum_forces_every_operand_in_both_orientations() {
    for reverse in [false, true] {
        let mut tx = txn();
        let maximum = maximum(hole("a"), maximum(hole("b"), hole("a")));
        let (a, b) = if reverse {
            pair(Level::zero(), maximum)
        } else {
            pair(maximum, Level::zero())
        };
        let report = tx.unify(&a, &b, budget()).unwrap();
        assert_eq!(report.universe_assignments.len(), 2);
        assert!(report.expression_assignments.is_empty());
        zero(&tx, "a");
        zero(&tx, "b");
        assert!(!tx.universes.is_assigned(&id("unrelated")));
        assert!(
            tx.unify(&a, &b, budget())
                .unwrap()
                .universe_assignments
                .is_empty()
        );
    }
}

#[test]
fn zero_imax_constrains_only_its_guard_even_with_a_positive_left_operand() {
    for reverse in [false, true] {
        for left in [
            hole("domain"),
            hole("domain").succ().unwrap(),
            parameter("rigid"),
        ] {
            let mut tx = txn();
            let guarded = imax(left, hole("codomain"));
            let (a, b) = if reverse {
                pair(Level::zero(), guarded)
            } else {
                pair(guarded, Level::zero())
            };
            let report = tx.unify(&a, &b, budget()).unwrap();
            assert_eq!(report.universe_assignments, vec![id("codomain")]);
            zero(&tx, "codomain");
            assert!(!tx.universes.is_assigned(&id("domain")));
        }
    }
}

#[test]
fn nested_guard_maxima_force_all_guards_without_constraining_the_domain() {
    let mut tx = txn();
    let (a, b) = pair(
        imax(
            hole("domain").succ().unwrap(),
            maximum(hole("a"), hole("b")),
        ),
        Level::zero(),
    );
    let report = tx.unify(&a, &b, budget()).unwrap();
    assert_eq!(report.universe_assignments.len(), 2);
    zero(&tx, "a");
    zero(&tx, "b");
    assert!(!tx.universes.is_assigned(&id("domain")));
}

#[test]
fn forced_zero_propagates_after_common_successor_cancellation() {
    let mut tx = txn();
    let (a, b) = pair(
        maximum(hole("a").succ().unwrap(), hole("b").succ().unwrap()),
        Level::one(),
    );
    tx.unify(&a, &b, budget()).unwrap();
    zero(&tx, "a");
    zero(&tx, "b");
}

#[test]
fn the_discarded_domain_can_be_independently_fixed_to_a_nonzero_universe() {
    for reverse_order in [false, true] {
        let mut tx = txn();
        let mut equations = vec![
            pair(imax(hole("domain"), hole("guard")), Level::zero()),
            pair(hole("domain"), Level::one().succ().unwrap()),
        ];
        if reverse_order {
            equations.reverse();
        }
        tx.unify_many_with(&equations, budget(), &|| false).unwrap();
        zero(&tx, "guard");
        assert_eq!(
            tx.universes.instantiate(&hole("domain")).unwrap(),
            Level::one().succ().unwrap()
        );
    }
}

#[test]
fn nonzero_or_rigid_equations_do_not_gain_guessed_solutions() {
    for (a, b) in [
        pair(maximum(hole("a"), hole("b")), Level::one()),
        pair(hole("a").succ().unwrap(), Level::zero()),
        pair(maximum(hole("a"), parameter("rigid")), Level::zero()),
        pair(imax(hole("domain"), parameter("rigid")), Level::zero()),
    ] {
        let mut tx = txn();
        let before = tx.clone();
        assert!(matches!(
            tx.unify(&a, &b, budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&tx, &before);
    }
}

fn two_zero_holes() -> Vec<(Expr, Expr)> {
    vec![pair(maximum(hole("a"), hole("b")), Level::zero())]
}

#[test]
fn a_later_conflict_rolls_back_every_forced_assignment() {
    let mut tx = txn();
    let before = tx.clone();
    let mut equations = two_zero_holes();
    equations.push(pair(hole("a"), Level::one()));
    assert!(matches!(
        tx.unify_many_with(&equations, budget(), &|| false),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&tx, &before);
    tx.unify_many_with(&two_zero_holes(), budget(), &|| false)
        .unwrap();
    zero(&tx, "a");
    zero(&tx, "b");
}

#[test]
fn assignment_and_work_limits_do_not_publish_partial_zero_solutions() {
    let initial = txn();
    let equations = two_zero_holes();
    let mut control = initial.clone();
    let report = control
        .unify_many_with(&equations, budget(), &|| false)
        .unwrap();
    let mut limited = budget();
    limited.max_assignments = 1;
    let mut tx = initial.clone();
    assert!(matches!(
        tx.unify_many_with(&equations, limited, &|| false),
        Err(UnificationError::AssignmentLimit { limit: 1 })
    ));
    unchanged(&tx, &initial);
    let mut limited = budget();
    limited.max_steps = report.unifier_steps - 1;
    let mut tx = initial.clone();
    assert!(matches!(
        tx.unify_many_with(&equations, limited, &|| false),
        Err(UnificationError::StepLimit { .. })
    ));
    unchanged(&tx, &initial);
    assert!(tx.budget.heartbeats_consumed > initial.budget.heartbeats_consumed);
    let mut limited = budget();
    limited.max_visited_nodes = report.visited_nodes - 1;
    let mut tx = initial.clone();
    assert!(matches!(
        tx.unify_many_with(&equations, limited, &|| false),
        Err(UnificationError::NodeLimit { .. })
    ));
    unchanged(&tx, &initial);
}

#[test]
fn cancellation_at_final_publication_rolls_back_forced_prop_universes() {
    let initial = txn();
    let equations = two_zero_holes();
    let polls = Cell::new(0);
    let mut control = initial.clone();
    control
        .unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let stop = polls.get();
    let calls = Cell::new(0);
    let mut tx = initial.clone();
    assert!(matches!(
        tx.unify_many_with(&equations, budget(), &|| {
            calls.set(calls.get() + 1);
            calls.get() == stop
        }),
        Err(UnificationError::Cancelled)
    ));
    unchanged(&tx, &initial);
    assert_eq!(calls.get(), stop);
    assert_eq!(
        tx.budget.heartbeats_consumed,
        control.budget.heartbeats_consumed
    );
}

#[test]
fn source_prop_results_infer_only_the_codomain_universe() {
    let env = fln_elab::seed::bootstrap_nat_environment(kernel_budget()).unwrap();
    for source in [
        "def inferProp (A : Sort _) (P : Sort _) : Prop := A -> P",
        "def inferDependentProp (A : Sort _) (P : A -> Sort _) : Prop := forall x : A, P x",
        "def inferShiftedProp.{u} (A : Type u) (P : Sort _) : Prop := A -> P",
    ] {
        let result = check_definition_source(source.as_bytes(), &env, kernel_budget())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert!(
            matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
            "{source}: {:?}",
            result.outcome
        );
        let Declaration::Defn(value) = result.declaration else {
            panic!("definition")
        };
        assert_eq!(
            value.base.level_params.len(),
            1,
            "only the domain universe is generalized: {source}"
        );
        assert!(!value.base.type_.has_level_mvar());
        assert!(!value.value.has_level_mvar());
    }
}
