//! Same-definition argument guessing is transactional, not an injectivity rule.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::ConstraintKind;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_elab::mvar::MetavarKind;
use fln_elab::txn::ElabTxn;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
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
fn budget() -> UnificationBudget {
    let mut budget = UnificationBudget::new(Budget::for_stack_bytes(1024 * 1024));
    budget.transparency = UnificationTransparency::Default;
    budget
}
fn transaction(polymorphic: bool) -> ElabTxn {
    let env = fln_elab::seed::bootstrap_nat_environment(budget().kernel).unwrap();
    let function = name("erase");
    let candidate = fln_kernel::Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: function.clone(),
            level_params: if polymorphic {
                vec![name("u"), name("v")]
            } else {
                vec![]
            },
            type_: Expr::forall_e(
                name("x"),
                nat(),
                Expr::forall_e(name("y"), nat(), nat(), BinderInfo::Default),
                BinderInfo::Default,
            ),
        },
        value: Expr::lam(
            name("x"),
            nat(),
            Expr::lam(name("y"), nat(), number(42), BinderInfo::Default),
            BinderInfo::Default,
        ),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![function],
    });
    let admitted = admit(&env, candidate, budget().kernel)
        .into_complete()
        .unwrap();
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture must pass ordinary kernel admission");
    };
    let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) = checked
        .publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        )
    else {
        panic!("checked fixture must publish");
    };
    ElabTxn::new(result.environment, KVMap::new(), 17)
}
fn hole(txn: &mut ElabTxn, s: &str) -> MVarId {
    let id = MVarId(name(s));
    txn.mvars.declare(
        id.clone(),
        id.0.clone(),
        nat(),
        txn.lctx.clone(),
        MetavarKind::Natural,
        0,
        None,
    );
    id
}
fn erased(levels: Vec<Level>, x: Expr, y: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(name("erase"), levels), x), y)
}
fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    let mut expected = before.clone();
    expected.budget.heartbeats_consumed = actual.budget.heartbeats_consumed;
    assert_eq!(actual, &expected);
}

#[test]
fn same_definition_arguments_are_inferred_before_delta_erases_them() {
    for reverse in [false, true] {
        let mut txn = transaction(false);
        let m = hole(&mut txn, "m");
        let left = erased(vec![], Expr::mvar(m.clone()), number(0));
        let right = erased(vec![], number(7), number(0));
        let (left, right) = if reverse {
            (right, left)
        } else {
            (left, right)
        };
        let report = txn.unify(&left, &right, budget()).unwrap();
        assert_eq!(txn.mvars.get_assigned_expr(&m), Some(&number(7)));
        assert_eq!(report.expression_assignments, vec![m]);
        assert!(report.kernel_checks > 0);
    }
}

#[test]
fn nonlinear_noninjective_guess_rolls_back_assignments_and_constraint_wakeups() {
    let mut txn = transaction(false);
    let m = hole(&mut txn, "m");
    txn.postpone(
        ConstraintKind::HasType {
            expr: Expr::mvar(m.clone()),
            expected_type: nat(),
        },
        0,
    );
    let before = txn.clone();
    let left = erased(vec![], Expr::mvar(m.clone()), Expr::mvar(m.clone()));
    let right = erased(vec![], number(1), number(2));
    let report = txn.unify(&left, &right, budget()).unwrap();
    // The arguments cannot all be equal, but both applications unfold to 42.
    // The first guessed assignment and its awakened constraint must disappear.
    unchanged(&txn, &before);
    assert!(report.expression_assignments.is_empty());
    assert!(report.awakened.is_empty());
    let report = txn
        .unify(&Expr::mvar(m.clone()), &number(9), budget())
        .unwrap();
    assert_eq!(txn.mvars.get_assigned_expr(&m), Some(&number(9)));
    assert_eq!(report.awakened.len(), 1);
}

#[test]
fn a_later_universe_mismatch_rolls_back_earlier_expression_and_universe_guesses() {
    let mut txn = transaction(true);
    let m = hole(&mut txn, "m");
    let u = LMVarId(name("universe"));
    let before = txn.clone();
    let left = erased(
        vec![Level::mvar(u), Level::zero()],
        Expr::mvar(m),
        number(0),
    );
    let right = erased(vec![Level::one(), Level::one()], number(7), number(0));
    let report = txn.unify(&left, &right, budget()).unwrap();
    unchanged(&txn, &before);
    assert!(report.expression_assignments.is_empty());
    assert!(report.universe_assignments.is_empty());
}

#[test]
fn assignment_exhaustion_in_a_guess_remains_a_typed_stop() {
    let mut txn = transaction(false);
    let m = hole(&mut txn, "m");
    let k = hole(&mut txn, "k");
    let before = txn.clone();
    let mut limits = budget();
    limits.max_assignments = 1;
    let result = txn.unify(
        &erased(vec![], Expr::mvar(m), Expr::mvar(k)),
        &erased(vec![], number(1), number(2)),
        limits,
    );
    assert!(matches!(
        result,
        Err(UnificationError::AssignmentLimit { limit: 1 })
    ));
    unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn exhausted_assignment_checker_is_not_reclassified_as_a_failed_guess() {
    let mut txn = transaction(false);
    let m = hole(&mut txn, "m");
    let before = txn.clone();
    let mut limits = budget();
    limits.kernel.steps = 0;
    let error = txn
        .unify(
            &erased(vec![], Expr::mvar(m), number(0)),
            &erased(vec![], number(7), number(0)),
            limits,
        )
        .unwrap_err();
    assert!(matches!(
        error,
        UnificationError::AssignmentCheck { outcome, .. }
        | UnificationError::ConversionCheck { outcome }
            if matches!(*outcome, Outcome::Inconclusive(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn speculative_work_stays_within_shared_step_node_and_cancellation_limits() {
    let mut base = transaction(false);
    let m = hole(&mut base, "m");
    let equations = [(
        erased(vec![], Expr::mvar(m), number(0)),
        erased(vec![], number(7), number(0)),
    )];
    let calls = Cell::new(0usize);
    let report = base
        .clone()
        .unify_many_with(&equations, budget(), &|| {
            calls.set(calls.get() + 1);
            false
        })
        .unwrap();
    let control_calls = calls.get();
    for dimension in 0..3 {
        let mut txn = base.clone();
        let before = txn.clone();
        let mut limits = budget();
        match dimension {
            0 => limits.max_steps = report.unifier_steps - 1,
            1 => limits.max_visited_nodes = report.visited_nodes - 1,
            _ => (),
        }
        calls.set(0);
        let result = txn.unify_many_with(&equations, limits, &|| {
            calls.set(calls.get() + 1);
            dimension == 2 && calls.get() >= control_calls / 2
        });
        match dimension {
            0 => assert!(matches!(result, Err(UnificationError::StepLimit { .. }))),
            1 => assert!(matches!(result, Err(UnificationError::NodeLimit { .. }))),
            _ => assert!(matches!(result, Err(UnificationError::Cancelled))),
        }
        unchanged(&txn, &before);
    }
}
