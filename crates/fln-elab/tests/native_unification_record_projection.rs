//! Field-driven record inference through the real transactional unifier.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{UnificationBudget, UnificationError, UnificationTransparency};
use fln_elab::lctx::LocalDecl;
use fln_elab::mvar::MetavarKind;
use fln_elab::records::{RecordBudget, RecordSpec, record_declarations};
use fln_elab::txn::ElabTxn;
use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::Budget;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn constant(text: &str) -> Expr {
    Expr::const_(name(text), vec![])
}
fn numeral(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn apply(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn mk(record: &str, fields: impl IntoIterator<Item = Expr>) -> Expr {
    apply(constant(&format!("{record}.mk")), fields)
}
fn proj(record: &str, index: u64, receiver: &Expr) -> Expr {
    Expr::proj(name(record), index, receiver.clone())
}
fn binder(text: &str, type_: Expr) -> LocalDecl {
    LocalDecl {
        id: FVarId(name(text)),
        user_name: name(text),
        type_,
        value: None,
        binder_info: BinderInfo::Default,
        index: 0,
    }
}
fn spec(text: &str, parameters: Vec<LocalDecl>, fields: Vec<LocalDecl>) -> RecordSpec {
    RecordSpec {
        name: name(text),
        level_params: vec![],
        parameters,
        fields,
        result_level: Level::one(),
        is_class: false,
    }
}
fn budget() -> UnificationBudget {
    let mut budget = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    budget.transparency = UnificationTransparency::None;
    budget
}
fn publish_block(env: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(env, declaration, budget().kernel) else {
        panic!("block admission did not complete");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("block admission was rejected");
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
fn add_record(txn: &mut ElabTxn, spec: RecordSpec) {
    let block = record_declarations(&spec, RecordBudget::default())
        .unwrap()
        .into_iter()
        .next()
        .unwrap();
    // Core Expr::Proj does not need the separately generated projection defs.
    txn.env = publish_block(&txn.env, block);
}
fn transaction() -> ElabTxn {
    let mut env = Environment::new();
    for declaration in [
        fln_elab::seed::nat_inductive_seed_declaration(),
        fln_elab::seed::bool_seed_declaration(),
        fln_elab::seed::eq_seed_declaration(),
    ] {
        env = publish_block(&env, declaration);
    }
    let mut txn = ElabTxn::new(env, KVMap::new(), 23);
    add_record(
        &mut txn,
        spec(
            "PairN",
            vec![],
            vec![
                binder("left", constant("Nat")),
                binder("right", constant("Nat")),
            ],
        ),
    );
    let a = binder("A", Expr::sort(Level::one()));
    add_record(
        &mut txn,
        spec(
            "Box",
            vec![a.clone()],
            vec![binder("value", Expr::fvar(a.id.clone()))],
        ),
    );
    add_record(&mut txn, spec("EmptyBox", vec![a], vec![]));
    let mut unit = spec("UniverseUnit", vec![], vec![]);
    unit.level_params = vec![name("u")];
    unit.result_level = Level::param(name("u")).succ().unwrap();
    add_record(&mut txn, unit);
    txn
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
fn a_singleton_projection_recovers_the_record_in_both_orientations() {
    for reversed in [false, true] {
        let mut txn = transaction();
        let r = goal(
            &mut txn,
            "record",
            Expr::app(constant("Box"), constant("Nat")),
        );
        let record = Expr::mvar(r.clone());
        let projection = proj("Box", 0, &record);
        let value = numeral(7);
        let (a, b) = if reversed {
            (&value, &projection)
        } else {
            (&projection, &value)
        };
        let report = txn.unify(a, b, budget()).unwrap();
        assert_eq!(
            txn.mvars.instantiate(&record),
            mk("Box", [constant("Nat"), numeral(7)])
        );
        assert_eq!(report.expression_assignments, vec![r]);
        assert_eq!(report.kernel_checks, 1);
        assert!(report.residual_metavariables.is_empty());
    }
}

#[test]
fn singleton_inversion_keeps_residual_values_as_obligations() {
    let mut txn = transaction();
    let x = goal(&mut txn, "field", constant("Nat"));
    let r = goal(
        &mut txn,
        "record",
        Expr::app(constant("Box"), constant("Nat")),
    );
    let record = Expr::mvar(r);
    let value = Expr::app(constant("Nat.succ"), Expr::mvar(x.clone()));
    let report = txn
        .unify(&proj("Box", 0, &record), &value, budget())
        .unwrap();
    assert_eq!(report.residual_metavariables, vec![x.clone()]);
    assert!(!txn.mvars.is_assigned(&x));
    assert_eq!(
        txn.mvars.instantiate(&record),
        mk("Box", [constant("Nat"), value])
    );
}

#[test]
fn multiple_fields_are_not_guessed_from_one_projection() {
    let mut txn = transaction();
    let r = goal(&mut txn, "record", constant("PairN"));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&proj("PairN", 0, &Expr::mvar(r)), &numeral(7), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn a_late_mismatch_discards_the_reconstructed_record() {
    let mut txn = transaction();
    let r = goal(
        &mut txn,
        "record",
        Expr::app(constant("Box"), constant("Nat")),
    );
    let record = Expr::mvar(r);
    let before = txn.clone();
    assert!(
        txn.unify_many_with(
            &[
                (proj("Box", 0, &record), numeral(7)),
                (proj("Box", 0, &record), numeral(9)),
            ],
            budget(),
            &|| false
        )
        .is_err()
    );
    unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn applied_record_holes_are_solved_as_checked_lambda_patterns() {
    let mut txn = transaction();
    let f = goal(
        &mut txn,
        "wrap",
        Expr::forall_e(
            name("n"),
            constant("Nat"),
            Expr::app(constant("Box"), constant("Nat")),
            BinderInfo::Default,
        ),
    );
    let n = local(&mut txn, "n", constant("Nat"));
    let receiver = Expr::app(Expr::mvar(f.clone()), n.clone());
    let report = txn.unify(&proj("Box", 0, &receiver), &n, budget()).unwrap();
    let expected = Expr::lam(
        name("n"),
        constant("Nat"),
        mk("Box", [constant("Nat"), Expr::bvar(0).unwrap()]),
        BinderInfo::Default,
    );
    assert_eq!(txn.mvars.get_assigned_expr(&f), Some(&expected));
    assert_eq!(report.kernel_checks, 1);
    assert!(report.residual_metavariables.is_empty());
}

#[test]
fn dependent_receiver_parameters_are_substituted_before_inversion() {
    let mut txn = transaction();
    let f = goal(
        &mut txn,
        "pack",
        Expr::forall_e(
            name("A"),
            Expr::sort(Level::one()),
            Expr::forall_e(
                name("a"),
                Expr::bvar(0).unwrap(),
                Expr::app(constant("Box"), Expr::bvar(1).unwrap()),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        ),
    );
    let a_type = local(&mut txn, "A", Expr::sort(Level::one()));
    let a = local(&mut txn, "a", a_type.clone());
    let receiver = apply(Expr::mvar(f.clone()), [a_type, a.clone()]);
    let report = txn.unify(&proj("Box", 0, &receiver), &a, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![f.clone()]);
    assert_eq!(report.kernel_checks, 1);
    let assigned = txn.mvars.get_assigned_expr(&f).unwrap();
    assert!(!assigned.has_fvar());
    assert!(!assigned.has_expr_mvar());
    txn.unify(&proj("Box", 0, &receiver), &a, budget()).unwrap();
}

#[test]
fn registered_classes_are_left_to_instance_synthesis() {
    let mut txn = transaction();
    txn.env = fln_elab::instances::register_class(&txn.env, &name("Box")).unwrap();
    let r = goal(
        &mut txn,
        "dictionary",
        Expr::app(constant("Box"), constant("Nat")),
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&proj("Box", 0, &Expr::mvar(r)), &numeral(7), budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn a_bad_field_value_is_vetoed_by_k1_without_assignment_publication() {
    let mut txn = transaction();
    let r = goal(
        &mut txn,
        "record",
        Expr::app(constant("Box"), constant("Nat")),
    );
    let before = txn.clone();
    assert!(matches!(
        txn.unify(
            &proj("Box", 0, &Expr::mvar(r)),
            &constant("Bool.true"),
            budget()
        ),
        Err(UnificationError::AssignmentCheck { .. })
    ));
    unchanged(&txn, &before);
}

#[test]
fn inversion_does_not_capture_a_local_outside_the_holes_scope() {
    let mut txn = transaction();
    let r = goal(
        &mut txn,
        "record",
        Expr::app(constant("Box"), constant("Nat")),
    );
    let late = local(&mut txn, "late", constant("Nat"));
    let before = txn.clone();
    assert!(matches!(
        txn.unify(&proj("Box", 0, &Expr::mvar(r)), &late, budget()),
        Err(UnificationError::Deferred(_))
    ));
    unchanged(&txn, &before);
}

#[test]
fn opaque_and_deeper_holes_are_not_assigned_by_projection_inversion() {
    for (kind, depth) in [(MetavarKind::SyntheticOpaque, 0), (MetavarKind::Natural, 1)] {
        let mut txn = transaction();
        let r = MVarId(name("record"));
        txn.mvars.declare(
            r.clone(),
            r.0.clone(),
            Expr::app(constant("Box"), constant("Nat")),
            txn.lctx.clone(),
            kind,
            depth,
            None,
        );
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&proj("Box", 0, &Expr::mvar(r)), &numeral(7), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn malformed_projection_metadata_cannot_choose_a_constructor() {
    for (family, index) in [("PairN", 0), ("Box", 1), ("Unknown", 0)] {
        let mut txn = transaction();
        let r = goal(
            &mut txn,
            "record",
            Expr::app(constant("Box"), constant("Nat")),
        );
        let before = txn.clone();
        assert!(matches!(
            txn.unify(&proj(family, index, &Expr::mvar(r)), &numeral(7), budget()),
            Err(UnificationError::Deferred(_))
        ));
        unchanged(&txn, &before);
    }
}

#[test]
fn exhaustion_and_final_cancellation_leave_no_partial_reconstruction() {
    use std::cell::Cell;
    let mut initial = transaction();
    let r = goal(
        &mut initial,
        "record",
        Expr::app(constant("Box"), constant("Nat")),
    );
    let equations = [(proj("Box", 0, &Expr::mvar(r)), numeral(7))];
    let polls = Cell::new(0_u64);
    let mut control = initial.clone();
    let report = control
        .unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    assert_eq!(report.kernel_checks, 1);
    let mut step_limit = budget();
    step_limit.max_steps = report.unifier_steps - 1;
    let mut node_limit = budget();
    node_limit.max_visited_nodes = report.visited_nodes - 1;
    let mut assignment_limit = budget();
    assignment_limit.max_assignments = 0;
    for limits in [step_limit, node_limit, assignment_limit] {
        let mut txn = initial.clone();
        assert!(matches!(
            txn.unify_many_with(&equations, limits, &|| false),
            Err(UnificationError::StepLimit { .. }
                | UnificationError::NodeLimit { .. }
                | UnificationError::AssignmentLimit { .. })
        ));
        unchanged(&txn, &initial);
        assert!(txn.budget.heartbeats_consumed > initial.budget.heartbeats_consumed);
    }
    let stop = polls.get();
    let calls = Cell::new(0_u64);
    let mut txn = initial.clone();
    assert!(matches!(
        txn.unify_many_with(&equations, budget(), &|| {
            calls.set(calls.get() + 1);
            calls.get() >= stop
        }),
        Err(UnificationError::Cancelled)
    ));
    unchanged(&txn, &initial);
    assert_eq!(
        txn.budget.heartbeats_consumed,
        control.budget.heartbeats_consumed
    );
}
