//! Record equations through ElabTxn and ordinary K1-checked assignments.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::{LMVarId, Level};
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{
    UnificationBudget, UnificationError, UnificationTransparency,
};
use fln_elab::lctx::LocalDecl;
use fln_elab::mvar::MetavarKind;
use fln_elab::records::{RecordBudget, RecordSpec, record_declarations};
use fln_elab::txn::ElabTxn;
use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};

fn name(text: &str) -> Name { Name::from_components(text.split('.')) }
fn constant(text: &str) -> Expr { Expr::const_(name(text), vec![]) }
fn numeral(n: u64) -> Expr { Expr::lit(Literal::Nat(NatLit::from_u64(n))) }
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
        id: FVarId(name(text)), user_name: name(text), type_, value: None,
        binder_info: BinderInfo::Default, index: 0,
    }
}
fn spec(text: &str, parameters: Vec<LocalDecl>, fields: Vec<LocalDecl>) -> RecordSpec {
    RecordSpec {
        name: name(text), level_params: vec![], parameters, fields,
        result_level: Level::one(), is_class: false,
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
        DeclarationBudget::default(), CollisionBudget::default(), None,
    ) else {
        panic!("block publication did not complete");
    };
    publication.environment
}
fn add_record(txn: &mut ElabTxn, spec: RecordSpec) {
    let block = record_declarations(&spec, RecordBudget::default()).unwrap()
        .into_iter().next().unwrap();
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
    add_record(&mut txn, spec("PairN", vec![], vec![
        binder("left", constant("Nat")), binder("right", constant("Nat")),
    ]));
    let a = binder("A", Expr::sort(Level::one()));
    add_record(&mut txn, spec("Box", vec![a.clone()], vec![
        binder("value", Expr::fvar(a.id.clone())),
    ]));
    add_record(&mut txn, spec("EmptyBox", vec![a], vec![]));
    let mut unit = spec("UniverseUnit", vec![], vec![]);
    unit.level_params = vec![name("u")];
    unit.result_level = Level::param(name("u")).succ().unwrap();
    add_record(&mut txn, unit);
    txn
}
fn local(txn: &mut ElabTxn, text: &str, type_: Expr) -> Expr {
    let id = FVarId(name(text));
    txn.lctx.add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn goal(txn: &mut ElabTxn, text: &str, type_: Expr) -> MVarId {
    let id = MVarId(name(text));
    txn.mvars.declare(id.clone(), id.0.clone(), type_, txn.lctx.clone(),
        MetavarKind::Natural, 0, None);
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
fn pair_problem(txn: &mut ElabTxn) -> (Expr, Expr, MVarId, MVarId) {
    let p = local(txn, "p", constant("PairN"));
    let x = goal(txn, "x", constant("Nat"));
    let y = goal(txn, "y", constant("Nat"));
    let reconstruction = mk("PairN", [Expr::mvar(x.clone()), Expr::mvar(y.clone())]);
    (reconstruction, p, x, y)
}

#[test]
fn reconstructed_records_compare_in_both_orientations_without_delta() {
    for reversed in [false, true] {
        let mut txn = transaction();
        let p = local(&mut txn, "p", constant("PairN"));
        let reconstruction = mk("PairN", [proj("PairN", 0, &p), proj("PairN", 1, &p)]);
        let before = txn.clone();
        let (left, right) = if reversed { (&p, &reconstruction) } else { (&reconstruction, &p) };
        let report = txn.unify(left, right, budget()).unwrap();
        assert!(report.expression_assignments.is_empty());
        assert_eq!(report.kernel_checks, 0);
        unchanged(&txn, &before);
    }
}

#[test]
fn field_holes_are_checked_and_published_in_field_order() {
    for reversed in [false, true] {
        let mut txn = transaction();
        let (record, p, x, y) = pair_problem(&mut txn);
        let env = txn.env.clone();
        let (left, right) = if reversed { (&p, &record) } else { (&record, &p) };
        let report = txn.unify(left, right, budget()).unwrap();
        assert_eq!(report.expression_assignments, vec![x.clone(), y.clone()]);
        assert_eq!(report.kernel_checks, 2);
        assert!(report.residual_metavariables.is_empty());
        assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("PairN", 0, &p)));
        assert_eq!(txn.mvars.get_assigned_expr(&y), Some(&proj("PairN", 1, &p)));
        assert_eq!(txn.env, env);
    }
}

#[test]
fn eta_precedes_rigid_application_congruence() {
    let mut txn = transaction();
    let f = local(&mut txn, "f", Expr::forall_e(
        name("n"), constant("Nat"), constant("PairN"), BinderInfo::Default,
    ));
    let value = Expr::app(f, numeral(19));
    let x = goal(&mut txn, "x", constant("Nat"));
    let record = mk("PairN", [Expr::mvar(x.clone()), proj("PairN", 1, &value)]);
    let report = txn.unify(&record, &value, budget()).unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("PairN", 0, &value)));
}

#[test]
fn dependent_function_results_infer_record_parameters_before_fields() {
    let mut txn = transaction();
    let f = local(&mut txn, "f", Expr::forall_e(
        name("A"), Expr::sort(Level::one()),
        Expr::app(constant("Box"), Expr::bvar(0).unwrap()), BinderInfo::Default,
    ));
    let value = Expr::app(f, constant("Nat"));
    let a = goal(&mut txn, "A", Expr::sort(Level::one()));
    let x = goal(&mut txn, "x", Expr::mvar(a.clone()));
    let record = mk("Box", [Expr::mvar(a.clone()), Expr::mvar(x.clone())]);
    let report = txn.unify(&record, &value, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![a.clone(), x.clone()]);
    assert_eq!(report.kernel_checks, 2);
    assert_eq!(txn.mvars.get_assigned_expr(&a), Some(&constant("Nat")));
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("Box", 0, &value)));
}

#[test]
fn empty_records_still_compare_and_infer_parameters() {
    let mut txn = transaction();
    let value = local(&mut txn, "p", Expr::app(constant("EmptyBox"), constant("Nat")));
    let a = goal(&mut txn, "A", Expr::sort(Level::one()));
    let report = txn.unify(&mk("EmptyBox", [Expr::mvar(a.clone())]), &value, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![a.clone()]);
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(txn.mvars.get_assigned_expr(&a), Some(&constant("Nat")));
    let before = txn.clone();
    assert!(matches!(txn.unify(&mk("EmptyBox", [constant("Bool")]), &value, budget()),
        Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn empty_records_do_not_erase_universe_constraints() {
    let mut txn = transaction();
    let value = local(&mut txn, "p", Expr::const_(name("UniverseUnit"), vec![Level::one()]));
    let u = LMVarId(name("unknown_u"));
    let constructor = Expr::const_(name("UniverseUnit.mk"), vec![Level::mvar(u.clone())]);
    let report = txn.unify(&constructor, &value, budget()).unwrap();
    assert_eq!(report.universe_assignments, vec![u]);
    assert!(report.expression_assignments.is_empty());
    let before = txn.clone();
    let wrong = Expr::const_(name("UniverseUnit.mk"), vec![Level::zero()]);
    assert!(matches!(txn.unify(&wrong, &value, budget()), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn later_type_assignments_wake_blocked_record_equations() {
    let mut txn = transaction();
    let t = goal(&mut txn, "T", Expr::sort(Level::one()));
    let value = local(&mut txn, "p", Expr::mvar(t.clone()));
    let x = goal(&mut txn, "x", constant("Nat"));
    let record = mk("PairN", [Expr::mvar(x.clone()), proj("PairN", 1, &value)]);
    let before = txn.clone();
    assert!(matches!(txn.unify(&record, &value, budget()), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
    let report = txn.unify_many_with(&[
        (record, value.clone()), (Expr::mvar(t.clone()), constant("PairN")),
    ], budget(), &|| false).unwrap();
    assert_eq!(report.expression_assignments, vec![t, x.clone()]);
    assert_eq!(report.kernel_checks, 2);
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("PairN", 0, &value)));
}

#[test]
fn unrelated_record_families_are_not_equated_by_field_count() {
    let mut txn = transaction();
    add_record(&mut txn, spec("OtherPair", vec![], vec![
        binder("left", constant("Nat")), binder("right", constant("Nat")),
    ]));
    let value = local(&mut txn, "p", constant("OtherPair"));
    let x = goal(&mut txn, "x", constant("Nat"));
    let record = mk("PairN", [Expr::mvar(x), numeral(0)]);
    let before = txn.clone();
    assert!(matches!(txn.unify(&record, &value, budget()), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn field_order_is_not_silently_permuted() {
    let mut txn = transaction();
    let p = local(&mut txn, "p", constant("PairN"));
    let wrong = mk("PairN", [proj("PairN", 1, &p), proj("PairN", 0, &p)]);
    let before = txn.clone();
    assert!(matches!(txn.unify(&wrong, &p, budget()), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn malformed_constructor_arity_and_universes_fail_closed() {
    let mut txn = transaction();
    let p = local(&mut txn, "p", constant("PairN"));
    for constructor in [
        constant("PairN.mk"), mk("PairN", [numeral(0)]),
        mk("PairN", [numeral(0), numeral(1), numeral(2)]),
        apply(Expr::const_(name("PairN.mk"), vec![Level::one()]), [numeral(0), numeral(1)]),
    ] {
        let before = txn.clone();
        assert!(matches!(txn.unify(&constructor, &p, budget()), Err(UnificationError::Deferred(_))));
        unchanged(&txn, &before);
    }
}

#[test]
fn recursive_multiconstructor_and_indexed_families_do_not_take_record_eta() {
    let mut txn = transaction();
    let n = local(&mut txn, "n", constant("Nat"));
    let b = local(&mut txn, "b", constant("Bool"));
    let equality = apply(Expr::const_(name("Eq"), vec![Level::one()]),
        [constant("Nat"), numeral(0), numeral(0)]);
    let h = local(&mut txn, "h", equality);
    let refl = apply(Expr::const_(name("Eq.refl"), vec![Level::one()]),
        [constant("Nat"), numeral(0)]);
    for (constructor, value) in [(constant("Nat.zero"), n), (constant("Bool.true"), b), (refl, h)] {
        let before = txn.clone();
        assert!(matches!(txn.unify(&constructor, &value, budget()), Err(UnificationError::Deferred(_))));
        unchanged(&txn, &before);
    }
}

#[test]
fn k1_vetoes_ill_typed_field_assignments() {
    let mut txn = transaction();
    let p = local(&mut txn, "p", constant("PairN"));
    let wrong = goal(&mut txn, "wrong", constant("Bool"));
    let record = mk("PairN", [Expr::mvar(wrong.clone()), proj("PairN", 1, &p)]);
    let before = txn.clone();
    match txn.unify(&record, &p, budget()).unwrap_err() {
        UnificationError::AssignmentCheck { id, outcome } => {
            assert_eq!(id, wrong);
            assert!(matches!(*outcome, Outcome::Complete(Verdict::Rejected { .. })));
        }
        other => panic!("expected K1 veto, got {other:?}"),
    }
    unchanged(&txn, &before);
}

#[test]
fn a_later_mismatch_discards_all_eta_assignments() {
    let mut txn = transaction();
    let (record, p, _, _) = pair_problem(&mut txn);
    let before = txn.clone();
    assert!(matches!(txn.unify_many_with(&[
        (record, p), (constant("Bool.false"), constant("Bool.true")),
    ], budget(), &|| false), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
    assert!(txn.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn final_barrier_cancellation_discards_k1_checked_eta_assignments() {
    use std::cell::Cell;
    let mut initial = transaction();
    let (record, p, _, _) = pair_problem(&mut initial);
    let equations = [(record, p)];
    let polls = Cell::new(0_u64);
    let mut control = initial.clone();
    let report = control.unify_many_with(&equations, budget(), &|| {
        polls.set(polls.get() + 1); false
    }).unwrap();
    assert_eq!(report.kernel_checks, 2);
    let stop = polls.get();
    let calls = Cell::new(0_u64);
    let mut cancelled = initial.clone();
    let result = cancelled.unify_many_with(&equations, budget(), &|| {
        calls.set(calls.get() + 1); calls.get() >= stop
    });
    assert!(matches!(result, Err(UnificationError::Cancelled)));
    assert_eq!(calls.get(), stop);
    unchanged(&cancelled, &initial);
    assert_eq!(cancelled.budget.heartbeats_consumed, control.budget.heartbeats_consumed);
}

#[test]
fn resource_stops_do_not_publish_partial_record_solutions() {
    let mut initial = transaction();
    let (record, p, _, _) = pair_problem(&mut initial);
    let mut control = initial.clone();
    let report = control.unify(&record, &p, budget()).unwrap();
    let mut limits = budget();
    limits.max_steps = report.unifier_steps - 1;
    let mut txn = initial.clone();
    assert!(matches!(txn.unify(&record, &p, limits), Err(UnificationError::StepLimit { .. })));
    unchanged(&txn, &initial);
    limits = budget();
    limits.max_visited_nodes = report.visited_nodes - 1;
    let mut txn = initial.clone();
    assert!(matches!(txn.unify(&record, &p, limits), Err(UnificationError::NodeLimit { .. })));
    unchanged(&txn, &initial);
    limits = budget();
    limits.max_assignments = 1;
    let mut txn = initial.clone();
    assert!(matches!(txn.unify(&record, &p, limits), Err(UnificationError::AssignmentLimit { .. })));
    unchanged(&txn, &initial);
}

#[test]
fn record_eta_does_not_widen_local_let_transparency() {
    let mut txn = transaction();
    let record = mk("PairN", [numeral(3), numeral(5)]);
    let id = FVarId(name("p"));
    txn.lctx.add_let(id.clone(), id.0.clone(), constant("PairN"), record.clone());
    let p = Expr::fvar(id);
    let mut closed = budget();
    closed.zeta_delta = false;
    let before = txn.clone();
    assert!(matches!(txn.unify(&record, &p, closed), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
    txn.unify(&record, &p, budget()).unwrap();
}

fn add_holder(txn: &mut ElabTxn) {
    add_record(txn, spec("Holder", vec![], vec![binder("pair", constant("PairN"))]));
}

#[test]
fn nested_record_projection_receivers_support_field_inference() {
    let mut txn = transaction();
    add_holder(&mut txn);
    let h = local(&mut txn, "h", constant("Holder"));
    let value = proj("Holder", 0, &h);
    let x = goal(&mut txn, "x", constant("Nat"));
    let record = mk("PairN", [Expr::mvar(x.clone()), proj("PairN", 1, &value)]);
    let report = txn.unify(&record, &value, budget()).unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("PairN", 0, &value)));
}

#[test]
fn dependent_record_fields_are_checked_after_earlier_field_inference() {
    let mut txn = transaction();
    let a = binder("A", Expr::sort(Level::one()));
    let mut pack = spec("Pack", vec![], vec![a.clone(), binder("value", Expr::fvar(a.id))]);
    pack.result_level = Level::one().succ().unwrap();
    add_record(&mut txn, pack);
    let p = local(&mut txn, "p", constant("Pack"));
    let a = goal(&mut txn, "A", Expr::sort(Level::one()));
    let x = goal(&mut txn, "x", Expr::mvar(a.clone()));
    let record = mk("Pack", [Expr::mvar(a.clone()), Expr::mvar(x.clone())]);
    let report = txn.unify(&record, &p, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![a.clone(), x.clone()]);
    assert_eq!(report.kernel_checks, 2);
    assert_eq!(txn.mvars.get_assigned_expr(&a), Some(&proj("Pack", 0, &p)));
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("Pack", 1, &p)));
}

#[test]
fn projected_record_parameters_use_earlier_fields_of_the_same_receiver() {
    let mut txn = transaction();
    let a = binder("A", Expr::sort(Level::one()));
    let box_type = Expr::app(constant("Box"), Expr::fvar(a.id.clone()));
    let mut envelope = spec("Envelope", vec![], vec![a, binder("box", box_type)]);
    envelope.result_level = Level::one().succ().unwrap();
    add_record(&mut txn, envelope);
    let p = local(&mut txn, "p", constant("Envelope"));
    let value = proj("Envelope", 1, &p);
    let a = goal(&mut txn, "A", Expr::sort(Level::one()));
    let x = goal(&mut txn, "x", Expr::mvar(a.clone()));
    let record = mk("Box", [Expr::mvar(a.clone()), Expr::mvar(x.clone())]);
    let report = txn.unify(&record, &value, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![a.clone(), x.clone()]);
    assert_eq!(report.kernel_checks, 2);
    assert_eq!(txn.mvars.get_assigned_expr(&a), Some(&proj("Envelope", 0, &p)));
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("Box", 0, &value)));
    assert!(report.residual_metavariables.is_empty());
}

#[test]
fn projected_functions_can_produce_records() {
    let mut txn = transaction();
    let function_type = Expr::forall_e(
        name("n"), constant("Nat"), constant("PairN"), BinderInfo::Default,
    );
    add_record(&mut txn, spec("Factory", vec![], vec![binder("make", function_type)]));
    let p = local(&mut txn, "p", constant("Factory"));
    let value = Expr::app(proj("Factory", 0, &p), numeral(31));
    let x = goal(&mut txn, "x", constant("Nat"));
    let record = mk("PairN", [Expr::mvar(x.clone()), proj("PairN", 1, &value)]);
    let report = txn.unify(&record, &value, budget()).unwrap();
    assert_eq!(report.kernel_checks, 1);
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("PairN", 0, &value)));
}

#[test]
fn dependent_projected_functions_preserve_application_substitution() {
    let mut txn = transaction();
    let function_type = Expr::forall_e(
        name("A"), Expr::sort(Level::one()),
        Expr::app(constant("Box"), Expr::bvar(0).unwrap()), BinderInfo::Default,
    );
    let mut factory = spec("PolyFactory", vec![], vec![binder("make", function_type)]);
    factory.result_level = Level::one().succ().unwrap();
    add_record(&mut txn, factory);
    let p = local(&mut txn, "p", constant("PolyFactory"));
    let value = Expr::app(proj("PolyFactory", 0, &p), constant("Nat"));
    let a = goal(&mut txn, "A", Expr::sort(Level::one()));
    let x = goal(&mut txn, "x", Expr::mvar(a.clone()));
    let record = mk("Box", [Expr::mvar(a.clone()), Expr::mvar(x.clone())]);
    let report = txn.unify(&record, &value, budget()).unwrap();
    assert_eq!(report.kernel_checks, 2);
    assert_eq!(txn.mvars.get_assigned_expr(&a), Some(&constant("Nat")));
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("Box", 0, &value)));
}

#[test]
fn invalid_projection_names_and_indices_do_not_invent_receiver_types() {
    let mut txn = transaction();
    add_holder(&mut txn);
    let p = local(&mut txn, "p", constant("Holder"));
    let x = goal(&mut txn, "x", constant("Nat"));
    let record = mk("PairN", [Expr::mvar(x), numeral(0)]);
    for value in [proj("PairN", 0, &p), proj("Holder", 1, &p), proj("Holder", u64::MAX, &p)] {
        let before = txn.clone();
        assert!(matches!(txn.unify(&record, &value, budget()), Err(UnificationError::Deferred(_))));
        unchanged(&txn, &before);
    }
}

#[test]
fn a_later_assignment_can_reveal_a_projected_receivers_record_type() {
    let mut txn = transaction();
    add_holder(&mut txn);
    let t = goal(&mut txn, "T", Expr::sort(Level::one()));
    let p = local(&mut txn, "p", Expr::mvar(t.clone()));
    let value = proj("Holder", 0, &p);
    let x = goal(&mut txn, "x", constant("Nat"));
    let record = mk("PairN", [Expr::mvar(x.clone()), proj("PairN", 1, &value)]);
    let before = txn.clone();
    assert!(matches!(txn.unify(&record, &value, budget()), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
    let report = txn.unify_many_with(&[
        (record, value.clone()), (Expr::mvar(t.clone()), constant("Holder")),
    ], budget(), &|| false).unwrap();
    assert_eq!(report.expression_assignments, vec![t, x.clone()]);
    assert_eq!(report.kernel_checks, 2);
    assert_eq!(txn.mvars.get_assigned_expr(&x), Some(&proj("PairN", 0, &value)));
}

#[test]
fn eta_cannot_assign_a_projection_outside_the_metavariables_scope() {
    let mut txn = transaction();
    add_holder(&mut txn);
    let x = goal(&mut txn, "x", constant("Nat"));
    // This receiver was not present when x's local context was captured.
    let p = local(&mut txn, "p", constant("Holder"));
    let value = proj("Holder", 0, &p);
    let record = mk("PairN", [Expr::mvar(x), proj("PairN", 1, &value)]);
    let before = txn.clone();
    assert!(matches!(txn.unify(&record, &value, budget()), Err(UnificationError::Deferred(_))));
    unchanged(&txn, &before);
}

#[test]
fn nested_parameterized_projection_chains_are_metered() {
    let mut txn = transaction();
    let mut type_ = constant("PairN");
    for _ in 0..32 { type_ = Expr::app(constant("Box"), type_); }
    let mut value = local(&mut txn, "p", type_);
    for _ in 0..32 { value = proj("Box", 0, &value); }
    let record = mk("PairN", [proj("PairN", 0, &value), proj("PairN", 1, &value)]);
    let mut generous = budget();
    generous.max_steps = 2_000_000;
    generous.max_visited_nodes = 1_500_000;
    txn.budget.max_heartbeats = generous.max_steps;
    let initial = txn.clone();
    let report = txn.unify(&record, &value, generous).unwrap();
    assert_eq!(report.kernel_checks, 0);
    unchanged(&txn, &initial);
    let mut limited = generous;
    limited.max_steps = report.unifier_steps - 1;
    let mut stopped = initial.clone();
    assert!(matches!(stopped.unify(&record, &value, limited), Err(UnificationError::StepLimit { .. })));
    unchanged(&stopped, &initial);
}

#[test]
fn record_eta_composes_with_function_eta_and_miller_patterns() {
    let mut txn = transaction();
    let f = local(&mut txn, "f", Expr::forall_e(
        name("n"), constant("Nat"), constant("PairN"), BinderInfo::Default,
    ));
    let arrow = Expr::forall_e(
        name("n"), constant("Nat"), constant("Nat"), BinderInfo::Default,
    );
    let x = goal(&mut txn, "x", arrow.clone());
    let y = goal(&mut txn, "y", arrow);
    let argument = Expr::bvar(0).unwrap();
    let body = mk("PairN", [
        Expr::app(Expr::mvar(x.clone()), argument.clone()),
        Expr::app(Expr::mvar(y.clone()), argument),
    ]);
    let left = Expr::lam(name("n"), constant("Nat"), body, BinderInfo::Default);
    let report = txn.unify(&left, &f, budget()).unwrap();
    assert_eq!(report.expression_assignments, vec![x.clone(), y.clone()]);
    assert_eq!(report.kernel_checks, 2);
    let value = Expr::app(f, numeral(42));
    for (index, id) in [(0, x), (1, y)] {
        let application = Expr::app(Expr::mvar(id), numeral(42));
        let report = txn.unify(&application, &proj("PairN", index, &value), budget()).unwrap();
        assert!(report.expression_assignments.is_empty());
    }
}
