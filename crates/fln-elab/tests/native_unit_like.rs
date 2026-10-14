//! Zero-field structure conversion through the transactional native solver.
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
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::DeclarationCommitted;
use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::Budget;

fn name(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn constant(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}
fn number(n: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(n)))
}
fn app(f: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}
fn pi(a: Expr, b: Expr) -> Expr {
    Expr::forall_e(Name::anonymous(), a, b, BinderInfo::Default)
}
fn binder(s: &str, type_: Expr) -> LocalDecl {
    LocalDecl {
        id: FVarId(name(s)),
        user_name: name(s),
        type_,
        value: None,
        binder_info: BinderInfo::Default,
        index: 0,
    }
}
fn budget() -> UnificationBudget {
    let mut b = UnificationBudget::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    b.transparency = UnificationTransparency::None;
    b
}
fn publish(tx: &mut ElabTxn, decl: Declaration) {
    let Outcome::Complete(admitted) = admit(&tx.env, decl, budget().kernel) else {
        panic!("admission did not complete")
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("kernel refused fixture")
    };
    tx.env = match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::BlockCommitted(p)) => p.environment,
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
            p.environment
        }
        other => panic!("publication: {other:?}"),
    };
}
fn record(
    tx: &mut ElabTxn,
    s: &str,
    parameters: Vec<LocalDecl>,
    fields: Vec<LocalDecl>,
    level: Level,
    universes: Vec<Name>,
) {
    let spec = RecordSpec {
        name: name(s),
        level_params: universes,
        parameters,
        fields,
        result_level: level,
        is_class: false,
    };
    let block = record_declarations(&spec, RecordBudget::default())
        .unwrap()
        .remove(0);
    publish(tx, block);
}
fn txn() -> ElabTxn {
    let mut tx = ElabTxn::new(Environment::new(), KVMap::new(), 23);
    publish(&mut tx, fln_elab::seed::nat_inductive_seed_declaration());
    publish(&mut tx, fln_elab::seed::bool_seed_declaration());
    record(&mut tx, "Empty", vec![], vec![], Level::one(), vec![]);
    record(&mut tx, "OtherEmpty", vec![], vec![], Level::one(), vec![]);
    record(
        &mut tx,
        "Phantom",
        vec![binder("A", Expr::sort(Level::one()))],
        vec![],
        Level::one(),
        vec![],
    );
    record(
        &mut tx,
        "Nonempty",
        vec![],
        vec![binder("field", constant("Nat"))],
        Level::one(),
        vec![],
    );
    tx
}
fn local(tx: &mut ElabTxn, s: &str, type_: Expr) -> Expr {
    let id = FVarId(name(s));
    tx.lctx
        .add_param(id.clone(), id.0.clone(), type_, BinderInfo::Default);
    Expr::fvar(id)
}
fn hole(tx: &mut ElabTxn, s: &str, type_: Expr, kind: MetavarKind) -> MVarId {
    let id = MVarId(name(s));
    tx.mvars.declare(
        id.clone(),
        id.0.clone(),
        type_,
        tx.lctx.clone(),
        kind,
        0,
        None,
    );
    id
}
fn unchanged(actual: &ElabTxn, before: &ElabTxn) {
    assert_eq!(actual.env, before.env);
    assert_eq!(actual.mvars, before.mvars);
    assert_eq!(actual.universes, before.universes);
    assert_eq!(actual.constraints, before.constraints);
    assert_eq!(actual.lctx, before.lctx);
    assert_eq!(actual.options, before.options);
    assert_eq!(actual.seed, before.seed);
}
fn definition(tx: &mut ElabTxn, s: &str, type_: Expr, value: Expr) {
    let n = name(s);
    publish(
        tx,
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: n.clone(),
                level_params: vec![],
                type_,
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![n],
        }),
    );
}

#[test]
fn distinct_neutral_inhabitants_of_an_empty_record_compare_without_delta() {
    let mut tx = txn();
    let a = local(&mut tx, "a", constant("Empty"));
    let b = local(&mut tx, "b", constant("Empty"));
    let before = tx.clone();
    for (a, b) in [(&a, &b), (&b, &a)] {
        let report = tx.unify(a, b, budget()).unwrap();
        assert!(report.expression_assignments.is_empty());
        assert!(report.universe_assignments.is_empty());
        assert!(report.kernel_checks > 0);
        unchanged(&tx, &before);
    }
}

#[test]
fn unit_like_conversion_does_not_require_proof_irrelevance() {
    let mut tx = txn();
    let a = local(&mut tx, "a", constant("Empty"));
    let b = local(&mut tx, "b", constant("Empty"));
    let mut limits = budget();
    limits.proof_irrelevance = false;
    tx.unify(&a, &b, limits).unwrap();
}

#[test]
fn neutral_function_results_and_projected_empty_values_compare() {
    let mut tx = txn();
    record(
        &mut tx,
        "Pair",
        vec![],
        vec![
            binder("empty", constant("Empty")),
            binder("value", constant("Nat")),
        ],
        Level::one(),
        vec![],
    );
    let f = local(&mut tx, "f", pi(constant("Nat"), constant("Empty")));
    let g = local(&mut tx, "g", pi(constant("Bool"), constant("Empty")));
    let receiver = local(&mut tx, "pair", constant("Pair"));
    let projected = Expr::proj(name("Pair"), 0, receiver);
    let fa = Expr::app(f, number(2));
    let gb = Expr::app(g, constant("Bool.true"));
    tx.unify(&fa, &gb, budget()).unwrap();
    tx.unify(&projected, &fa, budget()).unwrap();
}

#[test]
fn field_counts_do_not_equate_different_types_or_nonempty_records() {
    for (left_type, right_type) in [
        (constant("Empty"), constant("OtherEmpty")),
        (
            app(constant("Phantom"), [constant("Nat")]),
            app(constant("Phantom"), [constant("Bool")]),
        ),
        (constant("Nonempty"), constant("Nonempty")),
        (constant("Nat"), constant("Nat")),
        (constant("Bool"), constant("Bool")),
    ] {
        let mut tx = txn();
        let a = local(&mut tx, "a", left_type);
        let b = local(&mut tx, "b", right_type);
        let before = tx.clone();
        assert!(tx.unify(&a, &b, budget()).is_err());
        unchanged(&tx, &before);
    }
}

#[test]
fn the_original_application_arguments_are_checked_before_erasure() {
    let mut tx = txn();
    let f = local(&mut tx, "f", pi(constant("Nat"), constant("Empty")));
    let g = local(&mut tx, "g", pi(constant("Bool"), constant("Empty")));
    let a = local(&mut tx, "a", constant("Empty"));
    for malformed in [Expr::app(f, constant("Bool.true")), Expr::app(g, number(0))] {
        let before = tx.clone();
        assert!(tx.unify(&malformed, &a, budget()).is_err());
        assert!(tx.unify(&a, &malformed, budget()).is_err());
        unchanged(&tx, &before);
    }
}

#[test]
fn opaque_arguments_are_not_discarded_as_unit_like_obligations() {
    let mut tx = txn();
    let f = local(&mut tx, "f", pi(constant("Nat"), constant("Empty")));
    let a = local(&mut tx, "a", constant("Empty"));
    let hidden = hole(
        &mut tx,
        "hidden",
        constant("Nat"),
        MetavarKind::SyntheticOpaque,
    );
    let before = tx.clone();
    assert!(
        tx.unify(&Expr::app(f, Expr::mvar(hidden)), &a, budget())
            .is_err()
    );
    unchanged(&tx, &before);
}

#[test]
fn local_lets_and_closed_global_aliases_keep_their_transparency() {
    let mut tx = txn();
    definition(
        &mut tx,
        "NatAlias",
        Expr::sort(Level::one()),
        constant("Nat"),
    );
    let left = local(
        &mut tx,
        "left",
        app(constant("Phantom"), [constant("NatAlias")]),
    );
    let right = local(
        &mut tx,
        "right",
        app(constant("Phantom"), [constant("Nat")]),
    );
    let before = tx.clone();
    assert!(tx.unify(&left, &right, budget()).is_err());
    unchanged(&tx, &before);
    let mut open = budget();
    open.transparency = UnificationTransparency::SafeDefinitions;
    tx.unify(&left, &right, open).unwrap();
    let id = FVarId(name("let_empty"));
    tx.lctx.add_let(
        id.clone(),
        name("let_empty"),
        constant("Empty"),
        constant("Empty.mk"),
    );
    let other = local(&mut tx, "other", constant("Empty"));
    let mut closed = budget();
    closed.zeta_delta = false;
    tx.unify(&Expr::fvar(id), &other, closed).unwrap();
}

#[test]
fn kernel_nonanswers_and_later_mismatches_roll_back_the_batch() {
    let mut tx = txn();
    let a = local(&mut tx, "a", constant("Empty"));
    let b = local(&mut tx, "b", constant("Empty"));
    let n = hole(&mut tx, "n", constant("Nat"), MetavarKind::Natural);
    let before = tx.clone();
    let mut exhausted = budget();
    exhausted.kernel = exhausted.kernel.narrowed(0, exhausted.kernel.depth);
    assert!(
        matches!(tx.unify(&a, &b, exhausted), Err(UnificationError::ConversionCheck { outcome }) if matches!(*outcome, Outcome::Inconclusive(_)))
    );
    unchanged(&tx, &before);
    assert!(
        tx.unify_many_with(
            &[(Expr::mvar(n), number(7)), (a, b), (number(0), number(1))],
            budget(),
            &|| false
        )
        .is_err()
    );
    unchanged(&tx, &before);
    assert!(tx.budget.heartbeats_consumed > before.budget.heartbeats_consumed);
}

#[test]
fn final_barrier_cancellation_and_work_limits_preserve_all_state() {
    use std::cell::Cell;
    let mut tx = txn();
    let a = local(&mut tx, "a", constant("Empty"));
    let b = local(&mut tx, "b", constant("Empty"));
    let n = hole(&mut tx, "n", constant("Nat"), MetavarKind::Natural);
    let equations = [(Expr::mvar(n), number(7)), (a, b)];
    let before = tx.clone();
    let polls = Cell::new(0);
    tx.clone()
        .unify_many_with(&equations, budget(), &|| {
            polls.set(polls.get() + 1);
            false
        })
        .unwrap();
    let last = polls.get();
    let calls = Cell::new(0);
    assert!(matches!(
        tx.unify_many_with(&equations, budget(), &|| {
            calls.set(calls.get() + 1);
            calls.get() == last
        }),
        Err(UnificationError::Cancelled)
    ));
    unchanged(&tx, &before);
    for nodes in [true, false] {
        let mut b = budget();
        if nodes {
            b.max_visited_nodes = 0;
        } else {
            b.max_steps = 0;
        }
        assert!(tx.unify_many_with(&equations, b, &|| false).is_err());
        unchanged(&tx, &before);
    }
}
