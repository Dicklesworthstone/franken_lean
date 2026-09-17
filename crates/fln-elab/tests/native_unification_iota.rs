//! Native recursor equations through ElabTxn, not a model of the solver.
#![forbid(unsafe_code)]

use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_elab::constraint::unify::{
    UnificationBudget, UnificationError, UnificationTransparency,
};
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
        [lam(constant("Nat"), constant("Nat")), zero, successor, major],
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
    assert_eq!(txn.mvars.get_assigned_expr(&id), Some(&constant("Bool.true")));
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
        [constant("Nat"), numeral(7), motive, numeral(23), numeral(7), proof],
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
