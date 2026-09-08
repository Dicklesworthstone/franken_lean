//! Source text -> native inference -> the real kernel. No mock unifier.
#![forbid(unsafe_code)]
use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::{DefinitionFrontendError, NatDefinitionElabError, check_definition_source};
use fln_env::constants::{
    AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};

fn n(s: &str) -> Name {
    Name::from_components(s.split('.'))
}
fn b(i: u32) -> Expr {
    Expr::bvar(i).unwrap()
}
fn nat() -> Expr {
    Expr::const_(n("Nat"), vec![])
}
fn num(v: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(v)))
}
fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn publish(env: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(env, declaration, budget()) else {
        panic!("admission nonanswer");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("not accepted");
    };
    let Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) = checked
        .publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        )
    else {
        panic!("not published");
    };
    result.environment
}
fn env() -> Environment {
    let env = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    let u = n("u");
    let ty = Expr::forall_e(
        n("a"),
        Expr::sort(Level::param(u.clone())),
        Expr::forall_e(n("x"), b(0), b(1), BinderInfo::Default),
        BinderInfo::Implicit,
    );
    let value = Expr::lam(
        n("a"),
        Expr::sort(Level::param(u.clone())),
        Expr::lam(n("x"), b(0), b(0), BinderInfo::Default),
        BinderInfo::Implicit,
    );
    publish(
        &env,
        Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("polyId"),
                level_params: vec![u],
                type_: ty,
            },
            value,
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![n("polyId")],
        }),
    )
}
fn accepted(source: &str, env: &Environment) -> DefinitionVal {
    let result = check_definition_source(source.as_bytes(), env, budget()).unwrap();
    assert!(
        matches!(result.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{:?}",
        result.outcome
    );
    let Declaration::Defn(value) = result.declaration else {
        panic!("definition expected");
    };
    assert!(!value.base.type_.has_expr_mvar());
    assert!(!value.value.has_expr_mvar());
    assert!(!value.base.type_.has_level_mvar());
    assert!(!value.value.has_level_mvar());
    assert!(!value.value.has_fvar());
    value
}
#[test]
fn source_inserts_type_and_universe_arguments_from_the_explicit_argument() {
    let result = accepted("def answer := polyId 37", &env());
    assert_eq!(result.base.type_, nat());
    let expected = Expr::app(
        Expr::app(Expr::const_(n("polyId"), vec![Level::one()]), nat()),
        num(37),
    );
    assert_eq!(result.value, expected);
}
#[test]
fn nested_calls_share_expected_types_without_sharing_fresh_holes() {
    let result = accepted("def nested : Nat := polyId (polyId 9)", &env());
    assert_eq!(result.base.type_, nat());
}
#[test]
fn inferred_let_binders_receive_the_instantiated_dependent_result() {
    let result = accepted("def local : Nat := let x := polyId 9; polyId x", &env());
    let ExprNode::LetE { type_, .. } = result.value.node() else {
        panic!("let expected");
    };
    assert_eq!(type_, &nat());
}
#[test]
fn expected_result_infers_an_implicit_with_no_explicit_value_argument() {
    let env = env();
    let ty = Expr::forall_e(n("a"), Expr::sort(Level::one()), b(0), BinderInfo::Implicit);
    let env = publish(
        &env,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("choose"),
                level_params: vec![],
                type_: ty,
            },
            is_unsafe: false,
        }),
    );
    let result = accepted("def picked : Nat := choose", &env);
    assert_eq!(
        result.value,
        Expr::app(Expr::const_(n("choose"), vec![]), nat())
    );
}
#[test]
fn wrong_closed_result_still_receives_the_ordinary_kernel_rejection() {
    let env = env();
    let result = check_definition_source(b"def bad : Nat := polyId Nat", &env, budget()).unwrap();
    assert!(matches!(
        result.outcome,
        Outcome::Complete(Verdict::Rejected { .. })
    ));
    assert_eq!(check(&env, &result.declaration, budget()), result.outcome);
}
#[test]
fn unresolved_implicit_is_not_defaulted_or_published() {
    let env = env();
    let ty = Expr::forall_e(
        n("a"),
        Expr::sort(Level::one()),
        nat(),
        BinderInfo::Implicit,
    );
    let env = publish(
        &env,
        Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: n("mystery"),
                level_params: vec![],
                type_: ty,
            },
            is_unsafe: false,
        }),
    );
    assert!(matches!(
        check_definition_source(b"def missing : Nat := mystery", &env, budget()),
        Err(DefinitionFrontendError::Elaborate(
            NatDefinitionElabError::Inference(_)
        ))
    ));
    assert!(!env.contains(&n("missing")));
}
#[test]
fn local_parameter_names_shadow_global_functions() {
    let result = accepted("def shadow (polyId : Nat) : Nat := polyId", &env());
    let ExprNode::Lam { body, .. } = result.value.node() else {
        panic!("lambda expected");
    };
    assert_eq!(body, &b(0));
}
#[test]
fn query_entry_points_use_the_same_native_inference() {
    let env = env();
    for (source, eval) in [("#check polyId 9", false), ("#eval polyId 9", true)] {
        let parsed = fln_parse::parse_source_command(source.as_bytes()).unwrap();
        let name = Name::num(Name::anonymous(), 800);
        let declaration = if eval {
            fln_elab::elaborate_evaluation_in(parsed.syntax(), name, &env)
        } else {
            fln_elab::elaborate_check_in(parsed.syntax(), name, &env)
        }
        .unwrap();
        assert!(matches!(
            check(&env, &declaration, budget()),
            Outcome::Complete(Verdict::Accepted { .. })
        ));
    }
}
