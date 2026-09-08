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

#[test]
fn source_defined_implicit_identity_is_usable_by_the_next_declaration() {
    let environment = env();
    let identity = accepted("def identity {a : Type} (x : a) : a := x", &environment);
    assert!(matches!(
        identity.base.type_.node(),
        ExprNode::ForallE {
            binder_info: BinderInfo::Implicit,
            ..
        }
    ));
    let environment = publish(&environment, Declaration::Defn(identity));
    let answer = accepted("def answer := identity 42", &environment);
    assert_eq!(answer.base.type_, nat());
    assert_eq!(
        answer.value,
        Expr::app(
            Expr::app(Expr::const_(n("identity"), vec![]), nat()),
            num(42)
        )
    );
}

#[test]
fn strict_implicit_source_binders_are_inserted_before_explicit_arguments() {
    let environment = env();
    let identity = accepted("def strict ⦃a : Type⦄ (x : a) : a := x", &environment);
    assert!(matches!(
        identity.base.type_.node(),
        ExprNode::ForallE {
            binder_info: BinderInfo::StrictImplicit,
            ..
        }
    ));
    let environment = publish(&environment, Declaration::Defn(identity));
    assert_eq!(
        accepted("def value := strict 17", &environment).base.type_,
        nat()
    );
}

#[test]
fn source_placeholder_type_argument_is_solved_by_a_later_argument() {
    let environment = env();
    let identity = accepted("def explicit (a : Type) (x : a) : a := x", &environment);
    let environment = publish(&environment, Declaration::Defn(identity));
    let result = accepted("def inferred := explicit _ 37", &environment);
    assert_eq!(
        result.value,
        Expr::app(
            Expr::app(Expr::const_(n("explicit"), vec![]), nat()),
            num(37)
        )
    );
}

#[test]
fn dependent_function_types_and_local_let_ascriptions_are_checked() {
    let environment = env();
    accepted(
        "def apply {a b : Type} (f : a -> b) (x : a) : b := f x",
        &environment,
    );
    accepted(
        "def localType (a : Type) (x : a) : a := let y : a := x; y",
        &environment,
    );
    accepted(
        "def function (f : Nat → Nat) : Nat → Nat := f",
        &environment,
    );
    accepted("def proposition (p : Prop) (h : p) : p := h", &environment);
}

#[test]
fn unresolved_holes_in_unused_parameter_domains_are_still_refused() {
    let environment = env();
    assert!(
        check_definition_source(b"def wrong (x : _) : Nat := 0", &environment, budget()).is_err()
    );
    assert!(
        check_definition_source(b"def wrong : Nat := polyId _", &environment, budget()).is_err()
    );
    assert!(
        check_definition_source(b"def wrong (x : 1) : Nat := 0", &environment, budget()).is_err()
    );
}

#[test]
fn dependent_source_syntax_retains_original_bytes() {
    let source = "def id {α : Type} (f : α → α) (x : α) : α := f x\r\n";
    let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source.replace("\r\n", "\n").as_bytes()
    );
}

#[test]
fn implicit_type_arguments_may_be_functions_not_just_scalar_names() {
    let environment = env();
    accepted(
        "def higher (f : Nat -> Nat) : Nat -> Nat := polyId f",
        &environment,
    );
    accepted(
        "def higherCall (f : Nat -> Nat) : Nat := (polyId f) 5",
        &environment,
    );
}

#[test]
fn escaped_keywords_resolve_as_identifiers_not_as_universes_or_holes() {
    let environment = env();
    for keyword in ["Type", "Prop", "_"] {
        let source = format!("def «{keyword}» : Nat := 7");
        let declaration = accepted(&source, &environment);
        let environment = publish(&environment, Declaration::Defn(declaration));
        let usage = format!("def result : Nat := «{keyword}»");
        assert_eq!(
            accepted(&usage, &environment).value,
            Expr::const_(n(keyword), vec![])
        );
    }
}

#[test]
fn lambda_binders_receive_expected_domains() {
    let result = accepted("def identity : Nat -> Nat := fun x => x", &env());
    let ExprNode::Lam {
        binder_type, body, ..
    } = result.value.node()
    else {
        panic!("lambda expected");
    };
    assert_eq!(binder_type, &nat());
    assert_eq!(body, &b(0));
}
#[test]
fn lambda_application_infers_an_unannotated_domain() {
    let result = accepted("def answer := (fun x => x) 37", &env());
    assert_eq!(result.base.type_, nat());
}
#[test]
fn nested_lambda_binders_are_closed_capture_avoidantly() {
    let result = accepted("def first : Nat -> Nat -> Nat := fun x y => x", &env());
    let ExprNode::Lam { body, .. } = result.value.node() else {
        panic!("outer lambda");
    };
    let ExprNode::Lam { body, .. } = body.node() else {
        panic!("inner lambda");
    };
    assert_eq!(body, &b(1));
    accepted("def inner : Nat -> Nat := fun x => (fun y => x) 0", &env());
}
#[test]
fn unicode_lambdas_and_nested_calls_preserve_expected_types() {
    accepted("def identity : Nat → Nat := λ x ↦ polyId x", &env());
}
#[test]
fn higher_order_arguments_can_be_source_lambdas() {
    let env = env();
    let apply = accepted("def apply (f : Nat -> Nat) (x : Nat) : Nat := f x", &env);
    let env = publish(&env, Declaration::Defn(apply));
    accepted("def answer := apply (fun x => polyId x) 37", &env);
}
#[test]
fn a_bare_unconstrained_lambda_does_not_get_a_guessed_domain() {
    assert!(matches!(
        check_definition_source(b"def unknown := fun x => x", &env(), budget()),
        Err(DefinitionFrontendError::Elaborate(
            NatDefinitionElabError::Inference(_)
        ))
    ));
}
#[test]
fn lambda_scope_restoration_preserves_outer_bindings() {
    accepted("def shadow (x : Nat) : Nat -> Nat := fun x => x", &env());
    accepted("def shadow : Nat -> Nat := let x := 7; fun x => x", &env());
}
