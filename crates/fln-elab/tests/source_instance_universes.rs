//! Source text -> native instance search -> real kernel admission.
//! Fixtures are admitted declarations, not mocked class or unification tables.
#![forbid(unsafe_code)]
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_elab::instances::{register_class, register_instance};
use fln_elab::records::{RecordBudget, RecordSpec, record_declarations};
use fln_elab::{LocalContext, check_definition_source};
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_env::environment::{DeclarationBudget, DeclarationCommitted, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::{Budget, Verdict};

fn n(value: &str) -> Name {
    Name::from_components(value.split('.'))
}
fn c(value: &str) -> Expr {
    Expr::const_(n(value), vec![])
}
fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn budget() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn publish(env: &Environment, declaration: Declaration) -> Environment {
    let description = format!("{declaration:?}");
    let Outcome::Complete(admitted) = admit(env, declaration, budget()) else {
        panic!("fixture admission must answer: {description}");
    };
    let checked = match convene(&Council::nobody_was_asked(), admitted) {
        CouncilOutcome::Agreed(checked) => checked,
        _ => panic!("fixture must be kernel accepted: {description}"),
    };
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
            result.environment
        }
        Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
        other => panic!("fixture must publish atomically: {other:?}"),
    }
}
fn definition(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}
fn accepted(source: &str, env: &Environment) -> DefinitionVal {
    let checked = check_definition_source(source.as_bytes(), env, budget())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert!(
        matches!(checked.outcome, Outcome::Complete(Verdict::Accepted { .. })),
        "{source}: {:?}",
        checked.outcome
    );
    let Declaration::Defn(value) = checked.declaration else {
        panic!("definition expected");
    };
    for expr in [&value.base.type_, &value.value] {
        assert!(!expr.has_expr_mvar());
        assert!(!expr.has_level_mvar());
        assert!(!expr.has_fvar());
        assert!(!expr.has_loose_bvars());
    }
    value
}
fn has_constant(expr: &Expr, name: &str) -> bool {
    let mut work = vec![expr];
    while let Some(expr) = work.pop() {
        match expr.node() {
            ExprNode::Const { name: actual, .. } if actual == &n(name) => return true,
            ExprNode::App { f, a } => work.extend([f, a]),
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => work.extend([binder_type, body]),
            ExprNode::MData { expr, .. } => work.push(expr),
            _ => {}
        }
    }
    false
}
fn polymorphic_output_fixture(output: bool, higher: bool) -> Environment {
    let mut env = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    env = publish(&env, fln_elab::seed::out_param_seed_declaration());
    let u = Level::param(n("u"));
    let mut locals = LocalContext::new();
    let domain = if output {
        Expr::app(
            Expr::const_(n("outParam"), vec![u.clone().succ().unwrap()]),
            Expr::sort(u.clone()),
        )
    } else {
        Expr::sort(u.clone())
    };
    let a = locals
        .add_param(FVarId(n("a")), n("a"), domain, BinderInfo::Default)
        .clone();
    let field = locals
        .add_param(
            FVarId(n("value")),
            n("value"),
            Expr::fvar(a.id.clone()),
            BinderInfo::Default,
        )
        .clone();
    for declaration in record_declarations(
        &RecordSpec {
            name: n("Carrier"),
            level_params: vec![n("u")],
            parameters: vec![a],
            fields: vec![field],
            result_level: Level::max(Level::one(), u.clone()).unwrap(),
            is_class: true,
        },
        RecordBudget::default(),
    )
    .unwrap()
    {
        env = publish(&env, declaration);
    }
    env = register_class(&env, &n("Carrier")).unwrap();
    let b = |i| Expr::bvar(i).unwrap();
    let ty = Expr::forall_e(
        n("a"),
        Expr::sort(u.clone()),
        Expr::forall_e(
            n("d"),
            Expr::app(Expr::const_(n("Carrier"), vec![u.clone()]), b(0)),
            Expr::forall_e(n("dummy"), c("Nat"), b(2), BinderInfo::Default),
            BinderInfo::InstImplicit,
        ),
        BinderInfo::Implicit,
    );
    let value = Expr::lam(
        n("a"),
        Expr::sort(u.clone()),
        Expr::lam(
            n("d"),
            Expr::app(Expr::const_(n("Carrier"), vec![u.clone()]), b(0)),
            Expr::lam(
                n("dummy"),
                c("Nat"),
                app(Expr::const_(n("Carrier.value"), vec![u]), [b(2), b(1)]),
                BinderInfo::Default,
            ),
            BinderInfo::InstImplicit,
        ),
        BinderInfo::Implicit,
    );
    let mut probe = definition("polyProbe", ty, value);
    let Declaration::Defn(ref mut d) = probe else {
        unreachable!()
    };
    d.base.level_params = vec![n("u")];
    env = publish(&env, probe);
    let (ty, level, value) = if higher {
        (
            Expr::sort(Level::one()),
            Level::one().succ().unwrap(),
            c("Nat"),
        )
    } else {
        (
            c("Nat"),
            Level::one(),
            Expr::lit(fln_core::expr::Literal::Nat(
                fln_core::expr::NatLit::from_u64(7),
            )),
        )
    };
    env = publish(
        &env,
        definition(
            "carrier",
            Expr::app(Expr::const_(n("Carrier"), vec![level.clone()]), ty.clone()),
            app(Expr::const_(n("Carrier.mk"), vec![level]), [ty, value]),
        ),
    );
    register_instance(&env, &n("carrier"), 1000).unwrap()
}

#[test]
fn output_search_infers_the_class_universe_from_a_selected_instance() {
    let value = accepted(
        "def chosen := polyProbe 0",
        &polymorphic_output_fixture(true, false),
    );
    assert_eq!(value.base.type_, c("Nat"));
    assert!(has_constant(&value.value, "carrier"));
}

#[test]
fn output_search_infers_higher_universes_without_defaulting_to_type_zero() {
    let value = accepted(
        "def chosen := polyProbe 0",
        &polymorphic_output_fixture(true, true),
    );
    assert_eq!(value.base.type_, Expr::sort(Level::one()));
}

#[test]
fn universe_inference_does_not_guess_an_ordinary_class_input() {
    let env = polymorphic_output_fixture(false, true);
    assert!(check_definition_source(b"def blocked := polyProbe 0", &env, budget()).is_err());
    accepted("def chosen : Type := polyProbe 0", &env);
}

#[test]
fn polymorphic_output_cycles_fall_back_without_exhausting_search() {
    let mut env = polymorphic_output_fixture(true, true);
    let u = Level::param(n("u"));
    let b = |i| Expr::bvar(i).unwrap();
    let ty = Expr::forall_e(
        n("a"),
        Expr::sort(u.clone()),
        Expr::forall_e(
            n("d"),
            Expr::app(Expr::const_(n("Carrier"), vec![u.clone()]), b(0)),
            Expr::app(Expr::const_(n("Carrier"), vec![u.clone()]), b(1)),
            BinderInfo::InstImplicit,
        ),
        BinderInfo::Implicit,
    );
    let value = Expr::lam(
        n("a"),
        Expr::sort(u.clone()),
        Expr::lam(
            n("d"),
            Expr::app(Expr::const_(n("Carrier"), vec![u]), b(0)),
            b(0),
            BinderInfo::InstImplicit,
        ),
        BinderInfo::Implicit,
    );
    let mut loop_decl = definition("loopCarrier", ty, value);
    let Declaration::Defn(ref mut d) = loop_decl else {
        unreachable!()
    };
    d.base.level_params = vec![n("u")];
    env = publish(&env, loop_decl);
    env = register_instance(&env, &n("loopCarrier"), 3000).unwrap();
    let value = accepted("def chosen := polyProbe 0", &env);
    assert_eq!(value.base.type_, Expr::sort(Level::one()));
    assert!(!has_constant(&value.value, "loopCarrier"));
}
