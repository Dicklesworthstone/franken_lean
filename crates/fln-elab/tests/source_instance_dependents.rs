//! Source elaboration and real kernel admission for dependent class outputs.
#![forbid(unsafe_code)]
use fln_core::expr::{BinderInfo, Expr, ExprNode, FVarId, Literal, NatLit};
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
fn app(head: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(c(head), Expr::app)
}
fn number(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
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
            ExprNode::LetE {
                type_, value, body, ..
            } => work.extend([type_, value, body]),
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => work.push(expr),
            _ => {}
        }
    }
    false
}

/// Dict takes one ordinary input. Family's dictionary depends on an output.
/// Further adds a third, transitively dependent instance parameter.
fn add_class(env: &Environment, name: &str, depth: usize) -> Environment {
    let mut locals = LocalContext::new();
    let sort = Expr::sort(Level::one());
    let domain = if depth == 0 {
        sort
    } else {
        Expr::app(
            Expr::const_(n("outParam"), vec![Level::one().succ().unwrap()]),
            sort,
        )
    };
    let a = locals
        .add_param(FVarId(n("a")), n("a"), domain, BinderInfo::Default)
        .clone();
    let a_expr = Expr::fvar(a.id.clone());
    let mut parameters = vec![a];
    if depth > 0 {
        let dictionary = locals
            .add_param(
                FVarId(n("dictionary")),
                n("dictionary"),
                app("Dict", [a_expr.clone()]),
                BinderInfo::InstImplicit,
            )
            .clone();
        let dictionary_expr = Expr::fvar(dictionary.id.clone());
        parameters.push(dictionary);
        if depth > 1 {
            parameters.push(
                locals
                    .add_param(
                        FVarId(n("family")),
                        n("family"),
                        app("Family", [a_expr, dictionary_expr]),
                        BinderInfo::InstImplicit,
                    )
                    .clone(),
            );
        }
    }
    let field = locals
        .add_param(
            FVarId(n("value")),
            n("value"),
            c("Nat"),
            BinderInfo::Default,
        )
        .clone();
    let spec = RecordSpec {
        name: n(name),
        level_params: vec![],
        parameters,
        fields: vec![field],
        result_level: Level::one(),
        is_class: true,
    };
    let mut env = env.clone();
    for declaration in record_declarations(&spec, RecordBudget::default()).unwrap() {
        env = publish(&env, declaration);
    }
    register_class(&env, &n(name)).unwrap()
}
fn fixture() -> Environment {
    let mut env = fln_elab::seed::bootstrap_nat_environment(budget()).unwrap();
    env = publish(&env, fln_elab::seed::out_param_seed_declaration());
    env = add_class(&env, "Dict", 0);
    env = add_class(&env, "Family", 1);
    env = add_class(&env, "Further", 2);
    // These are distinct data-bearing dictionaries, not proof-irrelevant proofs.
    // Neither is registered: Family/Further must infer the dictionary output.
    for (name, value) in [("dictZero", 0), ("dictOne", 1)] {
        env = publish(
            &env,
            definition(
                name,
                app("Dict", [c("Nat")]),
                app("Dict.mk", [c("Nat"), number(value)]),
            ),
        );
    }
    for (name, dictionary, priority) in [
        ("familyHigh", "dictZero", 2000),
        ("familyLow", "dictOne", 500),
    ] {
        env = publish(
            &env,
            definition(
                name,
                app("Family", [c("Nat"), c(dictionary)]),
                app("Family.mk", [c("Nat"), c(dictionary), number(7)]),
            ),
        );
        env = register_instance(&env, &n(name), priority).unwrap();
    }
    env = publish(
        &env,
        definition(
            "further",
            app("Further", [c("Nat"), c("dictZero"), c("familyHigh")]),
            app(
                "Further.mk",
                [c("Nat"), c("dictZero"), c("familyHigh"), number(9)],
            ),
        ),
    );
    env = register_instance(&env, &n("further"), 1000).unwrap();
    for text in [
        "def useDict {a : Type} [d : Dict a] (dummy : Nat) : Nat := @Dict.value a d",
        "def useFamily {a : Type} [d : Dict a] [f : @Family a d] (dummy : Nat) : Nat := @Family.value a d f",
        "def useFurther {a : Type} [d : Dict a] [f : @Family a d] [g : @Further a d f] (dummy : Nat) : Nat := @Further.value a d f g",
    ] {
        env = publish(&env, Declaration::Defn(accepted(text, &env)));
    }
    env
}

#[test]
fn dependent_output_synthesis_unblocks_an_earlier_ordinary_instance_goal() {
    let value = accepted("def selected := useFamily 0", &fixture());
    assert_eq!(value.base.type_, c("Nat"));
    assert!(has_constant(&value.value, "dictZero"));
    assert!(has_constant(&value.value, "familyHigh"));
    assert!(!has_constant(&value.value, "familyLow"));
}

#[test]
fn transitive_dictionary_outputs_are_inferred_and_kernel_checked() {
    let value = accepted("def selected := useFurther 0", &fixture());
    assert_eq!(value.base.type_, c("Nat"));
    for name in ["dictZero", "familyHigh", "further"] {
        assert!(has_constant(&value.value, name), "missing inferred {name}");
    }
}

#[test]
fn known_dependent_outputs_do_not_filter_out_the_highest_priority_instance() {
    let env = fixture();
    accepted("def selected : @Family Nat dictZero := inferInstance", &env);
    // Selection must still choose familyHigh, then refuse the incompatible
    // dictOne output. Selecting familyLow instead would violate outParam order.
    assert!(
        check_definition_source(
            b"def wrong : @Family Nat dictOne := inferInstance",
            &env,
            budget(),
        )
        .is_err()
    );
    assert!(env.find(&n("wrong")).is_none());
    accepted("def recovered := useFamily 0", &env);
}

#[test]
fn local_instances_keep_precedence_over_global_dependent_output_candidates() {
    let value = accepted(
        "def selected [localFamily : @Family Nat dictOne] : @Family Nat dictOne := inferInstance",
        &fixture(),
    );
    assert!(!has_constant(&value.value, "familyHigh"));
    assert!(!has_constant(&value.value, "familyLow"));
    let ExprNode::Lam { body, .. } = value.value.node() else {
        panic!("local dictionary binder expected");
    };
    assert_eq!(body, &Expr::bvar(0).unwrap());
}

#[test]
fn ordinary_inputs_remain_blocked_and_failed_search_does_not_poison_recovery() {
    let env = fixture();
    assert!(check_definition_source(b"def blocked := useDict 0", &env, budget()).is_err());
    assert!(env.find(&n("blocked")).is_none());
    accepted("def recovered := useFurther 0", &env);
}
