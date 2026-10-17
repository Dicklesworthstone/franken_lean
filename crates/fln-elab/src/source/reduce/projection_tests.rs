//! The two native reducers share the pin's conditional class projection rule.

use super::*;
use crate::records::{RecordBudget, RecordSpec, record_declarations};
use fln_core::expr::NatLit;
use fln_core::outcome::Outcome;
use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
use fln_env::pmap::CollisionBudget;
use fln_kernel::capability::{Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn c(text: &str) -> Expr {
    Expr::const_(n(text), Vec::new())
}
fn numeral(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}
fn app(head: Expr, args: impl IntoIterator<Item = Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}
fn dictionary() -> Expr {
    app(
        c("Chooser.mk"),
        [
            c("Nat"),
            numeral(7),
            Expr::lam(
                n("x"),
                c("Nat"),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
        ],
    )
}
fn projection(field: &str, receiver: Expr) -> Expr {
    app(c(field), [c("Nat"), receiver])
}
fn limits() -> Budget {
    Budget::for_stack_bytes(2 * 1024 * 1024)
}
fn comparison_limits() -> UnificationBudget {
    let mut budget = UnificationBudget::new(limits());
    budget.transparency = UnificationTransparency::Instances;
    budget
}
fn publish(env: &Environment, declaration: Declaration) -> Environment {
    let Outcome::Complete(admitted) = admit(env, declaration, limits()) else {
        panic!("fixture admission did not complete");
    };
    let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted) else {
        panic!("fixture admission was refused");
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
        other => panic!("fixture publication failed: {other:?}"),
    }
}
fn binder(name: &str, type_: Expr) -> LocalDecl {
    LocalDecl {
        id: FVarId(n(name)),
        user_name: n(name),
        type_,
        value: None,
        binder_info: BinderInfo::Default,
        index: 0,
    }
}
fn environment(registered: bool) -> Environment {
    let mut env = crate::seed::bootstrap_nat_environment(limits()).unwrap();
    let a = binder("A", Expr::sort(Level::one()));
    let a_type = Expr::fvar(a.id.clone());
    let declarations = record_declarations(
        &RecordSpec {
            name: n("Chooser"),
            level_params: Vec::new(),
            parameters: vec![a],
            fields: vec![
                binder("value", a_type.clone()),
                binder(
                    "map",
                    Expr::forall_e(n("x"), a_type.clone(), a_type, BinderInfo::Default),
                ),
            ],
            result_level: Level::one(),
            is_class: true,
        },
        RecordBudget::default(),
    )
    .unwrap();
    let mut alias = None;
    for declaration in declarations {
        if let Declaration::Defn(definition) = &declaration
            && definition.base.name == n("Chooser.value")
        {
            let mut definition = definition.clone();
            definition.base.name = n("Chooser.alias");
            definition.all = vec![definition.base.name.clone()];
            alias = Some(Declaration::Defn(definition));
        }
        env = publish(&env, declaration);
    }
    env = publish(&env, alias.unwrap());
    for name in ["Chooser.value", "Chooser.map", "Chooser.alias"] {
        env = crate::reducibility::register(
            &env,
            &n(name),
            crate::reducibility::Reducibility::Semireducible,
        )
        .unwrap();
    }
    for name in ["hiddenDictionary", "visibleDictionary"] {
        env = publish(
            &env,
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n(name),
                    level_params: Vec::new(),
                    type_: Expr::app(c("Chooser"), c("Nat")),
                },
                value: dictionary(),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![n(name)],
            }),
        );
    }
    env = crate::reducibility::register(
        &env,
        &n("hiddenDictionary"),
        crate::reducibility::Reducibility::Semireducible,
    )
    .unwrap();
    if registered {
        env = crate::instances::register_class(&env, &n("Chooser")).unwrap();
        env = crate::instances::register_instance(&env, &n("visibleDictionary"), 1000).unwrap();
    }
    env
}

#[test]
fn both_reducers_project_constructors_and_instance_definitions_with_extra_arguments() {
    let env = environment(true);
    let local = FVarId(n("localDictionary"));
    let mut ctx = Context::new(&env, limits());
    ctx.txn.lctx.add_let(
        local.clone(),
        local.0.clone(),
        Expr::app(c("Chooser"), c("Nat")),
        dictionary(),
    );
    let receivers = [
        dictionary(),
        c("visibleDictionary"),
        Expr::fvar(local),
        Expr::let_e(
            n("d"),
            Expr::app(c("Chooser"), c("Nat")),
            dictionary(),
            Expr::bvar(0).unwrap(),
            false,
        ),
    ];
    for receiver in receivers {
        for (input, expected) in [
            (projection("Chooser.value", receiver.clone()), numeral(7)),
            (
                Expr::app(projection("Chooser.map", receiver), numeral(11)),
                numeral(11),
            ),
        ] {
            assert_eq!(
                ctx.whnf_with_transparency(&input, UnificationTransparency::Instances, true)
                    .unwrap(),
                expected
            );
            ctx.txn
                .unify(&input, &expected, comparison_limits())
                .unwrap();
        }
    }
    assert_eq!(ctx.txn.env, env);
    assert!(ctx.txn.mvars.is_empty());
}

#[test]
fn stuck_class_projections_keep_the_named_call_and_do_not_guess_instances() {
    let env = environment(true);
    let mut ctx = Context::new(&env, limits());
    let local = FVarId(n("unknownDictionary"));
    ctx.txn.lctx.add_param(
        local.clone(),
        local.0.clone(),
        Expr::app(c("Chooser"), c("Nat")),
        BinderInfo::InstImplicit,
    );
    for input in [
        projection("Chooser.value", c("hiddenDictionary")),
        projection("Chooser.value", Expr::fvar(local)),
        projection("Chooser.alias", dictionary()),
    ] {
        assert_eq!(
            ctx.whnf_with_transparency(&input, UnificationTransparency::Instances, true)
                .unwrap(),
            input
        );
        assert!(
            ctx.txn
                .unify(&input, &numeral(7), comparison_limits())
                .is_err()
        );
    }
    let partial = Expr::app(c("Chooser.value"), c("Nat"));
    assert_eq!(
        ctx.whnf_with_transparency(&partial, UnificationTransparency::Instances, true)
            .unwrap(),
        partial
    );
    assert_eq!(ctx.txn.env, env);
    assert!(ctx.txn.mvars.is_empty());
}

#[test]
fn class_registration_projection_opacity_and_local_zeta_policy_are_required() {
    let input = projection("Chooser.value", dictionary());
    let env = environment(false);
    let opaque = crate::reducibility::register(
        &environment(true),
        &n("Chooser.value"),
        crate::reducibility::Reducibility::Irreducible,
    )
    .unwrap();
    for env in [env, opaque] {
        let mut ctx = Context::new(&env, limits());
        assert_eq!(
            ctx.whnf_with_transparency(&input, UnificationTransparency::Instances, true)
                .unwrap(),
            input
        );
        assert!(
            ctx.txn
                .unify(&input, &numeral(7), comparison_limits())
                .is_err()
        );
    }
    let env = environment(true);
    let mut ctx = Context::new(&env, limits());
    let local = FVarId(n("d"));
    ctx.txn.lctx.add_let(
        local.clone(),
        local.0.clone(),
        Expr::app(c("Chooser"), c("Nat")),
        dictionary(),
    );
    let input = projection("Chooser.value", Expr::fvar(local));
    assert_eq!(
        ctx.whnf_with_transparency(&input, UnificationTransparency::Instances, false)
            .unwrap(),
        input
    );
    let mut budget = comparison_limits();
    budget.zeta_delta = false;
    assert!(ctx.txn.unify(&input, &numeral(7), budget).is_err());
}

#[test]
fn class_projection_reduction_stops_with_the_shared_work_budget() {
    let env = environment(true);
    let input = projection("Chooser.value", dictionary());
    let mut control = Context::new(&env, limits());
    assert_eq!(
        control
            .whnf_with_transparency(&input, UnificationTransparency::Instances, true)
            .unwrap(),
        numeral(7)
    );
    let mut limited = Context::new(&env, limits());
    limited.txn.budget.max_heartbeats = control.txn.budget.heartbeats_consumed - 1;
    assert!(matches!(
        limited.whnf_with_transparency(&input, UnificationTransparency::Instances, true),
        Err(NatDefinitionElabError::Inference(
            SourceInferenceError::ResourceLimit
        ))
    ));
    let report = control
        .txn
        .unify(&input, &numeral(7), comparison_limits())
        .unwrap();
    let mut budget = comparison_limits();
    budget.max_steps = report.unifier_steps - 1;
    let mut stopped = Context::new(&env, limits());
    assert!(matches!(
        stopped.txn.unify(&input, &numeral(7), budget),
        Err(UnificationError::StepLimit { .. })
    ));
    for ctx in [limited, stopped] {
        assert_eq!(ctx.txn.env, env);
        assert!(ctx.txn.mvars.is_empty());
    }
}
