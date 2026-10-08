//! Source search tests over small, explicit axiom signatures. These fixtures
//! exercise metadata and ordinary candidate checking, not artifact admission.
use super::*;
use crate::instances::{
    discr_tree::Key, imported, register_class, register_instance, set_instance,
};
use fln_core::level::Level;
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn constant(text: &str) -> Expr {
    Expr::const_(name(text), Vec::new())
}
fn type_() -> Expr {
    Expr::sort(Level::one())
}
fn forall(label: &str, domain: Expr, body: Expr, binder: BinderInfo) -> Expr {
    Expr::forall_e(name(label), domain, body, binder)
}
fn axiom(env: &Environment, label: &str, type_: Expr) -> Environment {
    env.add_decl(ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: name(label),
            level_params: Vec::new(),
            type_,
        },
        is_unsafe: false,
    }))
    .unwrap()
}
fn fixture() -> Environment {
    let mut env = axiom(&Environment::new(), "Token", type_());
    env = axiom(
        &env,
        "Mark",
        forall("A", type_(), type_(), BinderInfo::Default),
    );
    env = register_class(&env, &name("Mark")).unwrap();
    env = axiom(
        &env,
        "specific",
        Expr::app(constant("Mark"), constant("Token")),
    );
    env = register_instance(&env, &name("specific"), 1000).unwrap();
    env = axiom(
        &env,
        "generic",
        forall(
            "A",
            type_(),
            Expr::app(constant("Mark"), Expr::bvar(0).unwrap()),
            BinderInfo::Default,
        ),
    );
    register_instance(&env, &name("generic"), 1000).unwrap()
}
fn context(env: &Environment) -> Context {
    Context::new(env, Budget::for_stack_bytes(2 * 1024 * 1024))
}
fn selected(env: &Environment, registry: &InstanceRegistry) -> Expr {
    let mut ctx = context(env);
    let hole = ctx
        .instance_hole(Expr::app(constant("Mark"), constant("Token")))
        .unwrap();
    let ExprNode::MVar { id } = hole.node() else {
        unreachable!()
    };
    assert_eq!(
        ctx.search_instance(id.clone(), registry).unwrap(),
        SearchResult::Solved
    );
    ctx.instantiate(&hole).unwrap()
}
fn candidates(env: &Environment, registry: &InstanceRegistry) -> Vec<String> {
    let mut ctx = context(env);
    ctx.instance_search_index(registry)
        .unwrap()
        .narrow(
            env,
            &LocalContext::default(),
            &Expr::app(constant("Mark"), constant("Token")),
            registry.candidates(&name("Mark")),
        )
        .into_iter()
        .map(|entry| entry.declaration.to_display_string())
        .collect()
}

#[test]
fn native_specific_beats_newer_generic_and_priority_upserts_keep_their_slot() {
    let env = fixture();
    let original = env.clone();
    let registry = InstanceRegistry::read(&env).unwrap();
    assert_eq!(candidates(&env, &registry), ["specific", "generic"]);
    assert_eq!(selected(&env, &registry), constant("specific"));

    let mut updated = axiom(
        &env,
        "laterSpecific",
        Expr::app(constant("Mark"), constant("Token")),
    );
    updated = register_instance(&updated, &name("laterSpecific"), 1000).unwrap();
    updated = set_instance(&updated, &name("specific"), 2000).unwrap();
    let higher = InstanceRegistry::read(&updated).unwrap();
    assert_eq!(selected(&updated, &higher), constant("specific"));
    updated = set_instance(&updated, &name("specific"), 1000).unwrap();
    let tied = InstanceRegistry::read(&updated).unwrap();
    assert_eq!(
        candidates(&updated, &tied),
        ["laterSpecific", "specific", "generic"]
    );
    assert_eq!(selected(&updated, &tied), constant("laterSpecific"));
    assert_eq!(selected(&env, &registry), constant("specific"));
    assert_eq!(env, original);
}

#[test]
fn imported_and_native_peers_share_one_registration_order() {
    let mut env = fixture();
    env = imported::register_instance(
        &env,
        &name("specific"),
        &imported::InstanceParameters {
            priority: 1000,
            synth_order: Vec::new(),
            scope: None,
            keys: vec![Key::Const(name("Mark"), 1), Key::Const(name("Token"), 0)],
        },
    )
    .unwrap();
    env = axiom(&env, "last", Expr::app(constant("Mark"), constant("Token")));
    env = register_instance(&env, &name("last"), 1000).unwrap();
    let registry = InstanceRegistry::read(&env).unwrap();
    assert_eq!(candidates(&env, &registry), ["last", "specific", "generic"]);
    assert_eq!(selected(&env, &registry), constant("last"));
}

#[test]
fn unsupported_native_models_keep_the_existing_unindexed_fallback() {
    let mut env = fixture();
    env = env
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: name("Alias"),
                level_params: Vec::new(),
                type_: type_(),
            },
            value: constant("Token"),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name("Alias")],
        }))
        .unwrap();
    env = axiom(
        &env,
        "throughAlias",
        Expr::app(constant("Mark"), constant("Alias")),
    );
    env = register_instance(&env, &name("throughAlias"), 1000).unwrap();
    let registry = InstanceRegistry::read(&env).unwrap();
    assert_eq!(
        candidates(&env, &registry),
        ["throughAlias", "specific", "generic"]
    );
    let mut ctx = context(&env);
    assert!(
        ctx.instance_search_index(&registry)
            .unwrap()
            .native_synth_order(&name("throughAlias"))
            .is_none()
    );
}

#[test]
fn native_output_dependent_prerequisites_follow_the_derived_schedule() {
    let mut env = Environment::new();
    let fln_kernel::Declaration::Defn(marker) = crate::seed::out_param_seed_declaration() else {
        unreachable!("outParam is the ordinary identity definition")
    };
    env = env.add_decl(ConstantInfo::Defn(marker)).unwrap();
    env = axiom(
        &env,
        "Needs",
        forall("A", type_(), type_(), BinderInfo::Default),
    );
    let output = Expr::app(
        Expr::const_(name("outParam"), vec![Level::one().succ().unwrap()]),
        type_(),
    );
    env = axiom(
        &env,
        "Out",
        forall("A", output, type_(), BinderInfo::Default),
    );
    env = axiom(&env, "Result", type_());
    for class in ["Needs", "Out", "Result"] {
        env = register_class(&env, &name(class)).unwrap();
    }
    let signature = forall(
        "A",
        type_(),
        forall(
            "needs",
            Expr::app(constant("Needs"), Expr::bvar(0).unwrap()),
            forall(
                "out",
                Expr::app(constant("Out"), Expr::bvar(1).unwrap()),
                constant("Result"),
                BinderInfo::InstImplicit,
            ),
            BinderInfo::InstImplicit,
        ),
        BinderInfo::Default,
    );
    env = axiom(&env, "chain", signature);
    env = register_instance(&env, &name("chain"), 1000).unwrap();
    let registry = InstanceRegistry::read(&env).unwrap();
    let mut ctx = context(&env);
    assert_eq!(
        ctx.instance_search_index(&registry)
            .unwrap()
            .native_synth_order(&name("chain")),
        Some([2, 1].as_slice())
    );
    let expansion = ctx
        .expand_instance(
            &Candidate::Global(name("chain")),
            &constant("Result"),
            false,
            &registry,
        )
        .unwrap()
        .unwrap();
    let heads: Vec<_> = expansion
        .subgoals
        .iter()
        .map(|id| {
            let declaration = ctx.txn.mvars.get_decl(id).unwrap();
            result_head(&declaration.type_).unwrap()
        })
        .collect();
    assert_eq!(heads, [name("Out"), name("Needs")]);
}

#[test]
fn every_native_index_budget_stop_can_retry_without_publishing_partial_order() {
    let env = fixture();
    let original = env.clone();
    let fresh = InstanceRegistry::read(&env).unwrap();
    let mut control = context(&env);
    let before = control.txn.budget.heartbeats_consumed;
    control.instance_search_index(&fresh).unwrap();
    let used = control.txn.budget.heartbeats_consumed - before;
    assert!(used > 1);
    for allowance in 1..used {
        let registry = InstanceRegistry::read(&env).unwrap();
        let mut stopped = context(&env);
        stopped.txn.budget.max_heartbeats = allowance;
        assert!(
            stopped.instance_search_index(&registry).is_err(),
            "allowance {allowance}"
        );
        assert_eq!(stopped.txn.budget.heartbeats_consumed, allowance);
        // A partial publication would make this second one-heartbeat attempt
        // succeed. Unsupported is not a substitute for a budget failure.
        let mut again = context(&env);
        again.txn.budget.max_heartbeats = 1;
        assert!(again.instance_search_index(&registry).is_err());
        assert_eq!(selected(&env, &registry), constant("specific"));
    }
    assert_eq!(env, original);
}
