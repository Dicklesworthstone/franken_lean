use super::*;
use crate::reducibility::{self, Reducibility};
use fln_core::level::Level;
use fln_core::options::KVMap;
use fln_env::constants::{AxiomVal, ConstantVal, DefinitionVal};

fn n(name: &str) -> Name {
    Name::from_components(name.split('.'))
}
fn c(name: &str) -> Expr {
    Expr::const_(n(name), Vec::new())
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
fn pi(name: &str, domain: Expr, body: Expr, binder: BinderInfo) -> Expr {
    Expr::forall_e(n(name), domain, body, binder)
}
fn axiom(env: &Environment, name: &str, type_: Expr) -> Environment {
    env.add_decl(ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_,
        },
        is_unsafe: false,
    }))
    .unwrap()
}
fn definition(env: &Environment, name: &str, type_: Expr, value: Expr) -> Environment {
    env.add_decl(ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_,
        },
        value,
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    }))
    .unwrap()
}
fn fixture() -> Environment {
    let env = axiom(&Environment::new(), "Nat", ty());
    let env = axiom(&env, "Pick", pi("A", ty(), ty(), BinderInfo::Default));
    let env = register_class(&env, &n("Pick")).unwrap();
    let env = definition(&env, "Carrier", ty(), c("Nat"));
    let env = reducibility::register_default(&env, &n("Carrier")).unwrap();
    let target = Expr::app(c("Pick"), c("Carrier"));
    axiom(&axiom(&env, "before", target.clone()), "after", target)
}
fn model(carrier: &str) -> export::DerivedIndex {
    export::DerivedIndex {
        keys: vec![
            discr_tree::Key::Const(n("Pick"), 1),
            discr_tree::Key::Const(n(carrier), 0),
        ],
        synth_order: Vec::new(),
    }
}

#[test]
fn captured_models_preserve_attribute_epochs_search_slots_and_export_work() {
    let initial = fixture();
    let before = register_instance(&initial, &n("before"), 1000).unwrap();
    let first = InstanceRegistry::read(&before).unwrap();
    assert_eq!(
        first.captured_instance_index(&n("before")),
        Some(Some(&model("Carrier")))
    );
    let first_slot = first.candidates(&n("Pick"))[0].order;
    let changed = reducibility::register(&before, &n("Carrier"), Reducibility::Reducible).unwrap();
    let after = register_instance(&changed, &n("after"), 1000).unwrap();
    let after = set_instance(&after, &n("after"), 2000).unwrap();
    let registry = InstanceRegistry::read(&after).unwrap();
    assert_eq!(
        registry.captured_instance_index(&n("before")),
        Some(Some(&model("Carrier")))
    );
    assert_eq!(
        registry.captured_instance_index(&n("after")),
        Some(Some(&model("Nat")))
    );
    assert_eq!(registry.native_instances().count(), 2);
    assert_eq!(registry.candidates(&n("Pick"))[1].order, first_slot);
    let index = registry.instance_index(&after, &mut 1_000_000).unwrap();
    let narrowed = index.narrow(
        &after,
        &crate::lctx::LocalContext::new(),
        &Expr::app(c("Pick"), c("Nat")),
        registry.candidates(&n("Pick")),
    );
    assert_eq!(
        narrowed
            .iter()
            .map(|row| row.declaration.clone())
            .collect::<Vec<_>>(),
        [n("after")]
    );
    let root = after.logical_root(&KVMap::new());
    assert_eq!(
        set_instance(&after, &n("before"), 3000),
        Err(InstanceRegistryError::UnsupportedIndexUpdate(n("before")))
    );
    assert_eq!(after.logical_root(&KVMap::new()), root);
    let (rows, work) = export::registrations(&initial, &after, usize::MAX)
        .unwrap()
        .unwrap();
    assert_eq!(
        rows.instances
            .iter()
            .map(|row| row.keys.clone())
            .collect::<Vec<_>>(),
        [
            model("Carrier").keys,
            model("Nat").keys.clone(),
            model("Nat").keys
        ]
    );
    assert!(work > rows.bytes_examined);
    assert_eq!(
        export::registrations(&initial, &after, work).unwrap(),
        Some((rows, work))
    );
    assert_eq!(
        export::registrations(&initial, &after, work - 1),
        Err(InstanceRegistryError::Limit)
    );
}

#[test]
fn captured_scoped_and_local_overrides_keep_native_identity_and_original_path() {
    let initial = fixture();
    let env = scoped::register(&initial, &n("Feature"), &n("before"), 1000).unwrap();
    let original_slot =
        InstanceRegistry::read(&env).unwrap().scoped[&n("Feature")][&n("Pick")][0].order;
    let env = scoped::register(&env, &n("Feature"), &n("before"), 2000).unwrap();
    let dormant = InstanceRegistry::read(&env).unwrap();
    assert!(dormant.candidates(&n("Pick")).is_empty());
    assert_eq!(
        dormant.scoped[&n("Feature")][&n("Pick")][0].order,
        original_slot
    );
    assert_eq!(
        dormant.native_instances().collect::<Vec<_>>(),
        [&n("before")]
    );
    let mut scopes = scoped::ActiveScopes::default();
    scopes.register_local(&env, &n("before"), 3000).unwrap();
    scopes.activate(&env, &n("Feature")).unwrap();
    let active = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
    assert_eq!(
        active.local_instance_index(&n("before")),
        Some(&model("Carrier"))
    );
    assert_eq!(active.candidates(&n("Pick")).len(), 1);
    let prior = scopes.clone();
    let changed = reducibility::register(&env, &n("Carrier"), Reducibility::Reducible).unwrap();
    assert_eq!(
        scopes.register_local(&changed, &n("before"), 4000),
        Err(InstanceRegistryError::UnsupportedIndexUpdate(n("before")))
    );
    assert_eq!(scopes, prior);
    assert_eq!(
        scoped::register(&changed, &n("Feature"), &n("before"), 4000),
        Err(InstanceRegistryError::UnsupportedIndexUpdate(n("before")))
    );
}

fn unsupported_fixture() -> Environment {
    let function = pi("A", ty(), ty(), BinderInfo::Default);
    let env = axiom(
        &Environment::new(),
        "Higher",
        pi("F", function.clone(), ty(), BinderInfo::Default),
    );
    let env = register_class(&env, &n("Higher")).unwrap();
    let env = definition(
        &env,
        "Identity",
        function,
        Expr::lam(n("A"), ty(), Expr::bvar(0).unwrap(), BinderInfo::Default),
    );
    let env = reducibility::register(&env, &n("Identity"), Reducibility::Reducible).unwrap();
    axiom(&env, "higher", Expr::app(c("Higher"), c("Identity")))
}

#[test]
fn unsupported_captures_are_frozen_for_both_persistent_and_local_registrations() {
    let initial = unsupported_fixture();
    let env = register_instance(&initial, &n("higher"), 1000).unwrap();
    let registry = InstanceRegistry::read(&env).unwrap();
    assert_eq!(registry.captured_instance_index(&n("higher")), Some(None));
    assert_eq!(
        set_instance(&env, &n("higher"), 2000),
        Err(InstanceRegistryError::UnsupportedIndexUpdate(n("higher")))
    );
    let changed = reducibility::register(&env, &n("Identity"), Reducibility::Irreducible).unwrap();
    let registry = InstanceRegistry::read(&changed).unwrap();
    assert!(
        export::derive_registration_index(&changed, &registry, &n("higher"), &mut 1_000_000)
            .unwrap()
            .is_some()
    );
    assert_eq!(registry.captured_instance_index(&n("higher")), Some(None));
    assert_eq!(
        registry
            .instance_index(&changed, &mut 1_000_000)
            .unwrap()
            .native_synth_order(&n("higher")),
        None
    );
    assert_eq!(
        export::registrations(&initial, &changed, 1_000_000).unwrap(),
        None
    );
    let mut scopes = scoped::ActiveScopes::default();
    scopes.register_local(&initial, &n("higher"), 1000).unwrap();
    let original = scopes.clone();
    assert_eq!(
        scopes.register_local(&initial, &n("higher"), 2000),
        Err(InstanceRegistryError::UnsupportedIndexUpdate(n("higher")))
    );
    assert_eq!(scopes, original);
    let changed =
        reducibility::register(&initial, &n("Identity"), Reducibility::Irreducible).unwrap();
    let registry = InstanceRegistry::read_with_scopes(&changed, &scopes).unwrap();
    assert_eq!(registry.local_registration_index(&n("higher")), Some(None));
    assert_eq!(
        registry
            .instance_index(&changed, &mut 1_000_000)
            .unwrap()
            .native_synth_order(&n("higher")),
        None
    );
}

#[test]
fn captured_path_arity_scope_and_prerequisite_mutants_fail_closed() {
    let initial = fixture();
    let env = axiom(&initial, "Need", ty());
    let env = register_class(&env, &n("Need")).unwrap();
    let env = axiom(
        &env,
        "needs",
        pi(
            "h",
            c("Need"),
            Expr::app(c("Pick"), c("Nat")),
            BinderInfo::InstImplicit,
        ),
    );
    let valid = export::DerivedIndex {
        synth_order: vec![0],
        ..model("Nat")
    };
    validate(&env, &n("Pick"), &n("needs"), Some(&valid)).unwrap();
    let root = env.logical_root(&KVMap::new());
    let mut mutants = Vec::new();
    for keys in [
        vec![discr_tree::Key::Const(n("Pick"), 0)],
        vec![discr_tree::Key::Const(n("Need"), 0)],
        vec![discr_tree::Key::Const(n("Pick"), 1)],
        vec![
            discr_tree::Key::Const(n("Pick"), 1),
            discr_tree::Key::Const(n("Missing"), 0),
        ],
        vec![
            discr_tree::Key::Const(n("Pick"), 1),
            discr_tree::Key::FVar(fln_core::expr::FVarId(n("open")), 0),
        ],
    ] {
        mutants.push(export::DerivedIndex {
            keys,
            synth_order: vec![0],
        });
    }
    for synth_order in [vec![], vec![1], vec![0, 0]] {
        mutants.push(export::DerivedIndex {
            synth_order,
            ..model("Nat")
        });
    }
    for mutant in mutants {
        let row = payload(1, &n("Pick"), &n("needs"), 1000, None, Some(&mutant)).unwrap();
        let bad = append(&env, row).unwrap();
        assert_eq!(
            InstanceRegistry::read(&bad),
            Err(InstanceRegistryError::Malformed)
        );
        assert_eq!(
            export::registrations(&env, &bad, 1_000_000),
            Err(InstanceRegistryError::Malformed)
        );
    }
    let good = payload(1, &n("Pick"), &n("needs"), 1000, None, Some(&valid)).unwrap();
    let mut trailing = good.clone();
    trailing.push(0);
    for row in [trailing, good[..good.len() - 1].to_vec()] {
        let bad = append(&env, row).unwrap();
        assert_eq!(
            InstanceRegistry::read(&bad),
            Err(InstanceRegistryError::Malformed)
        );
        assert_eq!(
            export::registrations(&env, &bad, 1_000_000),
            Err(InstanceRegistryError::Malformed)
        );
    }
    assert_eq!(env.logical_root(&KVMap::new()), root);
    let accepted = append(&env, good).unwrap();
    assert_eq!(
        InstanceRegistry::read(&accepted)
            .unwrap()
            .captured_instance_index(&n("needs")),
        Some(Some(&valid))
    );
}

#[test]
fn captured_update_payloads_cannot_change_an_existing_schedule_or_erase_its_model() {
    let env = axiom(&Environment::new(), "Need", ty());
    let env = register_class(&env, &n("Need")).unwrap();
    let env = axiom(
        &env,
        "choice",
        pi(
            "a",
            c("Need"),
            pi("b", c("Need"), c("Need"), BinderInfo::InstImplicit),
            BinderInfo::InstImplicit,
        ),
    );
    let initial = register_instance(&env, &n("choice"), 1000).unwrap();
    let registry = InstanceRegistry::read(&initial).unwrap();
    let mut changed = registry
        .captured_instance_index(&n("choice"))
        .unwrap()
        .unwrap()
        .clone();
    changed.synth_order.reverse();
    for model in [Some(&changed), None] {
        let bad = append(
            &initial,
            payload(2, &n("Need"), &n("choice"), 2000, None, model).unwrap(),
        )
        .unwrap();
        assert_eq!(
            InstanceRegistry::read(&bad),
            Err(InstanceRegistryError::Malformed)
        );
        assert_eq!(
            export::registrations(&initial, &bad, 1_000_000),
            Err(InstanceRegistryError::Malformed)
        );
    }
}

#[test]
fn foreign_activation_stays_identical_and_legacy_rows_remain_conservative() {
    let initial = fixture();
    for scope in [None, Some(n("Foreign"))] {
        let parameters = imported::InstanceParameters {
            priority: 1000,
            scope,
            keys: model("Carrier").keys,
            synth_order: Vec::new(),
        };
        let one = imported::register_instance(&initial, &n("before"), &parameters).unwrap();
        let batch = imported::ImportActivation::new(initial.clone())
            .register_instance(&n("before"), &parameters)
            .unwrap()
            .finish()
            .unwrap();
        assert_eq!(one, batch);
        let registry = InstanceRegistry::read(&one).unwrap();
        assert_eq!(registry.captured_instance_index(&n("before")), None);
        assert_eq!(
            registry.imported_instance_parameters(&n("before")),
            Some(&parameters)
        );
        assert_eq!(registry.native_instances().count(), 0);
    }
    let legacy = append(
        &initial,
        instance_payload(1, &n("Pick"), &n("before"), 1000, None).unwrap(),
    )
    .unwrap();
    assert_eq!(
        InstanceRegistry::read(&legacy)
            .unwrap()
            .captured_instance_index(&n("before")),
        None
    );
    assert_eq!(
        export::registrations(&initial, &legacy, 1_000_000).unwrap(),
        None
    );
    let captured = register_instance(&initial, &n("before"), 1000).unwrap();
    assert!(
        export::registrations(&initial, &captured, 1_000_000)
            .unwrap()
            .is_some()
    );
}
