use super::*;
use fln_core::level::Level;
use fln_core::options::{DataValue, KVMap};
use fln_env::constants::{AxiomVal, ConstantVal};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn c(text: &str) -> Expr {
    Expr::const_(n(text), vec![])
}
fn ty() -> Expr {
    Expr::sort(Level::one())
}
fn b(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}
fn app(name: &str, arg: Expr) -> Expr {
    Expr::app(c(name), arg)
}
fn pi(name: &str, domain: Expr, body: Expr, binder: BinderInfo) -> Expr {
    Expr::forall_e(n(name), domain, body, binder)
}
fn axiom(env: &Environment, name: &str, type_: Expr) -> Environment {
    env.add_decl(ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        is_unsafe: false,
    }))
    .unwrap()
}
fn class(env: &Environment, name: &str, type_: Expr) -> Environment {
    register_class(&axiom(env, name, type_), &n(name)).unwrap()
}
fn register(env: &Environment, name: &str, type_: Expr) -> Environment {
    register_instance(&axiom(env, name, type_), &n(name), 1000).unwrap()
}
fn derive(env: &Environment, name: &str) -> Option<DerivedIndex> {
    derive_index(
        env,
        &InstanceRegistry::read(env).unwrap(),
        &n(name),
        &mut 1_000_000,
    )
    .unwrap()
}

#[test]
fn chronological_owned_updates_preserve_priority_order_and_exact_work_boundary() {
    let empty = Environment::new();
    let base = class(&empty, "Imported", ty());
    let env = class(&base, "Pick", ty());
    let env = register(&register(&env, "zFirst", c("Pick")), "aSecond", c("Pick"));
    let env = set_instance(&env, &n("zFirst"), 2000).unwrap();
    let env = set_instance(&env, &n("zFirst"), 1000).unwrap();
    let root = env.logical_root(&KVMap::new());
    let (rows, work) = registrations(&base, &env, usize::MAX).unwrap().unwrap();
    assert_eq!(
        rows.classes
            .iter()
            .map(|c| c.name.clone())
            .collect::<Vec<_>>(),
        [n("Pick")]
    );
    assert_eq!(
        rows.instances
            .iter()
            .map(|i| (&i.declaration, i.priority))
            .collect::<Vec<_>>(),
        [
            (&n("zFirst"), 1000),
            (&n("aSecond"), 1000),
            (&n("zFirst"), 2000),
            (&n("zFirst"), 1000)
        ]
    );
    assert!(
        rows.instances
            .iter()
            .all(|i| i.keys == [discr_tree::Key::Const(n("Pick"), 0)])
    );
    assert!(rows.bytes_examined > 0);
    assert_eq!(
        registrations(&base, &env, work).unwrap(),
        Some((rows, work))
    );
    assert_eq!(
        registrations(&base, &env, work - 1),
        Err(InstanceRegistryError::Limit)
    );
    assert_eq!(
        registrations(&env, &env, 0).unwrap(),
        Some((Registrations::default(), 0))
    );
    assert_eq!(env.logical_root(&KVMap::new()), root);
}

#[test]
fn generic_paths_and_authoritative_imported_out_parameters_determine_the_schedule() {
    let generic = pi("A", ty(), ty(), BinderInfo::Default);
    let env = class(&Environment::new(), "Pick", ty());
    let env = class(&class(&env, "Need", generic.clone()), "Choose", generic);
    // Deliberately override the syntactic class policy: imported metadata is
    // authoritative, and must not be recomputed from the unchanged telescope.
    let base = imported::register_class(
        &env,
        &n("Choose"),
        &imported::ClassParameters {
            out_params: vec![0],
            out_level_params: vec![],
        },
    )
    .unwrap();
    let instance_type = pi(
        "A",
        ty(),
        pi(
            "need",
            app("Need", b(0)),
            pi(
                "choose",
                app("Choose", b(1)),
                c("Pick"),
                BinderInfo::InstImplicit,
            ),
            BinderInfo::InstImplicit,
        ),
        BinderInfo::Implicit,
    );
    let env = register(&base, "combined", instance_type);
    let derived = derive(&env, "combined").unwrap();
    assert_eq!(derived.synth_order, [2, 1]);
    assert_eq!(derived.keys, [discr_tree::Key::Const(n("Pick"), 0)]);
    let (rows, _) = registrations(&base, &env, 1_000_000).unwrap().unwrap();
    assert_eq!(rows.instances[0].synth_order, [2, 1]);

    let env = register(
        &base,
        "genericNeed",
        pi("A", ty(), app("Need", b(0)), BinderInfo::Default),
    );
    assert_eq!(
        derive(&env, "genericNeed").unwrap().keys,
        [discr_tree::Key::Const(n("Need"), 1), discr_tree::Key::Star]
    );
    let env = register(
        &base,
        "genericChoose",
        pi("A", ty(), app("Choose", b(0)), BinderInfo::Default),
    );
    assert_eq!(
        derive(&env, "genericChoose"),
        None,
        "unassigned output variable is not a valid schedule"
    );
}

#[test]
fn dependent_function_prerequisites_keep_exact_keys_order_and_work_boundary() {
    let base = class(
        &Environment::new(),
        "Need",
        pi("A", ty(), ty(), BinderInfo::Default),
    );
    // {A} {B : A -> Type} [(a : A) -> Need (B a)] : Need ((a : A) -> B a).
    // This is the dependency shape of Pi.instNonempty/Pi.instInhabited.
    let instance_type = pi(
        "A",
        ty(),
        pi(
            "B",
            pi("a", b(0), ty(), BinderInfo::Default),
            pi(
                "family",
                pi(
                    "a",
                    b(1),
                    app("Need", Expr::app(b(1), b(0))),
                    BinderInfo::Default,
                ),
                app(
                    "Need",
                    pi("a", b(2), Expr::app(b(2), b(0)), BinderInfo::Default),
                ),
                BinderInfo::InstImplicit,
            ),
            BinderInfo::Implicit,
        ),
        BinderInfo::Implicit,
    );
    let env = register(&base, "pointwise", instance_type);
    let root = env.logical_root(&KVMap::new());
    let registry = InstanceRegistry::read(&env).unwrap();
    let mut remaining = 100_000;
    let expected = derive_index(&env, &registry, &n("pointwise"), &mut remaining)
        .unwrap()
        .unwrap();
    assert_eq!(expected.synth_order, [2]);
    assert_eq!(
        expected.keys,
        [
            discr_tree::Key::Const(n("Need"), 1),
            discr_tree::Key::Arrow,
            discr_tree::Key::Star,
        ]
    );
    let work = 100_000 - remaining;
    let mut exact = work;
    assert_eq!(
        derive_index(&env, &registry, &n("pointwise"), &mut exact).unwrap(),
        Some(expected.clone())
    );
    assert_eq!(exact, 0);
    assert_eq!(
        derive_index(&env, &registry, &n("pointwise"), &mut (work - 1)),
        Err(InstanceRegistryError::Limit)
    );
    let (rows, _) = registrations(&base, &env, 1_000_000).unwrap().unwrap();
    assert_eq!(rows.instances.len(), 1);
    assert_eq!(rows.instances[0].keys, expected.keys);
    assert_eq!(rows.instances[0].synth_order, expected.synth_order);
    assert_eq!(env.logical_root(&KVMap::new()), root);
}

#[test]
fn higher_order_prerequisites_preserve_output_readiness_and_stall_on_unknown_inputs() {
    let generic = pi("A", ty(), ty(), BinderInfo::Default);
    let dependent = pi(
        "A",
        ty(),
        pi(
            "a",
            b(0),
            pi("B", ty(), ty(), BinderInfo::Default),
            BinderInfo::Default,
        ),
        BinderInfo::Implicit,
    );
    let env = class(&Environment::new(), "Goal", generic.clone());
    let env = class(&env, "Ready", generic);
    let env = class(
        &class(&env, "OutAt", dependent.clone()),
        "NeedAt",
        dependent,
    );
    let base = imported::register_class(
        &env,
        &n("OutAt"),
        &imported::ClassParameters {
            out_params: vec![2],
            out_level_params: vec![],
        },
    )
    .unwrap();
    // {A B} [Ready B] [(a : A) -> OutAt a B] : Goal A.
    // The pin selects the dependent family first, which supplies output B.
    let instance_type = |family: &str| {
        pi(
            "A",
            ty(),
            pi(
                "B",
                ty(),
                pi(
                    "wait",
                    app("Ready", b(0)),
                    pi(
                        "family",
                        pi(
                            "a",
                            b(2),
                            Expr::app(Expr::app(app(family, b(3)), b(0)), b(2)),
                            BinderInfo::Default,
                        ),
                        app("Goal", b(3)),
                        BinderInfo::InstImplicit,
                    ),
                    BinderInfo::InstImplicit,
                ),
                BinderInfo::Implicit,
            ),
            BinderInfo::Implicit,
        )
    };
    let env = register(&base, "scheduled", instance_type("OutAt"));
    let derived = derive(&env, "scheduled").unwrap();
    assert_eq!(derived.synth_order, [3, 2]);
    assert_eq!(
        derived.keys,
        [discr_tree::Key::Const(n("Goal"), 1), discr_tree::Key::Star]
    );
    let (rows, _) = registrations(&base, &env, 1_000_000).unwrap().unwrap();
    assert_eq!(rows.instances[0].synth_order, [3, 2]);

    // Keeping B as an input must still stall: opening a rigid inner binder
    // cannot assign the unresolved outer input or discard its obligation.
    let env = register(&base, "stalled", instance_type("NeedAt"));
    assert_eq!(derive(&env, "stalled"), None);
    assert_eq!(registrations(&base, &env, 1_000_000).unwrap(), None);
}

/// The pin's `checkOutParam` (`Lean/Class.lean`), run by `addClass` on every new class.
#[test]
fn a_regular_parameter_may_not_depend_on_an_out_parameter() {
    let out = |domain| app("outParam", domain);
    let base = axiom(
        &Environment::new(),
        "Inhabited",
        pi("a", ty(), ty(), BinderInfo::Default),
    );
    // F (β : outParam Type) (b : β) : Type is refused, and registers nothing.
    let refused = axiom(
        &base,
        "F",
        pi(
            "β",
            out(ty()),
            pi("b", b(0), ty(), BinderInfo::Default),
            BinderInfo::Default,
        ),
    );
    assert_eq!(
        register_class(&refused, &n("F")),
        Err(InstanceRegistryError::OutParamDependency {
            class: n("F"),
            parameter: 2,
        })
    );
    assert!(!InstanceRegistry::read(&refused).unwrap().is_class(&n("F")));
    // G (β : outParam Type) (b : outParam β), D (β : outParam Type) [Inhabited β] (the
    // instance-implicit exception, pin issue #1852), and E (x : outParam Type) (α : Type), whose
    // α does not mention x, are classes.
    for (name, type_) in [
        (
            "G",
            pi(
                "β",
                out(ty()),
                pi("b", out(b(0)), ty(), BinderInfo::Default),
                BinderInfo::Default,
            ),
        ),
        (
            "D",
            pi(
                "β",
                out(ty()),
                pi("i", app("Inhabited", b(0)), ty(), BinderInfo::InstImplicit),
                BinderInfo::Default,
            ),
        ),
        (
            "E",
            pi(
                "x",
                out(ty()),
                pi("α", ty(), ty(), BinderInfo::Default),
                BinderInfo::Default,
            ),
        ),
    ] {
        let env = class(&base, name, type_);
        assert!(
            InstanceRegistry::read(&env).unwrap().is_class(&n(name)),
            "{name}"
        );
    }
}

#[test]
fn implicit_class_detection_uses_the_original_function_telescope() {
    let env = class(&Environment::new(), "C", ty());
    let env = class(&env, "Holder", pi("A", ty(), ty(), BinderInfo::Default));
    let env = axiom(&env, "h", c("C"));
    // F (A : Type) [x : A] : Type. FunInfo sees fresh A, not the
    // supplied class C; x therefore is NOT an instance argument to wildcard.
    let env = axiom(
        &env,
        "F",
        pi(
            "A",
            ty(),
            pi("x", b(0), ty(), BinderInfo::InstImplicit),
            BinderInfo::Default,
        ),
    );
    let applied = Expr::app(app("F", c("C")), c("h"));
    let env = register(&env, "held", app("Holder", applied));
    assert_eq!(
        derive(&env, "held").unwrap().keys,
        [
            discr_tree::Key::Const(n("Holder"), 1),
            discr_tree::Key::Const(n("F"), 2),
            discr_tree::Key::Const(n("C"), 0),
            discr_tree::Key::Const(n("h"), 0),
        ]
    );
}

#[test]
fn elaborated_numerals_and_successors_have_literal_keys_with_exact_budgeting() {
    use fln_core::expr::{Literal, NatLit};
    let env = axiom(&Environment::new(), "Nat", ty());
    let env = axiom(&env, "Nat.zero", c("Nat"));
    let env = axiom(
        &env,
        "Nat.succ",
        pi("n", c("Nat"), c("Nat"), BinderInfo::Default),
    );
    let env = class(&env, "At", pi("n", c("Nat"), ty(), BinderInfo::Default));
    let env = class(
        &env,
        "OfNat",
        pi(
            "A",
            ty(),
            pi("n", c("Nat"), ty(), BinderInfo::Default),
            BinderInfo::Default,
        ),
    );
    let name = n("OfNat.ofNat");
    let env = env
        .add_decl(ConstantInfo::Defn(fln_env::constants::DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: vec![],
                type_: pi(
                    "A",
                    ty(),
                    pi(
                        "n",
                        c("Nat"),
                        pi(
                            "d",
                            Expr::app(app("OfNat", b(1)), b(0)),
                            b(2),
                            BinderInfo::InstImplicit,
                        ),
                        BinderInfo::Default,
                    ),
                    BinderInfo::Default,
                ),
            },
            value: c("Nat.zero"),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![name],
        }))
        .unwrap();
    let literal = |n| Expr::lit(Literal::Nat(NatLit::from_u64(n)));
    let dictionary = Expr::app(app("OfNat", c("Nat")), literal(7));
    let env = axiom(&env, "dictionary", dictionary);
    let numeral = Expr::app(
        Expr::app(app("OfNat.ofNat", c("Nat")), literal(7)),
        c("dictionary"),
    );
    for (name, term, expected) in [
        ("zero", c("Nat.zero"), NatLit::from_u64(0)),
        ("literal", literal(7), NatLit::from_u64(7)),
        ("elaborated", numeral.clone(), NatLit::from_u64(7)),
        (
            "successor",
            app("Nat.succ", numeral.clone()),
            NatLit::from_u64(8),
        ),
        (
            "wide",
            app("Nat.succ", literal(u64::MAX)),
            NatLit::from_limbs_le(vec![0, 1]),
        ),
    ] {
        let env = register(&env, name, app("At", term));
        let registry = InstanceRegistry::read(&env).unwrap();
        let mut remaining = 100_000;
        let index = derive_index(&env, &registry, &n(name), &mut remaining)
            .unwrap()
            .unwrap();
        assert_eq!(
            index.keys,
            [
                discr_tree::Key::Const(n("At"), 1),
                discr_tree::Key::Lit(Literal::Nat(expected))
            ]
        );
        assert_eq!(
            registry.captured_instance_index(&n(name)),
            Some(Some(&index)),
            "captured numeral {name}; OfNat.ofNat status: {:?}",
            crate::reducibility::known_status(&env, &n("OfNat.ofNat")).unwrap()
        );
        let work = 100_000 - remaining;
        let mut exact = work;
        assert_eq!(
            derive_index(&env, &registry, &n(name), &mut exact).unwrap(),
            Some(index)
        );
        assert_eq!(exact, 0);
        assert_eq!(
            derive_index(&env, &registry, &n(name), &mut (work - 1)),
            Err(InstanceRegistryError::Limit)
        );
    }

    // The literal can become visible only after reducing an alias. A single
    // check before normalization, followed by the old head reducer, still
    // loses this row at the unrecorded OfNat.ofNat projection.
    let alias = n("aliasSeven");
    let env = env
        .add_decl(ConstantInfo::Defn(fln_env::constants::DefinitionVal {
            base: ConstantVal {
                name: alias.clone(),
                level_params: vec![],
                type_: c("Nat"),
            },
            value: Expr::let_e(Name::anonymous(), c("Nat"), numeral, b(0), true),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![alias.clone()],
        }))
        .unwrap();
    let env =
        crate::reducibility::register(&env, &alias, crate::reducibility::Reducibility::Reducible)
            .unwrap();
    let registered = register(&env, "aliased", app("At", c("aliasSeven")));
    let registry = InstanceRegistry::read(&registered).unwrap();
    let expected = DerivedIndex {
        keys: vec![
            discr_tree::Key::Const(n("At"), 1),
            discr_tree::Key::Lit(Literal::Nat(NatLit::from_u64(7))),
        ],
        synth_order: vec![],
    };
    assert_eq!(
        registry.captured_instance_index(&n("aliased")),
        Some(Some(&expected))
    );
    let mut remaining = 100_000;
    assert_eq!(
        derive_registration_index(&registered, &registry, &n("aliased"), &mut remaining).unwrap(),
        Some(expected.clone())
    );
    let work = 100_000 - remaining;
    let mut exact = work;
    assert_eq!(
        derive_registration_index(&registered, &registry, &n("aliased"), &mut exact).unwrap(),
        Some(expected)
    );
    assert_eq!(exact, 0);
    assert_eq!(
        derive_registration_index(&registered, &registry, &n("aliased"), &mut (work - 1)),
        Err(InstanceRegistryError::Limit)
    );
    assert_eq!(derive(&registered, "aliased"), None);
}

#[test]
fn unsupported_effects_impossible_binders_and_annotations_publish_no_prefix() {
    let empty = Environment::new();
    let base = class(&empty, "Box", pi("A", ty(), ty(), BinderInfo::Default));
    let impossible = pi(
        "A",
        ty(),
        pi("a", b(0), app("Box", b(1)), BinderInfo::Default),
        BinderInfo::Default,
    );
    let env = register(&base, "bad", impossible);
    assert_eq!(derive(&env, "bad"), None);
    assert_eq!(registrations(&base, &env, 1_000_000).unwrap(), None);

    let base = class(&empty, "Pick", ty());
    let env = axiom(&base, "scoped", c("Pick"));
    let scoped = scoped::register(&env, &n("Scope"), &n("scoped"), 1000).unwrap();
    let (rows, _) = registrations(&base, &scoped, 1_000_000).unwrap().unwrap();
    assert_eq!(rows.instances.len(), 1);
    assert_eq!(rows.instances[0].declaration, n("scoped"));
    assert_eq!(rows.instances[0].scope, Some(n("Scope")));
    assert_eq!(rows.instances[0].priority, 1000);
    assert_eq!(
        rows.instances[0].keys,
        [discr_tree::Key::Const(n("Pick"), 0)]
    );
    assert!(
        InstanceRegistry::read(&scoped)
            .unwrap()
            .candidates(&n("Pick"))
            .is_empty()
    );
    let imported = register(&base, "already", c("Pick"));
    let updated = set_instance(&imported, &n("already"), 2000).unwrap();
    let (rows, _) = registrations(&imported, &updated, 1_000_000)
        .unwrap()
        .unwrap();
    assert_eq!(rows.instances.len(), 1);
    assert_eq!(rows.instances[0].declaration, n("already"));
    assert_eq!(rows.instances[0].priority, 2000);

    let data = KVMap::from_entries(vec![(n("noindex"), DataValue::OfBool(true))]);
    let annotated = register(&base, "annotated", Expr::mdata(data, c("Pick")));
    assert_eq!(derive(&annotated, "annotated"), None);
}

#[test]
fn scoped_exports_preserve_namespaces_priorities_and_the_owned_suffix() {
    let base = class(&Environment::new(), "Pick", ty());
    let env = axiom(&base, "Scope.first", c("Pick"));
    let env = scoped::register(&env, &n("Scope"), &n("Scope.first"), 500).unwrap();
    let env = axiom(&env, "Other.second", c("Pick"));
    let env = scoped::register(&env, &n("Other"), &n("Other.second"), 2000).unwrap();
    let env = scoped::register(&env, &n("Scope"), &n("Scope.first"), 1000).unwrap();
    let (rows, work) = registrations(&base, &env, usize::MAX).unwrap().unwrap();
    assert_eq!(
        rows.instances
            .iter()
            .map(|row| (row.declaration.clone(), row.scope.clone(), row.priority))
            .collect::<Vec<_>>(),
        [
            (n("Scope.first"), Some(n("Scope")), 500),
            (n("Other.second"), Some(n("Other")), 2000),
            (n("Scope.first"), Some(n("Scope")), 1000),
        ]
    );
    assert!(rows.instances.iter().all(|row| {
        row.keys == [discr_tree::Key::Const(n("Pick"), 0)] && row.synth_order.is_empty()
    }));
    assert_eq!(
        registrations(&base, &env, work).unwrap(),
        Some((rows, work))
    );
    assert_eq!(
        registrations(&base, &env, work - 1),
        Err(InstanceRegistryError::Limit)
    );
    // An imported scoped entry stays inherited; only this module's new
    // registration or priority update is emitted.
    let extended = register(&env, "global", c("Pick"));
    let (rows, _) = registrations(&env, &extended, usize::MAX).unwrap().unwrap();
    assert_eq!(rows.instances.len(), 1);
    assert_eq!(rows.instances[0].declaration, n("global"));
    assert_eq!(rows.instances[0].scope, None);
    let overridden = scoped::register(&env, &n("Scope"), &n("Scope.first"), 3000).unwrap();
    let (rows, _) = registrations(&env, &overridden, usize::MAX)
        .unwrap()
        .unwrap();
    assert_eq!(rows.instances.len(), 1);
    assert_eq!(rows.instances[0].declaration, n("Scope.first"));
    assert_eq!(rows.instances[0].scope, Some(n("Scope")));
    assert_eq!(rows.instances[0].priority, 3000);
}

#[test]
fn rewritten_prefix_and_zero_budget_are_typed_refusals_and_do_not_mutate_the_input() {
    let base = class(&Environment::new(), "Pick", ty());
    let env = register(&base, "local", c("Pick"));
    let root = env.logical_root(&KVMap::new());
    let registry = InstanceRegistry::read(&env).unwrap();
    assert_eq!(
        derive_index(&env, &registry, &n("local"), &mut 0),
        Err(InstanceRegistryError::Limit)
    );
    let changed = set_instance(&env, &n("local"), 5).unwrap();
    let different = set_instance(&env, &n("local"), 7).unwrap();
    assert_eq!(
        registrations(&changed, &different, 1_000_000),
        Err(InstanceRegistryError::Malformed)
    );
    let lost = Environment::new();
    assert_eq!(
        registrations(&base, &lost, 1_000_000),
        Err(InstanceRegistryError::Malformed)
    );
    assert_eq!(env.logical_root(&KVMap::new()), root);
}

#[test]
fn unbound_projection_lookalikes_do_not_gain_the_pins_special_synthesis_order() {
    let env = class(&class(&Environment::new(), "Parent", ty()), "Child", ty());
    let name = n("Child.toParent");
    let env = env
        .add_decl(ConstantInfo::Defn(fln_env::constants::DefinitionVal {
            base: ConstantVal {
                name: name.clone(),
                level_params: vec![],
                type_: pi("self", c("Child"), c("Parent"), BinderInfo::InstImplicit),
            },
            value: Expr::lam(
                n("self"),
                c("Child"),
                Expr::proj(n("Child"), 0, b(0)),
                BinderInfo::InstImplicit,
            ),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name.clone()],
        }))
        .unwrap();
    let env = register_instance(&env, &name, 1000).unwrap();
    assert_eq!(derive(&env, "Child.toParent"), None);
}

#[test]
fn a_later_class_registration_cannot_rewrite_an_earlier_exported_key() {
    let empty = Environment::new();
    let env = axiom(&empty, "D", ty());
    let env = axiom(&env, "h", c("D"));
    let env = class(&env, "C", pi("x", c("D"), ty(), BinderInfo::Implicit));
    let env = register(&env, "earlier", app("C", c("h")));
    // Before D is a class, the implicit non-type h is already ignored, so
    // this particular policy change is harmless and remains exportable.
    let env = register_class(&env, &n("D")).unwrap();
    assert!(registrations(&empty, &env, 1_000_000).unwrap().is_some());

    // An instance-implicit (rather than ordinary implicit) parameter first
    // follows isProof(h); only after tagging D does FunInfo wildcard it.
    let env = axiom(&empty, "D", ty());
    let env = axiom(&env, "h", c("D"));
    let env = class(&env, "C", pi("x", c("D"), ty(), BinderInfo::InstImplicit));
    let declared = axiom(&env, "earlier", app("C", c("h")));
    let env = register_instance(&declared, &n("earlier"), 1000).unwrap();
    let original = derive(&env, "earlier").unwrap();
    assert_eq!(
        original.keys,
        [
            discr_tree::Key::Const(n("C"), 1),
            discr_tree::Key::Const(n("h"), 0),
        ]
    );
    let changed = register_class(&env, &n("D")).unwrap();
    let (rows, _) = registrations(&empty, &changed, 1_000_000).unwrap().unwrap();
    assert_eq!(rows.instances[0].keys, original.keys);
    assert_eq!(rows.instances[0].synth_order, original.synth_order);
    assert_ne!(derive(&changed, "earlier").unwrap().keys, original.keys);
    assert_eq!(
        set_instance(&changed, &n("earlier"), 2000),
        Err(InstanceRegistryError::UnsupportedIndexUpdate(n("earlier")))
    );

    // Old rows have no registration snapshot. Their original conservative
    // export gate remains: a changed class policy cannot be guessed away.
    let legacy = append(
        &declared,
        instance_payload(1, &n("C"), &n("earlier"), 1000, None).unwrap(),
    )
    .unwrap();
    let legacy = register_class(&legacy, &n("D")).unwrap();
    assert_eq!(registrations(&empty, &legacy, 1_000_000).unwrap(), None);
}

#[test]
fn scoped_export_preserves_registration_history_and_exact_budget_boundaries() {
    let base = class(&Environment::new(), "Pick", ty());
    let env = axiom(&axiom(&base, "zFirst", c("Pick")), "aSecond", c("Pick"));
    let env = scoped::register(&env, &n("Feature.Inner"), &n("zFirst"), 1000).unwrap();
    let env = scoped::register(&env, &n("Other"), &n("aSecond"), 2000).unwrap();
    let env = scoped::register(&env, &n("Feature.Inner"), &n("zFirst"), 3000).unwrap();
    let root = env.logical_root(&KVMap::new());
    let (rows, work) = registrations(&base, &env, usize::MAX).unwrap().unwrap();
    assert!(rows.classes.is_empty());
    assert_eq!(
        rows.instances
            .iter()
            .map(|row| (row.declaration.clone(), row.scope.clone(), row.priority))
            .collect::<Vec<_>>(),
        [
            (n("zFirst"), Some(n("Feature.Inner")), 1000),
            (n("aSecond"), Some(n("Other")), 2000),
            (n("zFirst"), Some(n("Feature.Inner")), 3000),
        ]
    );
    for row in &rows.instances {
        assert_eq!(row.keys, [discr_tree::Key::Const(n("Pick"), 0)]);
        assert!(row.synth_order.is_empty());
    }
    for cutoff in 0..work {
        assert_eq!(
            registrations(&base, &env, cutoff),
            Err(InstanceRegistryError::Limit)
        );
    }
    assert_eq!(
        registrations(&base, &env, work).unwrap(),
        Some((rows, work))
    );
    assert_eq!(env.logical_root(&KVMap::new()), root);
}

#[test]
fn scoped_export_accepts_imported_updates_without_changing_registration_scope() {
    let base = class(&Environment::new(), "Pick", ty());
    let declarations = axiom(&base, "candidate", c("Pick"));
    let scoped = scoped::register(&declarations, &n("First"), &n("candidate"), 1000).unwrap();
    let update = scoped::register(&scoped, &n("First"), &n("candidate"), 2000).unwrap();
    let (rows, _) = registrations(&scoped, &update, 1_000_000).unwrap().unwrap();
    assert_eq!(rows.instances.len(), 1);
    assert_eq!(rows.instances[0].priority, 2000);
    let (rows, _) = registrations(&declarations, &scoped, 1_000_000)
        .unwrap()
        .unwrap();
    assert_eq!(rows.instances.len(), 1);
    assert_eq!(rows.instances[0].scope, Some(n("First")));
    for namespace in ["Second", "First.Inner"] {
        assert!(scoped::register(&scoped, &n(namespace), &n("candidate"), 1000).is_err());
    }
    assert!(set_instance(&scoped, &n("candidate"), 1000).is_err());
}

#[test]
fn imported_priority_exports_require_the_live_index_and_prerequisite_schedule() {
    let base = class(&class(&Environment::new(), "Need", ty()), "Pick", ty());
    let base = axiom(
        &base,
        "candidate",
        pi(
            "first",
            c("Need"),
            pi("second", c("Need"), c("Pick"), BinderInfo::InstImplicit),
            BinderInfo::InstImplicit,
        ),
    );
    let model = derive(&base, "candidate").unwrap();
    assert_eq!(model.synth_order.len(), 2);
    for changed in 0..3 {
        let mut parameters = imported::InstanceParameters {
            priority: 1000,
            synth_order: model.synth_order.clone(),
            scope: None,
            keys: model.keys.clone(),
        };
        match changed {
            1 => parameters.keys = vec![discr_tree::Key::Star],
            2 => parameters.synth_order.reverse(),
            _ => {}
        }
        let imported = imported::register_instance(&base, &n("candidate"), &parameters).unwrap();
        let root = imported.logical_root(&KVMap::new());
        let update = set_instance(&imported, &n("candidate"), 2000);
        if changed == 0 {
            let updated = update.unwrap();
            let result = registrations(&imported, &updated, usize::MAX).unwrap();
            let (rows, work) = result.unwrap();
            assert!(rows.classes.is_empty());
            assert_eq!(rows.instances.len(), 1);
            assert_eq!(rows.instances[0].keys, model.keys);
            assert_eq!(rows.instances[0].synth_order, model.synth_order);
            assert_eq!(rows.instances[0].priority, 2000);
            assert!(rows.bytes_examined > 0);
            for allowance in [0, work - 1] {
                assert_eq!(
                    registrations(&imported, &updated, allowance),
                    Err(InstanceRegistryError::Limit)
                );
            }
            assert_eq!(
                registrations(&imported, &updated, work).unwrap(),
                Some((rows, work))
            );
        } else {
            assert_eq!(
                update,
                Err(InstanceRegistryError::UnsupportedIndexUpdate(n(
                    "candidate"
                ))),
                "a source priority change must not replace a physical import's model"
            );
        }
        assert_eq!(imported.logical_root(&KVMap::new()), root);
    }
}

fn local_alias_fixture() -> Environment {
    use fln_env::constants::DefinitionVal;
    let env = axiom(&Environment::new(), "Nat", ty());
    let mut env = class(&env, "Pick", pi("A", ty(), ty(), BinderInfo::Default));
    let level = Level::param(n("u"));
    for (name, parameters, type_, value) in [
        ("NatAlias", vec![], ty(), c("Nat")),
        (
            "AppliedAlias",
            vec![n("u")],
            pi(
                "A",
                Expr::sort(level.clone()),
                Expr::sort(level.clone()),
                BinderInfo::Default,
            ),
            Expr::lam(n("A"), Expr::sort(level.clone()), b(0), BinderInfo::Default),
        ),
    ] {
        env = env
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: n(name),
                    level_params: parameters,
                    type_,
                },
                value,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![n(name)],
            }))
            .unwrap();
        env = crate::reducibility::register(
            &env,
            &n(name),
            crate::reducibility::Reducibility::Reducible,
        )
        .unwrap();
    }
    axiom(
        &env,
        "aliasChoice",
        app(
            "Pick",
            Expr::app(
                Expr::const_(n("AppliedAlias"), vec![Level::one()]),
                c("NatAlias"),
            ),
        ),
    )
}

fn registration_model(env: &Environment, declaration: &str) -> Option<DerivedIndex> {
    derive_registration_index(
        env,
        &InstanceRegistry::read(env).unwrap(),
        &n(declaration),
        &mut 1_000_000,
    )
    .unwrap()
}

#[test]
fn registration_keys_retain_the_actual_definition_transparency_epoch() {
    use crate::reducibility::{self, Reducibility};
    use fln_env::constants::DefinitionVal;
    let empty = Environment::new();
    let env = axiom(&empty, "Nat", ty());
    let env = class(&env, "Pick", pi("A", ty(), ty(), BinderInfo::Default));
    let env = env
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("Carrier"),
                level_params: vec![],
                type_: ty(),
            },
            value: c("Nat"),
            hints: ReducibilityHints::Regular(1),
            safety: DefinitionSafety::Safe,
            all: vec![n("Carrier")],
        }))
        .unwrap();
    let env = axiom(&env, "before", app("Pick", c("Carrier")));
    assert_eq!(registration_model(&env, "before"), None);
    let env = reducibility::register_default(&env, &n("Carrier")).unwrap();
    let folded = registration_model(&env, "before").unwrap();
    assert_eq!(
        folded.keys,
        [
            discr_tree::Key::Const(n("Pick"), 1),
            discr_tree::Key::Const(n("Carrier"), 0),
        ]
    );
    assert!(folded.synth_order.is_empty());
    assert_eq!(
        derive(&env, "before"),
        None,
        "legacy derivation stays conservative"
    );
    let env = register_instance(&env, &n("before"), 1000).unwrap();
    let changed = reducibility::register(&env, &n("Carrier"), Reducibility::Reducible).unwrap();
    let unfolded = registration_model(&changed, "before").unwrap();
    assert_eq!(
        unfolded.keys,
        [
            discr_tree::Key::Const(n("Pick"), 1),
            discr_tree::Key::Const(n("Nat"), 0),
        ]
    );
    // The later source epoch captures a different leaf. The original row
    // retains its old folded leaf, exactly as the pinned discrimination tree.
    let changed = register(&changed, "after", app("Pick", c("Carrier")));
    let (rows, _) = registrations(&empty, &changed, 1_000_000).unwrap().unwrap();
    assert_eq!(rows.instances.len(), 2);
    assert_eq!(rows.instances[0].keys, folded.keys);
    assert_eq!(rows.instances[1].keys, unfolded.keys);
    assert_eq!(
        set_instance(&changed, &n("before"), 2000),
        Err(InstanceRegistryError::UnsupportedIndexUpdate(n("before")))
    );
    for status in [Reducibility::Irreducible, Reducibility::ImplicitReducible] {
        let view = reducibility::register(&env, &n("Carrier"), status).unwrap();
        assert_eq!(registration_model(&view, "before").unwrap(), folded);
    }
    // Smart unfolding needs its own exact computation; it is never guessed.
    let smart = axiom(&changed, "Carrier._sunfold", ty());
    assert_eq!(registration_model(&smart, "before"), None);
}

#[test]
fn registration_reduces_decidable_equality_telescope_and_prerequisite_aliases() {
    use fln_env::constants::DefinitionVal;
    let env = axiom(&Environment::new(), "Bool", ty());
    let env = axiom(
        &env,
        "Eq",
        pi(
            "A",
            ty(),
            pi(
                "a",
                b(0),
                pi("b", b(1), Expr::sort(Level::zero()), BinderInfo::Default),
                BinderInfo::Default,
            ),
            BinderInfo::Implicit,
        ),
    );
    let env = class(
        &env,
        "Decidable",
        pi("p", Expr::sort(Level::zero()), ty(), BinderInfo::Default),
    );
    let env = class(&env, "BEq", pi("A", ty(), ty(), BinderInfo::Default));
    let equality = Expr::app(Expr::app(app("Eq", b(2)), b(1)), b(0));
    let env = env
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("DecisionEq"),
                level_params: vec![],
                type_: pi("A", ty(), ty(), BinderInfo::Default),
            },
            value: Expr::lam(
                n("A"),
                ty(),
                pi(
                    "a",
                    b(0),
                    pi("b", b(1), app("Decidable", equality), BinderInfo::Default),
                    BinderInfo::Default,
                ),
                BinderInfo::Default,
            ),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![n("DecisionEq")],
        }))
        .unwrap();
    let env = crate::reducibility::register(
        &env,
        &n("DecisionEq"),
        crate::reducibility::Reducibility::Reducible,
    )
    .unwrap();
    let env = axiom(&env, "boolDecision", app("DecisionEq", c("Bool")));
    let env = axiom(
        &env,
        "fromDecision",
        pi(
            "A",
            ty(),
            pi(
                "dictionary",
                app("DecisionEq", b(0)),
                app("BEq", b(1)),
                BinderInfo::InstImplicit,
            ),
            BinderInfo::Implicit,
        ),
    );
    let direct = registration_model(&env, "boolDecision").unwrap();
    assert_eq!(
        direct.keys,
        [
            discr_tree::Key::Const(n("Decidable"), 1),
            discr_tree::Key::Const(n("Eq"), 3),
            discr_tree::Key::Const(n("Bool"), 0),
            discr_tree::Key::Star,
            discr_tree::Key::Star,
        ]
    );
    assert!(direct.synth_order.is_empty());
    let dependent = registration_model(&env, "fromDecision").unwrap();
    assert_eq!(dependent.synth_order, [1]);
    assert_eq!(
        dependent.keys,
        [discr_tree::Key::Const(n("BEq"), 1), discr_tree::Key::Star]
    );
    assert_eq!(derive(&env, "boolDecision"), None);
    assert_eq!(derive(&env, "fromDecision"), None);
    let opaque = crate::reducibility::register(
        &env,
        &n("DecisionEq"),
        crate::reducibility::Reducibility::Irreducible,
    )
    .unwrap();
    assert_eq!(registration_model(&opaque, "boolDecision"), None);
    assert_eq!(registration_model(&opaque, "fromDecision"), None);
}

#[test]
fn registration_delta_beta_instantiates_levels_and_keeps_exact_fuel_limits() {
    let env = local_alias_fixture();
    let root = env.logical_root(&KVMap::new());
    let registry = InstanceRegistry::read(&env).unwrap();
    let mut remaining = 1_000_000;
    let model = derive_registration_index(&env, &registry, &n("aliasChoice"), &mut remaining)
        .unwrap()
        .unwrap();
    assert_eq!(
        model.keys,
        [
            discr_tree::Key::Const(n("Pick"), 1),
            discr_tree::Key::Const(n("Nat"), 0)
        ]
    );
    let work = 1_000_000 - remaining;
    let mut exact = work;
    assert_eq!(
        derive_registration_index(&env, &registry, &n("aliasChoice"), &mut exact).unwrap(),
        Some(model)
    );
    assert_eq!(exact, 0);
    assert_eq!(
        derive_registration_index(&env, &registry, &n("aliasChoice"), &mut (work - 1)),
        Err(InstanceRegistryError::Limit)
    );
    let malformed = axiom(
        &env,
        "wrongLevels",
        app("Pick", Expr::app(c("AppliedAlias"), c("Nat"))),
    );
    assert_eq!(registration_model(&malformed, "wrongLevels"), None);
    assert_eq!(env.logical_root(&KVMap::new()), root);
}

#[test]
fn borrowed_registration_types_and_aliases_preserve_exact_paths_and_work_limits() {
    use fln_env::constants::DefinitionVal;
    let borrowed = |expr| {
        Expr::mdata(
            KVMap::from_entries(vec![(n("borrowed"), DataValue::OfBool(true))]),
            expr,
        )
    };
    let env = axiom(&Environment::new(), "Nat", ty());
    let env = class(&env, "Rel", pi("A", ty(), ty(), BinderInfo::Default));
    let env = class(
        &env,
        "Decision",
        pi("p", Expr::sort(Level::zero()), ty(), BinderInfo::Default),
    );
    let env = axiom(
        &env,
        "Rel.rel",
        pi(
            "A",
            ty(),
            pi(
                "dictionary",
                app("Rel", b(0)),
                pi(
                    "n",
                    b(1),
                    pi("m", b(2), Expr::sort(Level::zero()), BinderInfo::Default),
                    BinderInfo::Default,
                ),
                BinderInfo::InstImplicit,
            ),
            BinderInfo::Implicit,
        ),
    );
    let env = axiom(&env, "relation", app("Rel", c("Nat")));
    let env = env
        .add_decl(ConstantInfo::Defn(DefinitionVal {
            base: ConstantVal {
                name: n("BorrowedNat"),
                level_params: vec![],
                type_: ty(),
            },
            value: borrowed(c("Nat")),
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![n("BorrowedNat")],
        }))
        .unwrap();
    let env = crate::reducibility::register(
        &env,
        &n("BorrowedNat"),
        crate::reducibility::Reducibility::Reducible,
    )
    .unwrap();
    let domain = borrowed(c("BorrowedNat"));
    let predicate = [domain.clone(), c("relation"), b(1), b(0)]
        .into_iter()
        .fold(c("Rel.rel"), Expr::app);
    let type_ = borrowed(pi(
        "n",
        domain.clone(),
        pi("m", domain, app("Decision", predicate), BinderInfo::Default),
        BinderInfo::Default,
    ));
    let root = env.logical_root(&KVMap::new());
    let registered = register(&env, "borrowedDecision", type_.clone());
    let registry = InstanceRegistry::read(&registered).unwrap();
    let mut remaining = 1_000_000;
    let model = derive_registration_index(
        &registered,
        &registry,
        &n("borrowedDecision"),
        &mut remaining,
    )
    .unwrap()
    .unwrap();
    // The pin's Nat.decLe/Nat.decLt shape: the type argument remains
    // concrete, the dictionary and both telescope variables are wildcards.
    assert_eq!(
        model.keys,
        [
            discr_tree::Key::Const(n("Decision"), 1),
            discr_tree::Key::Const(n("Rel.rel"), 4),
            discr_tree::Key::Const(n("Nat"), 0),
            discr_tree::Key::Star,
            discr_tree::Key::Star,
            discr_tree::Key::Star,
        ]
    );
    assert!(model.synth_order.is_empty());
    let work = 1_000_000 - remaining;
    let mut exact = work;
    assert_eq!(
        derive_registration_index(&registered, &registry, &n("borrowedDecision"), &mut exact)
            .unwrap(),
        Some(model.clone())
    );
    assert_eq!(exact, 0);
    assert_eq!(
        derive_registration_index(
            &registered,
            &registry,
            &n("borrowedDecision"),
            &mut (work - 1),
        ),
        Err(InstanceRegistryError::Limit)
    );
    let (rows, _) = registrations(&env, &registered, 1_000_000)
        .unwrap()
        .unwrap();
    assert_eq!(rows.instances.len(), 1);
    assert_eq!(rows.instances[0].keys, model.keys);
    assert_eq!(rows.instances[0].synth_order, model.synth_order);
    assert_eq!(derive(&registered, "borrowedDecision"), None);
    assert_eq!(
        registered
            .find(&n("borrowedDecision"))
            .unwrap()
            .constant_val()
            .type_,
        type_,
        "index normalization must not erase the compiler's annotations"
    );
    assert_eq!(env.logical_root(&KVMap::new()), root);
}

#[test]
fn noncanonical_and_index_changing_annotations_remain_unsupported() {
    let env = local_alias_fixture();
    let root = env.logical_root(&KVMap::new());
    for entries in [
        vec![(n("borrowed"), DataValue::OfBool(false))],
        vec![(n("borrowed"), DataValue::OfNat(1))],
        vec![(n("noindex"), DataValue::OfBool(true))],
        vec![(n("unknown"), DataValue::OfBool(true))],
        vec![
            (n("borrowed"), DataValue::OfBool(true)),
            (n("noindex"), DataValue::OfBool(true)),
        ],
        vec![
            (n("borrowed"), DataValue::OfBool(true)),
            (n("borrowed"), DataValue::OfBool(true)),
        ],
    ] {
        let inner = Expr::mdata(KVMap::from_entries(entries), c("Nat"));
        // A supported outer annotation cannot hide an unsupported inner map.
        let annotated = Expr::mdata(
            KVMap::from_entries(vec![(n("borrowed"), DataValue::OfBool(true))]),
            inner,
        );
        let registered = register(&env, "annotated", app("Pick", annotated));
        assert_eq!(registration_model(&registered, "annotated"), None);
        assert_eq!(registrations(&env, &registered, 1_000_000).unwrap(), None);
    }
    assert_eq!(env.logical_root(&KVMap::new()), root);
}

#[test]
fn local_registration_normalizes_aliases_with_universes_and_exact_work_limits() {
    let env = local_alias_fixture();
    let root = env.logical_root(&KVMap::new());
    let registry = InstanceRegistry::read(&env).unwrap();
    let mut remaining = 1_000_000;
    let index = derive_local_index(&env, &registry, &n("aliasChoice"), &mut remaining)
        .unwrap()
        .unwrap();
    assert_eq!(
        index.keys,
        [
            discr_tree::Key::Const(n("Pick"), 1),
            discr_tree::Key::Const(n("Nat"), 0)
        ]
    );
    assert!(index.synth_order.is_empty());
    assert_eq!(
        derive(&env, "aliasChoice"),
        None,
        "export remains immutable"
    );
    let work = 1_000_000 - remaining;
    let mut exact = work;
    assert_eq!(
        derive_local_index(&env, &registry, &n("aliasChoice"), &mut exact).unwrap(),
        Some(index)
    );
    assert_eq!(exact, 0);
    assert_eq!(
        derive_local_index(&env, &registry, &n("aliasChoice"), &mut (work - 1)),
        Err(InstanceRegistryError::Limit)
    );
    assert_eq!(env.logical_root(&KVMap::new()), root);
}

#[test]
fn local_alias_keys_stay_frozen_when_reducibility_changes() {
    let env = local_alias_fixture();
    let mut scopes = scoped::ActiveScopes::default();
    scopes
        .register_local(&env, &n("aliasChoice"), 1000)
        .unwrap();
    let original = scopes.clone();
    let changed = crate::reducibility::register(
        &env,
        &n("NatAlias"),
        crate::reducibility::Reducibility::Irreducible,
    )
    .unwrap();
    let registry = InstanceRegistry::read_with_scopes(&changed, &scopes).unwrap();
    let index = registry.instance_index(&changed, &mut 1_000_000).unwrap();
    let rows = registry.candidates(&n("Pick"));
    assert_eq!(rows.len(), 1);
    // The pin's old C/Nat path cannot match a now-irreducible C/Alias goal.
    // Re-deriving None and falling back to an unfiltered row would accept it.
    assert!(
        index
            .narrow(
                &changed,
                &crate::lctx::LocalContext::new(),
                &app("Pick", c("NatAlias")),
                rows,
            )
            .is_empty()
    );
    assert_eq!(
        scopes.register_local(&changed, &n("aliasChoice"), 2000),
        Err(InstanceRegistryError::UnsupportedIndexUpdate(n(
            "aliasChoice"
        )))
    );
    assert_eq!(scopes, original, "failed re-registration is atomic");
    assert!(
        InstanceRegistry::read(&changed)
            .unwrap()
            .candidates(&n("Pick"))
            .is_empty()
    );
}

#[test]
fn local_reregistration_preserves_imported_paths_or_refuses_atomically() {
    let env = local_alias_fixture();
    for keys in [
        vec![],
        vec![
            discr_tree::Key::Const(n("Pick"), 1),
            discr_tree::Key::Const(n("NatAlias"), 0),
        ],
        vec![
            discr_tree::Key::Const(n("Pick"), 1),
            discr_tree::Key::Const(n("Nat"), 0),
        ],
    ] {
        let same = keys.last() == Some(&discr_tree::Key::Const(n("Nat"), 0));
        let imported = imported::register_instance(
            &env,
            &n("aliasChoice"),
            &imported::InstanceParameters {
                priority: 1000,
                synth_order: vec![],
                scope: None,
                keys,
            },
        )
        .unwrap();
        let root = imported.logical_root(&KVMap::new());
        let mut scopes = scoped::ActiveScopes::default();
        let original = scopes.clone();
        let result = scopes.register_local(&imported, &n("aliasChoice"), 2000);
        if same {
            result.unwrap();
            let selected = InstanceRegistry::read_with_scopes(&imported, &scopes).unwrap();
            assert_eq!(selected.candidates(&n("Pick"))[0].priority, 2000);
        } else {
            assert_eq!(
                result,
                Err(InstanceRegistryError::UnsupportedIndexUpdate(n(
                    "aliasChoice"
                )))
            );
            assert_eq!(scopes, original);
        }
        assert_eq!(imported.logical_root(&KVMap::new()), root);
    }
}

#[test]
fn local_alias_override_keeps_imported_index_when_namespace_opens() {
    let env = imported::register_instance(
        &local_alias_fixture(),
        &n("aliasChoice"),
        &imported::InstanceParameters {
            priority: 1000,
            synth_order: vec![],
            scope: Some(n("N")),
            keys: vec![
                discr_tree::Key::Const(n("Pick"), 1),
                discr_tree::Key::Const(n("Nat"), 0),
            ],
        },
    )
    .unwrap();
    assert_eq!(derive(&env, "aliasChoice"), None);
    let mut scopes = scoped::ActiveScopes::default();
    scopes
        .register_local(&env, &n("aliasChoice"), 2000)
        .unwrap();
    let before_open = scopes.clone();
    let local = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
    assert_eq!(local.candidates(&n("Pick"))[0].priority, 2000);
    let captured = local.local_instance_index(&n("aliasChoice")).unwrap();

    // Opening the namespace replays its saved imported entry. It changes the
    // priority without re-deriving or discarding the normalized alias path.
    scopes.activate(&env, &n("N")).unwrap();
    let opened = InstanceRegistry::read_with_scopes(&env, &scopes).unwrap();
    assert_eq!(opened.candidates(&n("Pick")).len(), 1);
    assert_eq!(opened.candidates(&n("Pick"))[0].priority, 1000);
    assert_eq!(
        opened.local_instance_index(&n("aliasChoice")),
        Some(captured)
    );
    assert_eq!(
        InstanceRegistry::read_with_scopes(&env, &before_open)
            .unwrap()
            .candidates(&n("Pick"))[0]
            .priority,
        2000,
        "restoring the lexical snapshot restores the local priority"
    );
    assert!(
        InstanceRegistry::read(&env)
            .unwrap()
            .candidates(&n("Pick"))
            .is_empty()
    );
}
