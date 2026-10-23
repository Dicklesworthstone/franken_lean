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
        ("successor", app("Nat.succ", numeral), NatLit::from_u64(8)),
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
    assert_eq!(registrations(&imported, &updated, 1_000_000).unwrap(), None);

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
    // An imported scoped entry stays inherited; only the new module's entry is
    // emitted, and re-registering an imported declaration remains unsupported.
    let extended = register(&env, "global", c("Pick"));
    let (rows, _) = registrations(&env, &extended, usize::MAX).unwrap().unwrap();
    assert_eq!(rows.instances.len(), 1);
    assert_eq!(rows.instances[0].declaration, n("global"));
    assert_eq!(rows.instances[0].scope, None);
    let overridden = scoped::register(&env, &n("Scope"), &n("Scope.first"), 3000).unwrap();
    assert_eq!(registrations(&env, &overridden, usize::MAX).unwrap(), None);
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
    let env = register(&env, "earlier", app("C", c("h")));
    let changed = register_class(&env, &n("D")).unwrap();
    assert_eq!(registrations(&empty, &changed, 1_000_000).unwrap(), None);
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
fn scoped_export_keeps_imported_name_updates_and_scope_changes_unsupported() {
    let base = class(&Environment::new(), "Pick", ty());
    let declarations = axiom(&base, "candidate", c("Pick"));
    let scoped = scoped::register(&declarations, &n("First"), &n("candidate"), 1000).unwrap();
    let update = scoped::register(&scoped, &n("First"), &n("candidate"), 2000).unwrap();
    assert_eq!(registrations(&scoped, &update, 1_000_000).unwrap(), None);
    assert_eq!(
        registrations(&declarations, &scoped, 1_000_000).unwrap(),
        None
    );
    for namespace in ["Second", "First.Inner"] {
        assert!(scoped::register(&scoped, &n(namespace), &n("candidate"), 1000).is_err());
    }
    assert!(set_instance(&scoped, &n("candidate"), 1000).is_err());
}
