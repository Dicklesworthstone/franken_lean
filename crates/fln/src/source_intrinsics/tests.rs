use super::*;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn renamed(expr: &Expr) -> Expr {
    match expr.node() {
        ExprNode::Lam {
            binder_type,
            body,
            binder_info,
            ..
        } => Expr::lam(
            name("hygienic.value"),
            renamed(binder_type),
            renamed(body),
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_type,
            body,
            binder_info,
            ..
        } => Expr::forall_e(
            name("hygienic.type"),
            Expr::mdata(KVMap::new(), renamed(binder_type)),
            renamed(body),
            *binder_info,
        ),
        ExprNode::App { f, a } => Expr::app(renamed(f), renamed(a)),
        ExprNode::MData { expr, .. } => renamed(expr),
        _ => expr.clone(),
    }
}

fn admitted(change_helper: bool, annotations: bool) -> Engine {
    let mut engine = Engine::from_environment(Environment::new());
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    for mut declaration in std::iter::once(fln_elab::seed::nat_inductive_seed_declaration())
        .chain(fln_elab::seed::nat_add_support_seed_declarations())
        .chain(std::iter::once(fln_elab::seed::nat_add_seed_declaration()))
    {
        if let Declaration::Defn(value) = &mut declaration {
            if annotations {
                value.base.type_ = renamed(&value.base.type_);
                value.value = renamed(&value.value);
            }
            if change_helper && value.base.name == name("Nat.add._f") {
                let mut binders = Vec::new();
                let mut body = &value.value;
                while let ExprNode::Lam {
                    binder_name,
                    binder_type,
                    binder_info,
                    body: inner,
                } = body.node()
                {
                    binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
                    body = inner;
                }
                assert_eq!(binders.len(), 3);
                let mut body = Expr::lit(Literal::Nat(NatLit::from_u64(0)));
                for (name, type_, info) in binders.into_iter().rev() {
                    body = Expr::lam(name, type_, body, info);
                }
                value.value = body;
            }
        }
        engine = engine
            .admit_declaration(declaration, &KVMap::new(), limits)
            .expect("the model candidate passes both admission engines")
            .into_complete()
            .expect("both admission engines complete")
            .engine;
    }
    engine
}

#[test]
fn labels_and_metadata_preserve_the_complete_admitted_addition_model() {
    let engine = admitted(false, true);
    let root = engine.logical_root(&KVMap::new());
    assert!(nat_add_matches(engine.environment(), &mut 0, IngressLimits::default()).unwrap());
    let run = engine
        .execute_source_commands_with_checks(
            b"#eval Nat.add 20 22",
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        closed_vm_value(&run.batch.executions.last().unwrap().exit).unwrap(),
        Some(ClosedVmValue::Scalar(42))
    );
    assert_eq!(root, engine.logical_root(&KVMap::new()));
}

#[test]
fn a_well_typed_changed_helper_cannot_authorize_native_addition() {
    let canonical = admitted(false, false);
    let changed = admitted(true, false);
    assert_eq!(
        canonical.environment().find(&name("Nat.add")),
        changed.environment().find(&name("Nat.add"))
    );
    assert!(nat_add_matches(canonical.environment(), &mut 0, IngressLimits::default()).unwrap());
    assert!(!nat_add_matches(changed.environment(), &mut 0, IngressLimits::default()).unwrap());
}

#[test]
fn recognition_keeps_declaration_metadata_and_de_bruijn_structure() {
    let Declaration::Defn(model) = fln_elab::seed::nat_add_seed_declaration() else {
        unreachable!()
    };
    let expected = ConstantInfo::Defn(model.clone());
    let mut mutants = Vec::new();
    let mut changed = model.clone();
    changed.all.clear();
    mutants.push(changed);
    let mut changed = model.clone();
    changed.hints = ReducibilityHints::Abbrev;
    mutants.push(changed);
    let mut changed = model.clone();
    changed.safety = DefinitionSafety::Unsafe;
    mutants.push(changed);
    let mut changed = model;
    let ExprNode::Lam {
        binder_name,
        binder_type,
        body,
        binder_info,
    } = changed.value.node()
    else {
        unreachable!()
    };
    let ExprNode::Lam {
        binder_name: n,
        binder_type: t,
        binder_info: i,
        ..
    } = body.node()
    else {
        unreachable!()
    };
    changed.value = Expr::lam(
        binder_name.clone(),
        binder_type.clone(),
        Expr::lam(n.clone(), t.clone(), Expr::bvar(1).unwrap(), *i),
        *binder_info,
    );
    mutants.push(changed);
    for changed in mutants {
        assert!(
            !Comparison {
                visited: &mut 0,
                limits: IngressLimits::default()
            }
            .info(&ConstantInfo::Defn(changed), &expected)
            .unwrap()
        );
    }
    let mut comparison = Comparison {
        visited: &mut 0,
        limits: IngressLimits::default(),
    };
    let a = Expr::lam(
        name("x"),
        Expr::sort(Level::one()),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    let b = Expr::forall_e(
        name("x"),
        Expr::sort(Level::one()),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    assert!(!comparison.expression(&a, &b).unwrap());
}

#[test]
fn recognition_is_metered_and_a_failed_attempt_does_not_change_the_model() {
    let engine = admitted(false, true);
    let root = engine.logical_root(&KVMap::new());
    let limits = IngressLimits {
        max_nodes: 1,
        ..IngressLimits::default()
    };
    assert!(matches!(
        nat_add_matches(engine.environment(), &mut 0, limits),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            ..
        })
    ));
    assert!(nat_add_matches(engine.environment(), &mut 0, IngressLimits::default()).unwrap());
    assert_eq!(root, engine.logical_root(&KVMap::new()));
}
