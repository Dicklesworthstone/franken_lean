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

// Recursor regeneration inherits the family's parameter labels but supplies
// its own motive and minor labels. Rename only the inherited alpha parameter
// so this fixture still passes ordinary admission in both checking engines.
fn transport_labels(expr: &Expr) -> Expr {
    let label = |original: &Name| {
        if original == &name("α") {
            name("hygienic.alpha")
        } else {
            original.clone()
        }
    };
    match expr.node() {
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::lam(
            label(binder_name),
            transport_labels(binder_type),
            transport_labels(body),
            *binder_info,
        ),
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            binder_info,
        } => Expr::forall_e(
            label(binder_name),
            transport_labels(binder_type),
            transport_labels(body),
            *binder_info,
        ),
        ExprNode::App { f, a } => Expr::app(transport_labels(f), transport_labels(a)),
        _ => expr.clone(),
    }
}

fn hygienic_transport_engine() -> Engine {
    let mut engine = Engine::from_environment(Environment::new());
    let options = KVMap::new();
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    for mut declaration in [
        fln_elab::seed::nat_inductive_seed_declaration(),
        fln_elab::seed::eq_seed_declaration(),
        fln_elab::seed::quotient_seed_declaration(),
    ] {
        match &mut declaration {
            Declaration::Inductive(block) if block.types[0].base.name == name("Eq") => {
                for value in &mut block.types {
                    value.base.type_ = transport_labels(&value.base.type_);
                }
                for value in &mut block.ctors {
                    value.base.type_ = transport_labels(&value.base.type_);
                }
                for value in &mut block.recursors {
                    value.base.type_ = transport_labels(&value.base.type_);
                    for rule in &mut value.rules {
                        rule.rhs = transport_labels(&rule.rhs);
                    }
                }
            }
            Declaration::Quotient(values) => {
                for value in values {
                    value.base.type_ = transport_labels(&value.base.type_);
                }
            }
            _ => {}
        }
        engine = engine
            .admit_declaration(declaration, &options, limits)
            .expect("hygienic transport model passes both checking engines")
            .into_complete()
            .expect("transport model admission completes")
            .engine;
    }
    engine
}

fn transport_application(label: &str, levels: Vec<Level>, arguments: &[Expr]) -> Expr {
    arguments
        .iter()
        .cloned()
        .fold(Expr::const_(name(label), levels), Expr::app)
}

fn execute_transport(engine: &Engine, value: Expr) -> usize {
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    let entry = name("transportAnswer");
    let execution = engine
        .execute_definition(
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: entry.clone(),
                    level_params: vec![],
                    type_: Expr::const_(name("Nat"), vec![]),
                },
                value,
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![entry],
            }),
            &options,
            EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .expect("checked transport compiles and executes")
        .into_complete()
        .expect("transport execution completes");
    assert_eq!(root, engine.logical_root(&options));
    let Some(ClosedVmValue::Scalar(value)) = closed_vm_value(&execution.exit).unwrap() else {
        panic!("transport must preserve its scalar payload");
    };
    value
}

#[test]
fn hygienic_equality_family_executes_checked_transport() {
    let engine = hygienic_transport_engine();
    assert!(
        equality_family_matches(engine.environment(), &mut 0, IngressLimits::default()).unwrap()
    );
    let nat = Expr::const_(name("Nat"), vec![]);
    let value = Expr::lit(Literal::Nat(NatLit::from_u64(42)));
    let equation = transport_application(
        "Eq",
        vec![Level::one()],
        &[nat.clone(), value.clone(), Expr::bvar(0).unwrap()],
    );
    let motive = Expr::lam(
        name("endpoint"),
        nat.clone(),
        Expr::lam(name("proof"), equation, nat.clone(), BinderInfo::Default),
        BinderInfo::Default,
    );
    let proof = transport_application("Eq.refl", vec![Level::one()], &[nat.clone(), value.clone()]);
    let transport = transport_application(
        "Eq.rec",
        vec![Level::one(), Level::one()],
        &[nat, value.clone(), motive, value.clone(), value, proof],
    );
    assert_eq!(execute_transport(&engine, transport), 42);
}

#[test]
fn hygienic_quotient_family_executes_checked_representatives() {
    let engine = hygienic_transport_engine();
    assert!(
        quotient_family_matches(engine.environment(), &mut 0, IngressLimits::default()).unwrap()
    );
    let nat = Expr::const_(name("Nat"), vec![]);
    let relation = transport_application("Eq", vec![Level::one()], std::slice::from_ref(&nat));
    let function = Expr::lam(
        name("value"),
        nat.clone(),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    let equation = transport_application(
        "Eq",
        vec![Level::one()],
        &[nat.clone(), Expr::bvar(1).unwrap(), Expr::bvar(0).unwrap()],
    );
    let respects = Expr::lam(
        name("left"),
        nat.clone(),
        Expr::lam(
            name("right"),
            nat.clone(),
            Expr::lam(
                name("proof"),
                equation,
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let representative = transport_application(
        "Quot.mk",
        vec![Level::one()],
        &[
            nat.clone(),
            relation.clone(),
            Expr::lit(Literal::Nat(NatLit::from_u64(42))),
        ],
    );
    let lifted = transport_application(
        "Quot.lift",
        vec![Level::one(), Level::one()],
        &[
            nat.clone(),
            relation,
            nat,
            function,
            respects,
            representative,
        ],
    );
    assert_eq!(execute_transport(&engine, lifted), 42);
}

#[test]
fn metadata_is_transparent_when_comparing_transport_models() {
    let Declaration::Inductive(block) = fln_elab::seed::eq_seed_declaration() else {
        unreachable!()
    };
    let recursor = block.recursors[0].clone();
    let mut annotated = recursor.clone();
    annotated.base.type_ = renamed(&annotated.base.type_);
    for rule in &mut annotated.rules {
        rule.rhs = renamed(&rule.rhs);
    }
    assert!(
        Comparison {
            visited: &mut 0,
            limits: IngressLimits::default(),
        }
        .info(&ConstantInfo::Rec(annotated), &ConstantInfo::Rec(recursor))
        .unwrap()
    );
    let Declaration::Quotient(values) = fln_elab::seed::quotient_seed_declaration() else {
        unreachable!()
    };
    for expected in values {
        let mut annotated = expected.clone();
        annotated.base.type_ = renamed(&annotated.base.type_);
        assert!(
            Comparison {
                visited: &mut 0,
                limits: IngressLimits::default(),
            }
            .info(
                &ConstantInfo::Quot(annotated),
                &ConstantInfo::Quot(expected)
            )
            .unwrap()
        );
    }
}

#[test]
fn quotient_recognition_preserves_kinds_universes_and_binder_structure() {
    let Declaration::Quotient(values) = fln_elab::seed::quotient_seed_declaration() else {
        unreachable!()
    };
    let model = values[2].clone();
    let expected = ConstantInfo::Quot(model.clone());
    let mut mutants = Vec::new();
    let mut changed = model.clone();
    changed.kind = fln_env::constants::QuotKind::Ind;
    mutants.push(changed);
    let mut changed = model.clone();
    changed.base.level_params.swap(0, 1);
    mutants.push(changed);
    let mut changed = model.clone();
    changed.base.type_ = Expr::sort(Level::zero());
    mutants.push(changed);
    let mut changed = model;
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        body,
        ..
    } = changed.base.type_.node()
    else {
        unreachable!()
    };
    changed.base.type_ = Expr::forall_e(
        binder_name.clone(),
        binder_type.clone(),
        body.clone(),
        BinderInfo::Default,
    );
    mutants.push(changed);
    for changed in mutants {
        assert!(
            !Comparison {
                visited: &mut 0,
                limits: IngressLimits::default(),
            }
            .info(&ConstantInfo::Quot(changed), &expected)
            .unwrap()
        );
    }
}

#[test]
fn transport_model_budget_stops_are_not_negative_matches() {
    let engine = hygienic_transport_engine();
    let root = engine.logical_root(&KVMap::new());
    for matches in [equality_family_matches, quotient_family_matches] {
        assert!(matches!(
            matches(
                engine.environment(),
                &mut 0,
                IngressLimits {
                    max_nodes: 1,
                    ..IngressLimits::default()
                },
            ),
            Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                ..
            })
        ));
        assert!(matches(engine.environment(), &mut 0, IngressLimits::default()).unwrap());
    }
    assert_eq!(root, engine.logical_root(&KVMap::new()));
}
