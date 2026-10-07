//! The admitted pin's history carrier is reduced before ordinary signatures.

use super::*;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn constant(label: &str) -> Expr {
    Expr::const_(name(label), vec![])
}

fn nat(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn list(values: &[u64]) -> Expr {
    let natural = constant("Nat");
    let mut result = Expr::app(
        Expr::const_(name("List.nil"), vec![Level::zero()]),
        natural.clone(),
    );
    for value in values.iter().rev() {
        result = application(
            Expr::const_(name("List.cons"), vec![Level::zero()]),
            [natural.clone(), nat(*value), result],
        );
    }
    result
}

fn admitted_scaffold(altered: Option<&str>) -> Engine {
    let mut engine = Engine::from_environment(Environment::new());
    for mut declaration in fln_elab::seed::imported_list_recursion_model_declarations()
        .into_iter()
        .chain([fln_elab::seed::nat_inductive_seed_declaration()])
    {
        if let Some(altered) = altered
            && let Declaration::Defn(definition) = &mut declaration
            && definition.base.name == name(altered)
        {
            definition.value = Expr::app(
                Expr::lam(
                    Name::anonymous(),
                    definition.base.type_.clone(),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                definition.value.clone(),
            );
        }
        engine = engine
            .admit_declaration(
                declaration,
                &KVMap::new(),
                EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
    }
    engine
}

fn list_type() -> Expr {
    Expr::app(
        Expr::const_(name("List"), vec![Level::zero()]),
        constant("Nat"),
    )
}

fn motive() -> Expr {
    Expr::lam(
        Name::anonymous(),
        list_type(),
        constant("Nat"),
        BinderInfo::Default,
    )
}

fn history(value: Expr) -> Expr {
    application(
        Expr::const_(name("List.below"), vec![Level::one(), Level::zero()]),
        [constant("Nat"), motive(), value],
    )
}

fn functional(value: u64) -> Expr {
    Expr::lam(
        Name::anonymous(),
        list_type(),
        Expr::lam(
            Name::anonymous(),
            history(Expr::bvar(0).unwrap()),
            nat(value),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    )
}

fn declaration(label: &str, type_: Expr, value: Expr) -> Declaration {
    let label = name(label);
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: label.clone(),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![label],
    })
}

#[test]
fn complete_list_scaffold_is_dual_admitted_and_preserves_actual_functionals() {
    let engine = admitted_scaffold(None);
    let options = KVMap::new();
    let root = engine.logical_root(&options);
    assert!(
        crate::source_intrinsics::imported_list_recursion_matches(
            engine.environment(),
            &mut 0,
            IngressLimits::default()
        )
        .unwrap()
    );
    for expected in [7, 42] {
        let body = application(
            Expr::const_(name("List.brecOn"), vec![Level::one(), Level::zero()]),
            [
                constant("Nat"),
                motive(),
                list(&[1, 2]),
                functional(expected),
            ],
        );
        let executed = engine
            .execute_definition(
                declaration("answer", constant("Nat"), body),
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            closed_vm_value(&executed.exit).unwrap(),
            Some(ClosedVmValue::Scalar(usize::try_from(expected).unwrap()))
        );
        assert_eq!(root, engine.logical_root(&options));
    }
    for altered in ["List.below", "List.brecOn.go", "List.brecOn"] {
        let changed = admitted_scaffold(Some(altered));
        if altered != "List.brecOn" {
            assert_eq!(
                engine.environment().find(&name("List.brecOn")),
                changed.environment().find(&name("List.brecOn"))
            );
        }
        assert!(
            !crate::source_intrinsics::imported_list_recursion_matches(
                changed.environment(),
                &mut 0,
                IngressLimits::default(),
            )
            .unwrap(),
            "altered checked dependency: {altered}"
        );
    }
    assert!(matches!(
        crate::source_intrinsics::imported_list_recursion_matches(
            engine.environment(),
            &mut 0,
            IngressLimits {
                max_nodes: 1,
                ..IngressLimits::default()
            }
        ),
        Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            ..
        })
    ));
}

#[test]
fn list_motive_comparison_preserves_decorated_element_arguments() {
    let engine = admitted_scaffold(None);
    let element = Expr::mdata(
        KVMap::from_entries(vec![(name("borrowed"), DataValue::OfBool(true))]),
        constant("Nat"),
    );
    let family = Expr::app(
        Expr::const_(name("List"), vec![Level::zero()]),
        element.clone(),
    );
    let motive = Expr::lam(
        Name::anonymous(),
        family.clone(),
        constant("Nat"),
        BinderInfo::Default,
    );
    let head = Expr::const_(name("List.brecOn"), vec![Level::one(), Level::zero()]);
    let arguments = [element.clone(), motive, list(&[1]), functional(42)];
    let executed = engine
        .execute_definition(
            declaration(
                "decoratedList",
                constant("Nat"),
                application(head.clone(), arguments.clone()),
            ),
            &KVMap::new(),
            EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(
        closed_vm_value(&executed.exit).unwrap(),
        Some(ClosedVmValue::Scalar(42))
    );
    let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
    let fold = preparation
        .imported_list_recursion(&head, &arguments)
        .unwrap()
        .unwrap();
    let (_, arguments) = preparation.spine(&fold).unwrap();
    assert_eq!(arguments[0], element);
    let ExprNode::Lam { binder_type, .. } = arguments[1].node() else {
        panic!("emitted fold motive")
    };
    assert_eq!(binder_type, &family);
}

#[test]
fn list_history_administration_preserves_strict_arguments_and_initializers() {
    let engine = admitted_scaffold(None);
    let work_type = Expr::forall_e(
        Name::anonymous(),
        constant("Nat"),
        constant("Nat"),
        BinderInfo::Default,
    );
    let work_body = Expr::lam(
        Name::anonymous(),
        constant("Nat"),
        Expr::bvar(0).unwrap(),
        BinderInfo::Default,
    );
    let checked = engine
        .admit_declaration(
            declaration("strictWork", work_type, work_body),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let engine = checked.engine;
    let computation = Expr::app(constant("strictWork"), nat(42));
    let strict_let = Expr::let_e(
        Name::anonymous(),
        constant("Nat"),
        computation.clone(),
        nat(7),
        false,
    );
    let strict_beta = Expr::app(
        Expr::lam(
            Name::anonymous(),
            constant("Nat"),
            nat(7),
            BinderInfo::Default,
        ),
        computation.clone(),
    );
    let marker = FVarId(name("forbiddenHistory"));
    for source in [strict_let, strict_beta] {
        engine
            .admit_declaration(
                declaration("strictAnswer", constant("Nat"), source.clone()),
                &KVMap::new(),
                EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        let mut preparation = Preparation::new(engine.environment(), IngressLimits::default());
        assert_eq!(
            preparation.list_history_reduce(&source, &marker).unwrap(),
            source
        );
    }
    let producer = Expr::let_e(
        Name::anonymous(),
        constant("Nat"),
        computation,
        functional(42),
        false,
    );
    let head = Expr::const_(name("List.brecOn"), vec![Level::one(), Level::zero()]);
    let args = [constant("Nat"), motive(), list(&[1]), producer];
    engine
        .admit_declaration(
            declaration(
                "strictCallback",
                constant("Nat"),
                application(head.clone(), args.clone()),
            ),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(
        Preparation::new(engine.environment(), IngressLimits::default())
            .imported_list_recursion(&head, &args)
            .unwrap()
            .is_none()
    );
}

#[test]
fn an_opaque_history_consumer_is_refused_after_admission() {
    let engine = admitted_scaffold(None);
    let callback_type = Expr::forall_e(
        Name::anonymous(),
        list_type(),
        Expr::forall_e(
            Name::anonymous(),
            history(Expr::bvar(0).unwrap()),
            constant("Nat"),
            BinderInfo::Default,
        ),
        BinderInfo::Default,
    );
    let head = Expr::const_(name("List.brecOn"), vec![Level::one(), Level::zero()]);
    let args = [
        constant("Nat"),
        motive(),
        list(&[1, 2]),
        Expr::bvar(0).unwrap(),
    ];
    let type_ = Expr::forall_e(
        Name::anonymous(),
        callback_type.clone(),
        constant("Nat"),
        BinderInfo::Default,
    );
    let body = Expr::lam(
        Name::anonymous(),
        callback_type,
        application(head.clone(), args.clone()),
        BinderInfo::Default,
    );
    engine
        .admit_declaration(
            declaration("opaqueHistory", type_, body),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(
        Preparation::new(engine.environment(), IngressLimits::default())
            .imported_list_recursion(&head, &args),
        Err(IngressError::UnsupportedNode {
            kind: "List course-of-values history escapes"
        })
    ));
}

#[test]
fn an_admitted_functional_observing_deeper_history_is_refused() {
    type Local = (FVarId, Expr);
    fn local(label: &str, type_: Expr) -> Local {
        (FVarId(name(label)), type_)
    }
    fn value(local: &Local) -> Expr {
        Expr::fvar(local.0.clone())
    }
    fn bind(locals: &[Local], mut body: Expr, lambda: bool) -> Expr {
        for (id, type_) in locals.iter().rev() {
            body = body.lift_loose(0, 1).unwrap().abstract_fvar(id, 0).unwrap();
            body = if lambda {
                Expr::lam(id.0.clone(), type_.clone(), body, BinderInfo::Default)
            } else {
                Expr::forall_e(id.0.clone(), type_.clone(), body, BinderInfo::Default)
            };
        }
        body
    }
    fn cons(head: Expr, tail: Expr) -> Expr {
        application(
            Expr::const_(name("List.cons"), vec![Level::zero()]),
            [constant("Nat"), head, tail],
        )
    }
    fn pair_type(tail: Expr) -> Expr {
        application(
            Expr::const_(name("PProd"), vec![Level::one(), Level::one()]),
            [constant("Nat"), history(tail)],
        )
    }
    fn recurse(motive: Expr, first: Expr, step: Expr, major: Expr, history: Expr) -> Expr {
        application(
            Expr::const_(name("List.rec"), vec![Level::one(), Level::zero()]),
            [constant("Nat"), motive, first, step, major, history],
        )
    }
    // This is the checked term for two constructor matches. In the second
    // cons branch `previous.2.1` observes the result two tails below this one.
    // The Reference kernel accepts the same functional and evaluates a two
    // element List to 1; immediate-IH erasure must not pretend to execute it.
    let xs = local("outer_xs", list_type());
    let previous = local("outer_previous", history(value(&xs)));
    let outer_motive = bind(
        std::slice::from_ref(&xs),
        bind(std::slice::from_ref(&previous), constant("Nat"), false),
        true,
    );
    let nil_history = local("nil_history", history(list(&[])));
    let first = bind(&[nil_history], nat(1), true);
    let head = local("outer_head", constant("Nat"));
    let tail = local("outer_tail", list_type());
    let unused = local("outer_ih", Expr::app(outer_motive.clone(), value(&tail)));
    let step_history = local("step_history", history(cons(value(&head), value(&tail))));
    let inner_list = local("inner_list", list_type());
    let inner_pair = local("inner_pair", pair_type(value(&inner_list)));
    let inner_motive = bind(
        &[inner_list],
        bind(&[inner_pair], constant("Nat"), false),
        true,
    );
    let inner_nil_pair = local("inner_nil_pair", pair_type(list(&[])));
    let inner_first = bind(&[inner_nil_pair], nat(2), true);
    let second_head = local("second_head", constant("Nat"));
    let second_tail = local("second_tail", list_type());
    let second_ih = local(
        "second_ih",
        Expr::app(inner_motive.clone(), value(&second_tail)),
    );
    let second_pair = local(
        "second_pair",
        pair_type(cons(value(&second_head), value(&second_tail))),
    );
    let deeper = Expr::proj(
        name("PProd"),
        0,
        Expr::proj(name("PProd"), 1, value(&second_pair)),
    );
    let inner_step = bind(
        &[second_head, second_tail, second_ih, second_pair],
        deeper,
        true,
    );
    let selected = recurse(
        inner_motive,
        inner_first,
        inner_step,
        value(&tail),
        value(&step_history),
    );
    let step = bind(&[head, tail, unused, step_history], selected, true);
    let selected = recurse(outer_motive, first, step, value(&xs), value(&previous));
    let functional = bind(&[xs, previous], selected, true);
    assert!(!functional.has_fvar() && !functional.has_loose_bvars());
    let engine = admitted_scaffold(None);
    let head = Expr::const_(name("List.brecOn"), vec![Level::one(), Level::zero()]);
    let args = [constant("Nat"), motive(), list(&[10, 20]), functional];
    engine
        .admit_declaration(
            declaration(
                "deeperHistory",
                constant("Nat"),
                application(head.clone(), args.clone()),
            ),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(
        Preparation::new(engine.environment(), IngressLimits::default())
            .imported_list_recursion(&head, &args),
        Err(IngressError::UnsupportedNode {
            kind: "List course-of-values history escapes"
        })
    ));
}

#[test]
fn admitted_list_dependencies_have_uniform_signatures_after_history_reduction() {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(std::path::PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                std::path::PathBuf::from(home)
                    .join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.is_dir());
    let Some(library) = library else {
        assert!(std::env::var_os("FLN_REQUIRE_REFERENCE").is_none());
        eprintln!("SKIP: pinned Reference lib/lean is absent");
        return;
    };
    const STACK: usize = 256 * 1024 * 1024;
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let path = library.join("Init/Prelude.olean");
            let parts = [
                std::fs::read(&path).unwrap(),
                std::fs::read(path.with_extension("olean.server")).unwrap(),
                std::fs::read(path.with_extension("olean.private")).unwrap(),
            ];
            let module = name("Init.Prelude");
            let inputs = [OleanModuleInput {
                name: &module,
                artifact: &parts[0],
                server_artifact: Some(&parts[1]),
                private_artifact: Some(&parts[2]),
            }];
            let options = KVMap::new();
            let imported = Engine::from_environment(Environment::new())
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&module),
                    &options,
                    crate::source_check::modules::imported::SourceOleanImportLimits::new(
                        OleanCheckLimits::new(256 * 1024 * 1024, Budget::for_stack_bytes(STACK)),
                    ),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert!(
                crate::source_intrinsics::imported_list_recursion_matches(
                    imported.engine.environment(),
                    &mut 0,
                    IngressLimits::default(),
                )
                .unwrap(),
                "actual pinned List scaffold matches the complete model"
            );
            let natural = constant("Nat");
            let result_type = Expr::app(
                Expr::const_(name("List"), vec![Level::zero()]),
                natural.clone(),
            );
            let callback = Expr::lam(
                name("n"),
                natural.clone(),
                application(constant("Nat.add"), [Expr::bvar(0).unwrap(), nat(1)]),
                BinderInfo::Default,
            );
            let mut cases = vec![
                (
                    "List.append",
                    result_type.clone(),
                    application(
                        Expr::const_(name("List.append"), vec![Level::zero()]),
                        [natural.clone(), list(&[20]), list(&[22])],
                    ),
                ),
                (
                    "List.map",
                    result_type.clone(),
                    application(
                        Expr::const_(name("List.map"), vec![Level::zero(), Level::zero()]),
                        [natural.clone(), natural, callback, list(&[41])],
                    ),
                ),
            ];
            let source = b"def classified (limit : Nat) : List Nat := List.map (fun n => if Nat.beq n limit then 20 else 22) [2, 4]";
            let checked = imported
                .engine
                .check_source_files(
                    &[source],
                    &options,
                    SourceCheckLimits::new(EngineAdmissionLimits::new(
                        Budget::for_stack_bytes(STACK),
                    )),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let Some(ConstantInfo::Defn(definition)) =
                checked.engine.environment().find(&name("classified"))
            else {
                panic!("checked conditional map definition")
            };
            cases.push((
                "List.map computed predicate",
                definition.base.type_.clone(),
                definition.value.clone(),
            ));
            for (label, result_type, body) in cases {
                let entry = name("diagnosticListResult");
                let checked = imported
                    .engine
                    .admit_declaration(
                        Declaration::Defn(DefinitionVal {
                            base: ConstantVal {
                                name: entry.clone(),
                                level_params: vec![],
                                type_: result_type.clone(),
                            },
                            value: body.clone(),
                            hints: ReducibilityHints::Abbrev,
                            safety: DefinitionSafety::Safe,
                            all: vec![entry],
                        }),
                        &options,
                        EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
                    )
                    .unwrap()
                    .into_complete()
                    .unwrap();
                let limits = IngressLimits::default();
                let mut preparation = Preparation::new(checked.engine.environment(), limits);
                let prepared = preparation
                    .expression_at_type(&body, Some(result_type.clone()))
                    .unwrap();
                let catalog = crate::executable_dependencies(
                    checked.engine.environment(),
                    &prepared,
                    limits,
                    &mut preparation,
                )
                .unwrap();
                assert!(!catalog.functions.is_empty(), "{label}");
                let mappings: BTreeMap<_, _> = preparation
                    .specializations
                    .instances
                    .iter()
                    .map(|(key, generated)| (generated.clone(), key.0.clone()))
                    .collect();
                let definitions: Vec<_> = preparation
                    .specializations
                    .definitions
                    .values()
                    .cloned()
                    .collect();
                for definition in definitions {
                    let generated = &definition.base.name;
                    let original = mappings.get(generated);
                    let signature = preparation.signature(&definition, true).unwrap();
                    assert!(
                        signature.is_some(),
                        "{label}: {generated:?} <- {original:?}"
                    );
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
