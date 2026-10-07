use super::*;

fn name(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn nat(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn admitted_model(label: &str, change_body: bool) -> Engine {
    let target = if label == "Nat.pred" {
        label.to_owned()
    } else {
        format!("{label}._f")
    };
    admitted_model_changing(label, change_body.then_some(target.as_str()))
}

fn admitted_model_changing(label: &str, change_target: Option<&str>) -> Engine {
    let mut engine = Engine::from_environment(Environment::new());
    let options = KVMap::new();
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    let target = change_target.map(name);
    let declarations = fln_elab::seed::imported_nat_intrinsic_model_declarations(&name(label))
        .expect("fixed imported model");
    for mut declaration in declarations {
        if let Declaration::Defn(definition) = &mut declaration
            && target.as_ref() == Some(&definition.base.name)
        {
            let mut binders = Vec::new();
            let mut body = &definition.value;
            while let ExprNode::Lam {
                binder_name,
                binder_type,
                body: inner,
                binder_info,
            } = body.node()
            {
                binders.push((binder_name.clone(), binder_type.clone(), *binder_info));
                body = inner;
            }
            let mut body = if matches!(label, "Nat.beq" | "Nat.ble") {
                Expr::const_(name("Bool.false"), vec![])
            } else {
                nat(0)
            };
            for (name, type_, info) in binders.into_iter().rev() {
                body = Expr::lam(name, type_, body, info);
            }
            definition.value = body;
        }
        let declaration_name = match &declaration {
            Declaration::Defn(value) => value.base.name.clone(),
            Declaration::Inductive(block) => block.types[0].base.name.clone(),
            _ => unreachable!("logical model declaration kind"),
        };
        engine = engine
            .admit_declaration(declaration, &options, limits)
            .unwrap_or_else(|error| panic!("{label}, {declaration_name:?}: {error:?}"))
            .into_complete()
            .expect("both checking engines complete")
            .engine;
    }
    engine
}

#[test]
fn complete_nat_models_pass_both_checkers_and_execute_native_values() {
    for (label, arguments, expected, result) in [
        ("Nat.pred", vec![43], 42, "Nat"),
        ("Nat.beq", vec![42, 42], 1, "Bool"),
        ("Nat.ble", vec![41, 42], 1, "Bool"),
        ("Nat.mul", vec![6, 7], 42, "Nat"),
        ("Nat.sub", vec![45, 3], 42, "Nat"),
        ("Nat.pow", vec![2, 5], 32, "Nat"),
    ] {
        let engine = admitted_model(label, false);
        assert!(
            imported_nat_matches(
                engine.environment(),
                &name(label),
                &mut 0,
                IngressLimits::default(),
            )
            .unwrap()
        );
        let options = KVMap::new();
        let root = engine.logical_root(&options);
        let entry = name("modelAnswer");
        let body = arguments
            .into_iter()
            .fold(Expr::const_(name(label), vec![]), |function, argument| {
                Expr::app(function, nat(argument))
            });
        let execution = engine
            .execute_definition(
                Declaration::Defn(DefinitionVal {
                    base: ConstantVal {
                        name: entry.clone(),
                        level_params: vec![],
                        type_: Expr::const_(name(result), vec![]),
                    },
                    value: body,
                    hints: ReducibilityHints::Abbrev,
                    safety: DefinitionSafety::Safe,
                    all: vec![entry],
                }),
                &options,
                EngineExecutionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
            )
            .unwrap_or_else(|error| panic!("{label}: {error:?}"))
            .into_complete()
            .unwrap();
        assert_eq!(
            closed_vm_value(&execution.exit).unwrap(),
            Some(ClosedVmValue::Scalar(expected))
        );
        assert_eq!(root, engine.logical_root(&options));
    }
}

#[test]
fn changed_well_typed_bodies_do_not_authorize_imported_nat_intrinsics() {
    for label in [
        "Nat.pred", "Nat.beq", "Nat.ble", "Nat.mul", "Nat.sub", "Nat.pow",
    ] {
        let canonical = admitted_model(label, false);
        let changed = admitted_model(label, true);
        if label != "Nat.pred" {
            assert_eq!(
                canonical.environment().find(&name(label)),
                changed.environment().find(&name(label)),
                "the root stays identical while its checked dependency changes",
            );
        }
        assert!(
            !imported_nat_matches(
                changed.environment(),
                &name(label),
                &mut 0,
                IngressLimits::default(),
            )
            .unwrap(),
            "{label}"
        );
    }
}

#[test]
fn ordering_and_power_require_unchanged_roots_and_arithmetic_dependencies() {
    for (label, target) in [
        ("Nat.ble", "Nat.ble"),
        ("Nat.pow", "Nat.pow"),
        ("Nat.pow", "Nat.mul._f"),
    ] {
        let canonical = admitted_model(label, false);
        let changed = admitted_model_changing(label, Some(target));
        assert_ne!(
            canonical.environment().find(&name(target)),
            changed.environment().find(&name(target)),
            "the replacement is independently admitted and changes {target}",
        );
        if label != target {
            assert_eq!(
                canonical.environment().find(&name(label)),
                changed.environment().find(&name(label)),
                "the unchanged power root cannot authorize altered multiplication",
            );
        }
        assert!(
            !imported_nat_matches(
                changed.environment(),
                &name(label),
                &mut 0,
                IngressLimits::default(),
            )
            .unwrap(),
            "{label}: changed {target}",
        );
    }
}

#[test]
fn imported_model_resource_exhaustion_is_not_a_negative_match() {
    for label in ["Nat.beq", "Nat.ble", "Nat.pow"] {
        let engine = admitted_model(label, false);
        let name = name(label);
        assert!(matches!(
            imported_nat_matches(
                engine.environment(),
                &name,
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
        assert!(
            imported_nat_matches(
                engine.environment(),
                &name,
                &mut 0,
                IngressLimits::default()
            )
            .unwrap()
        );
    }
}

#[test]
fn admitted_pin_matches_every_primitive_model_dependency() {
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
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference is required"
        );
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
            let imported = Engine::from_environment(Environment::new())
                .import_olean_modules_for_source(
                    &inputs,
                    std::slice::from_ref(&module),
                    &KVMap::new(),
                    crate::source_check::modules::imported::SourceOleanImportLimits::new(
                        OleanCheckLimits::new(256 * 1024 * 1024, Budget::for_stack_bytes(STACK)),
                    ),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            let environment = imported.engine.environment();
            for operation in [
                "Nat.pred",
                "Nat.beq",
                "Nat.ble",
                "Nat.mul",
                "Nat.sub",
                "Nat.pow",
                "List.brecOn",
            ] {
                let declarations = if operation == "List.brecOn" {
                    fln_elab::seed::imported_list_recursion_model_declarations()
                } else {
                    fln_elab::seed::imported_nat_intrinsic_model_declarations(&name(operation))
                        .unwrap()
                };
                for declaration in declarations {
                    let constants = match declaration {
                        Declaration::Defn(value) => vec![ConstantInfo::Defn(value)],
                        Declaration::Inductive(block) => block
                            .types
                            .into_iter()
                            .map(ConstantInfo::Induct)
                            .chain(block.ctors.into_iter().map(ConstantInfo::Ctor))
                            .chain(block.recursors.into_iter().map(ConstantInfo::Rec))
                            .collect(),
                        _ => unreachable!(),
                    };
                    for expected in constants {
                        let mut comparison = Comparison {
                            visited: &mut 0,
                            limits: IngressLimits::default(),
                        };
                        assert!(
                            comparison.constant(environment, expected.clone()).unwrap(),
                            "{operation}: model dependency {:?}",
                            expected.name()
                        );
                    }
                }
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
