//! The same independently decoded pin fixture used by logical Array iteration
//! supplies native representation contracts. Execution and FLBC replay live in
//! source_imported_arrays; these tests exercise the substitution boundary.
use super::*;
use crate::runtime::array_iteration::tests::{replace, with_fixture, without};
use fln_elab::externs::{self, ExternEntry};
use fln_elab::implemented_by;

fn nat_array() -> Expr {
    family(&Level::zero(), &c("Nat"))
}

fn changed_body(environment: &Environment, label: &str) -> Environment {
    let Some(ConstantInfo::Defn(original)) = environment.find(&name(label)) else {
        panic!("the actual pinned {label} is a definition");
    };
    let mut changed = original.clone();
    changed.value = Expr::app(
        Expr::lam(
            Name::anonymous(),
            changed.base.type_.clone(),
            b(0).unwrap(),
            BinderInfo::Default,
        ),
        changed.value,
    );
    replace(environment, ConstantInfo::Defn(changed))
}

#[test]
fn actual_array_model_maps_storage_and_every_supported_primitive_without_kernel_changes() {
    with_fixture(|environment| {
        if std::env::var_os("FLN_DUMP_NATIVE_ARRAY_CONTRACTS").is_some() {
            for row in super::extraction::rows(environment) {
                println!("{row}");
            }
        }
        let original = environment.find(&name("Array")).unwrap().clone();
        let original_constructor = environment.find(&name("Array.mk")).unwrap().clone();
        let count = environment.constants().count();
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        assert!(preparation.native_arrays_enabled().unwrap());
        assert_eq!(
            preparation.value_type(&nat_array()).unwrap(),
            Some(ValueType::Array)
        );
        assert!(preparation.record_shape(&nat_array()).unwrap().is_none());
        for operation in Operation::ALL {
            let primitive = preparation
                .array_primitive(operation)
                .unwrap_or_else(|error| panic!("{operation:?}: {error:?}"))
                .expect("each supported actual primitive selects native storage");
            let ExprNode::Const { name, levels } = primitive.node() else {
                panic!("a private primitive is a constant");
            };
            assert!(levels.is_empty());
            let binding = preparation.array_intrinsic_binding(name).unwrap();
            assert_eq!(binding.row, format!("extern:{}", operation.label()));
            assert_eq!(binding.arguments.len(), binding.argument_ownership.len());
            assert_eq!(binding.universe_arity, 0);
        }
        assert_eq!(environment.find(&name("Array")), Some(&original));
        assert_eq!(
            environment.find(&name("Array.mk")),
            Some(&original_constructor)
        );
        assert_eq!(environment.constants().count(), count);
        assert!(!environment.contains(&name(HANDLE)));
        assert!(!environment.contains(&name(PAYLOAD)));
    });
}

#[test]
fn arrays_of_data_and_callbacks_share_one_erased_primitive_with_typed_recovery() {
    with_fixture(|environment| {
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        let payloads = [
            c("Nat"),
            list(&Level::zero(), &c("Nat")),
            function(&[c("Nat")], c("Nat")),
        ];
        for payload in &payloads {
            for operation in [Operation::Push, Operation::Get, Operation::ToList] {
                let wrapper = preparation
                    .array_wrapper(operation, &Level::zero(), payload)
                    .unwrap()
                    .expect("a concrete element type retains its interface");
                assert!(!wrapper.has_loose_bvars());
                assert!(!wrapper.has_level_param());
            }
            assert_eq!(
                preparation
                    .value_type(&family(&Level::zero(), payload))
                    .unwrap(),
                Some(ValueType::Array)
            );
        }
        assert_eq!(preparation.arrays.bindings.iter().flatten().count(), 3);
        let (push, _) = preparation.arrays.bindings[Operation::Push.index()]
            .as_ref()
            .unwrap();
        assert_eq!(push.arguments, [ValueType::Array, ValueType::Abi]);
        assert_eq!(
            push.argument_ownership,
            [ArgumentOwnership::Owned, ArgumentOwnership::Owned]
        );
        let (get, _) = preparation.arrays.bindings[Operation::Get.index()]
            .as_ref()
            .unwrap();
        assert_eq!(get.arguments, [ValueType::Array, ValueType::Nat]);
        assert_eq!(get.result, ValueType::Abi);
        for payload in payloads {
            let recovery = preparation.arrays.payloads.get(&payload).unwrap();
            let signature = preparation
                .array_function_signature(recovery)
                .unwrap()
                .unwrap();
            assert_eq!(signature.parameters, [ValueType::Abi]);
            assert_eq!(
                signature.result,
                preparation.value_type(&payload).unwrap().unwrap()
            );
        }
    });
}

#[test]
fn type_valued_array_elements_are_inert_and_keep_the_original_container_type() {
    with_fixture(|environment| {
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        for (level, payload, element) in [
            (Level::one(), Expr::sort(Level::one()), c("String")),
            (Level::zero(), Expr::sort(Level::zero()), c("True")),
        ] {
            let source = family(&level, &payload);
            assert_eq!(
                preparation.array_element_type(&source).unwrap(),
                Some((level.clone(), payload.clone()))
            );
            assert_eq!(
                preparation.array_payload(&payload).unwrap(),
                proofs::erased_type()
            );
            let empty = application(
                Expr::const_(name("Array.emptyWithCapacity"), vec![level.clone()]),
                [payload.clone(), c("Nat.zero")],
            );
            let push = preparation
                .array_call(
                    &Expr::const_(name("Array.push"), vec![level.clone()]),
                    &[payload.clone(), empty, element],
                )
                .unwrap()
                .unwrap();
            let (_, arguments) = preparation.spine(&push).unwrap();
            assert_eq!(arguments.last(), Some(&proofs::erased_value()));
            preparation
                .array_wrapper(Operation::ToList, &level, &payload)
                .unwrap()
                .unwrap();
            assert!(
                preparation
                    .arrays
                    .payloads
                    .contains_key(&list(&level, &payload))
            );
            assert_eq!(
                preparation.value_type(&source).unwrap(),
                Some(ValueType::Array)
            );
        }
    });
}

#[test]
fn canonical_native_array_rows_are_registered_once_regardless_of_repeated_dependency_visits() {
    with_fixture(|environment| {
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        preparation
            .array_primitive(Operation::Get)
            .unwrap()
            .unwrap();
        let (binding, _) = preparation.arrays.bindings[Operation::Get.index()]
            .as_ref()
            .unwrap()
            .clone();
        let mut intrinsics = Vec::new();
        let mut functions = Vec::new();
        assert!(
            preparation
                .array_intrinsic_alias(&binding, &mut intrinsics, &mut functions)
                .unwrap()
        );
        assert!(
            preparation
                .array_intrinsic_alias(&binding, &mut intrinsics, &mut functions)
                .unwrap()
        );
        assert_eq!(intrinsics, [binding]);
        assert!(functions.is_empty());
    });
}

#[test]
fn source_only_array_records_do_not_acquire_native_representation_by_name() {
    with_fixture(|environment| {
        let mut logical = Environment::new();
        for (label, _) in environment.constants() {
            logical = logical
                .with_entry(environment.entry(label).unwrap())
                .unwrap();
        }
        let mut preparation = Preparation::new(&logical, IngressLimits::default());
        assert!(!preparation.native_arrays_enabled().unwrap());
        assert_eq!(
            preparation.value_type(&nat_array()).unwrap(),
            Some(ValueType::Constructor)
        );
        assert!(preparation.record_shape(&nat_array()).unwrap().is_some());
        assert!(
            preparation
                .array_primitive(Operation::Push)
                .unwrap()
                .is_none()
        );
        assert!(preparation.arrays.bindings.iter().all(Option::is_none));
    });
}

#[test]
fn changed_array_family_and_transitive_operation_models_refuse_native_substitution() {
    with_fixture(|environment| {
        let changed = changed_body(environment, "Array.toList");
        let mut preparation = Preparation::new(&changed, IngressLimits::default());
        assert!(matches!(
            preparation.native_arrays_enabled(),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(preparation.arrays.bindings.iter().all(Option::is_none));

        let changed = changed_body(environment, "List.length");
        let mut preparation = Preparation::new(&changed, IngressLimits::default());
        assert!(preparation.native_arrays_enabled().unwrap());
        assert!(matches!(
            preparation.array_primitive(Operation::Size),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(preparation.arrays.bindings[Operation::Size.index()].is_none());

        let missing = without(environment, &name("List.cons"));
        let mut preparation = Preparation::new(&missing, IngressLimits::default());
        assert!(matches!(
            preparation.native_arrays_enabled(),
            Err(IngressError::UnsupportedNode { .. })
        ));
    });
}

#[test]
fn array_mutation_contracts_bind_recursive_companion_presence_and_bodies() {
    with_fixture(|environment| {
        for (operation, companion) in [
            (Operation::Push, "List.concat._unsafe_rec"),
            (Operation::Set, "List.set._unsafe_rec"),
            (Operation::Pop, "List.dropLast._unsafe_rec"),
        ] {
            let removed = without(environment, &name(companion));
            let mut preparation = Preparation::new(&removed, IngressLimits::default());
            assert!(
                matches!(
                    preparation.array_primitive(operation),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "removed {companion}"
            );
            assert!(preparation.arrays.bindings[operation.index()].is_none());

            let changed = changed_body(environment, companion);
            let mut preparation = Preparation::new(&changed, IngressLimits::default());
            assert!(
                matches!(
                    preparation.array_primitive(operation),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "changed {companion}"
            );
            assert!(preparation.arrays.bindings[operation.index()].is_none());
        }
    });
}

#[test]
fn native_arrays_preserve_selected_implementations_externs_and_initializers() {
    with_fixture(|environment| {
        let Some(ConstantInfo::Defn(original)) = environment.find(&name("Array.push")) else {
            unreachable!("the actual push model is a definition");
        };
        let mut replacement = original.clone();
        replacement.base.name = name("alternateArrayPush");
        replacement.all = vec![replacement.base.name.clone()];
        let changed = environment
            .add_decl(ConstantInfo::Defn(replacement))
            .unwrap();
        let changed =
            implemented_by::register(&changed, &name("Array.push"), &name("alternateArrayPush"))
                .unwrap();
        let mut preparation = Preparation::new(&changed, IngressLimits::default());
        assert!(matches!(
            preparation.array_primitive(Operation::Push),
            Err(IngressError::UnsupportedNode { .. })
        ));

        let changed = externs::register(
            environment,
            &name("Array.push"),
            vec![ExternEntry::Standard {
                backend: name("all"),
                symbol: "foreign_array_push".to_owned(),
            }],
        )
        .unwrap();
        let mut preparation = Preparation::new(&changed, IngressLimits::default());
        assert!(matches!(
            preparation.array_primitive(Operation::Push),
            Err(IngressError::UnsupportedNode { .. })
        ));

        for label in ["Array.mk", "Array.push", "List.concat"] {
            let initializers = BTreeSet::from([name(label)]);
            let mut preparation = Preparation::new(environment, IngressLimits::default())
                .with_runtime_initializers(&initializers);
            assert!(
                matches!(
                    preparation.array_primitive(Operation::Push),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{label}"
            );
            assert!(preparation.arrays.bindings[Operation::Push.index()].is_none());
        }
    });
}

#[test]
fn explicit_implementations_can_target_only_authorized_native_array_operations() {
    with_fixture(|environment| {
        let Some(ConstantInfo::Defn(original)) = environment.find(&name("Array.size")) else {
            unreachable!("the actual size model is a definition");
        };
        let alias = name("nativeArraySizeAlias");
        let mut declaration = original.clone();
        declaration.base.name = alias.clone();
        declaration.all = vec![alias.clone()];
        let selected = environment
            .add_decl(ConstantInfo::Defn(declaration))
            .unwrap();
        let selected = implemented_by::register(&selected, &alias, &name("Array.size")).unwrap();
        let mut preparation = Preparation::new(&selected, IngressLimits::default());
        assert_eq!(
            preparation.implementation_target(&alias).unwrap(),
            Some(name("Array.size"))
        );
        assert!(preparation.arrays.bindings[Operation::Size.index()].is_some());
        assert!(
            preparation
                .specialized_definition(&name("_fln_runtime_array_size"))
                .is_none()
        );

        let changed = changed_body(&selected, "Array.size");
        let mut preparation = Preparation::new(&changed, IngressLimits::default());
        assert!(matches!(
            preparation.implementation_target(&alias),
            Err(IngressError::UnsupportedNode { .. })
        ));
        assert!(preparation.arrays.bindings[Operation::Size.index()].is_none());

        // With no native annotations, the same explicit edge selects the
        // ordinary checked definition and leaves the logical record layout.
        let mut logical = Environment::new();
        for (label, _) in selected.constants() {
            logical = logical.with_entry(selected.entry(label).unwrap()).unwrap();
        }
        let logical = implemented_by::register(&logical, &alias, &name("Array.size")).unwrap();
        let mut preparation = Preparation::new(&logical, IngressLimits::default());
        assert_eq!(
            preparation.implementation_target(&alias).unwrap(),
            Some(name("Array.size"))
        );
        assert!(preparation.arrays.bindings.iter().all(Option::is_none));
        assert_eq!(
            preparation.value_type(&nat_array()).unwrap(),
            Some(ValueType::Constructor)
        );
    });
}

#[test]
fn canonical_array_modify_uses_its_checked_body_without_changing_logical_declarations() {
    with_fixture(|environment| {
        let logical = name("Array.modifyM");
        let original = environment.find(&logical).unwrap().clone();
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        let target = preparation
            .implementation_target(&logical)
            .unwrap()
            .unwrap();
        assert_eq!(target, name("_fln_runtime_array_modifyM"));
        let adapter = preparation.specialized_definition(&target).unwrap();
        let ConstantInfo::Defn(original_definition) = &original else {
            unreachable!("the actual modify model is a definition");
        };
        assert_eq!(adapter.value, original_definition.value);
        assert_eq!(adapter.base.type_, original_definition.base.type_);
        assert_eq!(
            adapter.base.level_params,
            original_definition.base.level_params
        );
        assert_eq!(adapter.safety, DefinitionSafety::Safe);
        assert_eq!(
            preparation.implementation_target(&logical).unwrap(),
            Some(target.clone())
        );
        assert_eq!(environment.find(&logical), Some(&original));
        assert!(!environment.contains(&target));
    });
}

#[test]
fn array_modify_adapter_preserves_changed_helpers_edges_and_initialization_authority() {
    with_fixture(|environment| {
        let logical = name("Array.modifyM");
        for label in ["Array.modifyM", "Array.modifyMUnsafe", "Array.getInternal"] {
            let changed = changed_body(environment, label);
            let mut preparation = Preparation::new(&changed, IngressLimits::default());
            assert!(
                matches!(
                    preparation.implementation_target(&logical),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{label}"
            );
            assert!(preparation.arrays.modify.is_none());
        }
        for label in ["Array.modifyM", "Array.modifyMUnsafe", "Array.getInternal"] {
            let initializers = BTreeSet::from([name(label)]);
            let mut preparation = Preparation::new(environment, IngressLimits::default())
                .with_runtime_initializers(&initializers);
            assert!(
                matches!(
                    preparation.implementation_target(&logical),
                    Err(IngressError::UnsupportedNode { .. })
                ),
                "{label}"
            );
            assert!(preparation.arrays.modify.is_none());
        }
        let Some(ConstantInfo::Defn(original)) = environment.find(&name("Array.modifyMUnsafe"))
        else {
            unreachable!("the actual selected implementation is a definition");
        };
        let mut alternative = original.clone();
        let alternate = name("alternateArrayModifyImplementation");
        alternative.base.name = alternate.clone();
        alternative.all = vec![alternate.clone()];
        let changed = environment
            .add_decl(ConstantInfo::Defn(alternative))
            .unwrap();
        let changed = implemented_by::register(&changed, &logical, &alternate).unwrap();
        let mut preparation = Preparation::new(&changed, IngressLimits::default());
        assert_eq!(
            preparation.implementation_target(&logical).unwrap(),
            Some(alternate)
        );
        assert!(preparation.arrays.modify.is_none());
    });
}

#[test]
fn native_array_validation_and_private_names_obey_ingress_bounds() {
    with_fixture(|environment| {
        for max_nodes in [0, 16, 128] {
            let mut preparation = Preparation::new(
                environment,
                IngressLimits {
                    max_nodes,
                    ..IngressLimits::default()
                },
            );
            assert!(matches!(
                preparation.array_primitive(Operation::Push),
                Err(IngressError::ResourceLimit { .. })
            ));
            assert!(preparation.arrays.bindings.iter().all(Option::is_none));
        }
        let Some(ConstantInfo::Defn(original)) = environment.find(&name("Array.size")) else {
            unreachable!("the actual size model is a definition");
        };
        let mut collision = original.clone();
        collision.base.name = name(HANDLE);
        collision.all = vec![collision.base.name.clone()];
        let changed = environment.add_decl(ConstantInfo::Defn(collision)).unwrap();
        let mut preparation = Preparation::new(&changed, IngressLimits::default());
        assert!(
            matches!(preparation.array_primitive(Operation::Push), Err(IngressError::UnsupportedNode { kind }) if kind.contains("collision"))
        );
        assert!(preparation.arrays.bindings.iter().all(Option::is_none));
    });
}

#[test]
fn array_projections_and_recursor_minor_keep_their_checked_list_interface() {
    with_fixture(|environment| {
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        let projection = preparation
            .array_projection_factory(&nat_array(), &name("Array"), 0)
            .unwrap()
            .unwrap();
        assert!(!projection.has_loose_bvars());
        assert!(matches!(
            preparation.array_projection_factory(&nat_array(), &name("Array"), 1),
            Err(IngressError::UnsupportedNode { .. })
        ));
        let motive = Expr::lam(
            Name::anonymous(),
            nat_array(),
            c("Nat"),
            BinderInfo::Default,
        );
        let minor = Expr::lam(
            Name::anonymous(),
            list(&Level::zero(), &c("Nat")),
            c("Nat.zero"),
            BinderInfo::Default,
        );
        let empty = application(
            Expr::const_(name("Array.emptyWithCapacity"), vec![Level::zero()]),
            [c("Nat"), c("Nat.zero")],
        );
        let recursor = preparation
            .array_call(
                &Expr::const_(name("Array.rec"), vec![Level::one(), Level::zero()]),
                &[c("Nat"), motive, minor, empty],
            )
            .unwrap()
            .unwrap();
        assert!(!recursor.has_loose_bvars());
    });
}

#[test]
fn native_array_views_preserve_erased_element_parameters_within_discovery_budget() {
    with_fixture(|environment| {
        let large = (0..2048).fold(c("Nat.zero"), |value, _| Expr::app(c("Nat.succ"), value));
        for element in [
            Expr::app(c("Fin"), large.clone()),
            Expr::app(c("BitVec"), large),
        ] {
            let source = family(&Level::zero(), &element);
            let mut preparation = Preparation::new(environment, IngressLimits::default());
            preparation
                .array_primitive(Operation::ToList)
                .unwrap()
                .unwrap();
            // Isolate discovery after the complete immutable model check.
            // The same cache is reused by successive views in real programs.
            preparation.visited = 0;
            preparation.limits.max_nodes = 4096;
            assert_eq!(
                preparation.array_element_type(&source).unwrap(),
                Some((Level::zero(), element.clone()))
            );
            let factory = preparation
                .array_projection_factory(&source, &name("Array"), 0)
                .unwrap()
                .unwrap();
            assert!(!factory.has_loose_bvars());
            assert!(
                preparation
                    .arrays
                    .payloads
                    .contains_key(&list(&Level::zero(), &element))
            );

            let mut eager = Preparation::new(
                environment,
                IngressLimits {
                    max_nodes: 4096,
                    ..IngressLimits::default()
                },
            );
            assert!(
                matches!(
                    eager.normalize_type(&source),
                    Err(IngressError::ResourceLimit { .. })
                ),
                "the old whole-receiver traversal exceeds the unchanged discovery budget"
            );
        }
    });
}
