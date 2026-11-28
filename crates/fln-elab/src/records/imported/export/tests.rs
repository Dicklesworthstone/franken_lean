use super::super::tests::{base, c, local, n, publish, record, rows};
use super::*;
use crate::records::{RecordSpec, record_declarations_with_member_names};
use fln_core::options::KVMap;
use fln_kernel::Declaration;

fn projection(
    declaration: &str,
    constructor: &str,
    num_params: u32,
    field_index: u32,
    from_class: bool,
) -> ProjectionFunction {
    ProjectionFunction {
        declaration: n(declaration),
        constructor: n(constructor),
        num_params,
        field_index,
        from_class,
    }
}

fn descriptor_record(
    env: &Environment,
    spec: &RecordSpec,
    constructor: &Name,
    projections: &[Name],
) -> Environment {
    let mut env = env.clone();
    for declaration in record_declarations_with_member_names(
        spec,
        constructor,
        projections,
        RecordBudget::default(),
    )
    .unwrap()
    {
        env = publish(&env, declaration);
    }
    let row = StructureEntry {
        name: spec.name.clone(),
        fields: spec
            .fields
            .iter()
            .zip(projections)
            .map(|(field, projection)| StructureField {
                name: field.user_name.clone(),
                projection: projection.clone(),
                subobject: None,
                binder_info: field.binder_info,
            })
            .collect(),
        parents: vec![],
    };
    register(&env, &[row]).unwrap()
}

fn replay_journals(
    mut into: Environment,
    from: &Environment,
    mut edit: impl FnMut(&mut ExtensionDescriptor),
) -> Environment {
    for (name, state) in from.extensions() {
        let mut descriptor = state.descriptor.clone();
        edit(&mut descriptor);
        into = into.register_extension(descriptor).unwrap();
        for entry in state.entries() {
            into = into
                .push_extension_entry(name, entry.payload.to_vec())
                .unwrap();
        }
    }
    into
}

#[test]
fn projection_index_reuses_the_validated_world_and_requires_registered_identity() {
    let raw = base();
    assert!(!is_registered_projection(&raw, &n("Parent.value")).unwrap());
    let registered = register(&raw, &rows()).unwrap();
    let first = projection_index(&registered).unwrap();
    assert!(first.contains(&n("Parent.value")));
    assert!(!first.contains(&n("Nat")));
    assert!(Arc::ptr_eq(
        &first,
        &projection_index(&registered.clone()).unwrap()
    ));
    let mut unrelated = descriptor();
    unrelated.name = n("Unrelated.journal");
    let extended = registered.register_extension(unrelated).unwrap();
    assert!(Arc::ptr_eq(&first, &projection_index(&extended).unwrap()));
}

#[test]
fn imported_structure_metadata_validates_private_shapes_without_exposing_them() {
    let complete = register(&base(), &rows()).unwrap();
    let mut public = Environment::new();
    for (name, _) in complete.constants() {
        let text = name.to_display_string();
        if name == &n("Parent.mk") || text == "Child" || text.starts_with("Child.") {
            continue;
        }
        public = public.with_entry(complete.entry(name).unwrap()).unwrap();
    }
    for (name, state) in complete.extensions() {
        public = public.register_extension(state.descriptor.clone()).unwrap();
        for entry in state.entries() {
            public = public
                .push_extension_entry(name, entry.payload.clone())
                .unwrap();
        }
    }
    assert!(ImportedStructures::read(&public).is_err());
    let bound = public.with_imported_metadata_validation(&complete);
    let structures = ImportedStructures::read(&bound).unwrap();
    assert!(structures.get(&n("Parent")).is_some());
    assert!(structures.get(&n("Child")).is_none());
    assert!(
        RecordParents::read(&bound)
            .unwrap()
            .parents(&n("Child"))
            .is_empty()
    );
    assert!(is_registered_projection(&bound, &n("Parent.value")).unwrap());
    assert!(!is_registered_projection(&bound, &n("Child.extra")).unwrap());
    assert!(!bound.contains(&n("Parent.mk")));
    assert!(!bound.contains(&n("Child")));
    assert!(
        projection_index(&public).is_err(),
        "the cached validator is not transferable"
    );
    let copied_row = complete
        .extension(&extension_name())
        .unwrap()
        .entries()
        .next()
        .unwrap()
        .payload
        .clone();
    let changed = bound
        .push_extension_entry(&extension_name(), copied_row)
        .unwrap();
    assert!(
        ImportedStructures::read(&changed).is_err(),
        "new rows must see the visible constructors"
    );
}

#[test]
fn projection_index_revalidates_structure_payloads_and_descriptor_policies() {
    let raw = base();
    let registered = register(&raw, &rows()).unwrap();
    let first = projection_index(&registered).unwrap();
    let malformed = registered
        .push_extension_entry(&extension_name(), vec![0])
        .unwrap();
    assert!(registered.has_same_declarations(&malformed));
    assert!(matches!(
        projection_index(&malformed),
        Err(RecordError::InvalidTelescope)
    ));
    let foreign = replay_journals(raw, &registered, |descriptor| {
        if descriptor.name == extension_name() {
            descriptor.provenance = PayloadProvenance::Opaque;
        }
    });
    assert!(registered.has_same_declarations(&foreign));
    assert!(matches!(
        projection_index(&foreign),
        Err(RecordError::InvalidTelescope)
    ));
    assert!(
        Arc::ptr_eq(&first, &projection_index(&registered).unwrap()),
        "failed validation must not replace the last valid index"
    );
}

#[test]
fn projection_index_revalidates_parent_journals_including_orphans() {
    let raw = base();
    let registered = register(&raw, &rows()).unwrap();
    projection_index(&registered).unwrap();
    let malformed = registered
        .push_extension_entry(&inheritance::descriptor().name, vec![0])
        .unwrap();
    assert!(registered.has_same_declarations(&malformed));
    assert!(matches!(
        projection_index(&malformed),
        Err(RecordError::InvalidTelescope)
    ));
    let foreign = replay_journals(raw.clone(), &registered, |descriptor| {
        if descriptor.name == inheritance::descriptor().name {
            descriptor.provenance = PayloadProvenance::Opaque;
        }
    });
    assert!(matches!(
        projection_index(&foreign),
        Err(RecordError::InvalidTelescope)
    ));
    projection_index(&raw).unwrap();
    let orphan = inheritance::register_parents(
        &raw,
        &[RecordParent {
            record: n("Child"),
            field: 0,
            parent: n("Parent"),
        }],
    )
    .unwrap();
    assert!(raw.has_same_declarations(&orphan));
    assert!(matches!(
        projection_index(&orphan),
        Err(RecordError::InvalidTelescope)
    ));
}

#[test]
fn projection_index_binds_declarations_not_just_journals_and_cardinality() {
    let raw = base();
    let registered = register(&raw, &rows()).unwrap();
    projection_index(&registered).unwrap();
    // Deliberately corrupt a decoded candidate, without asserting admission.
    let mut changed = Environment::new();
    for (_, constant) in raw.constants() {
        let mut constant = constant.clone();
        if let ConstantInfo::Defn(value) = &mut constant
            && value.base.name == n("Parent.value")
        {
            value.value = Expr::sort(Level::zero());
        }
        changed = changed.add_decl(constant).unwrap();
    }
    let changed = replay_journals(changed, &registered, |_| {});
    assert_eq!(changed.len(), registered.len());
    for (name, state) in registered.extensions() {
        assert_eq!(
            changed.extension(name).unwrap().content_digest(),
            state.content_digest()
        );
    }
    assert!(!changed.has_same_declarations(&registered));
    assert!(matches!(
        projection_index(&changed),
        Err(RecordError::InvalidTelescope)
    ));
    assert!(is_registered_projection(&registered, &n("Parent.value")).unwrap());
}

#[test]
fn projection_index_retains_payload_resource_limits() {
    let registered = register(&base(), &rows()).unwrap();
    projection_index(&registered).unwrap();
    let oversized = registered
        .push_extension_entry(&extension_name(), vec![0; MAX_PAYLOAD + 1])
        .unwrap();
    assert_eq!(
        projection_index(&oversized),
        Err(RecordError::ResourceLimit)
    );
    assert!(is_registered_projection(&registered, &n("Parent.value")).unwrap());
}

#[test]
fn complete_interfaces_export_only_owned_rows_with_exact_work_limits() {
    let raw = base();
    let rows = rows();
    let registered = register(&raw, &rows).unwrap();
    let empty = Environment::new();
    let exported = registrations(&empty, &registered, MAX_NODES).unwrap();
    assert_eq!(exported.structures, rows);
    assert_eq!(
        exported.projections,
        vec![
            projection("Parent.value", "Parent.mk", 0, 0, false),
            projection("Child.toParent", "Child.mk", 0, 0, false),
            projection("Child.extra", "Child.mk", 0, 1, false),
            projection("Box.value", "Box.mk", 1, 0, false),
        ]
    );
    assert!(exported.bytes_examined > 0);
    assert!(exported.structures.iter().all(|row| row.name != n("Nat")));
    assert_eq!(
        registrations(&empty, &registered, exported.work).unwrap(),
        exported
    );
    assert_eq!(
        registrations(&empty, &registered, exported.work - 1),
        Err(RecordError::ResourceLimit)
    );
    assert!(
        registrations(&registered, &registered, MAX_NODES)
            .unwrap()
            .structures
            .is_empty()
    );
    assert!(
        registrations(&registered, &registered, MAX_NODES)
            .unwrap()
            .projections
            .is_empty()
    );
    assert!(
        registrations(&raw, &registered, MAX_NODES).is_err(),
        "an imported declaration cannot acquire a new structure interface"
    );
}

#[test]
fn an_imported_parent_and_owned_child_export_the_child_interface_only() {
    let nat = publish(
        &Environment::new(),
        crate::seed::nat_inductive_seed_declaration(),
    );
    let parent = record(
        &nat,
        "Parent",
        vec![],
        vec![local("value", c("Nat"), BinderInfo::Default)],
    );
    let rows = rows();
    let parent = register(&parent, &rows[..1]).unwrap();
    let child = record(
        &parent,
        "Child",
        vec![],
        vec![
            local("toParent", c("Parent"), BinderInfo::InstImplicit),
            local("extra", c("Nat"), BinderInfo::Default),
        ],
    );
    let child = register(&child, &rows[1..2]).unwrap();
    let exported = registrations(&parent, &child, MAX_NODES).unwrap();
    assert_eq!(exported.structures, rows[1..2]);
    assert_eq!(
        exported.projections,
        vec![
            projection("Child.toParent", "Child.mk", 0, 0, false),
            projection("Child.extra", "Child.mk", 0, 1, false),
        ]
    );
    assert_eq!(
        registrations(&parent, &child, exported.work).unwrap(),
        exported
    );
    assert_eq!(
        registrations(&parent, &child, exported.work - 1),
        Err(RecordError::ResourceLimit)
    );
}

#[test]
fn orphan_parent_rows_missing_native_parents_and_rewritten_prefixes_are_refused() {
    let raw = base();
    let rows = rows();
    let native = inheritance::register_parents(
        &raw,
        &[RecordParent {
            record: n("Child"),
            field: 0,
            parent: n("Parent"),
        }],
    )
    .unwrap();
    assert!(registrations(&Environment::new(), &native, MAX_NODES).is_err());

    let incomplete = register(&raw, &rows[1..2]).unwrap();
    assert!(
        registrations(&Environment::new(), &incomplete, MAX_NODES).is_err(),
        "an owned child cannot export a parent without an authored/imported interface"
    );

    let missing = raw
        .register_extension(descriptor())
        .unwrap()
        .push_extension_entry(&extension_name(), encode(&rows[1]).unwrap())
        .unwrap();
    assert!(registrations(&Environment::new(), &missing, MAX_NODES).is_err());

    let registered = register(&raw, &rows).unwrap();
    let rewritten = register(&raw, &[rows[1].clone(), rows[0].clone(), rows[2].clone()]).unwrap();
    assert!(registrations(&registered, &rewritten, MAX_NODES).is_err());
    assert!(registrations(&registered, &raw, MAX_NODES).is_err());
}

#[test]
fn malformed_inherited_payloads_and_foreign_descriptors_do_not_gain_validity() {
    let malformed = Environment::new()
        .register_extension(descriptor())
        .unwrap()
        .push_extension_entry(&extension_name(), vec![0])
        .unwrap();
    assert!(registrations(&malformed, &malformed, MAX_NODES).is_err());
    let mut foreign = descriptor();
    foreign.provenance = PayloadProvenance::Opaque;
    let malformed = Environment::new().register_extension(foreign).unwrap();
    assert!(registrations(&malformed, &malformed, MAX_NODES).is_err());

    let raw = base();
    let row = rows().remove(0);
    let duplicate = raw
        .register_extension(descriptor())
        .unwrap()
        .push_extension_entry(&extension_name(), encode(&row).unwrap())
        .unwrap()
        .push_extension_entry(&extension_name(), encode(&row).unwrap())
        .unwrap();
    assert_eq!(
        registrations(&Environment::new(), &duplicate, MAX_NODES),
        Err(RecordError::DuplicateField)
    );
}

#[test]
fn projection_class_origin_is_immutable_under_later_class_registration() {
    let parameter = local("A", Expr::sort(Level::one()), BinderInfo::Default);
    let carrier = Expr::fvar(parameter.id.clone());
    let function = Expr::forall_e(n("x"), carrier.clone(), carrier, BinderInfo::Default);
    let mut env = Environment::new();
    for (name, is_class) in [("Ordinary", false), ("DeclaredClass", true)] {
        let spec = RecordSpec {
            name: n(name),
            level_params: vec![],
            parameters: vec![parameter.clone()],
            fields: vec![local("run", function.clone(), BinderInfo::Default)],
            result_level: Level::one(),
            is_class,
        };
        env = descriptor_record(
            &env,
            &spec,
            &n(&format!("{name}.mk")),
            &[n(&format!("{name}.run"))],
        );
    }
    let expected = vec![
        projection("Ordinary.run", "Ordinary.mk", 1, 0, false),
        projection("DeclaredClass.run", "DeclaredClass.mk", 1, 0, true),
    ];
    assert_eq!(
        registrations(&Environment::new(), &env, MAX_NODES)
            .unwrap()
            .projections,
        expected
    );
    let classified = crate::instances::register_class(&env, &n("Ordinary")).unwrap();
    let classified = crate::instances::register_class(&classified, &n("DeclaredClass")).unwrap();
    assert!(env.has_same_declarations(&classified));
    assert_eq!(
        registrations(&Environment::new(), &classified, MAX_NODES)
            .unwrap()
            .projections,
        expected,
        "the receiver convention comes from generation, not the final class registry"
    );
}

#[test]
fn proof_projection_descriptors_retain_constructor_field_indices() {
    let parameter = local("P", Expr::sort(Level::zero()), BinderInfo::Default);
    let proposition = Expr::fvar(parameter.id.clone());
    let spec = RecordSpec {
        name: n("ProofClass"),
        level_params: vec![],
        parameters: vec![parameter],
        fields: vec![
            local("first", proposition.clone(), BinderInfo::Default),
            local("second", proposition, BinderInfo::Default),
        ],
        result_level: Level::zero(),
        is_class: true,
    };
    let env = descriptor_record(
        &Environment::new(),
        &spec,
        &n("ProofClass.mk"),
        &[n("ProofClass.first"), n("ProofClass.second")],
    );
    for name in ["ProofClass.first", "ProofClass.second"] {
        assert!(matches!(env.find(&n(name)), Some(ConstantInfo::Thm(_))));
    }
    let exported = registrations(&Environment::new(), &env, MAX_NODES).unwrap();
    assert_eq!(
        exported.projections,
        vec![
            projection("ProofClass.first", "ProofClass.mk", 1, 0, true),
            projection("ProofClass.second", "ProofClass.mk", 1, 1, true),
        ]
    );
    assert_eq!(
        registrations(&Environment::new(), &env, exported.work).unwrap(),
        exported
    );
    assert_eq!(
        registrations(&Environment::new(), &env, exported.work - 1),
        Err(RecordError::ResourceLimit)
    );
}

#[test]
fn private_projection_descriptors_use_authenticated_bodies_and_visible_names() {
    let nat = publish(
        &Environment::new(),
        crate::seed::nat_inductive_seed_declaration(),
    );
    let private = Name::num(n("_private.ProjectionMetadata"), 0);
    let constructor = private.append_core(&n("PublicRecord.mk"));
    let secret = private.append_core(&n("PublicRecord.secret"));
    let spec = RecordSpec {
        name: n("PublicRecord"),
        level_params: vec![],
        parameters: vec![],
        fields: vec![
            local("visible", c("Nat"), BinderInfo::Default),
            local("secret", c("Nat"), BinderInfo::Default),
        ],
        result_level: Level::one(),
        is_class: false,
    };
    let complete = descriptor_record(
        &nat,
        &spec,
        &constructor,
        &[n("PublicRecord.visible"), secret.clone()],
    );
    let visible_projection = ProjectionFunction {
        declaration: n("PublicRecord.visible"),
        constructor: constructor.clone(),
        num_params: 0,
        field_index: 0,
        from_class: false,
    };
    assert_eq!(
        registrations(&nat, &complete, MAX_NODES)
            .unwrap()
            .projections,
        vec![
            visible_projection.clone(),
            ProjectionFunction {
                declaration: secret.clone(),
                constructor: constructor.clone(),
                num_params: 0,
                field_index: 1,
                from_class: false,
            },
        ]
    );
    let mut public = Environment::new();
    for (name, _) in complete.constants() {
        if name != &secret {
            public = public.with_entry(complete.entry(name).unwrap()).unwrap();
        }
    }
    let public = replay_journals(public, &complete, |_| {});
    assert!(registrations(&nat, &public, MAX_NODES).is_err());
    let bound = public.with_imported_metadata_validation(&complete);
    let exported = registrations(&nat, &bound, MAX_NODES).unwrap();
    assert_eq!(exported.projections, vec![visible_projection]);
    assert!(bound.contains(&constructor));
    assert!(!bound.contains(&secret));
    assert_eq!(exported.structures[0].fields[1].projection, secret);
    assert_eq!(
        registrations(&nat, &bound, exported.work).unwrap(),
        exported
    );
    assert_eq!(
        registrations(&nat, &bound, exported.work - 1),
        Err(RecordError::ResourceLimit)
    );
}

#[test]
fn admitted_receiver_style_changes_do_not_gain_projection_metadata() {
    let nat = publish(
        &Environment::new(),
        crate::seed::nat_inductive_seed_declaration(),
    );
    let spec = RecordSpec {
        name: n("Altered"),
        level_params: vec![],
        parameters: vec![],
        fields: vec![local("value", c("Nat"), BinderInfo::Default)],
        result_level: Level::one(),
        is_class: false,
    };
    let row = StructureEntry {
        name: n("Altered"),
        fields: vec![StructureField {
            name: n("value"),
            projection: n("Altered.value"),
            subobject: None,
            binder_info: BinderInfo::Default,
        }],
        parents: vec![],
    };
    for (type_style, value_style) in [
        (BinderInfo::Default, BinderInfo::InstImplicit),
        (BinderInfo::Implicit, BinderInfo::Implicit),
        (BinderInfo::StrictImplicit, BinderInfo::StrictImplicit),
    ] {
        let mut env = nat.clone();
        let declarations = record_declarations_with_member_names(
            &spec,
            &n("Altered.mk"),
            &[n("Altered.value")],
            RecordBudget::default(),
        )
        .unwrap();
        for mut declaration in declarations {
            if let Declaration::Defn(definition) = &mut declaration {
                let ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    ..
                } = definition.base.type_.node()
                else {
                    panic!("the generated projection has one receiver");
                };
                definition.base.type_ = Expr::forall_e(
                    binder_name.clone(),
                    binder_type.clone(),
                    body.clone(),
                    type_style,
                );
                let ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    ..
                } = definition.value.node()
                else {
                    panic!("the generated projection body has one receiver");
                };
                definition.value = Expr::lam(
                    binder_name.clone(),
                    binder_type.clone(),
                    body.clone(),
                    value_style,
                );
            }
            // Binder conventions do not grant kernel authority: the changed
            // declarations must still pass the ordinary admission path.
            env = publish(&env, declaration);
        }
        let env = register(&env, std::slice::from_ref(&row)).unwrap();
        assert!(
            ImportedStructures::read(&env)
                .unwrap()
                .get(&row.name)
                .is_some()
        );
        let before = env.logical_root(&KVMap::new());
        assert_eq!(
            registrations(&nat, &env, MAX_NODES),
            Err(RecordError::InvalidTelescope)
        );
        assert_eq!(env.logical_root(&KVMap::new()), before);
    }
}
