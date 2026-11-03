use super::super::tests::{base, c, local, n, publish, record, rows};
use super::*;

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
