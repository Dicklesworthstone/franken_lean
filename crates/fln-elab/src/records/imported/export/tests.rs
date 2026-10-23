use super::super::tests::{base, c, local, n, publish, record, rows};
use super::*;

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
