use super::*;

fn fixture() -> (RegisteredMacros, CheckedOleanModule) {
    let z = checked(
        "Z",
        &[owner("Z.first"), owner("Z.last"), owner("Z.scoped")],
        &[],
    );
    let a = checked(
        "A",
        &[
            owner("A.first"),
            owner("A.last"),
            owner("A.scoped"),
            owner("A.only"),
        ],
        &[],
    );
    let z_rows = journal(&[
        ("choice", "Z.first", None),
        ("choice", "Z.last", None),
        ("choice", "Z.scoped", Some("Shared")),
    ]);
    let a_rows = journal(&[
        ("choice", "A.first", None),
        ("choice", "A.last", None),
        ("choice", "A.scoped", Some("Shared")),
        ("choice", "A.only", Some("OnlyA")),
    ]);
    let registry = prepare(
        &[
            MacroRegistrationModule {
                checked: &z,
                extensions: &z_rows,
            },
            MacroRegistrationModule {
                checked: &a,
                extensions: &a_rows,
            },
        ],
        &code(vec![
            function("Z.first", Behavior::Unsupported),
            function("Z.last", Behavior::Identity),
            function("Z.scoped", Behavior::Identity),
            function("A.first", Behavior::Identity),
            function("A.last", Behavior::Unsupported),
            function("A.scoped", Behavior::Identity),
            function("A.only", Behavior::Identity),
        ]),
    );
    (registry, z)
}

fn selected(registry: &RegisteredMacros) -> Vec<Name> {
    registry.declarations(&name("choice")).cloned().collect()
}

#[test]
fn projection_reorders_imports_and_preserves_every_within_module_tie() {
    let (registry, _) = fixture();
    assert_eq!(
        selected(&registry),
        ["A.last", "A.first", "Z.last", "Z.first"].map(name)
    );
    let projected = registry.project_imports(&[name("A"), name("Z")]).unwrap();
    assert_eq!(
        selected(&projected),
        ["Z.last", "Z.first", "A.last", "A.first"].map(name)
    );
    let report = run(&projected, MacroDispatchLimits::default());
    assert!(matches!(report.outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded { declaration, .. }))
        if declaration == name("Z.last")));
    assert_eq!(report.attempts.len(), 1);
    let original = run(&registry, MacroDispatchLimits::default());
    assert!(matches!(original.outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded { declaration, .. }))
        if declaration == name("A.first")));
    assert_eq!(original.attempts.len(), 2);
}

#[test]
fn projection_discards_sibling_owners_and_lexical_activation() {
    let (registry, z) = fixture();
    let activated = registry
        .activate_scoped(&name("Shared"))
        .unwrap()
        .activate_scoped(&name("OnlyA"))
        .unwrap();
    let projected = activated.project_imports(&[name("Z")]).unwrap();
    assert_eq!(selected(&projected), ["Z.last", "Z.first"].map(name));
    assert_eq!(
        projected.scoped_namespaces().cloned().collect::<Vec<_>>(),
        vec![name("Shared")]
    );
    let reopened = projected.activate_scoped(&name("Shared")).unwrap();
    assert_eq!(
        selected(&reopened),
        ["Z.scoped", "Z.last", "Z.first"].map(name)
    );
    assert_eq!(
        selected(&projected.activate_scoped(&name("OnlyA")).unwrap()),
        selected(&projected)
    );

    // This is an owner-binding unit fixture. The module graph tests separately
    // use real artifact admission to establish the import receipt.
    let mut engine = crate::Engine::from_environment(environment(&[&z]));
    engine.imported_modules = Arc::new(BTreeSet::from([name("Z")]));
    projected.validate_source_engine(&engine).unwrap();
    assert!(registry.validate_source_engine(&engine).is_err());
    let empty = activated.project_imports(&[]).unwrap();
    assert!(selected(&empty).is_empty());
    assert_eq!(empty.scoped_namespaces().count(), 0);
    empty
        .validate_source_engine(&crate::Engine::from_environment(Environment::new()))
        .unwrap();
}

#[test]
fn projection_rejects_unknown_duplicate_missing_and_reversed_imports() {
    let dependency = checked("Dependency", &[], &[]);
    let consumer = checked("Consumer", &[owner("Consumer.rule")], &["Dependency"]);
    let rows = journal(&[("choice", "Consumer.rule", None)]);
    let registry = prepare(
        &[
            MacroRegistrationModule {
                checked: &dependency,
                extensions: &[],
            },
            MacroRegistrationModule {
                checked: &consumer,
                extensions: &rows,
            },
        ],
        &code(vec![function("Consumer.rule", Behavior::Identity)]),
    );
    assert!(matches!(
        registry.project_imports(&[name("Unknown")]),
        Err(MacroRegistrationError::Owner { .. })
    ));
    assert!(matches!(
        registry.project_imports(&[name("Dependency"), name("Dependency")]),
        Err(MacroRegistrationError::DuplicateModule(_))
    ));
    assert!(matches!(
        registry.project_imports(&[name("Consumer")]),
        Err(MacroRegistrationError::MissingImport { .. })
    ));
    assert!(matches!(
        registry.project_imports(&[name("Consumer"), name("Dependency")]),
        Err(MacroRegistrationError::ImportOrder { .. })
    ));
    let projected = registry
        .project_imports(&[name("Dependency"), name("Consumer")])
        .unwrap();
    assert_eq!(selected(&projected), vec![name("Consumer.rule")]);
}
