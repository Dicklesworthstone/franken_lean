//! Synthetic ownership graphs around declarations admitted through the ordinary
//! source checker. Artifact decoding and actual receipts are tested separately.
#![cfg(test)]
use super::*;

fn n(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn admitted() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits).unwrap().into_complete().unwrap()
        .check_source_files(
            &[b"structure Parent where\n  value : Nat\nstructure Child extends Parent where\n  extra : Nat\nstructure Foreign where\n  value : Nat"],
            &KVMap::new(), SourceCheckLimits::new(limits),
        ).unwrap().into_complete().unwrap().engine
}

fn interface(engine: &Engine, record: &str) -> Vec<ConstantInfo> {
    let prefix = format!("{record}.");
    engine
        .environment
        .constants()
        .filter(|(name, _)| {
            let name = name.to_display_string();
            name == record || name.starts_with(&prefix)
        })
        .map(|(_, info)| info.clone())
        .collect()
}

fn checked_module(
    engine: &Engine,
    name: &str,
    imports: &[&str],
    constants: Vec<ConstantInfo>,
) -> CheckedOleanModule {
    let root = engine.logical_root(&KVMap::new());
    CheckedOleanModule {
        name: n(name),
        decoded: DecodedOlean {
            header: OleanHeader {
                version: OLEAN_ACCEPTED_VERSIONS[0],
                flags: 0,
                lean_version: OLEAN_PIN_TAG.into(),
                githash: OLEAN_PIN_COMMIT.into(),
                base_addr: 0,
            },
            walk: OleanWalkReport::default(),
            module: OleanModuleData {
                is_module: false,
                imports: imports
                    .iter()
                    .map(|name| OleanModuleImport {
                        module: n(name),
                        import_all: false,
                        is_exported: true,
                        is_meta: false,
                    })
                    .collect(),
                const_names: constants
                    .iter()
                    .map(|info| info.name().to_display_string())
                    .collect(),
                constants: constants.len() as u64,
                extra_const_names: 0,
                extensions: vec![],
            },
            constants,
            independent: IndependentReading::Unread(
                "synthetic metadata graph; no artifact claim".into(),
            ),
            companion_parts_loaded: false,
        },
        base_logical_root: root,
        result_logical_root: root,
        declarations: vec![],
    }
}

fn graph(engine: &Engine, parent_import: bool) -> CheckedOleanSet {
    CheckedOleanSet {
        engine: engine.clone(),
        base_logical_root: engine.logical_root(&KVMap::new()),
        result_logical_root: engine.logical_root(&KVMap::new()),
        modules: vec![
            checked_module(engine, "ParentModule", &[], interface(engine, "Parent")),
            checked_module(
                engine,
                "ChildModule",
                if parent_import {
                    &["ParentModule"]
                } else {
                    &[]
                },
                interface(engine, "Child"),
            ),
            checked_module(engine, "SiblingModule", &[], interface(engine, "Foreign")),
        ],
    }
}

fn row(engine: &Engine) -> metadata::StructureEntry {
    let ConstantInfo::Induct(family) = engine.environment.find(&n("Child")).unwrap() else {
        panic!("checked child")
    };
    let ConstantInfo::Ctor(ctor) = engine.environment.find(&family.ctors[0]).unwrap() else {
        panic!("checked child constructor")
    };
    let mut cursor = &ctor.base.type_;
    for _ in 0..ctor.num_params {
        let ExprNode::ForallE { body, .. } = cursor.node() else {
            panic!("parameters")
        };
        cursor = body;
    }
    let mut fields = Vec::new();
    for _ in 0..ctor.num_fields {
        let ExprNode::ForallE {
            binder_name,
            binder_info,
            body,
            ..
        } = cursor.node()
        else {
            panic!("fields")
        };
        fields.push(metadata::StructureField {
            name: binder_name.clone(),
            projection: n("Child").append_core(binder_name),
            subobject: (binder_name == &n("toParent")).then(|| n("Parent")),
            binder_info: *binder_info,
            auto_param: None,
        });
        cursor = body;
    }
    metadata::StructureEntry {
        name: n("Child"),
        fields,
        parents: vec![metadata::StructureParent {
            name: n("Parent"),
            subobject: true,
            projection: n("Child.toParent"),
        }],
    }
}

fn limits() -> SourceOleanImportLimits {
    SourceOleanImportLimits::new(OleanCheckLimits::new(
        1024 * 1024,
        Budget::for_stack_bytes(2 * 1024 * 1024),
    ))
}

#[test]
fn structure_parent_targets_require_the_declared_closure_or_exact_original_environment() {
    let engine = admitted();
    let before = engine.logical_root(&KVMap::new());
    let row = row(&engine);
    for present in [true, false] {
        let checked = graph(&engine, present);
        let mut scopes = Scopes::new(&checked, std::slice::from_ref(&row), 100_000).unwrap();
        let result = scopes.validate(
            &checked,
            &Environment::new(),
            &engine.environment,
            1,
            &row.name,
            &n("Parent"),
        );
        assert_eq!(result.is_ok(), present);
        if let Err(error) = result {
            assert!(matches!(
                error,
                SourceOleanImportError::Metadata {
                    reason: "a structure parent is outside this module's checked import closure",
                    ..
                }
            ));
        }
        // A checked declaration already present before this import remains a
        // legitimate origin independently of the supplied sibling graph.
        scopes
            .validate(
                &checked,
                &engine.environment,
                &engine.environment,
                1,
                &row.name,
                &n("Parent"),
            )
            .unwrap();
    }
    let checked = graph(&engine, true);
    let mut other = row.clone();
    other.parents[0].name = n("Foreign");
    let mut scopes = Scopes::new(&checked, &[other], 100_000).unwrap();
    assert!(
        scopes
            .validate(
                &checked,
                &Environment::new(),
                &engine.environment,
                1,
                &row.name,
                &n("Foreign"),
            )
            .is_err(),
        "a simultaneously checked unrelated sibling is not an import"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn structure_interface_ownership_is_exact_and_failure_does_not_publish_a_prefix() {
    let engine = admitted();
    let before = engine.logical_root(&KVMap::new());
    let structures_before =
        fln_elab::records::imported::ImportedStructures::read(&engine.environment).unwrap();
    assert!(
        structures_before.get(&n("Child")).is_some(),
        "the ordinary source checker must publish its structure metadata"
    );
    let checked = graph(&engine, true);
    let row = row(&engine);
    let mut scopes = Scopes::new(&checked, std::slice::from_ref(&row), 100_000).unwrap();
    let mut rows = vec![row.clone()].into_iter();
    let accepted = module(
        &checked,
        &Environment::new(),
        &engine.environment,
        1,
        1,
        &mut rows,
        &mut scopes,
        &limits(),
        None,
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(accepted.len(), 1);
    assert_eq!(accepted[0].name, n("Child"));
    let registered = fln_elab::records::imported::register(&engine.environment, &accepted).unwrap();
    assert!(
        fln_elab::records::imported::ImportedStructures::read(&registered)
            .unwrap()
            .get(&n("Child"))
            .is_some()
    );

    let constants = interface(&engine, "Child");
    let mut owners = AttributeOwners::new(&constants, 4, 100, 100).unwrap();
    validate_owner(
        &mut owners,
        &engine.environment,
        &n("ChildModule"),
        &n("Child.extra"),
        &mut 100_000,
    )
    .unwrap();
    assert!(
        validate_owner(
            &mut owners,
            &engine.environment,
            &n("ChildModule"),
            &n("Child.extra"),
            &mut 100_000
        )
        .is_err()
    );
    assert!(
        validate_owner(
            &mut owners,
            &engine.environment,
            &n("ChildModule"),
            &n("Parent.value"),
            &mut 100_000
        )
        .is_err()
    );

    let mut changed = constants.clone();
    let ConstantInfo::Defn(projection) = changed
        .iter_mut()
        .find(|info| info.name() == &n("Child.extra"))
        .unwrap()
    else {
        panic!("checked projection")
    };
    projection.hints = fln_env::constants::ReducibilityHints::Opaque;
    let mut owners = AttributeOwners::new(&changed, 1, 100, 100).unwrap();
    assert!(
        validate_owner(
            &mut owners,
            &engine.environment,
            &n("ChildModule"),
            &n("Child.extra"),
            &mut 100_000
        )
        .is_err()
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
    assert_eq!(
        fln_elab::records::imported::ImportedStructures::read(&engine.environment).unwrap(),
        structures_before,
    );
}

#[test]
fn structure_metadata_work_limits_and_cancellation_remain_nonanswers() {
    let engine = admitted();
    let before = engine.logical_root(&KVMap::new());
    let checked = graph(&engine, true);
    let row = row(&engine);
    assert!(
        Scopes::new(&checked, std::slice::from_ref(&row), 0)
            .err()
            .unwrap()
            .metadata_resource_exhausted()
    );
    let mut scopes = Scopes::new(&checked, std::slice::from_ref(&row), 100_000).unwrap();
    scopes.work_left = 0;
    assert!(
        scopes
            .validate(
                &checked,
                &Environment::new(),
                &engine.environment,
                1,
                &row.name,
                &n("Parent"),
            )
            .unwrap_err()
            .metadata_resource_exhausted()
    );
    let constants = interface(&engine, "Child");
    let mut owners = AttributeOwners::new(&constants, 1, 100, 100).unwrap();
    assert!(
        validate_owner(
            &mut owners,
            &engine.environment,
            &n("ChildModule"),
            &n("Child.extra"),
            &mut 0,
        )
        .unwrap_err()
        .metadata_resource_exhausted()
    );

    struct Cancelled;
    impl CancellationProbe for Cancelled {
        fn is_cancelled(&self) -> bool {
            true
        }
    }
    let mut scopes = Scopes::new(&checked, std::slice::from_ref(&row), 100_000).unwrap();
    let mut rows = vec![row].into_iter();
    assert!(matches!(
        module(
            &checked,
            &Environment::new(),
            &engine.environment,
            1,
            1,
            &mut rows,
            &mut scopes,
            &limits(),
            Some(&Cancelled)
        )
        .unwrap(),
        Outcome::Inconclusive(_),
    ));
    assert_eq!(
        rows.len(),
        1,
        "cancellation does not consume a metadata row"
    );
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
