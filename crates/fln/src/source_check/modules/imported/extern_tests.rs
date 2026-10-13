use super::*;
use fln_elab::externs::{ExternEntry, ExternTable};

fn n(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn admitted() -> Engine {
    let limits = EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024));
    Engine::with_source_seed(limits)
        .unwrap()
        .into_complete()
        .unwrap()
        .check_source_files(
            &[b"def owned : Nat := 7\ndef sibling : Nat := 8"],
            &KVMap::new(),
            SourceCheckLimits::new(limits),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine
}

#[test]
fn extern_metadata_requires_the_exact_checked_owner_and_unique_module_row() {
    let engine = admitted();
    let env = &engine.environment;
    let root = engine.logical_root(&KVMap::new());
    let owned = [env.find(&n("owned")).unwrap().clone()];
    let mut owners = AttributeOwners::new(&owned, 4, 4, 4).unwrap();
    owners.validate(env, &n("OwnModule"), &n("owned")).unwrap();
    assert!(matches!(
        owners.validate(env, &n("OwnModule"), &n("owned")),
        Err(SourceOleanImportError::Metadata {
            reason: "duplicate attribute for one module declaration",
            ..
        })
    ));
    for declaration in [n("sibling"), n("missing")] {
        assert!(matches!(
            owners.validate(env, &n("OwnModule"), &declaration),
            Err(SourceOleanImportError::Metadata {
                reason: "an attribute does not belong to this module's checked declarations",
                ..
            })
        ));
    }
    let mut different = owned.clone();
    let ConstantInfo::Defn(definition) = &mut different[0] else {
        panic!("checked definition")
    };
    definition.value = fln_core::expr::Expr::const_(n("Nat.zero"), vec![]);
    assert!(matches!(
        AttributeOwners::new(&different, 1, 4, 4).unwrap().validate(
            env,
            &n("OwnModule"),
            &n("owned")
        ),
        Err(SourceOleanImportError::Metadata {
            reason: "an attribute owner differs from its active admitted declaration",
            ..
        })
    ));
    let mut missing_active = AttributeOwners::new(&owned, 1, 4, 4).unwrap();
    assert!(
        missing_active
            .validate(&Environment::new(), &n("OwnModule"), &n("owned"))
            .is_err()
    );
    assert_eq!(engine.logical_root(&KVMap::new()), root);
}

#[test]
fn extern_owner_allocations_and_registry_limits_remain_resource_nonanswers() {
    let engine = admitted();
    let owned = [engine.environment.find(&n("owned")).unwrap().clone()];
    for error in [
        AttributeOwners::new(&owned, 1, 0, 1).err().unwrap(),
        AttributeOwners::new(&owned, 2, 1, 1).err().unwrap(),
        extern_error(
            &n("Module"),
            &n("owned"),
            fln_elab::externs::ExternError::Limit,
        ),
    ] {
        assert!(error.metadata_resource_exhausted(), "{error}");
    }
    let malformed = extern_error(
        &n("Module"),
        &n("owned"),
        fln_elab::externs::ExternError::Malformed,
    );
    assert!(!malformed.metadata_resource_exhausted());
    let duplicate = [owned[0].clone(), owned[0].clone()];
    assert!(matches!(
        AttributeOwners::new(&duplicate, 1, 2, 1),
        Err(SourceOleanImportError::Internal(_))
    ));
}

#[test]
fn extern_activation_matches_per_call_registration_without_dropping_variants() {
    let engine = admitted();
    let entries: Vec<ExternEntry> = vec![
        metadata::ExternEntry::Adhoc {
            backend: n("custom"),
        },
        metadata::ExternEntry::Inline {
            backend: Name::anonymous(),
            pattern: "λ $0".into(),
        },
        metadata::ExternEntry::Standard {
            backend: n("all"),
            symbol: "lean_example".into(),
        },
        metadata::ExternEntry::Opaque,
    ]
    .into_iter()
    .map(extern_entry)
    .collect();
    fn activate<R: Registrar>(env: &Environment, entries: Vec<ExternEntry>) -> Environment {
        R::new(env.clone())
            .register_extern(&n("owned"), entries)
            .unwrap()
            .register_extern(&n("sibling"), vec![])
            .unwrap()
            .finish()
            .unwrap()
    }
    let batched =
        activate::<instances::imported::ImportActivation>(&engine.environment, entries.clone());
    let per_call = activate::<super::tests::Sequential>(&engine.environment, entries.clone());
    assert_eq!(batched, per_call);
    assert_eq!(
        batched.logical_root(&KVMap::new()),
        per_call.logical_root(&KVMap::new())
    );
    let table = ExternTable::read(&batched).unwrap();
    assert_eq!(table.get(&n("owned")), Some(entries.as_slice()));
    assert_eq!(table.get(&n("sibling")), Some([].as_slice()));
    assert_eq!(table.get(&n("absent")), None);
    assert!(ExternTable::read(&engine.environment).unwrap().is_empty());
}
