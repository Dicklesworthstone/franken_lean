//! Full computed-field validation charges work it performs, while keeping its
//! declaration, cached-layout and generated-adapter checks at both boundaries.
use super::*;
use fln_elab::computed_fields::{self as model, ComputedFieldError};
use fln_elab::records::RecordBudget;

fn changed_declaration(original: &Environment, changed: ConstantInfo) -> Environment {
    let mut env = Environment::new();
    for (key, _) in original.constants() {
        if key != changed.name() {
            env = env.with_entry(original.entry(key).unwrap()).unwrap();
        }
    }
    env = env.add_decl(changed).unwrap();
    for (journal, state) in original.extensions() {
        env = env.register_extension(state.descriptor.clone()).unwrap();
        for entry in state.entries() {
            env = env
                .push_extension_entry(journal, entry.payload.clone())
                .unwrap();
        }
    }
    env
}

#[test]
fn computed_validation_meters_regeneration_and_rejects_altered_adapters() {
    on_stack(|| {
        let engine = checked(
            &Engine::builder().build_empty(),
            &format!("{PRIMITIVES}{CAST}{FLAG}"),
        );
        let original = engine.logical_root(&KVMap::new());
        let env = engine.environment();
        let family = name("Flag");
        let phase = RecordBudget::default();
        let aggregate = SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())).max_work;

        let (families, claim_work) = model::families_with_work(env, phase).unwrap();
        assert_eq!(families.as_slice(), std::slice::from_ref(&family));
        assert!(claim_work > 0);
        assert_eq!(
            model::families_with_work(
                env,
                RecordBudget {
                    max_nodes: claim_work,
                    ..phase
                },
            )
            .unwrap(),
            (families, claim_work),
        );
        assert_eq!(
            model::families_with_work(
                env,
                RecordBudget {
                    max_nodes: claim_work - 1,
                    ..phase
                },
            )
            .unwrap_err(),
            ComputedFieldError::ResourceLimit,
        );

        let expected = model::validated_family(env, &family, limits().kernel, phase)
            .unwrap()
            .unwrap();
        let (generated, used) =
            model::validated_family_with_work(env, &family, limits().kernel, phase, aggregate)
                .unwrap();
        assert_eq!(generated, Some(expected.clone()));
        assert!(
            used > claim_work,
            "cached declarations and bodies must be regenerated"
        );
        assert_eq!(
            model::validated_family_with_work(env, &family, limits().kernel, phase, used).unwrap(),
            (Some(expected), used),
        );
        assert_eq!(
            model::validated_family_with_work(env, &family, limits().kernel, phase, used - 1)
                .unwrap_err(),
            ComputedFieldError::ResourceLimit,
        );
        assert_eq!(
            model::validated_family_with_work(
                env,
                &family,
                limits().kernel,
                RecordBudget {
                    max_nodes: 0,
                    ..phase
                },
                aggregate,
            )
            .unwrap_err(),
            ComputedFieldError::ResourceLimit,
            "an ample aggregate budget cannot bypass the independent phase bound",
        );

        // This body has the adapter's type but constructs the logical layout.
        // Keeping its type, safety and journal claims cannot authorize the
        // replacement of the regenerated cached constructor conversion.
        let Some(ConstantInfo::Defn(mut adapter)) = env.find(&name("Flag.on._override")).cloned()
        else {
            panic!("missing generated cached-constructor adapter");
        };
        let changed = Expr::const_(name("Flag.on"), Vec::new());
        assert_ne!(adapter.value, changed);
        adapter.value = changed;
        let altered = changed_declaration(env, ConstantInfo::Defn(adapter));
        assert_eq!(
            model::validated_family_with_work(
                &altered, &family, limits().kernel, phase, aggregate,
            ).unwrap_err(),
            ComputedFieldError::InvalidInventory,
        );
        assert_eq!(
            model::validated_family(&altered, &family, limits().kernel, phase).unwrap_err(),
            ComputedFieldError::InvalidInventory,
        );
        assert_eq!(engine.logical_root(&KVMap::new()), original);
    });
}

#[test]
fn small_computed_family_artifacts_preserve_checked_behavior_with_bounded_work() {
    on_stack(|| {
        let source = format!("prelude\n{PRIMITIVES}{CAST}{FLAG}");
        let initial = Engine::builder().build_empty();
        let module = name("ComputedWork");
        let mut module_limits = SourceModuleCheckLimits::new(SourceCheckLimits::new(limits()));
        // This small artifact fits this ordinary bound both before and after
        // consumed-work accounting; complete generation and import stay checked.
        module_limits.max_work = 32_000;
        let built = initial
            .compile_source_modules(
                &[SourceModuleInput {
                    name: &module,
                    source: source.as_bytes(),
                }],
                &module,
                &KVMap::new(),
                module_limits,
                OleanWriteBudget::default(),
            )
            .unwrap_or_else(|error| panic!("bounded computed artifact: {error:?}"))
            .into_complete()
            .unwrap();
        assert!(initial.environment().is_empty());
        assert_eq!(built.artifacts.len(), 1);
        let artifact = &built.artifacts[0];
        let blocks = fln_olean::region::OleanView::parse(&artifact.bytes)
            .unwrap()
            .extension_payloads(OleanWalkBudget::default(), STACK)
            .unwrap();
        let metadata = fln_olean::source_extensions::decode(&blocks, Default::default()).unwrap();
        assert_eq!(metadata.computed_fields, [name("Flag.value")]);
        assert_eq!(metadata.implemented_by.len(), 4);
        let companions = artifact.companions.as_ref();
        let fresh = Engine::builder().build_empty();
        let loaded = fresh
            .import_olean_modules_for_source(
                &[OleanModuleInput {
                    name: &artifact.name,
                    artifact: &artifact.bytes,
                    server_artifact: companions.map(|parts| parts.server.as_slice()),
                    private_artifact: companions.map(|parts| parts.private.as_slice()),
                }],
                std::slice::from_ref(&artifact.name),
                &KVMap::new(),
                SourceOleanImportLimits::new(OleanCheckLimits::new(STACK, limits().kernel)),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert!(fresh.environment().is_empty());
        assert_eq!(loaded.modules[0].computed_fields, 1);
        let expected = model::validated_family(
            built.checked.checked.engine.environment(),
            &name("Flag"),
            limits().kernel,
            RecordBudget::default(),
        )
        .unwrap()
        .unwrap();

        for engine in [&built.checked.checked.engine, &loaded.engine] {
            assert_bundle(engine.environment(), "Flag", "value", &["off", "on"]);
            let (recovered, _) = model::validated_family_with_work(
                engine.environment(),
                &name("Flag"),
                limits().kernel,
                RecordBudget::default(),
                module_limits.max_work,
            )
            .unwrap();
            assert_eq!(recovered, Some(expected.clone()));
            let original = engine.logical_root(&KVMap::new());
            checked(
                engine,
                "theorem selected (P : Bool -> Prop) (h : P Bool.true) : P (Flag.value (Flag.on Bool.true)) := h",
            );
            let error = match engine.check_source_files(
                &[b"theorem rejected (P : Bool -> Prop) (h : P Bool.false) : P (Flag.value (Flag.on Bool.true)) := h"],
                &KVMap::new(),
                module_limits.source,
            ) {
                Err(error) => error,
                Ok(_) => panic!("the checked computed getter must not change Bool.true to Bool.false"),
            };
            assert_eq!(error.disposition(), ("elaboration", false, 1));
            assert_eq!(engine.logical_root(&KVMap::new()), original);
            for uncommitted in ["selected", "rejected"] {
                assert!(!engine.environment().contains(&name(uncommitted)));
            }
        }
    });
}
