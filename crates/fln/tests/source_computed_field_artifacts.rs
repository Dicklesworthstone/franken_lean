//! Computed fields retain checked logic, complete cached representations, and
//! persistent compiler metadata across the ordinary source/artifact boundary.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::source_check::modules::{SourceModuleBuild, SourceModuleCheckLimits};
use fln::*;
use fln_elab::computed_fields::tags as computed_fields;
use fln_elab::implemented_by::ImplementedByTable;
use std::collections::BTreeSet;

#[path = "source_computed_field_artifacts/pin.rs"]
mod pin;

#[path = "source_computed_field_artifacts/work.rs"]
mod work;

const STACK: usize = 16 << 20;
const CAST: &str = "unsafe axiom unsafeCast.{u, v} {A : Sort u} {B : Sort v} (a : A) : B\n";
const PRIMITIVES: &str = "inductive PUnit where | unit\ninductive Bool where | false | true\n";
const TREE: &str = r#"inductive Tree where
  | leaf
  | branch (value : Nat) (tail : Tree)
with
  @[computed_field, inline] sum : Tree → Nat
    | .leaf => 0
    | .branch value tail => value + tail.sum
"#;
const FLAG: &str = r#"inductive Flag where
  | off
  | on (value : Bool)
with
  @[computed_field] value : Flag → Bool
    | .off => Bool.false
    | .on value => value
"#;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn limits() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}

fn on_stack(body: impl FnOnce() + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(scope, body)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn checked(base: &Engine, source: &str) -> Engine {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(limits()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
}

fn seed() -> Engine {
    let base = Engine::with_source_seed(limits())
        .unwrap()
        .into_complete()
        .unwrap();
    // The bounded seed has no unsafeCast. Its ordinary unsafe axiom is enough
    // to check adapter types; this fixture never grants it a runtime primitive.
    checked(&base, CAST)
}

fn assert_bundle(env: &Environment, family: &str, field: &str, ctors: &[&str]) {
    let field_name = name(&format!("{family}.{field}"));
    assert!(
        computed_fields::read_tags(env)
            .unwrap()
            .contains(&field_name)
    );
    assert!(
        fln_elab::noncomputable::read(env)
            .unwrap()
            .contains(&field_name)
    );
    let table = ImplementedByTable::read(env).unwrap();
    for original in ctors
        .iter()
        .map(|ctor| format!("{family}.{ctor}"))
        .chain([format!("{family}.casesOn"), format!("{family}.{field}")])
    {
        let original = name(&original);
        let implementation = Name::str(original.clone(), "_override");
        assert_eq!(table.get(&original), Some(&implementation));
        let Some(ConstantInfo::Defn(adapter)) = env.find(&implementation) else {
            panic!("missing adapter {implementation:?}")
        };
        assert_eq!(adapter.safety, fln_env::constants::DefinitionSafety::Unsafe);
        assert!(!env.is_assumed(&implementation));
    }
    assert!(
        fln_elab::aux_recursors::AuxRecursors::read(env)
            .unwrap()
            .contains(&name(&format!("{family}._impl.casesOn")))
    );
}

// The ordinary terminating mutual elaborator requires Prelude's checked
// infrastructure, which the minimal source seed deliberately omits. The pin
// oracle calls these checks using its retained real Prelude import, with the
// ordinary source budget and without another heavyweight import.
fn assert_recursive_computed_field_bundle(base: &Engine) {
    let root = base.logical_root(&KVMap::new());
    let batch = base
        .admit_source_command(TREE.as_bytes(), &KVMap::new(), limits())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(base.logical_root(&KVMap::new()), root);
    assert_eq!(batch.base_logical_root, root);
    assert_eq!(
        batch.result_logical_root,
        batch.engine.logical_root(&KVMap::new())
    );
    assert_bundle(
        batch.engine.environment(),
        "Tree",
        "sum",
        &["leaf", "branch"],
    );
    let Some(ConstantInfo::Ctor(cached)) =
        batch.engine.environment().find(&name("Tree.branch._impl"))
    else {
        panic!("missing cached constructor")
    };
    assert_eq!(cached.num_fields, 3, "cache precedes both original fields");
    let mut cursor = cached.base.type_.clone();
    let mut types = Vec::new();
    while let ExprNode::ForallE {
        binder_type, body, ..
    } = cursor.node()
    {
        types.push(binder_type.clone());
        cursor = body.clone();
    }
    assert_eq!(
        types,
        ["Nat", "Nat", "Tree"].map(|value| Expr::const_(name(value), vec![]))
    );
    assert_eq!(cursor, Expr::const_(name("Tree._impl"), vec![]));
    let Some(ConstantInfo::Ctor(leaf)) = batch.engine.environment().find(&name("Tree.leaf._impl"))
    else {
        panic!("missing nullary cached constructor")
    };
    assert_eq!(leaf.num_fields, 0, "nullary constructors carry no cache");
    let proved = checked(
        &batch.engine,
        "theorem sum_is_42 : Tree.sum (.branch 12 (.branch 30 .leaf)) = 42 := rfl\n",
    );
    assert!(matches!(
        proved.environment().find(&name("sum_is_42")),
        Some(ConstantInfo::Thm(_))
    ));
    assert!(!base.environment().contains(&name("Tree")));
}

fn assert_mutual_computed_field_order(base: &Engine) {
    let source = r#"inductive MutualCache where
  | leaf
  | branch (value : Nat) (tail : MutualCache)
with
  @[computed_field, inline] zed : MutualCache → Nat
    | .leaf => 0
    | .branch value tail => Nat.add value tail.alpha
  @[computed_field] alpha : MutualCache → Nat
    | .leaf => 1
    | .branch _ tail => Nat.add 1 tail.zed
"#;
    let engine = checked(base, source);
    let environment = engine.environment();
    for field in ["zed", "alpha"] {
        assert_bundle(environment, "MutualCache", field, &["leaf", "branch"]);
    }
    let model = fln_elab::computed_fields::validated_family(
        environment,
        &name("MutualCache"),
        limits().kernel,
        fln_elab::records::RecordBudget::default(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(
        model
            .fields
            .iter()
            .map(|field| field.name.clone())
            .collect::<Vec<_>>(),
        [name("MutualCache.zed"), name("MutualCache.alpha")],
        "source declaration order determines cache slots"
    );
    assert_eq!(model.inline_fields, [name("MutualCache.zed")]);
    let mut expected_tags = computed_fields::read_tags(base.environment()).unwrap();
    expected_tags.extend([name("MutualCache.alpha"), name("MutualCache.zed")]);
    assert_eq!(
        computed_fields::read_tags(environment).unwrap(),
        expected_tags
    );
    let proved = checked(
        &engine,
        "theorem zed_value : MutualCache.zed (.branch 12 (.branch 30 .leaf)) = 13 := rfl\n\
             theorem alpha_value : MutualCache.alpha (.branch 12 (.branch 30 .leaf)) = 32 := rfl\n",
    );
    for theorem in ["zed_value", "alpha_value"] {
        assert!(matches!(
            proved.environment().find(&name(theorem)),
            Some(ConstantInfo::Thm(_))
        ));
    }
}

#[test]
fn incomplete_fields_name_collisions_and_resource_stops_publish_nothing() {
    on_stack(|| {
        let base = seed();
        let root = base.logical_root(&KVMap::new());
        let accepted = TREE.replace(
            "| .branch value tail => value + tail.sum",
            "| .branch value _ => value",
        );
        let admitted = base
            .admit_source_command(accepted.as_bytes(), &KVMap::new(), limits())
            .unwrap()
            .into_complete()
            .unwrap();
        assert_bundle(
            admitted.engine.environment(),
            "Tree",
            "sum",
            &["leaf", "branch"],
        );
        for source in [
            accepted.replace("computed_field, inline", "inline"),
            accepted.replace("@[computed_field, inline]", "@[computed_field, macro_inline]"),
            "inductive Tree (A : Type) where\n | leaf\n | branch (a : A)\nwith\n @[computed_field] sum : Tree A → Nat\n | .leaf => 0\n | .branch _ => 1\n".into(),
            "inductive Tree where\n | leaf\nwith\n @[computed_field] sum : Tree → Nat\n | .leaf => 0\n".into(),
            "inductive Tree where\n | leaf\n | branch (tail : Tree)\nwith\n @[computed_field] copy : Tree → Tree\n | .leaf => .leaf\n | .branch tail => .branch tail\n".into(),
        ] {
            assert!(base.admit_source_command(source.as_bytes(), &KVMap::new(), limits()).is_err(), "accepted {source}");
            assert_eq!(base.logical_root(&KVMap::new()), root);
            assert!(!base.environment().contains(&name("Tree")));
            assert!(computed_fields::read_tags(base.environment()).unwrap().is_empty());
        }
        let collided = checked(&base, "def Tree.sum._override : Nat := 7\n");
        let collision_root = collided.logical_root(&KVMap::new());
        assert!(
            collided
                .admit_source_command(accepted.as_bytes(), &KVMap::new(), limits())
                .is_err()
        );
        assert_eq!(collided.logical_root(&KVMap::new()), collision_root);
        assert!(!collided.environment().contains(&name("Tree._impl")));
        assert!(
            computed_fields::read_tags(collided.environment())
                .unwrap()
                .is_empty()
        );

        let mut bounded = limits();
        bounded.kernel.steps = 0;
        assert!(matches!(
            base.admit_source_command(accepted.as_bytes(), &KVMap::new(), bounded),
            Ok(Outcome::Inconclusive(_))
        ));
        assert_eq!(base.logical_root(&KVMap::new()), root);
        assert!(
            base.admit_source_command(
                b"@[computed_field] def standalone : Nat := 1",
                &KVMap::new(),
                limits()
            )
            .is_err()
        );
    });
}

fn build(source: &str) -> SourceModuleBuild {
    let initial = Engine::builder().build_empty();
    let module = name("Computed");
    let result = initial
        .compile_source_modules(
            &[SourceModuleInput {
                name: &module,
                source: source.as_bytes(),
            }],
            &module,
            &KVMap::new(),
            SourceModuleCheckLimits::new(SourceCheckLimits::new(limits())),
            OleanWriteBudget::default(),
        )
        .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
        .into_complete()
        .unwrap();
    assert!(initial.environment().is_empty());
    result
}

#[test]
fn cached_fields_survive_source_artifacts_and_owned_metadata_reimport() {
    on_stack(|| {
        for header in [
            "prelude\n",
            "module\nprelude\npublic section\n@[expose] section\n",
            "module\nprelude\npublic section\n",
        ] {
            let source = format!("{header}{PRIMITIVES}{CAST}{FLAG}");
            let built = build(&source);
            let artifact = &built.artifacts[0];
            let blocks = fln_olean::region::OleanView::parse(&artifact.bytes)
                .unwrap()
                .extension_payloads(OleanWalkBudget::default(), 16 << 20)
                .unwrap();
            let metadata =
                fln_olean::source_extensions::decode(&blocks, Default::default()).unwrap();
            assert_eq!(metadata.computed_fields, [name("Flag.value")]);
            assert_eq!(metadata.implemented_by.len(), 4);
            assert!(!metadata.uninterpreted.contains(&name(
                fln_olean::source_extensions::COMPUTED_FIELD_EXTENSION
            )));
            let companions = artifact.companions.as_ref();
            let loaded = Engine::builder()
                .build_empty()
                .import_olean_modules_for_source(
                    &[OleanModuleInput {
                        name: &artifact.name,
                        artifact: &artifact.bytes,
                        server_artifact: companions.map(|parts| parts.server.as_slice()),
                        private_artifact: companions.map(|parts| parts.private.as_slice()),
                    }],
                    std::slice::from_ref(&artifact.name),
                    &KVMap::new(),
                    SourceOleanImportLimits::new(OleanCheckLimits::new(16 << 20, limits().kernel)),
                )
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(loaded.modules[0].computed_fields, 1);
            assert_bundle(loaded.engine.environment(), "Flag", "value", &["off", "on"]);
            let recovered = fln_elab::computed_fields::validated_family(
                loaded.engine.environment(),
                &name("Flag"),
                limits().kernel,
                Default::default(),
            )
            .unwrap()
            .expect("complete native declarations must regenerate their representation authority");
            let original = fln_elab::computed_fields::validated_family(
                built.checked.checked.engine.environment(),
                &name("Flag"),
                limits().kernel,
                Default::default(),
            )
            .unwrap()
            .unwrap();
            assert_eq!(recovered, original);
            assert_eq!(
                computed_fields::read_tags(loaded.engine.environment()).unwrap(),
                BTreeSet::from([name("Flag.value")])
            );
            checked(
                &loaded.engine,
                "noncomputable def downstream : Bool := Flag.value (Flag.on Bool.true)\n",
            );
        }
    });
}

#[test]
fn inert_computed_tags_share_recovery_work_across_families_and_modules() {
    use fln_core::{expr::Expr, level::Level};
    use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
    use fln_olean::write::source::{SourceMetadata, encode_module_with_source_metadata};

    on_stack(|| {
        let constants = (0..16)
            .map(|index| {
                let declaration = name(&format!("Foreign{index}.hash"));
                ConstantInfo::Defn(DefinitionVal {
                    base: ConstantVal {
                        name: declaration.clone(),
                        level_params: Vec::new(),
                        type_: Expr::sort(Level::succ(Level::zero()).unwrap()),
                    },
                    value: Expr::sort(Level::zero()),
                    hints: ReducibilityHints::Abbrev,
                    safety: DefinitionSafety::Safe,
                    all: vec![declaration],
                })
            })
            .collect::<Vec<_>>();
        for (split_modules, constant_count) in [(false, 0), (false, 16), (true, 16)] {
            let constants = &constants[..constant_count];
            let expected = constants
                .iter()
                .map(|info| info.name().clone())
                .collect::<BTreeSet<_>>();
            let groups = if split_modules {
                constants
                    .iter()
                    .cloned()
                    .map(|info| vec![info])
                    .collect::<Vec<_>>()
            } else {
                vec![constants.to_vec()]
            };
            let modules = (0..groups.len())
                .map(|index| name(&format!("ForeignTags{index}")))
                .collect::<Vec<_>>();
            let artifacts = groups
                .iter()
                .map(|constants| {
                    encode_module_with_source_metadata(
                        OleanModuleWriteInput {
                            is_module: false,
                            imports: &[],
                            constants,
                            extra_const_names: &[],
                        },
                        &SourceMetadata {
                            computed_fields: constants
                                .iter()
                                .map(|info| info.name().clone())
                                .collect(),
                            ..Default::default()
                        },
                        OleanWriteHeader {
                            version: fln_olean::format::OLEAN_ACCEPTED_VERSIONS[0],
                            flags: 1,
                            lean_version: fln_olean::format::PIN_TAG.strip_prefix('v').unwrap(),
                            githash: fln_olean::format::PIN_COMMIT,
                            base_addr: 2 * fln_olean::format::REGION_ALIGN as u64,
                        },
                        OleanWriteBudget::default(),
                    )
                    .unwrap()
                    .bytes
                })
                .collect::<Vec<_>>();
            let inputs = modules
                .iter()
                .zip(&artifacts)
                .map(|(module, bytes)| OleanModuleInput {
                    name: module,
                    artifact: bytes,
                    server_artifact: None,
                    private_artifact: None,
                })
                .collect::<Vec<_>>();
            let initial = Engine::builder().build_empty();
            let mut import_limits =
                SourceOleanImportLimits::new(OleanCheckLimits::new(STACK, limits().kernel));
            if constant_count == 0 {
                import_limits.metadata.max_objects = 0;
            }
            let imported = initial
                .import_olean_modules_for_source(&inputs, &modules, &KVMap::new(), import_limits)
                .expect("inert tags must not consume a full recovery allowance per family")
                .into_complete()
                .unwrap();
            assert!(initial.environment().is_empty());
            assert_eq!(
                imported
                    .modules
                    .iter()
                    .map(|module| module.computed_fields)
                    .sum::<usize>(),
                constant_count
            );
            assert_eq!(
                computed_fields::read_tags(imported.engine.environment()).unwrap(),
                expected
            );
            assert!(
                fln_elab::computed_fields::families(
                    imported.engine.environment(),
                    Default::default()
                )
                .unwrap()
                .is_empty()
            );
            assert!(
                imported
                    .engine
                    .environment()
                    .extension(&fln_elab::computed_fields::journal_name())
                    .is_none()
            );
        }
    });
}

#[test]
fn hidden_public_fields_keep_their_bodies_private_and_expose_checked_adapters() {
    on_stack(|| {
        let source = format!("module\nprelude\npublic section\n{PRIMITIVES}{CAST}{FLAG}");
        let built = build(&source);
        let public =
            decode_olean_artifact(&built.artifacts[0].bytes, OleanDecodeLimits::new(16 << 20))
                .unwrap();
        assert!(matches!(
            public.constants.iter().find(|info| info.name() == &name("Flag.value")),
            Some(ConstantInfo::Axiom(axiom)) if !axiom.is_unsafe
        ));
        assert!(matches!(
            built
                .checked
                .checked
                .engine
                .environment()
                .find(&name("Flag.value")),
            Some(ConstantInfo::Defn(_))
        ));
        for helper in [
            "Flag._impl.casesOn",
            "Flag.casesOn._override",
            "Flag.off._override",
            "Flag.on._override",
            "Flag.value._override",
        ] {
            assert!(
                matches!(
                    public
                        .constants
                        .iter()
                        .find(|info| info.name() == &name(helper)),
                    Some(ConstantInfo::Defn(_))
                ),
                "missing exposed generated helper {helper}"
            );
        }
        assert!(built.artifacts[0].companions.is_some());
        let original = built.checked.checked.engine.environment();
        let getter = name("Flag.value");
        let public_getter = public
            .constants
            .iter()
            .find(|info| info.name() == &getter)
            .unwrap();
        let mut header_only = Environment::new();
        for (label, _) in original.constants() {
            if label != &getter {
                header_only = header_only
                    .with_entry(original.entry(label).unwrap())
                    .unwrap();
            }
        }
        header_only = header_only.add_decl(public_getter.clone()).unwrap();
        for (journal, state) in original.extensions() {
            header_only = header_only
                .register_extension(state.descriptor.clone())
                .unwrap();
            for entry in state.entries() {
                header_only = header_only
                    .push_extension_entry(journal, entry.payload.clone())
                    .unwrap();
            }
        }
        let error = fln_elab::computed_fields::validated_family(
            &header_only,
            &name("Flag"),
            limits().kernel,
            Default::default(),
        )
        .expect_err("public headers and a journal claim cannot authorize private cached execution");
        assert!(!error.is_resource_limit(), "{error:?}");
        assert!(
            fln_elab::computed_fields::recover_imported(
                &header_only,
                &name("Flag"),
                &[getter],
                &[],
                limits().kernel,
                Default::default(),
            )
            .unwrap()
            .is_none()
        );
    });
}
