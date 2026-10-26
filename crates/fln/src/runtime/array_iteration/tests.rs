//! Actual decoded comparison data for the private runtime model boundary.
//! The integration target separately admits the full 74-module artifact graph
//! with both checkers before executing source and replaying its FLBC artifacts.
use super::*;
use fln_elab::externs::{self, ExternEntry};
use fln_elab::implemented_by::{self, ImplementedByTable};
use fln_olean::source_extensions as metadata;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const INVENTORY: &str = include_str!("../../source_intrinsics/array_iteration/dependencies.txt");

fn named(label: &str) -> Name {
    Name::from_components(label.split('.'))
}

fn parts(library: &Path, label: &Name) -> [Vec<u8>; 3] {
    let path = library
        .join(label.to_display_string().replace('.', "/"))
        .with_extension("olean");
    [
        std::fs::read(&path).expect("actual exported Array dependency"),
        std::fs::read(path.with_extension("olean.server")).expect("actual server Array dependency"),
        std::fs::read(path.with_extension("olean.private"))
            .expect("actual private Array dependency"),
    ]
}

fn pinned_library() -> Option<PathBuf> {
    std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|path| path.is_dir())
}

fn fixture() -> &'static Environment {
    static FIXTURE: OnceLock<Environment> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let library = pinned_library().expect("the actual pinned Array model is mandatory here");
        let mut pending = vec![
            (named("Init.Data.Array.Basic"), false),
            (named("Init.Data.List.Control"), false),
        ];
        let mut seen = BTreeSet::new();
        let mut ordered = Vec::new();
        let mut artifacts = BTreeMap::new();
        while let Some((module, finished)) = pending.pop() {
            if finished {
                ordered.push(module);
                continue;
            }
            if !seen.insert(module.clone()) {
                continue;
            }
            assert!(seen.len() <= 256);
            let bytes = parts(&library, &module);
            let imports =
                crate::olean_module_imports(&bytes[0], crate::OleanDecodeLimits::new(BYTES))
                    .unwrap();
            artifacts.insert(module.clone(), bytes);
            pending.push((module, true));
            pending.extend(imports.into_iter().rev().map(|module| (module, false)));
        }
        assert_eq!(
            ordered.len(),
            74,
            "the complete actual Array/List artifact closure"
        );
        let mut constants = BTreeMap::new();
        let mut extern_rows = Vec::new();
        let mut implementation_rows = Vec::new();
        for module in ordered {
            let bytes = &artifacts[&module];
            let decoded = crate::decode_olean_module_artifacts(
                &bytes[0],
                &bytes[1],
                &bytes[2],
                crate::OleanDecodeLimits::new(BYTES),
            )
            .unwrap();
            let view = if decoded.module.is_module {
                fln_olean::region::OleanView::parse_with_dependencies(
                    &bytes[2],
                    &[bytes[0].as_slice(), bytes[1].as_slice()],
                )
            } else {
                fln_olean::region::OleanView::parse(&bytes[0])
            }
            .unwrap();
            let blocks = view
                .extension_payloads(crate::OleanWalkBudget::default(), BYTES)
                .unwrap();
            let extensions = metadata::decode(&blocks, metadata::DecodeLimits::default()).unwrap();
            extern_rows.extend(extensions.externs);
            implementation_rows.extend(extensions.implemented_by);
            for info in decoded.constants {
                // Keep the actual extractor's first occurrence. Expected model
                // hashes never choose, synthesize or repair fixture constants.
                constants.entry(info.name().clone()).or_insert(info);
            }
        }
        let mut environment = Environment::new();
        for info in constants.into_values() {
            environment = environment.add_decl(info).unwrap();
        }
        for row in extern_rows {
            let entries = row
                .entries
                .into_iter()
                .map(|entry| match entry {
                    metadata::ExternEntry::Adhoc { backend } => ExternEntry::Adhoc { backend },
                    metadata::ExternEntry::Inline { backend, pattern } => {
                        ExternEntry::Inline { backend, pattern }
                    }
                    metadata::ExternEntry::Standard { backend, symbol } => {
                        ExternEntry::Standard { backend, symbol }
                    }
                    metadata::ExternEntry::Opaque => ExternEntry::Opaque,
                })
                .collect();
            environment = externs::register(&environment, &row.declaration, entries).unwrap();
        }
        for row in implementation_rows {
            environment =
                implemented_by::register(&environment, &row.declaration, &row.implementation)
                    .unwrap();
        }
        assert_eq!(
            ImplementedByTable::read(&environment)
                .unwrap()
                .get(&logical_name()),
            Some(&selected_name()),
        );
        environment
    })
}

/// The actual pinned model is the only model these tests accept; without it they take the
/// typed skip every other pin-gated test takes, and `FLN_REQUIRE_REFERENCE` (set by the
/// lane that installs the pin) turns that skip into a failure.
fn with_fixture(test: impl FnOnce(&Environment) + Send + 'static) {
    if pinned_library().is_none() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
        );
        eprintln!("SKIP: pinned Reference lib/lean is absent");
        return;
    }
    std::thread::Builder::new()
        .name("actual-array-runtime-model".to_owned())
        .stack_size(STACK)
        .spawn(move || test(fixture()))
        .unwrap()
        .join()
        .unwrap();
}

fn inventory_names() -> BTreeSet<Name> {
    let mut names = BTreeSet::new();
    for line in INVENTORY.lines() {
        let columns: Vec<_> = line.split('\t').collect();
        assert_eq!(columns.len(), 5);
        let mut label = Name::anonymous();
        for component in columns[0].split('/') {
            label = if let Some(text) = component.strip_prefix("s:") {
                Name::str(label, text)
            } else {
                Name::num(
                    label,
                    component.strip_prefix("n:").unwrap().parse().unwrap(),
                )
            };
        }
        assert!(names.insert(label));
    }
    assert!(
        !names.is_empty(),
        "the tested actual model must be generated before functional tests"
    );
    names
}

fn replace(environment: &Environment, info: ConstantInfo) -> Environment {
    let target = info.name();
    let mut result = Environment::new();
    for (label, _) in environment.constants() {
        if label != target {
            result = result
                .with_entry(environment.entry(label).unwrap())
                .unwrap();
        }
    }
    for (journal, state) in environment.extensions() {
        result = result.register_extension(state.descriptor.clone()).unwrap();
        for entry in state.entries() {
            result = result
                .push_extension_entry(journal, entry.payload.clone())
                .unwrap();
        }
    }
    result.add_decl(info).unwrap()
}

fn identity_body(value: &mut DefinitionVal) {
    value.value = Expr::app(
        Expr::lam(
            named("preserveArrayModelType"),
            value.base.type_.clone(),
            Expr::bvar(0).unwrap(),
            BinderInfo::Default,
        ),
        value.value.clone(),
    );
}

fn refused(environment: &Environment, kind: &str) {
    let mut preparation = Preparation::new(environment, IngressLimits::default());
    let error = preparation
        .implementation_target(&logical_name())
        .unwrap_err();
    assert!(
        matches!(error, IngressError::UnsupportedNode { kind: actual } if actual == kind),
        "{error:?}",
    );
    assert!(
        preparation
            .specialized_definition(&private_name())
            .is_none()
    );
    assert!(preparation.array_iteration.adapter.is_none());
}

#[test]
fn actual_model_selects_one_private_adapter_without_changing_logical_constants() {
    with_fixture(|environment| {
        let original = environment.find(&logical_name()).unwrap().clone();
        let count = environment.constants().count();
        let mut preparation = Preparation::new(environment, IngressLimits::default());
        assert_eq!(
            preparation.implementation_target(&logical_name()).unwrap(),
            Some(private_name()),
        );
        let adapter = preparation.specialized_definition(&private_name()).unwrap();
        assert_eq!(adapter.safety, DefinitionSafety::Safe);
        assert_eq!(adapter.base.type_, original.constant_val().type_);
        assert_eq!(
            adapter.base.level_params,
            original.constant_val().level_params
        );
        assert!(!adapter.value.has_loose_bvars());
        assert!(!adapter.value.has_fvar());
        assert!(!adapter.value.has_expr_mvar());
        assert_eq!(
            preparation.implementation_target(&logical_name()).unwrap(),
            Some(private_name()),
        );
        assert_eq!(
            preparation.specialized_definition(&private_name()),
            Some(adapter)
        );
        assert_eq!(environment.find(&logical_name()), Some(&original));
        assert_eq!(environment.constants().count(), count);
        assert!(!environment.contains(&private_name()));
    });
}

#[test]
fn initializers_cannot_be_bypassed_by_the_array_adapter() {
    with_fixture(|environment| {
        for label in [logical_name(), named("List.forIn'")] {
            let initializers = BTreeSet::from([label]);
            let mut preparation = Preparation::new(environment, IngressLimits::default())
                .with_runtime_initializers(&initializers);
            assert!(matches!(
                preparation.implementation_target(&logical_name()),
                Err(IngressError::UnsupportedNode {
                    kind: "Array iteration dependency requires runtime initialization",
                }),
            ));
            assert!(
                preparation
                    .specialized_definition(&private_name())
                    .is_none()
            );
            assert!(preparation.array_iteration.adapter.is_none());
        }
        let mut fresh = Preparation::new(environment, IngressLimits::default());
        assert_eq!(
            fresh.implementation_target(&logical_name()).unwrap(),
            Some(private_name())
        );
    });
}

#[test]
fn resource_refusals_do_not_publish_a_partial_array_callable() {
    with_fixture(|environment| {
        let implementations = ImplementedByTable::read(environment).unwrap();
        for max_nodes in [0, 16, 128] {
            let mut preparation = Preparation::new(
                environment,
                IngressLimits {
                    max_nodes,
                    ..IngressLimits::default()
                },
            );
            // Focus this budget on the actual dependency inventory, not on
            // validating unrelated imported implemented_by journal rows.
            preparation.implementations = Some(implementations.clone());
            assert!(matches!(
                preparation.array_iteration_target(),
                Err(IngressError::ResourceLimit {
                    resource: IngressResource::Nodes, limit, observed,
                }) if limit == max_nodes && observed > limit,
            ));
            assert!(
                preparation
                    .specialized_definition(&private_name())
                    .is_none()
            );
            assert!(preparation.array_iteration.adapter.is_none());
        }
        let mut shallow = Preparation::new(
            environment,
            IngressLimits {
                max_context_depth: 2,
                ..IngressLimits::default()
            },
        );
        assert!(matches!(
            shallow.implementation_target(&logical_name()),
            Err(IngressError::ResourceLimit { .. }),
        ));
        assert!(shallow.specialized_definition(&private_name()).is_none());
        assert!(shallow.array_iteration.adapter.is_none());
        let mut fresh = Preparation::new(environment, IngressLimits::default());
        assert_eq!(
            fresh.implementation_target(&logical_name()).unwrap(),
            Some(private_name())
        );
    });
}

#[test]
fn private_name_collisions_and_direct_unsafe_calls_do_not_gain_authority() {
    with_fixture(|environment| {
        let Some(ConstantInfo::Defn(original)) = environment.find(&logical_name()) else {
            unreachable!("actual safe Array definition");
        };
        let mut collision = original.clone();
        collision.base.name = private_name();
        collision.all = vec![private_name()];
        let collided = environment.add_decl(ConstantInfo::Defn(collision)).unwrap();
        let mut preparation = Preparation::new(&collided, IngressLimits::default());
        let error = preparation
            .implementation_target(&logical_name())
            .unwrap_err();
        assert!(
            matches!(error, IngressError::UnsupportedNode { kind } if kind.contains("collision")),
            "{error:?}",
        );
        assert!(
            preparation
                .specialized_definition(&private_name())
                .is_none()
        );
        assert!(preparation.array_iteration.adapter.is_none());

        let mut direct = Preparation::new(environment, IngressLimits::default());
        // An explicitly unsafe definition is its own executable body (b28eab42), as the pin's
        // `#eval` runs a direct call to it. That grants it no adapter or replacement authority.
        let own = direct
            .executable_definition(&selected_name())
            .unwrap()
            .expect("the unsafe implementation is its own executable body");
        assert_eq!(own.base.name, selected_name());
        assert_eq!(own.safety, DefinitionSafety::Unsafe);
        assert!(direct.specialized_definition(&private_name()).is_none());
        assert!(direct.array_iteration.adapter.is_none());
        let mut fresh = Preparation::new(environment, IngressLimits::default());
        assert_eq!(
            fresh.implementation_target(&logical_name()).unwrap(),
            Some(private_name())
        );
    });
}

#[test]
fn changed_selected_replacements_and_externs_preserve_execution_authority() {
    with_fixture(|environment| {
        let Some(ConstantInfo::Defn(original)) = environment.find(&selected_name()) else {
            unreachable!("actual unsafe Array implementation");
        };
        let mut unsafe_target = original.clone();
        unsafe_target.base.name = named("alternateUnsafeArrayIteration");
        unsafe_target.all = vec![unsafe_target.base.name.clone()];
        let unsafe_name = unsafe_target.base.name.clone();
        let changed = environment
            .add_decl(ConstantInfo::Defn(unsafe_target))
            .unwrap();
        let changed = implemented_by::register(&changed, &logical_name(), &unsafe_name).unwrap();
        // A different admitted unsafe implementation can execute its own body,
        // but only the canonical pair authorizes the checked logical adapter.
        let mut preparation = Preparation::new(&changed, IngressLimits::default());
        assert_eq!(
            preparation.implementation_target(&logical_name()).unwrap(),
            Some(unsafe_name.clone()),
        );
        let body = preparation
            .executable_definition(&logical_name())
            .unwrap()
            .unwrap();
        assert_eq!(body.base.name, unsafe_name);
        assert_eq!(body.value, original.value);
        assert_eq!(body.safety, DefinitionSafety::Unsafe);
        assert!(
            preparation
                .specialized_definition(&private_name())
                .is_none()
        );
        assert!(preparation.array_iteration.adapter.is_none());

        let list_name = named("List.forIn'");
        let Some(ConstantInfo::Defn(original)) = environment.find(&list_name) else {
            unreachable!("actual safe List traversal");
        };
        let mut list_target = original.clone();
        list_target.base.name = named("alternateSafeListIteration");
        list_target.all = vec![list_target.base.name.clone()];
        let target_name = list_target.base.name.clone();
        let changed = environment
            .add_decl(ConstantInfo::Defn(list_target))
            .unwrap();
        let changed = implemented_by::register(&changed, &list_name, &target_name).unwrap();
        assert_eq!(
            changed.entry(&list_name).unwrap().digest(),
            environment.entry(&list_name).unwrap().digest()
        );
        refused(
            &changed,
            "Array iteration dependency has a different selected implementation",
        );

        let changed = externs::register(
            environment,
            &list_name,
            vec![ExternEntry::Standard {
                backend: named("all"),
                symbol: "unsupported_array_iteration_foreign_body".to_owned(),
            }],
        )
        .unwrap();
        let mut preparation = Preparation::new(&changed, IngressLimits::default());
        let error = preparation
            .implementation_target(&logical_name())
            .unwrap_err();
        assert!(
            matches!(error, IngressError::UnsupportedNode { kind } if kind.contains("extern")),
            "{error:?}",
        );
        assert!(
            preparation
                .specialized_definition(&private_name())
                .is_none()
        );
        assert!(preparation.array_iteration.adapter.is_none());
    });
}

#[test]
fn recursive_companion_presence_and_bodies_are_part_of_the_exact_model() {
    with_fixture(|environment| {
        let inventory = inventory_names();
        let logical = inventory
            .iter()
            .find_map(|label| match environment.find(label) {
                Some(ConstantInfo::Defn(value))
                    if value.safety == DefinitionSafety::Safe
                        && value.all.as_slice() == std::slice::from_ref(label)
                        && !environment.contains(&Name::str(label.clone(), "_unsafe_rec")) =>
                {
                    Some(value.clone())
                }
                _ => None,
            })
            .expect("the pin has a singleton logical dependency without a companion");
        let label = logical.base.name.clone();
        let logical_digest = environment.entry(&label).unwrap().digest();
        let companion_name = Name::str(label.clone(), "_unsafe_rec");
        let mut companion = logical;
        companion.base.name = companion_name.clone();
        companion.safety = DefinitionSafety::Partial;
        companion.all = vec![companion_name.clone()];
        let added = environment
            .add_decl(ConstantInfo::Defn(companion.clone()))
            .unwrap();
        assert_eq!(added.entry(&label).unwrap().digest(), logical_digest);
        assert_eq!(
            Preparation::new(&added, IngressLimits::default())
                .recursive_definition(&label)
                .unwrap(),
            Some(companion.clone()),
            "this is a correctly linked executable sibling, not a malformed-name refusal",
        );
        refused(
            &added,
            "Array iteration dependency has a different recursive companion",
        );

        identity_body(&mut companion);
        let changed = replace(&added, ConstantInfo::Defn(companion.clone()));
        assert_eq!(changed.entry(&label).unwrap().digest(), logical_digest);
        assert_ne!(
            changed.entry(&companion_name).unwrap().digest(),
            added.entry(&companion_name).unwrap().digest()
        );
        assert_eq!(
            Preparation::new(&changed, IngressLimits::default())
                .recursive_definition(&label)
                .unwrap(),
            Some(companion),
            "ordinary linkage alone cannot distinguish a changed executable body",
        );
        refused(
            &changed,
            "Array iteration dependency has a different recursive companion",
        );

        // A future exact pin may also carry selected executable siblings.
        // When present, mutate every one rather than silently relying on its
        // safe parent's digest. The new-sibling tests above always run.
        let mut actual_companions = 0usize;
        for label in &inventory {
            let Some(ConstantInfo::Defn(value)) = environment.find(label) else {
                continue;
            };
            if value.safety != DefinitionSafety::Partial
                || !matches!(
                    label.leaf_view(),
                    fln_core::name::LeafView::Str("_unsafe_rec")
                )
            {
                continue;
            }
            actual_companions += 1;
            assert!(
                inventory.contains(&label.parent()),
                "the selected sibling's parent attributes are bound"
            );
            let mut altered = value.clone();
            identity_body(&mut altered);
            let changed = replace(environment, ConstantInfo::Defn(altered));
            refused(
                &changed,
                "Array iteration dependency differs from the exact pinned model",
            );
        }
        eprintln!(
            "checked new companion presence/body plus {actual_companions} actual selected companion bodies"
        );
    });
}
