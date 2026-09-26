//! The Lake export consumes checked module deltas, never a seeded snapshot.
#![forbid(unsafe_code)]

use fln::source_check::modules::{
    SourceModuleBuild, SourceModuleBuildError, SourceModuleCheckError, SourceModuleCheckLimits,
};
use fln::{
    Budget, Engine, EngineAdmissionLimits, KVMap, Name, OleanCheckLimits, OleanModuleInput,
    OleanWriteBudget, Outcome, SourceCheckLimits, SourceModuleInput,
};

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

fn build(
    engine: &Engine,
    files: &[(&str, &str)],
    write_budget: OleanWriteBudget,
) -> Result<Outcome<SourceModuleBuild>, SourceModuleBuildError> {
    let names: Vec<_> = files.iter().map(|(value, _)| name(value)).collect();
    let modules: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    engine.compile_source_modules(
        &modules,
        &name("Main"),
        &KVMap::new(),
        limits(),
        write_budget,
    )
}

const LIB: &str = "prelude\ndef identity.{u} {A : Sort u} (x : A) : A := x";
const MAIN: &str = "prelude\nimport Lib Lib\ndef use.{u} {A : Sort u} (x : A) : A := identity x";

#[test]
fn artifacts_are_separate_importable_deltas_rechecked_by_both_engines() {
    let initial = Engine::builder().build_empty();
    let result = build(
        &initial,
        &[("Main", MAIN), ("Lib", LIB)],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(result.artifacts.len(), 2);
    assert_eq!(result.artifacts[0].name, name("Lib"));
    assert_eq!(result.artifacts[1].name, name("Main"));
    assert!(initial.environment().is_empty());
    assert_eq!(result.artifacts[0].report.constants, 1);
    assert_eq!(result.artifacts[1].report.constants, 1);
    let imports = fln::decode_olean_artifact(
        &result.artifacts[1].bytes,
        fln::OleanDecodeLimits::new(1024 * 1024),
    )
    .unwrap()
    .module
    .imports;
    assert_eq!(
        imports
            .iter()
            .map(|row| row.module.clone())
            .collect::<Vec<_>>(),
        [name("Lib"), name("Lib")]
    );
    assert!(
        imports
            .iter()
            .all(|row| row.is_exported && !row.import_all && !row.is_meta)
    );
    let inputs: Vec<_> = result
        .artifacts
        .iter()
        .map(|artifact| OleanModuleInput {
            name: &artifact.name,
            artifact: &artifact.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    let loaded = initial
        .check_olean_modules(
            &inputs,
            &KVMap::new(),
            OleanCheckLimits::new(1024 * 1024, limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(loaded.engine.environment().len(), 2);
    assert!(loaded.engine.environment().contains(&name("identity")));
    assert!(loaded.engine.environment().contains(&name("use")));
    assert_eq!(
        loaded.engine.logical_root(&KVMap::new()),
        result.checked.checked.result_logical_root
    );
}

#[test]
fn library_export_has_no_ambient_seed_or_implicit_init_fallback() {
    let seeded = Engine::with_source_seed(limits().source.admission)
        .unwrap()
        .into_complete()
        .unwrap();
    assert!(matches!(
        build(&seeded, &[("Main", LIB)], OleanWriteBudget::default()),
        Err(SourceModuleBuildError::UnboundBase)
    ));
    let initial = Engine::builder().build_empty();
    assert!(
        matches!(build(&initial, &[("Main", "def identity.{u} {A : Sort u} (x : A) : A := x")], OleanWriteBudget::default()),
        Err(SourceModuleBuildError::Check(SourceModuleCheckError::MissingModule { module, .. })) if module == name("Init"))
    );
}

#[test]
fn implicit_init_is_a_real_dependency_and_preserves_both_pinned_import_rows() {
    let initial = Engine::builder().build_empty();
    let result = build(
        &initial,
        &[
            ("Main", "def use.{u} {A : Sort u} (x : A) : A := identity x"),
            ("Init", LIB),
        ],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(result.checked.module_order, [name("Init"), name("Main")]);
    let imports = fln::decode_olean_artifact(
        &result.artifacts[1].bytes,
        fln::OleanDecodeLimits::new(1024 * 1024),
    )
    .unwrap()
    .module
    .imports;
    assert_eq!(imports.len(), 2);
    assert_eq!(imports[0].module, name("Init"));
    assert_eq!(imports[1].module, name("Init"));
    assert!(!imports[0].is_meta);
    assert!(imports[1].is_meta);
}

#[test]
fn late_rejection_and_aggregate_writer_exhaustion_return_no_products() {
    let initial = Engine::builder().build_empty();
    let bad = "prelude\nimport Lib\ndef broken : Type := absent";
    assert!(
        matches!(build(&initial, &[("Main", bad), ("Lib", LIB)], OleanWriteBudget::default()),
        Err(SourceModuleBuildError::Check(SourceModuleCheckError::Source { module, .. })) if module == name("Main"))
    );
    let complete = build(
        &initial,
        &[("Main", MAIN), ("Lib", LIB)],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let first_bytes = complete.artifacts[0].report.file_bytes;
    let budget = OleanWriteBudget {
        max_bytes: first_bytes,
        ..OleanWriteBudget::default()
    };
    let error = build(&initial, &[("Main", MAIN), ("Lib", LIB)], budget).unwrap_err();
    assert_eq!(error.disposition(), ("resource", false, 3));
    assert!(
        matches!(error, SourceModuleBuildError::Encode { module, .. } if module == name("Main"))
    );
    assert!(initial.environment().is_empty());
}

#[test]
fn native_extension_effects_are_not_silently_lost_in_serialization() {
    let initial = Engine::builder().build_empty();
    let error = build(
        &initial,
        &[(
            "Main",
            "prelude\nclass Container (A : Type) where\n  value : A",
        )],
        OleanWriteBudget::default(),
    )
    .unwrap_err();
    assert!(
        matches!(
            error,
            SourceModuleBuildError::Check(SourceModuleCheckError::Extension { .. })
        ),
        "{error:?}"
    );
}

#[test]
fn external_imports_must_be_declared_and_the_imported_base_must_remain_exact() {
    let initial = Engine::builder().build_empty();
    let lib = build(&initial, &[("Main", LIB)], OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap()
        .artifacts
        .pop()
        .unwrap();
    let lib_name = name("Lib");
    let imported = initial
        .check_olean_modules(
            &[OleanModuleInput {
                name: &lib_name,
                artifact: &lib.bytes,
                server_artifact: None,
                private_artifact: None,
            }],
            &KVMap::new(),
            OleanCheckLimits::new(1024 * 1024, limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let legal = build(&imported, &[("Main", MAIN)], OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(legal.artifacts[0].report.constants, 1);
    let undeclared = "prelude\ndef use.{u} {A : Sort u} (x : A) : A := identity x";
    assert!(
        matches!(build(&imported, &[("Main", undeclared)], OleanWriteBudget::default()),
        Err(SourceModuleBuildError::Check(SourceModuleCheckError::AmbientImport { import, .. })) if import == lib_name)
    );
    let changed = imported
        .check_source_files(
            &[b"def ambient.{u} {A : Sort u} (x : A) : A := x"],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    assert!(matches!(
        build(&changed, &[("Main", MAIN)], OleanWriteBudget::default()),
        Err(SourceModuleBuildError::UnboundBase)
    ));
}

#[test]
fn external_dependency_edges_and_local_imports_preserve_transitive_visibility() {
    let initial = Engine::builder().build_empty();
    let built = build(
        &initial,
        &[("Main", MAIN), ("Lib", LIB)],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let api = name("Api");
    let lib = name("Lib");
    let inputs = [
        OleanModuleInput {
            name: &lib,
            artifact: &built.artifacts[0].bytes,
            server_artifact: None,
            private_artifact: None,
        },
        OleanModuleInput {
            name: &api,
            artifact: &built.artifacts[1].bytes,
            server_artifact: None,
            private_artifact: None,
        },
    ];
    let imported = initial
        .check_olean_modules(
            &inputs,
            &KVMap::new(),
            OleanCheckLimits::new(1024 * 1024, limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    let result = build(
        &imported,
        &[
            (
                "Main",
                "prelude\nimport Local\ndef final.{u} {A : Sort u} (x : A) : A := middle x",
            ),
            (
                "Local",
                "prelude\nimport Api\ndef middle.{u} {A : Sort u} (x : A) : A := use x",
            ),
        ],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    assert_eq!(result.artifacts.len(), 2);
    assert!(
        result
            .artifacts
            .iter()
            .all(|artifact| artifact.report.constants == 1)
    );
    let local_imports = fln::olean_module_imports(
        &result.artifacts[0].bytes,
        fln::OleanDecodeLimits::new(1024 * 1024),
    )
    .unwrap();
    let main_imports = fln::olean_module_imports(
        &result.artifacts[1].bytes,
        fln::OleanDecodeLimits::new(1024 * 1024),
    )
    .unwrap();
    assert_eq!(local_imports, [api]);
    assert_eq!(main_imports, [name("Local")]);
}

#[test]
fn replacing_imported_module_identities_cannot_authorize_a_new_artifact_graph() {
    let initial = Engine::builder().build_empty();
    let built = build(
        &initial,
        &[("Main", MAIN), ("Lib", LIB)],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap();
    let lib = name("Lib");
    let main = name("Main");
    let imported = initial
        .check_olean_modules(
            &[
                OleanModuleInput {
                    name: &lib,
                    artifact: &built.artifacts[0].bytes,
                    server_artifact: None,
                    private_artifact: None,
                },
                OleanModuleInput {
                    name: &main,
                    artifact: &built.artifacts[1].bytes,
                    server_artifact: None,
                    private_artifact: None,
                },
            ],
            &KVMap::new(),
            OleanCheckLimits::new(1024 * 1024, limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    // Replacing Main while retaining the imported Main's declarations would
    // otherwise emit a graph whose names no longer identify those constants.
    assert!(
        matches!(build(&imported, &[("Main", "prelude\nimport Lib")], OleanWriteBudget::default()),
        Err(SourceModuleBuildError::Check(SourceModuleCheckError::DuplicateModule(module))) if module == main)
    );
    let empty = build(
        &initial,
        &[("Main", "prelude")],
        OleanWriteBudget::default(),
    )
    .unwrap()
    .into_complete()
    .unwrap()
    .artifacts
    .pop()
    .unwrap();
    let rebound = imported
        .check_olean_modules(
            &[OleanModuleInput {
                name: &lib,
                artifact: &empty.bytes,
                server_artifact: None,
                private_artifact: None,
            }],
            &KVMap::new(),
            OleanCheckLimits::new(1024 * 1024, limits().source.admission.kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .engine;
    // The constants are unchanged, but Lib was just rebound to an empty
    // artifact. Exact-environment equality alone must not authenticate it.
    assert!(matches!(
        build(&rebound, &[("Main", MAIN)], OleanWriteBudget::default()),
        Err(SourceModuleBuildError::UnboundBase)
    ));
}
