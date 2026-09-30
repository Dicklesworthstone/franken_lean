//! Source class declarations survive compiled library boundaries and cache reuse.
use super::*;
use fln::source_check::modules::imported::{SourceOleanImport, SourceOleanImportLimits};
use fln::source_check::modules::{SourceModuleCacheLimits, SourceModuleSession};
use fln_olean::source_extensions::{self, ClassEntry, DecodeLimits};

const CLASS: &str = "prelude\nclass Mapper (A : Type) where\n  apply : A -> A";

fn compiled(files: &[(&str, &str)]) -> SourceModuleBuild {
    build(
        &Engine::builder().build_empty(),
        files,
        OleanWriteBudget::default(),
    )
    .unwrap_or_else(|error| panic!("{files:?}: {error:?}"))
    .into_complete()
    .unwrap()
}

fn imported(built: &SourceModuleBuild) -> SourceOleanImport {
    let modules: Vec<_> = built
        .artifacts
        .iter()
        .map(|a| OleanModuleInput {
            name: &a.name,
            artifact: &a.bytes,
            server_artifact: None,
            private_artifact: None,
        })
        .collect();
    Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &modules,
            &[name("Main")],
            &KVMap::new(),
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                4 * 1024 * 1024,
                limits().source.admission.kernel,
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap()
}

fn metadata(bytes: &[u8]) -> source_extensions::SourceExtensions {
    let view = fln_olean::region::OleanView::parse(bytes).unwrap();
    let blocks = view
        .extension_payloads(fln::OleanWalkBudget::default(), 4 * 1024 * 1024)
        .unwrap();
    source_extensions::decode(&blocks, DecodeLimits::default()).unwrap()
}

#[test]
fn source_classes_enable_downstream_instances_after_dual_checked_import() {
    let built = compiled(&[("Main", CLASS)]);
    let receipt = imported(&built);
    assert_eq!(receipt.modules[0].classes, 1);
    let registry =
        fln_elab::instances::InstanceRegistry::read(receipt.engine.environment()).unwrap();
    assert!(registry.is_class(&name("Mapper")));
    receipt
        .engine
        .check_source_files(
            &[br#"
instance mapperId (A : Type) : Mapper A := { apply := fun x => x }
def use (A : Type) (x : A) : A := Mapper.apply x
"#],
            &KVMap::new(),
            limits().source,
        )
        .unwrap()
        .into_complete()
        .unwrap();
}

#[test]
fn only_owned_class_rows_are_exported_across_a_diamond() {
    let built = compiled(&[
        (
            "Main",
            "prelude\nimport Left Right\nclass Outer (A : Type) where\n  apply : A -> A",
        ),
        ("Left", "prelude\nimport Base"),
        ("Right", "prelude\nimport Base"),
        ("Base", CLASS),
    ]);
    let counts: Vec<_> = built
        .artifacts
        .iter()
        .map(|a| (a.name.clone(), metadata(&a.bytes).classes.len()))
        .collect();
    assert_eq!(
        counts,
        [
            (name("Base"), 1),
            (name("Left"), 0),
            (name("Right"), 0),
            (name("Main"), 1)
        ]
    );
    let receipt = imported(&built);
    assert_eq!(receipt.modules.iter().map(|m| m.classes).sum::<usize>(), 2);
}

#[test]
fn output_parameters_and_output_only_universes_keep_the_pinned_metadata() {
    let built = compiled(&[(
        "Main",
        r#"prelude
def outParam.{u} (A : Sort u) : Sort u := A
class Convert.{u,v} (A : Type u) (B : outParam (Type v)) where
  convert : A -> B
class Carrier.{w} : Type (w + 1) where
  type : Type w
"#,
    )]);
    let rows = metadata(&built.artifacts[0].bytes).classes;
    assert_eq!(
        rows,
        [
            ClassEntry {
                name: name("Convert"),
                out_params: vec![1],
                out_level_params: vec![1]
            },
            ClassEntry {
                name: name("Carrier"),
                out_params: vec![],
                out_level_params: vec![0]
            },
        ]
    );
    let receipt = imported(&built);
    let registry =
        fln_elab::instances::InstanceRegistry::read(receipt.engine.environment()).unwrap();
    let params = registry
        .imported_class_parameters(&name("Convert"))
        .unwrap();
    assert_eq!(params.out_params, [1]);
    assert_eq!(params.out_level_params, [1]);
}

#[test]
fn warm_class_artifacts_remain_byte_identical_and_writer_failures_preserve_cache() {
    let mut session = SourceModuleSession::new(
        Engine::builder().build_empty(),
        KVMap::new(),
        limits(),
        SourceModuleCacheLimits::default(),
    );
    let module = name("Main");
    let inputs = [SourceModuleInput {
        name: &module,
        source: CLASS.as_bytes(),
    }];
    let cold = session
        .compile(&inputs, &module, OleanWriteBudget::default())
        .unwrap()
        .into_complete()
        .unwrap();
    let bytes = cold.artifacts[0].bytes.clone();
    let report = &cold.artifacts[0].report;
    let exact = OleanWriteBudget {
        max_bytes: report.file_bytes,
        max_objects: report.runtime_objects,
    };
    let warm = session
        .compile(&inputs, &module, exact)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!((warm.reused_modules, warm.elaborated_modules), (1, 0));
    assert_eq!(warm.artifacts[0].bytes, bytes);
    for budget in [
        OleanWriteBudget {
            max_bytes: exact.max_bytes - 1,
            ..exact
        },
        OleanWriteBudget {
            max_objects: exact.max_objects - 1,
            ..exact
        },
    ] {
        let error = session.compile(&inputs, &module, budget).unwrap_err();
        assert_eq!(error.disposition(), ("resource", false, 3));
    }
    let recovered = session
        .compile(&inputs, &module, exact)
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(recovered.reused_modules, 1);
    assert_eq!(recovered.artifacts[0].bytes, bytes);
    imported(&recovered);
}

#[test]
fn unsupported_instance_rows_cannot_escape_in_an_incomplete_artifact() {
    let initial = Engine::builder().build_empty();
    let root = initial.logical_root(&KVMap::new());
    let source =
        format!("{CLASS}\ninstance mapperId (A : Type) : Mapper A := Mapper.mk (fun x => x)");
    assert!(matches!(
        build(&initial, &[("Main", &source)], OleanWriteBudget::default()),
        Err(SourceModuleBuildError::Check(
            SourceModuleCheckError::Extension { .. }
        ))
    ));
    assert_eq!(initial.logical_root(&KVMap::new()), root);
    imported(&compiled(&[("Main", CLASS)]));
}

#[test]
fn class_metadata_collection_is_bounded_and_does_not_modify_the_source_environment() {
    let built = compiled(&[("Main", CLASS)]);
    let env = built.checked.checked.engine.environment();
    let root = built.checked.checked.engine.logical_root(&KVMap::new());
    assert!(matches!(
        fln_elab::instances::export::classes(&fln::Environment::new(), env, 0),
        Err(fln_elab::instances::InstanceRegistryError::Limit)
    ));
    let (rows, work) = fln_elab::instances::export::classes(&fln::Environment::new(), env, 1000)
        .unwrap()
        .unwrap();
    assert_eq!(rows.len(), 1);
    assert!(work > 0);
    assert!(fln_elab::instances::export::classes(&fln::Environment::new(), env, work - 1).is_err());
    assert_eq!(
        built.checked.checked.engine.logical_root(&KVMap::new()),
        root
    );
}
