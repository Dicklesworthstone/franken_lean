//! Public import results stay identical across serial, parallel, and mixed reuse.
#![forbid(unsafe_code)]

use fln::source_check::modules::SourceModuleCheckLimits;
use fln::source_check::modules::imported::{
    SourceOleanImport, SourceOleanImportError, SourceOleanImportLimits,
};
use fln::source_check::modules::reuse::{
    CheckerIdentity, ImportClosureKey, ImportPostureRequest, ImportReuseStore, RecordLookup,
    ReuseVerified,
};
use fln::{
    AxiomVal, Budget, ConstantInfo, ConstantVal, Engine, EngineAdmissionLimits, Expr, KVMap, Level,
    Name, OLEAN_ACCEPTED_VERSIONS, OLEAN_PIN_COMMIT, OLEAN_PIN_TAG, OLEAN_REGION_ALIGN,
    OleanCheckError, OleanCheckLimits, OleanFrontierJobs, OleanModuleImport, OleanModuleInput,
    OleanModuleWriteInput, OleanWriteBudget, OleanWriteHeader, SourceCheckLimits,
    SourceModuleInput, TheoremVal, encode_olean_module,
};
use std::collections::BTreeMap;
use std::num::NonZeroUsize;
use std::sync::Mutex;

const STACK: usize = 16 * 1024 * 1024;
type Artifacts = Vec<(Name, Vec<u8>)>;

fn n(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn on_import_stack(body: impl FnOnce() + Send) {
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .stack_size(STACK)
            .spawn_scoped(scope, body)
            .unwrap()
            .join()
            .unwrap();
    });
}

fn source_limits() -> SourceModuleCheckLimits {
    SourceModuleCheckLimits::new(SourceCheckLimits::new(EngineAdmissionLimits::new(
        Budget::for_stack_bytes(2 * 1024 * 1024),
    )))
}

fn limits(threads: usize) -> SourceOleanImportLimits {
    SourceOleanImportLimits {
        jobs: OleanFrontierJobs {
            threads: NonZeroUsize::new(threads).unwrap(),
            worker_stack_bytes: STACK,
        },
        ..SourceOleanImportLimits::new(OleanCheckLimits::new(
            1 << 20,
            Budget::for_stack_bytes(STACK),
        ))
    }
}

fn inputs(artifacts: &Artifacts) -> Vec<OleanModuleInput<'_>> {
    artifacts
        .iter()
        .map(|(name, artifact)| OleanModuleInput {
            name,
            artifact,
            server_artifact: None,
            private_artifact: None,
        })
        .collect()
}

#[derive(Default)]
struct Memory(Mutex<BTreeMap<ImportClosureKey, Vec<u8>>>);

impl ImportReuseStore for Memory {
    fn load(&self, key: ImportClosureKey) -> Result<Option<Vec<u8>>, String> {
        Ok(self.0.lock().unwrap().get(&key).cloned())
    }

    fn save(&self, key: ImportClosureKey, bytes: &[u8]) -> Result<(), String> {
        self.0.lock().unwrap().insert(key, bytes.to_vec());
        Ok(())
    }
}

fn reuse(checker: CheckerIdentity, store: &Memory) -> ImportPostureRequest<'_> {
    ImportPostureRequest::ReuseVerified(ReuseVerified { checker, store })
}

fn diamond() -> Artifacts {
    let files = [
        (
            "Main",
            "prelude\nimport Left\nimport Right\ndef run.{u} {A : Sort u} (x : A) : A := leftId (rightId x)",
        ),
        (
            "Left",
            "prelude\nimport Base\ndef leftId.{u} {A : Sort u} (x : A) : A := baseId x",
        ),
        (
            "Right",
            "prelude\nimport Base\ndef rightId.{u} {A : Sort u} (x : A) : A := baseId x",
        ),
        (
            "Base",
            "prelude\ndef baseId.{u} {A : Sort u} (x : A) : A := x",
        ),
    ];
    let names: Vec<_> = files.iter().map(|(name, _)| n(name)).collect();
    let modules: Vec<_> = files
        .iter()
        .zip(&names)
        .map(|((_, source), name)| SourceModuleInput {
            name,
            source: source.as_bytes(),
        })
        .collect();
    Engine::builder()
        .build_empty()
        .compile_source_modules(
            &modules,
            &n("Main"),
            &KVMap::new(),
            source_limits(),
            OleanWriteBudget::default(),
        )
        .unwrap()
        .into_complete()
        .unwrap()
        .artifacts
        .into_iter()
        .map(|artifact| (artifact.name, artifact.bytes))
        .collect()
}

fn same_import(left: &SourceOleanImport, right: &SourceOleanImport) {
    assert!(left.engine.environment() == right.engine.environment());
    assert_eq!(
        left.engine.imported_modules(),
        right.engine.imported_modules()
    );
    assert_eq!(left.result_logical_root, right.result_logical_root);
    assert_eq!(left.modules, right.modules, "metadata replay order");
    assert_eq!(
        left.checked.base_logical_root,
        right.checked.base_logical_root
    );
    assert_eq!(
        left.checked.result_logical_root,
        right.checked.result_logical_root
    );
    assert_eq!(left.checked.modules.len(), right.checked.modules.len());
    for (left, right) in left.checked.modules.iter().zip(&right.checked.modules) {
        assert_eq!(left.name, right.name);
        assert_eq!(left.base_logical_root, right.base_logical_root);
        assert_eq!(left.result_logical_root, right.result_logical_root);
        assert_eq!(left.declarations, right.declarations, "checker rows");
        assert!(left.decoded.constants == right.decoded.constants);
        assert_eq!(left.decoded.module.imports, right.decoded.module.imports);
    }
}

fn same_source_contexts(left: &SourceOleanImport, right: &SourceOleanImport) {
    for (module, callee, has_left, has_right) in [
        ("Base", "baseId", false, false),
        ("Left", "leftId", true, false),
        ("Right", "rightId", false, true),
        ("Main", "run", true, true),
    ] {
        let consumer = n("Consumer");
        let source = format!(
            "prelude\nimport {module}\ndef selected.{{u}} {{A : Sort u}} (x : A) : A := {callee} x"
        );
        let check = |import: &SourceOleanImport| {
            import
                .check_source_modules(
                    &[SourceModuleInput {
                        name: &consumer,
                        source: source.as_bytes(),
                    }],
                    &consumer,
                    &KVMap::new(),
                    source_limits(),
                    None,
                )
                .unwrap()
                .into_complete()
                .unwrap()
                .checked
        };
        let (left, right) = (check(left), check(right));
        assert_eq!(left.base_logical_root, right.base_logical_root);
        assert_eq!(left.result_logical_root, right.result_logical_root);
        assert!(left.engine.environment() == right.engine.environment());
        assert_eq!(right.engine.environment().contains(&n("leftId")), has_left);
        assert_eq!(
            right.engine.environment().contains(&n("rightId")),
            has_right
        );
    }
}

#[test]
fn cold_mixed_and_warm_public_imports_match_at_one_and_eight_workers() {
    on_import_stack(|| {
        let artifacts = diamond();
        let all = inputs(&artifacts);
        let roots = [n("Main")];
        let options = KVMap::new();
        let engine = Engine::builder().build_empty();
        let checker = CheckerIdentity::of_executable(b"public parallel import fixture");
        let (serial, _) = engine
            .import_olean_modules_with_posture(
                &all,
                &roots,
                &options,
                limits(1),
                ImportPostureRequest::Recheck,
                None,
            )
            .unwrap()
            .into_complete()
            .unwrap();
        for threads in [1, 8] {
            for warm_base in [false, true] {
                let store = Memory::default();
                if warm_base {
                    let base: Vec<_> = all
                        .iter()
                        .copied()
                        .filter(|m| *m.name == n("Base"))
                        .collect();
                    engine
                        .import_olean_modules_with_posture(
                            &base,
                            &[n("Base")],
                            &options,
                            limits(threads),
                            reuse(checker, &store),
                            None,
                        )
                        .unwrap()
                        .into_complete()
                        .unwrap();
                }
                let run = || {
                    engine
                        .import_olean_modules_with_posture(
                            &all,
                            &roots,
                            &options,
                            limits(threads),
                            reuse(checker, &store),
                            None,
                        )
                        .unwrap()
                        .into_complete()
                        .unwrap()
                };
                let (actual, report) = run();
                assert_eq!(report.reused_modules, usize::from(warm_base));
                assert_eq!(report.council_modules, 4 - usize::from(warm_base));
                same_import(&serial, &actual);
                same_source_contexts(&serial, &actual);
                let (warm, report) = run();
                assert_eq!(report.record, RecordLookup::Hit);
                assert_eq!((report.reused_modules, report.council_modules), (4, 0));
                same_import(&serial, &warm);
                same_source_contexts(&serial, &warm);
            }
        }
    });
}

fn raw_module(name: &str, constants: &[ConstantInfo], imports: &[&str]) -> (Name, Vec<u8>) {
    let imports: Vec<_> = imports
        .iter()
        .map(|name| OleanModuleImport {
            module: n(name),
            import_all: false,
            is_exported: false,
            is_meta: false,
        })
        .collect();
    let encoded = encode_olean_module(
        OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: OLEAN_PIN_COMMIT,
            base_addr: (OLEAN_REGION_ALIGN as u64) * 2,
        },
        OleanWriteBudget::default(),
    )
    .unwrap();
    (n(name), encoded.bytes)
}

fn axiom(name: &str, type_: Expr) -> ConstantInfo {
    ConstantInfo::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: Vec::new(),
            type_,
        },
        is_unsafe: false,
    })
}

#[test]
fn parallel_public_import_reports_the_first_failure_and_publishes_no_records() {
    on_import_stack(|| {
        let p = Expr::const_(n("Fixture.P"), Vec::new());
        let artifacts = vec![
            raw_module(
                "Fixture.A",
                &[axiom("Fixture.P", Expr::sort(Level::zero()))],
                &[],
            ),
            raw_module(
                "Fixture.B",
                &[ConstantInfo::Thm(TheoremVal {
                    base: ConstantVal {
                        name: n("Fixture.bad"),
                        level_params: Vec::new(),
                        type_: p.clone(),
                    },
                    value: p,
                    all: Vec::new(),
                })],
                &["Fixture.A"],
            ),
            raw_module(
                "Fixture.C",
                &[axiom(
                    "Fixture.missing",
                    Expr::const_(n("Fixture.absent"), Vec::new()),
                )],
                &[],
            ),
        ];
        let all = inputs(&artifacts);
        let engine = Engine::builder().build_empty();
        let options = KVMap::new();
        let serial = engine
            .check_olean_modules(&all, &options, limits(1).check)
            .unwrap_err();
        assert!(matches!(serial, OleanCheckError::Admission(_)));
        for threads in [1, 8] {
            let store = Memory::default();
            let outcome = engine.import_olean_modules_with_posture(
                &all,
                &[n("Fixture.B"), n("Fixture.C")],
                &options,
                limits(threads),
                reuse(
                    CheckerIdentity::of_executable(b"public ordered failure fixture"),
                    &store,
                ),
                None,
            );
            assert!(
                matches!(outcome, Err(SourceOleanImportError::Check(error)) if *error == serial)
            );
            assert!(
                store.0.lock().unwrap().is_empty(),
                "failed work must not publish partial records"
            );
        }
    });
}
