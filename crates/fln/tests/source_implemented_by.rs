//! Real serialized metadata crosses both checkers before native execution.
#![forbid(unsafe_code)]
use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::imported::{
    SourceOleanImport, SourceOleanImportError, SourceOleanImportLimits,
};
use fln::source_check::modules::reuse::{
    CheckerIdentity, ImportClosureKey, ImportPostureRequest, ImportReuseStore, ReuseVerified,
};
use fln::*;
use fln_elab::implemented_by::ImplementedByTable;
use fln_olean::source_extensions::IMPLEMENTED_BY_EXTENSION;
use fln_olean::{ModuleExtensionInput, encode_module_with_extensions};
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use std::collections::BTreeMap;
use std::num::NonZeroUsize;
use std::sync::Mutex;

const STACK: usize = 16 << 20;
type Artifacts = Vec<(Name, Vec<u8>)>;

fn n(label: &str) -> Name {
    Name::from_components(label.split('.'))
}
fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(2 << 20))
}
fn execution() -> EngineExecutionLimits {
    EngineExecutionLimits::new(admission().kernel)
}
fn limits(threads: usize) -> SourceOleanImportLimits {
    let jobs = OleanFrontierJobs {
        threads: NonZeroUsize::new(threads).unwrap(),
        worker_stack_bytes: STACK,
    };
    SourceOleanImportLimits {
        jobs,
        read_jobs: jobs,
        ..SourceOleanImportLimits::new(OleanCheckLimits::new(32 << 20, admission().kernel))
    }
}
fn seed() -> Engine {
    Engine::with_source_seed(admission())
        .unwrap()
        .into_complete()
        .unwrap()
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
fn added(base: &Engine, source: &str) -> Vec<ConstantInfo> {
    base.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(admission()),
    )
    .unwrap_or_else(|error| panic!("{source}\n{error:?}"))
    .into_complete()
    .unwrap()
    .engine
    .environment()
    .constants()
    .filter(|(name, _)| !base.environment().contains(name))
    .map(|(_, constant)| constant.clone())
    .collect()
}
fn row(source: &str, implementation: &str) -> Obj {
    Obj::mk_ctor(
        0,
        vec![inject_name(&n(source)), inject_name(&n(implementation))],
        &[],
    )
}
fn encode(constants: &[ConstantInfo], imports: &[&str], rows: Vec<Obj>) -> Vec<u8> {
    let extension = n(IMPLEMENTED_BY_EXTENSION);
    encode_extensions(
        constants,
        imports,
        &[ModuleExtensionInput {
            name: &extension,
            entries: &rows,
        }],
    )
}
fn encode_extensions(
    constants: &[ConstantInfo],
    imports: &[&str],
    extensions: &[ModuleExtensionInput<'_>],
) -> Vec<u8> {
    let imports: Vec<_> = imports
        .iter()
        .map(|module| OleanModuleImport {
            module: n(module),
            import_all: false,
            is_exported: true,
            is_meta: false,
        })
        .collect();
    encode_module_with_extensions(
        OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        extensions,
        OleanWriteHeader {
            version: OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap(),
            githash: OLEAN_PIN_COMMIT,
            base_addr: (OLEAN_REGION_ALIGN as u64) * 2,
        },
        OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes
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
fn import(
    base: &Engine,
    artifacts: &Artifacts,
    roots: &[Name],
    threads: usize,
) -> SourceOleanImport {
    base.import_olean_modules_for_source(&inputs(artifacts), roots, &KVMap::new(), limits(threads))
        .unwrap()
        .into_complete()
        .unwrap()
}
fn returned(exit: &VmExit, expected: &str) {
    let VmExit::Returned(value) = exit else {
        panic!("runtime did not return: {exit:?}")
    };
    assert_eq!(nat_decimal(&value.value).as_deref(), Some(expected));
}
fn evaluate(engine: &Engine, expression: &str, expected: &str) {
    let source = format!("#eval {expression}");
    let run = engine
        .execute_source_definitions(&[source.as_bytes()], &KVMap::new(), execution())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_complete()
        .unwrap();
    let value = run.executions.last().unwrap();
    returned(&value.exit, expected);
    let replay = execute_flbc_artifact(&value.flbc_artifact, &KVMap::new(), Default::default())
        .unwrap()
        .into_complete()
        .unwrap();
    returned(&replay, expected);
}

#[test]
fn imported_replacements_execute_through_direct_alias_higher_order_and_staged_calls() {
    on_stack(|| {
        let base = seed();
        let constants = added(
            &base,
            r#"
def original (x : Nat) : Nat := 0
def replacement (x : Nat) : Nat := x + 1
def alias : Nat -> Nat := original
def invoke (f : Nat -> Nat) (x : Nat) : Nat := f x
def logicalMaker (n : Nat) : Nat -> Nat := fun (x : Nat) => 0
def actualMaker (n : Nat) : Nat -> Nat := let paid : Nat := n + 1; fun (x : Nat) => paid + x
def polyOriginal.{u} {A : Sort u} (x y : A) : A := x
def polyReplacement.{v} {B : Sort v} (a b : B) : B := b
structure Box where
  value : Nat
def logicalBox : Box := Box.mk 0
def actualBox : Box := Box.mk 42
def aliasBox : Box := logicalBox
"#,
        );
        let artifacts = vec![(
            n("Library"),
            encode(
                &constants,
                &[],
                vec![
                    row("original", "replacement"),
                    row("logicalMaker", "actualMaker"),
                    row("polyOriginal", "polyReplacement"),
                    row("logicalBox", "actualBox"),
                ],
            ),
        )];
        let imported = import(&base, &artifacts, &[n("Library")], 1);
        assert_eq!(imported.modules[0].implemented_by, 4);
        assert!(imported.modules[0].uninterpreted.is_empty());
        assert_eq!(
            ImplementedByTable::read(imported.engine.environment())
                .unwrap()
                .len(),
            4
        );
        for constant in &constants {
            assert_eq!(
                imported.engine.environment().find(constant.name()),
                Some(constant)
            );
        }
        for (expression, expected) in [
            ("original 40", "41"),
            ("alias 40", "41"),
            ("invoke original 40", "41"),
            ("let f : Nat -> Nat := original; f 40", "41"),
            ("logicalMaker 20 21", "42"),
            (
                "let make : Nat -> Nat -> Nat := logicalMaker; make 20 21",
                "42",
            ),
            ("polyOriginal 7 42", "42"),
            ("Box.value aliasBox", "42"),
        ] {
            evaluate(&imported.engine, expression, expected);
        }
        let proof = imported.engine.check_source_files(
            &[b"theorem stillLogical : original 40 = 0 := by rfl\ntheorem stillFirst : polyOriginal 7 42 = 7 := by rfl"],
            &KVMap::new(), SourceCheckLimits::new(admission()),
        ).unwrap().into_complete().unwrap();
        assert!(proof.engine.environment().contains(&n("stillLogical")));
        assert!(!base.environment().contains(&n("original")));
    });
}

#[test]
fn replacement_chains_and_checked_partial_targets_use_their_executable_bodies() {
    on_stack(|| {
        let base = seed();
        let mut constants = added(
            &base,
            "def original (x : Nat) : Nat := 0\ndef middle (x : Nat) : Nat := 1\ndef actual (x : Nat) : Nat := x + 2",
        );
        let actual = constants
            .iter()
            .find(|constant| constant.name() == &n("actual"))
            .unwrap();
        let ConstantInfo::Defn(actual) = actual else {
            panic!("definition")
        };
        let mut partial = actual.clone();
        partial.base.name = n("loop._unsafe_rec");
        partial.safety = DefinitionSafety::Partial;
        partial.all = vec![partial.base.name.clone()];
        let mut logical = actual.base.clone();
        logical.name = n("loop");
        constants.push(ConstantInfo::Opaque(OpaqueVal {
            base: logical,
            value: actual.value.clone(),
            is_unsafe: false,
            all: vec![n("loop")],
        }));
        constants.push(ConstantInfo::Defn(partial));
        let artifacts = vec![(
            n("Library"),
            encode(
                &constants,
                &[],
                vec![row("original", "middle"), row("middle", "loop")],
            ),
        )];
        let imported = import(&base, &artifacts, &[n("Library")], 1);
        assert_eq!(
            ImplementedByTable::read(imported.engine.environment())
                .unwrap()
                .implementation(&n("original")),
            Some(&n("loop"))
        );
        evaluate(&imported.engine, "original 40", "42");
    });
}

#[test]
fn unsafe_or_unsupported_extern_replacements_refuse_instead_of_running_logical_defaults() {
    on_stack(|| {
        let base = seed();
        let mut constants = added(
            &base,
            "def original (x : Nat) : Nat := 0\ndef actual (x : Nat) : Nat := x + 2",
        );
        let constant = constants
            .iter_mut()
            .find(|constant| constant.name() == &n("actual"))
            .unwrap();
        let ConstantInfo::Defn(actual) = constant else {
            panic!("definition")
        };
        actual.safety = DefinitionSafety::Unsafe;
        let artifacts = vec![(
            n("Library"),
            encode(&constants, &[], vec![row("original", "actual")]),
        )];
        let imported = import(&base, &artifacts, &[n("Library")], 1);
        let root = imported.result_logical_root;
        let error = imported
            .engine
            .execute_source_definitions(&[b"#eval original 40"], &KVMap::new(), execution())
            .unwrap_err();
        assert!(
            format!("{error:?}")
                .contains("implemented_by target has no supported safe or partial executable body")
        );
        assert_eq!(imported.engine.logical_root(&KVMap::new()), root);

        let checked = base
            .check_source_files(
                &[b"def logical (x : Nat) : Nat := 0\ndef selected (x : Nat) : Nat := x + 2"],
                &KVMap::new(),
                SourceCheckLimits::new(admission()),
            )
            .unwrap()
            .into_complete()
            .unwrap()
            .engine;
        let env = fln_elab::implemented_by::register(
            checked.environment(),
            &n("logical"),
            &n("selected"),
        )
        .unwrap();
        let env = fln_elab::externs::register(
            &env,
            &n("selected"),
            vec![fln_elab::externs::ExternEntry::Standard {
                backend: n("all"),
                symbol: "unavailable_implementation".into(),
            }],
        )
        .unwrap();
        let engine = Engine::from_environment(env);
        let error = engine
            .execute_source_definitions(&[b"#eval logical 40"], &KVMap::new(), execution())
            .unwrap_err();
        assert!(
            format!("{error:?}")
                .contains("native extern attribute does not match the supported ABI")
        );
    });
}

#[test]
fn malformed_duplicate_cyclic_and_cross_module_attributes_return_no_import() {
    on_stack(|| {
        let base = seed();
        let before = base.logical_root(&KVMap::new());
        let constants = added(
            &base,
            "def original (x : Nat) : Nat := 0\ndef actual (x : Nat) : Nat := x + 2\ndef wrong (x : Nat) : Bool := false",
        );
        for rows in [
            vec![row("original", "absent")],
            vec![row("original", "wrong")],
            vec![row("original", "original")],
            vec![row("original", "actual"), row("original", "actual")],
            vec![row("original", "actual"), row("actual", "original")],
            vec![row("Nat.add", "actual")],
            vec![row("original", "actual"), Obj::mk_nat(0)],
        ] {
            let artifacts = vec![(n("Library"), encode(&constants, &[], rows))];
            assert!(
                base.import_olean_modules_for_source(
                    &inputs(&artifacts),
                    &[n("Library")],
                    &KVMap::new(),
                    limits(1)
                )
                .is_err()
            );
            assert_eq!(base.logical_root(&KVMap::new()), before);
            assert!(!base.environment().contains(&n("original")));
        }
        let own: Vec<_> = constants
            .iter()
            .filter(|c| c.name() == &n("original"))
            .cloned()
            .collect();
        let other: Vec<_> = constants
            .iter()
            .filter(|c| c.name() == &n("actual"))
            .cloned()
            .collect();
        let roots = [n("Own"), n("Other")];
        for rows in [
            vec![row("original", "actual")],
            vec![row("actual", "original")],
        ] {
            let artifacts = vec![
                (n("Own"), encode(&own, &[], rows)),
                (n("Other"), encode(&other, &[], vec![])),
            ];
            let error = base
                .import_olean_modules_for_source(
                    &inputs(&artifacts),
                    &roots,
                    &KVMap::new(),
                    limits(8),
                )
                .unwrap_err();
            assert!(matches!(error, SourceOleanImportError::Metadata { .. }));
        }
        let valid = vec![
            (
                n("Own"),
                encode(&own, &["Other"], vec![row("original", "actual")]),
            ),
            (n("Other"), encode(&other, &[], vec![])),
        ];
        evaluate(
            &import(&base, &valid, &[n("Own")], 8).engine,
            "original 40",
            "42",
        );
    });
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

fn own_context(imported: &SourceOleanImport) {
    let root = n("Consumer");
    let run = imported
        .execute_source_modules(
            &[SourceModuleInput {
                name: &root,
                source: b"prelude\nimport Own\n#eval original 40",
            }],
            &root,
            &KVMap::new(),
            SourceProgramLimits::new(execution()),
            None,
        )
        .unwrap()
        .into_complete()
        .unwrap();
    returned(
        &run.modules
            .last()
            .unwrap()
            .commands
            .batch
            .executions
            .last()
            .unwrap()
            .exit,
        "42",
    );
}

#[test]
fn metadata_and_executable_selection_survive_cold_mixed_and_warm_import_reuse() {
    on_stack(|| {
        let base = seed();
        let own = added(&base, "def original (x : Nat) : Nat := 0");
        let other = added(&base, "def actual (x : Nat) : Nat := x + 2");
        let artifacts = vec![
            (
                n("Own"),
                encode(&own, &["Other"], vec![row("original", "actual")]),
            ),
            (n("Other"), encode(&other, &[], vec![])),
        ];
        let all = inputs(&artifacts);
        let roots = [n("Own")];
        let serial = import(&base, &artifacts, &roots, 1);
        let checker = CheckerIdentity::of_executable(b"implemented_by native import fixture");
        for threads in [1, 8] {
            for warm_dependency in [false, true] {
                let store = Memory::default();
                let request = || {
                    ImportPostureRequest::ReuseVerified(ReuseVerified {
                        checker,
                        store: &store,
                    })
                };
                if warm_dependency {
                    base.import_olean_modules_with_posture(
                        &[all[1]],
                        &[n("Other")],
                        &KVMap::new(),
                        limits(threads),
                        request(),
                        None,
                    )
                    .unwrap()
                    .into_complete()
                    .unwrap();
                }
                for _ in 0..2 {
                    let (actual, _) = base
                        .import_olean_modules_with_posture(
                            &all,
                            &roots,
                            &KVMap::new(),
                            limits(threads),
                            request(),
                            None,
                        )
                        .unwrap()
                        .into_complete()
                        .unwrap();
                    assert_eq!(serial.modules, actual.modules);
                    assert_eq!(serial.result_logical_root, actual.result_logical_root);
                    assert_eq!(serial.engine.environment(), actual.engine.environment());
                    assert_eq!(
                        serial
                            .checked
                            .modules
                            .iter()
                            .map(|m| &m.declarations)
                            .collect::<Vec<_>>(),
                        actual
                            .checked
                            .modules
                            .iter()
                            .map(|m| &m.declarations)
                            .collect::<Vec<_>>()
                    );
                    own_context(&actual);
                }
            }
        }
    });
}

#[test]
fn imported_opaque_values_execute_while_the_kernel_keeps_them_opaque() {
    on_stack(|| {
        let base = seed();
        let constants = added(
            &base,
            r#"
opaque hidden : Nat := 42
opaque hiddenIdentity.{u} {A : Sort u} (x : A) : A := x
opaque hiddenMaker (n : Nat) : Nat -> Nat := fun m => n + m
def hiddenAlias : Nat := hidden
"#,
        );
        let artifacts = vec![(n("Own"), encode(&constants, &[], vec![]))];
        let imported = import(&base, &artifacts, &[n("Own")], 1);
        for expression in [
            "hidden",
            "hiddenAlias",
            "hiddenIdentity 42",
            "hiddenMaker 20 22",
            "let f : Nat -> Nat := hiddenMaker 20; f 22",
        ] {
            evaluate(&imported.engine, expression, "42");
        }
        assert!(
            imported
                .engine
                .check_source_files(
                    &[b"theorem revealHidden : hidden = 42 := by rfl"],
                    &KVMap::new(),
                    SourceCheckLimits::new(admission()),
                )
                .is_err(),
            "executable opacity must not become logical transparency"
        );
        // The same declarations without the private import lineage cannot
        // inherit executable-body authority from their spelling or raw values.
        let detached = Engine::from_environment(imported.engine.environment().clone());
        assert!(
            detached
                .execute_source_definitions(&[b"#eval hidden"], &KVMap::new(), execution())
                .is_err()
        );
    });
}

#[test]
fn initialized_globals_never_execute_stored_placeholder_values() {
    on_stack(|| {
        let base = seed();
        let constants = added(
            &base,
            r#"
def IO (A : Type) : Type := A
opaque hidden : Nat := 0
def globalDefinition : Nat := 0
def initializeHidden : IO Nat := (42 : Nat)
opaque ordinary : Nat := 42
structure InitializedBox where
  value : Nat
def initializedBox : InitializedBox := InitializedBox.mk 0
def initializeBox : IO InitializedBox := InitializedBox.mk 42
def initializedBoxAlias : InitializedBox := initializedBox
"#,
        );
        for extension in [
            fln_olean::initializers::REGULAR_INIT_EXTENSION,
            fln_olean::initializers::BUILTIN_INIT_EXTENSION,
        ] {
            let extension = n(extension);
            let entries = [
                row("hidden", "initializeHidden"),
                row("globalDefinition", "initializeHidden"),
                row("initializedBox", "initializeBox"),
            ];
            let artifacts = vec![(
                n("Own"),
                encode_extensions(
                    &constants,
                    &[],
                    &[ModuleExtensionInput {
                        name: &extension,
                        entries: &entries,
                    }],
                ),
            )];
            let imported = import(&base, &artifacts, &[n("Own")], 1);
            assert!(!imported.modules[0].uninterpreted.contains(&extension));
            assert_eq!(
                imported.modules[0].regular_initializers + imported.modules[0].builtin_initializers,
                3
            );
            evaluate(&imported.engine, "ordinary", "42");
            for expression in [
                "hidden",
                "globalDefinition",
                "initializedBox.value",
                "initializedBoxAlias.value",
                "let box : InitializedBox := initializedBox; box.value",
            ] {
                let source = format!("#eval {expression}");
                assert!(
                    imported
                        .engine
                        .execute_source_definitions(
                            &[source.as_bytes()],
                            &KVMap::new(),
                            execution()
                        )
                        .is_err(),
                    "{extension:?}: {expression} must await its initializer"
                );
            }
        }
    });
}

#[test]
fn initializer_metadata_validates_ownership_duplicates_and_exact_action_types() {
    on_stack(|| {
        let base = seed();
        let own = added(
            &base,
            "def IO (A : Type) : Type := A\nopaque own : Nat := 42\ndef initOwn : IO Nat := (0 : Nat)",
        );
        let other = added(&base, "opaque other : Nat := 42");
        let extension = n(fln_olean::initializers::REGULAR_INIT_EXTENSION);
        for entries in [
            vec![row("other", "initOwn")],
            vec![row("own", "missingInitializer")],
            vec![row("own", "initOwn"), row("own", "initOwn")],
            vec![row("own", "own")],
            vec![Obj::mk_ctor(
                0,
                vec![inject_name(&n("own")), inject_name(&Name::anonymous())],
                &[],
            )],
        ] {
            let artifacts = vec![
                (
                    n("Own"),
                    encode_extensions(
                        &own,
                        &["Other"],
                        &[ModuleExtensionInput {
                            name: &extension,
                            entries: &entries,
                        }],
                    ),
                ),
                (n("Other"), encode(&other, &[], vec![])),
            ];
            assert!(matches!(
                base.import_olean_modules_for_source(
                    &inputs(&artifacts),
                    &[n("Own")],
                    &KVMap::new(),
                    limits(1)
                ),
                Err(SourceOleanImportError::Metadata { .. })
            ));
        }
    });
}

#[test]
fn opaque_execution_classification_survives_reuse_and_each_modules_import_world() {
    on_stack(|| {
        let base = seed();
        let own = added(
            &base,
            "opaque original (x : Nat) : Nat := x + 2\ndef IO (A : Type) : Type := A\nopaque waiting : Nat := 0\ndef initializeWaiting : IO Nat := (17 : Nat)",
        );
        let other = added(&base, "opaque inaccessible : Nat := 17");
        let extension = n(fln_olean::initializers::REGULAR_INIT_EXTENSION);
        let entries = [row("waiting", "initializeWaiting")];
        let artifacts = vec![
            (
                n("Own"),
                encode_extensions(
                    &own,
                    &[],
                    &[ModuleExtensionInput {
                        name: &extension,
                        entries: &entries,
                    }],
                ),
            ),
            (n("Other"), encode(&other, &[], vec![])),
        ];
        let roots = [n("Own"), n("Other")];
        let store = Memory::default();
        let checker = CheckerIdentity::of_executable(b"opaque classification fixture");
        let mut logical_root = None;
        for threads in [1, 8, 32] {
            let (imported, _) = base
                .import_olean_modules_with_posture(
                    &inputs(&artifacts),
                    &roots,
                    &KVMap::new(),
                    limits(threads),
                    ImportPostureRequest::ReuseVerified(ReuseVerified {
                        checker,
                        store: &store,
                    }),
                    None,
                )
                .unwrap()
                .into_complete()
                .unwrap();
            if let Some(expected) = &logical_root {
                assert_eq!(expected, &imported.result_logical_root);
            } else {
                logical_root = Some(imported.result_logical_root);
            }
            own_context(&imported);
            let consumer = n("Consumer");
            assert!(
                imported
                    .engine
                    .execute_source_definitions(&[b"#eval waiting"], &KVMap::new(), execution())
                    .is_err(),
                "reusing a record must preserve initialized-global classification"
            );
            assert!(
                imported
                    .execute_source_modules(
                        &[SourceModuleInput {
                            name: &consumer,
                            source: b"prelude\nimport Own\n#eval waiting",
                        }],
                        &consumer,
                        &KVMap::new(),
                        SourceProgramLimits::new(execution()),
                        None,
                    )
                    .is_err(),
                "module projection must preserve initialized-global classification"
            );
            assert!(
                imported
                    .execute_source_modules(
                        &[SourceModuleInput {
                            name: &consumer,
                            source: b"prelude\nimport Own\n#eval inaccessible",
                        }],
                        &consumer,
                        &KVMap::new(),
                        SourceProgramLimits::new(execution()),
                        None,
                    )
                    .is_err(),
                "an unrelated root's opaque cannot enter a module's import world"
            );
        }
    });
}
