use super::*;
use crate::source_check::modules::execution::SourceProgramLimits;
use crate::source_check::modules::imported::SourceOleanImportLimits;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 1 << 30;
const FIXTURE_MODULES: [&str; 4] = [
    "Init.Prelude",
    "Init.Data.String.Bootstrap",
    "Init.Data.String.Basic",
    "Init.Data.String.Length",
];
const FIXTURE_EXTERNS: [&str; 3] = ["String.length", "String.toList", "String.Internal.append"];
type Parts = [Vec<u8>; 3];

fn reference_library() -> Option<PathBuf> {
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|library| library.is_dir());
    if library.is_none() {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference library is required"
        );
        eprintln!("SKIP: pinned Reference lib/lean absent");
    }
    library
}

fn read_parts(library: &Path, module: &Name) -> Parts {
    let path = library
        .join(module.to_display_string().replace('.', "/"))
        .with_extension("olean");
    let optional = |path: PathBuf| match std::fs::read(&path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Vec::new(),
        Err(error) => panic!("{}: {error}", path.display()),
    };
    [
        std::fs::read(&path).unwrap(),
        optional(path.with_extension("olean.server")),
        optional(path.with_extension("olean.private")),
    ]
}

fn artifacts(library: &Path, root: &Name) -> BTreeMap<Name, Parts> {
    let mut pending = vec![root.clone()];
    let mut modules = BTreeMap::new();
    while let Some(module) = pending.pop() {
        if modules.contains_key(&module) {
            continue;
        }
        let parts = read_parts(library, &module);
        pending.extend(olean_module_imports(&parts[0], OleanDecodeLimits::new(BYTES)).unwrap());
        modules.insert(module, parts);
    }
    modules
}

#[test]
fn actual_pinned_string_declarations_match_the_complete_supported_contract() {
    let Some(library) = reference_library() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let expected = model();
            let needed: BTreeSet<_> = expected.iter().map(|info| info.name().clone()).collect();
            let mut environment = Environment::new();
            for module in FIXTURE_MODULES {
                let parts = read_parts(&library, &name(module));
                let decoded = decode_olean_module_artifacts(
                    &parts[0],
                    &parts[1],
                    &parts[2],
                    OleanDecodeLimits::new(BYTES),
                )
                .unwrap();
                for info in decoded
                    .constants
                    .into_iter()
                    .filter(|info| needed.contains(info.name()))
                {
                    environment = environment.add_decl(info).unwrap();
                }
            }
            // This test compares decodes only. The execution test below obtains its
            // authority from both native checking engines over actual artifact bytes.
            for expected in expected {
                let mut comparison = Comparison {
                    visited: &mut 0,
                    limits: IngressLimits::default(),
                };
                assert!(
                    comparison.constant(&environment, expected.clone()).unwrap(),
                    "pinned contract mismatch for {}: actual {:?}; expected {:?}",
                    expected.name().to_display_string(),
                    environment.find(expected.name()),
                    expected
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A diagnostic fixture, not an admitted module closure. It keeps actual
/// declarations and actual extern entries from exactly the four modules used
/// by the contract calibration above. No missing dependency is synthesized or
/// loaded from another module; the complete import gate below stays separate.
fn decoded_four_module_fixture(library: &Path) -> Engine {
    let mut constants = BTreeMap::<Name, ConstantInfo>::new();
    let mut native_externs = BTreeMap::new();
    for module in FIXTURE_MODULES {
        let parts = read_parts(library, &name(module));
        let decoded = decode_olean_module_artifacts(
            &parts[0],
            &parts[1],
            &parts[2],
            OleanDecodeLimits::new(BYTES),
        )
        .unwrap();
        let view = if decoded.module.is_module {
            fln_olean::region::OleanView::parse_with_dependencies(
                &parts[2],
                &[parts[0].as_slice(), parts[1].as_slice()],
            )
        } else {
            fln_olean::region::OleanView::parse(&parts[0])
        }
        .unwrap();
        let blocks = view
            .extension_payloads(OleanWalkBudget::default(), BYTES)
            .unwrap();
        let extensions = fln_olean::source_extensions::decode(
            &blocks,
            fln_olean::source_extensions::DecodeLimits::default(),
        )
        .unwrap();
        for attribute in extensions.externs {
            if !FIXTURE_EXTERNS
                .iter()
                .any(|label| attribute.declaration == name(label))
            {
                continue;
            }
            let entries: Vec<_> = attribute
                .entries
                .into_iter()
                .map(|entry| {
                    use fln_olean::source_extensions::ExternEntry as Artifact;
                    match entry {
                        Artifact::Adhoc { backend } => ExternEntry::Adhoc { backend },
                        Artifact::Inline { backend, pattern } => {
                            ExternEntry::Inline { backend, pattern }
                        }
                        Artifact::Standard { backend, symbol } => {
                            ExternEntry::Standard { backend, symbol }
                        }
                        Artifact::Opaque => ExternEntry::Opaque,
                    }
                })
                .collect();
            if let Some(previous) = native_externs.insert(attribute.declaration, entries.clone()) {
                assert_eq!(previous, entries, "conflicting actual fixture externs");
            }
        }
        for info in decoded.constants {
            let replace = if let Some(previous) = constants.get(info.name()) {
                if previous == &info {
                    false
                } else {
                    // Public views can repeat a theorem with a different
                    // actual proof body or with its public axiom header. Keep
                    // an actual theorem only when the full statement and its
                    // mutual envelope agree; this is not an import receipt.
                    assert_eq!(previous.constant_val(), info.constant_val());
                    match (previous, &info) {
                        (ConstantInfo::Thm(first), ConstantInfo::Thm(second)) => {
                            assert_eq!(first.all, second.all);
                            false
                        }
                        (ConstantInfo::Axiom(first), ConstantInfo::Thm(second))
                            if !first.is_unsafe
                                && second.all.as_slice()
                                    == std::slice::from_ref(&second.base.name) =>
                        {
                            true
                        }
                        (ConstantInfo::Thm(first), ConstantInfo::Axiom(second))
                            if !second.is_unsafe
                                && first.all.as_slice()
                                    == std::slice::from_ref(&first.base.name) =>
                        {
                            false
                        }
                        _ => panic!("unsupported raw-fixture duplicate: {:?}", info.name()),
                    }
                }
            } else {
                true
            };
            if replace {
                constants.insert(info.name().clone(), info);
            }
        }
    }
    let constant_count = constants.len();
    let mut environment = Environment::new();
    for info in constants.into_values() {
        environment = environment.add_decl(info).unwrap();
    }
    assert_eq!(native_externs.len(), FIXTURE_EXTERNS.len());
    for (declaration, entries) in native_externs {
        assert!(environment.contains(&declaration));
        environment = externs::register(&environment, &declaration, entries).unwrap();
    }
    let table = externs::ExternTable::read(&environment).unwrap();
    for label in FIXTURE_EXTERNS {
        assert_eq!(table.get(&name(label)), Some([canonical(label)].as_slice()));
    }
    eprintln!(
        "DECODED RAW STRING FIXTURE, NOT MODULE ADMISSION: {} modules, {constant_count} declarations",
        FIXTURE_MODULES.len()
    );
    Engine::from_environment(environment)
}

fn rebuild_environment(engine: &Engine, without: Option<&Name>, keep_externs: bool) -> Environment {
    let original = engine.environment();
    let mut environment = Environment::new();
    for (name, _) in original.constants() {
        if without != Some(name) {
            environment = environment
                .with_entry(original.entry(name).unwrap())
                .unwrap();
        }
    }
    for (name, state) in original.extensions() {
        if !keep_externs && name == &externs::journal_name() {
            continue;
        }
        environment = environment
            .register_extension(state.descriptor.clone())
            .unwrap();
        for entry in state.entries() {
            environment = environment
                .push_extension_entry(name, entry.payload.clone())
                .unwrap();
        }
    }
    environment
}

fn replace_checked_body(engine: &Engine, target: &str, body: Expr) -> Engine {
    let target = name(target);
    let Some(ConstantInfo::Defn(value)) = engine.environment().find(&target) else {
        panic!("actual safe string definition")
    };
    let mut value = value.clone();
    value.value = lambda(constant("String"), body);
    Engine::from_environment(rebuild_environment(engine, Some(&target), true))
        .admit_declaration(
            Declaration::Defn(value),
            &KVMap::new(),
            EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK)),
        )
        .expect("changed body is well typed under both checkers")
        .into_complete()
        .unwrap()
        .engine
}

fn query(label: &str) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(label),
            level_params: Vec::new(),
            type_: constant("Nat"),
        },
        value: Expr::app(
            constant("String.length"),
            Expr::lit(Literal::Str("λé😀".to_owned())),
        ),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(label)],
    })
}

#[test]
fn decoded_four_module_string_fixture_executes_unicode_without_import_admission() {
    let Some(library) = reference_library() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let engine = decoded_four_module_fixture(&library);
            let options = KVMap::new();
            let root = engine.logical_root(&options);
            let source = "#eval String.length \"\"\n#eval (\"é😀a\").length\n#eval String.length \"é\"\n#eval String.length (String.Internal.append \"λ\" \"é😀\")\n";
            let limits = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
            let run = || {
                engine
                    .execute_source_commands_with_checks(source.as_bytes(), &options, limits)
                    .expect("four-module raw fixture must suffice without loading more imports")
                    .into_complete()
                    .unwrap()
            };
            let first = run();
            let indices = &first.batch.source_evaluation_indices;
            assert_eq!(indices.len(), 4);
            for (&index, expected) in indices.iter().zip([0, 3, 2, 3]) {
                let execution = &first.batch.executions[index];
                assert_eq!(execution.checker.schema, "fln.checker-admission/1");
                assert_eq!(
                    execution.checker.ground,
                    CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
                );
                assert_eq!(
                    closed_vm_value(&execution.exit).unwrap(),
                    Some(ClosedVmValue::Scalar(expected))
                );
                let row = b"extern:String.length";
                assert!(execution.flbc_artifact.windows(row.len()).any(|bytes| bytes == row));
            }
            let repeated = run();
            assert_eq!(indices, &repeated.batch.source_evaluation_indices);
            for &index in indices {
                assert_eq!(
                    first.batch.executions[index].flbc_artifact,
                    repeated.batch.executions[index].flbc_artifact
                );
            }
            assert_eq!(engine.logical_root(&options), root);
            drop(repeated);
            drop(first);

            let wrong_length = replace_checked_body(
                &engine,
                "String.length",
                Expr::lit(Literal::Nat(NatLit::from_u64(37))),
            );
            let wrong_view = replace_checked_body(
                &engine,
                "String.toList",
                Expr::app(
                    Expr::const_(name("List.nil"), vec![Level::zero()]),
                    constant("Char"),
                ),
            );
            for changed in [&wrong_length, &wrong_view] {
                let before = changed.logical_root(&options);
                let failure = changed
                    .execute_definition(query("changedRawStringContract"), &options, limits)
                    .expect_err("a well-typed changed body must not acquire native string length");
                assert!(
                    matches!(failure, EngineExecutionError::Ingress(IngressError::UnsupportedNode { .. })),
                    "{failure:?}"
                );
                assert_eq!(changed.logical_root(&options), before);
            }
            let ordinary =
                Engine::from_environment(rebuild_environment(&wrong_length, None, false));
            let before = ordinary.logical_root(&options);
            let executed = ordinary
                .execute_definition(query("ordinaryRawStringLength"), &options, limits)
                .unwrap()
                .into_complete()
                .unwrap();
            assert_eq!(
                closed_vm_value(&executed.exit).unwrap(),
                Some(ClosedVmValue::Scalar(37))
            );
            assert_eq!(ordinary.logical_root(&options), before);
            assert_eq!(engine.logical_root(&options), root);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn admitted_public_string_length_executes_unicode_and_rejects_changed_checked_bodies() {
    let Some(library) = reference_library() else {
        return;
    };
    std::thread::Builder::new().stack_size(STACK).spawn(move || {
        let module = name("Init.Data.String.Length");
        let artifacts = artifacts(&library, &module);
        let inputs: Vec<_> = artifacts.iter().map(|(name, [public, server, private])| OleanModuleInput {
            name,
            artifact: public,
            server_artifact: (!server.is_empty()).then_some(server.as_slice()),
            private_artifact: (!private.is_empty()).then_some(private.as_slice()),
        }).collect();
        let options = KVMap::new();
        let mut admission = SourceOleanImportLimits::new(OleanCheckLimits::new(BYTES, Budget::for_stack_bytes(STACK)));
        admission.jobs = OleanFrontierJobs {
                    threads: std::num::NonZeroUsize::new(1).unwrap(),
            worker_stack_bytes: STACK,
        };
        let imported = Engine::from_environment(Environment::new())
            .import_olean_modules_for_source(&inputs, std::slice::from_ref(&module), &options, admission)
            .unwrap().into_complete().unwrap();
        assert!(imported.modules.iter().any(|report| report.module == module && report.externs > 0));
        let actual_externs = externs::ExternTable::read(imported.engine.environment()).unwrap();
        for target in ["String.length", "String.toList"] {
            assert_eq!(actual_externs.get(&name(target)), Some([canonical(target)].as_slice()),
                "real artifacts provide the execution contracts");
        }
        drop(inputs);
        drop(artifacts);
        eprintln!("String.Length closure admitted: {} modules", imported.modules.len());
        let root = imported.engine.logical_root(&options);
        let source = "prelude\nimport Init.Data.String.Length\n#eval String.length \"\"\n#eval (\"é😀a\").length\n#eval String.length \"é\"\n#eval String.length (String.Internal.append \"λ\" \"é😀\")\n";
        let entry = name("Main");
        let modules = [SourceModuleInput { name: &entry, source: source.as_bytes() }];
        let limits = SourceProgramLimits::new(EngineExecutionLimits::new(Budget::for_stack_bytes(STACK)));
        let run = || imported.execute_source_modules(&modules, &entry, &options, limits, None).unwrap().into_complete().unwrap();
        let first = run();
        let executions = &first.modules[0].commands.batch.executions;
        assert_eq!(executions.iter().map(|execution| closed_vm_value(&execution.exit).unwrap()).collect::<Vec<_>>(),
            [0, 3, 2, 3].map(|value| Some(ClosedVmValue::Scalar(value))));
        for execution in executions {
            let row = b"extern:String.length";
            assert!(execution.flbc_artifact.windows(row.len()).any(|bytes| bytes == row),
                "the canonical bytecode calls the real native string length row");
        }
        let repeated = run();
        assert_eq!(executions.iter().map(|execution| &execution.flbc_artifact).collect::<Vec<_>>(),
            repeated.modules[0].commands.batch.executions.iter().map(|execution| &execution.flbc_artifact).collect::<Vec<_>>());
        assert_eq!(imported.engine.logical_root(&options), root);

        drop(repeated);
        drop(first);
        let wrong_length = replace_checked_body(&imported.engine, "String.length", Expr::lit(Literal::Nat(NatLit::from_u64(37))));
        let wrong_view = replace_checked_body(&imported.engine, "String.toList", Expr::app(
            Expr::const_(name("List.nil"), vec![Level::zero()]), constant("Char"),
        ));
        for changed in [&wrong_length, &wrong_view] {
            let before = changed.logical_root(&options);
            let failure = changed.execute_definition(query("changedStringContract"), &options, limits.execution)
                .expect_err("a well-typed changed body cannot acquire the supported extern");
            assert!(matches!(failure, EngineExecutionError::Ingress(IngressError::UnsupportedNode { .. })), "{failure:?}");
            assert_eq!(changed.logical_root(&options), before);
        }
        let ordinary = Engine::from_environment(rebuild_environment(&wrong_length, None, false));
        let before = ordinary.logical_root(&options);
        let executed = ordinary.execute_definition(query("ordinaryStringLength"), &options, limits.execution).unwrap().into_complete().unwrap();
        assert_eq!(closed_vm_value(&executed.exit).unwrap(), Some(ClosedVmValue::Scalar(37)),
            "without the extern, an ordinary definition executes its own checked body");
        assert_eq!(ordinary.logical_root(&options), before);
        assert_eq!(imported.engine.logical_root(&options), root);
    }).unwrap().join().unwrap();
}
