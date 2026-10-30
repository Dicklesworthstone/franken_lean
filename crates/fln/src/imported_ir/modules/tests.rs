use super::*;
use crate::imported_ir::{
    CompiledIr, EntryArgument, IrExecutionError, IrExecutionLimits, IrNat, VerifiedPartition,
    compile,
};
use fln_comp::flbc;
use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir_archive::CensusPartition;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn artifacts(imports: &[&str], with_code: bool) -> ModuleArtifacts {
    let imports: Vec<_> = imports
        .iter()
        .map(|text| crate::OleanModuleImport {
            module: name(text),
            import_all: false,
            is_exported: false,
            is_meta: false,
        })
        .collect();
    let olean = crate::encode_olean_module(
        crate::OleanModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants: &[],
            extra_const_names: &[],
        },
        crate::OleanWriteHeader {
            version: 2,
            flags: 0,
            lean_version: "4.32.0",
            githash: crate::OLEAN_PIN_COMMIT,
            base_addr: 0x1000,
        },
        crate::OleanWriteBudget::default(),
    )
    .unwrap()
    .bytes;
    ModuleArtifacts {
        olean,
        ir: with_code.then(|| {
            include_bytes!("../../../../fln-olean/fixtures/ir/Init.Data.Nat.Basic.ir").to_vec()
        }),
    }
}

fn graph() -> BTreeMap<Name, ModuleArtifacts> {
    [
        ("Root", artifacts(&["Right", "Left", "Left"], false)),
        ("Left", artifacts(&["Dependency"], false)),
        ("Right", artifacts(&["Dependency"], false)),
        ("Dependency", artifacts(&[], true)),
    ]
    .into_iter()
    .map(|(module, bytes)| (name(module), bytes))
    .collect()
}

fn resolve(
    graph: &BTreeMap<Name, ModuleArtifacts>,
    roots: &[Name],
    limits: ModuleLoadLimits,
) -> Result<LoadedModules, ModuleLoadError> {
    load(roots, limits, |module, _remaining| {
        Ok(graph.get(module).cloned())
    })
}

fn policy(class: &str) -> VerifiedPartition {
    let key = "a/s\"Nat\"/s\"min\"";
    let text = format!("constant_count\t1\npartition\t{key:?}\t{class}\ttest-only\n");
    VerifiedPartition {
        partition: CensusPartition::parse(&text, GraphArchiveLimits::default()).unwrap(),
    }
}

fn program(modules: &LoadedModules, class: &str) -> Result<CompiledIr, IrExecutionError> {
    compile(
        modules.modules(),
        &name("Nat.min"),
        &[
            EntryArgument::Nat(IrNat::Small(42)),
            EntryArgument::Nat(IrNat::Small(99)),
        ],
        &policy(class),
        &BTreeSet::new(),
        IrExecutionLimits::default(),
    )
}

fn replay(modules: &LoadedModules) -> Vec<u8> {
    let compiled = program(modules, "library-code").unwrap();
    assert_eq!(compiled.reference_functions().len(), 1);
    assert_eq!(compiled.reference_functions()[0].producer(), "reference");
    let bytes =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&decoded, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    for code in [compiled.program.program(), &decoded] {
        match fln_vm::interpreter::execute(code, crate::VmExecutionLimits::default(), None) {
            crate::Outcome::Complete(crate::VmExit::Returned(value)) => {
                assert_eq!(crate::nat_decimal(&value.value).as_deref(), Some("42"));
            }
            outcome => panic!("{outcome:?}"),
        }
    }
    bytes
}

#[test]
fn transitive_diamond_loads_once_and_executes_real_reference_ir() {
    let graph = graph();
    let mut calls = Vec::new();
    let mut previous_remaining = usize::MAX;
    let loaded = load(
        &[name("Root"), name("Root")],
        ModuleLoadLimits::default(),
        |module, remaining| {
            assert!(remaining < previous_remaining);
            previous_remaining = remaining;
            calls.push(module.clone());
            Ok(graph.get(module).cloned())
        },
    )
    .unwrap();
    assert_eq!(calls.len(), 4);
    assert_eq!(calls.iter().cloned().collect::<BTreeSet<_>>().len(), 4);
    assert_eq!(
        loaded.module_names(),
        graph.keys().cloned().collect::<Vec<_>>()
    );
    assert_eq!(
        loaded.missing_ir_modules(),
        [name("Left"), name("Right"), name("Root")]
    );
    assert_eq!(
        loaded.bytes_read(),
        graph
            .values()
            .map(|a| a.olean.len() + a.ir.as_ref().map_or(0, Vec::len))
            .sum::<usize>()
    );
    replay(&loaded);
}

#[test]
fn root_and_import_order_cannot_change_code_identity() {
    let mut graph = graph();
    let first = resolve(
        &graph,
        &[name("Root"), name("Left")],
        ModuleLoadLimits::default(),
    )
    .unwrap();
    graph.insert(name("Root"), artifacts(&["Left", "Right", "Left"], false));
    let second = resolve(
        &graph,
        &[name("Left"), name("Root")],
        ModuleLoadLimits::default(),
    )
    .unwrap();
    assert_eq!(first.module_names(), second.module_names());
    assert_eq!(first.modules(), second.modules());
    assert_eq!(replay(&first), replay(&second));
}

#[test]
fn module_labels_and_imports_grant_no_execution_classification() {
    let loaded = resolve(&graph(), &[name("Root")], ModuleLoadLimits::default()).unwrap();
    assert!(matches!(
        program(&loaded, "toolchain-api"),
        Err(IrExecutionError::ToolchainApi(_))
    ));
    let users = BTreeSet::from([name("Nat.min")]);
    assert!(matches!(
        compile(
            loaded.modules(),
            &name("Nat.min"),
            &[],
            &policy("library-code"),
            &users,
            IrExecutionLimits::default()
        ),
        Err(IrExecutionError::UserOverridesCensus(_))
    ));
    replay(&loaded);
}

#[test]
fn absent_code_is_reported_and_does_not_invent_a_definition() {
    let graph = BTreeMap::from([(name("Root"), artifacts(&[], false))]);
    let loaded = resolve(&graph, &[name("Root")], ModuleLoadLimits::default()).unwrap();
    assert_eq!(loaded.missing_ir_modules(), [name("Root")]);
    assert!(matches!(
        program(&loaded, "library-code"),
        Err(IrExecutionError::MissingDeclaration(_))
    ));
}

#[test]
fn missing_modules_and_cycles_are_distinct_failures() {
    let mut graph = graph();
    graph.remove(&name("Dependency"));
    assert!(matches!(
        resolve(&graph, &[name("Root")], ModuleLoadLimits::default()),
        Err(ModuleLoadError::MissingModule(module)) if module == name("Dependency")
    ));
    for imports in [&["Root"][..], &["Left"][..]] {
        graph.insert(name("Root"), artifacts(imports, false));
        graph.insert(name("Left"), artifacts(&["Root"], false));
        assert!(matches!(
            resolve(&graph, &[name("Root")], ModuleLoadLimits::default()),
            Err(ModuleLoadError::ImportCycle(_))
        ));
    }
}

#[test]
fn cumulative_limits_stop_the_whole_load_and_retries_start_clean() {
    let graph = graph();
    let roots = [name("Root")];
    let baseline = resolve(&graph, &roots, ModuleLoadLimits::default()).unwrap();
    let total_declarations = baseline.modules().iter().map(|m| m.decls.len()).sum();
    let exact = ModuleLoadLimits {
        max_modules: 4,
        max_bytes: baseline.bytes_read(),
        max_imports: 5,
        max_declarations: total_declarations,
    };
    assert_eq!(
        resolve(&graph, &roots, exact).unwrap().modules(),
        baseline.modules()
    );
    for limits in [
        ModuleLoadLimits {
            max_modules: 3,
            ..exact
        },
        ModuleLoadLimits {
            max_bytes: exact.max_bytes - 1,
            ..exact
        },
        ModuleLoadLimits {
            max_imports: 4,
            ..exact
        },
        ModuleLoadLimits {
            max_declarations: 0,
            ..exact
        },
    ] {
        assert!(resolve(&graph, &roots, limits).unwrap_err().is_resource());
        assert_eq!(
            resolve(&graph, &roots, exact).unwrap().modules(),
            baseline.modules()
        );
    }
    let mut called = false;
    assert!(
        load(
            &roots,
            ModuleLoadLimits {
                max_modules: 0,
                ..exact
            },
            |_, _| {
                called = true;
                Ok(None)
            }
        )
        .unwrap_err()
        .is_resource()
    );
    assert!(!called);
    assert!(matches!(
        load(&[], exact, |_, _| panic!("no root")),
        Err(ModuleLoadError::NoRoots)
    ));
}

#[test]
fn malformed_companions_are_not_treated_as_missing_code() {
    for bad_olean in [false, true] {
        let mut input = artifacts(&[], true);
        if bad_olean {
            input.olean = b"not an olean".to_vec();
        } else {
            input.ir = Some(b"not IR".to_vec());
        }
        let result = load(
            &[name("Broken")],
            ModuleLoadLimits::default(),
            |_, _| Ok(Some(input.clone())),
        );
        assert!(matches!(
            result,
            Err(ModuleLoadError::Decode {
                resource: false,
                ..
            })
        ));
    }
}

#[test]
fn different_module_names_cannot_hide_duplicate_declarations() {
    let graph = BTreeMap::from([
        (name("First"), artifacts(&[], true)),
        (name("Second"), artifacts(&[], true)),
    ]);
    let loaded = resolve(
        &graph,
        &[name("First"), name("Second")],
        ModuleLoadLimits::default(),
    )
    .unwrap();
    assert!(matches!(
        program(&loaded, "library-code"),
        Err(IrExecutionError::DuplicateDeclaration(_))
    ));
}

#[test]
fn resolver_failures_remain_failures_instead_of_partial_closures() {
    let graph = graph();
    let result = load(
        &[name("Root")],
        ModuleLoadLimits::default(),
        |module, _| {
            if module == &name("Dependency") {
                Err(ModuleLoadError::Resolve {
                    module: module.clone(),
                    detail: "unavailable".to_owned(),
                })
            } else {
                Ok(graph.get(module).cloned())
            }
        },
    );
    assert!(matches!(result, Err(ModuleLoadError::Resolve { .. })));
    replay(&resolve(&graph, &[name("Root")], ModuleLoadLimits::default()).unwrap());
}
