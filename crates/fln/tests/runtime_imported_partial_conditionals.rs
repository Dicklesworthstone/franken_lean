//! Pinned partial bodies cross ordinary council admission and run natively.
//! Reference Lean only produces fixture artifacts; it never runs product code.
#![forbid(unsafe_code)]

use fln::source_check::modules::execution::SourceProgramLimits;
use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, ClosedVmValue, Engine, EngineExecutionLimits, Environment, KVMap, Name,
    OleanCheckLimits, OleanDecodeLimits, OleanFrontierJobs, OleanModuleInput, SourceModuleInput,
};
use fln_core::outcome::Outcome;
use std::collections::BTreeMap;
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::Command;

const STACK: usize = 256 * 1024 * 1024;
const BYTES: usize = 256 * 1024 * 1024;
const FIXTURE: &str = include_str!("fixtures/PartialRuntime.lean");

type OleanParts = (Vec<u8>, Option<Vec<u8>>, Option<Vec<u8>>);

fn name(value: &str) -> Name {
    Name::from_components(value.split('.'))
}

fn reference() -> Option<(PathBuf, PathBuf)> {
    let default = std::env::var_os("HOME")
        .map(|home| PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0"));
    let lean = std::env::var_os("FLN_REFERENCE_BIN")
        .map(PathBuf::from)
        .or_else(|| default.as_ref().map(|root| root.join("bin/lean")));
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| default.map(|root| root.join("lib/lean")));
    match (lean, lib) {
        (Some(lean), Some(lib)) if lean.is_file() && lib.is_dir() => Some((lean, lib)),
        _ => {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "the pinned Reference binary and library are required"
            );
            eprintln!("SKIP: pinned Reference binary or library unavailable");
            None
        }
    }
}

fn fixture_directory() -> PathBuf {
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let path = std::env::temp_dir().join(format!(
        "fln-imported-partial-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir(&path).unwrap();
    path
}

fn artifacts(root: &Name, fixture: &Path, lib: &Path) -> BTreeMap<Name, OleanParts> {
    let mut pending = vec![root.clone()];
    let mut modules = BTreeMap::new();
    while let Some(module) = pending.pop() {
        if modules.contains_key(&module) {
            continue;
        }
        let relative = module.to_display_string().replace('.', "/");
        let path = [fixture, lib]
            .into_iter()
            .map(|base| base.join(&relative).with_extension("olean"))
            .find(|path| path.is_file())
            .unwrap_or_else(|| panic!("missing actual module {relative}"));
        let read_optional = |path: PathBuf| match std::fs::read(path) {
            Ok(bytes) => Some(bytes),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => panic!("reading fixture companion: {error}"),
        };
        let public = std::fs::read(&path).unwrap();
        pending.extend(fln::olean_module_imports(&public, OleanDecodeLimits::new(BYTES)).unwrap());
        modules.insert(
            module,
            (
                public,
                read_optional(path.with_extension("olean.server")),
                read_optional(path.with_extension("olean.private")),
            ),
        );
    }
    modules
}

#[test]
fn actual_partial_bodies_preserve_recursion_mutual_calls_and_lazy_conditionals() {
    let Some((lean, lib)) = reference() else {
        return;
    };
    let expected_commit = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|field| field.strip_prefix("commit="))
        })
        .expect("Reference commit in SUITE.lock");
    let version = Command::new(&lean).arg("--githash").output().unwrap();
    assert!(
        version.status.success(),
        "{}",
        String::from_utf8_lossy(&version.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&version.stdout).trim(),
        expected_commit
    );
    let fixture = fixture_directory();
    std::fs::write(fixture.join("PartialRuntime.lean"), FIXTURE).unwrap();
    let produced = Command::new(&lean)
        .current_dir(&fixture)
        .args(["-o", "PartialRuntime.olean", "PartialRuntime.lean"])
        .output()
        .unwrap();
    assert!(
        produced.status.success(),
        "fixture build: {}{}",
        String::from_utf8_lossy(&produced.stdout),
        String::from_utf8_lossy(&produced.stderr)
    );
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || {
            let root_module = name("PartialRuntime");
            let artifacts = artifacts(&root_module, &fixture, &lib);
            assert_eq!(
                artifacts.len(),
                4,
                "bounded actual Init.Notation closure plus fixture"
            );
            let modules: Vec<_> = artifacts
                .iter()
                .map(|(module, (public, server, private))| OleanModuleInput {
                    name: module,
                    artifact: public,
                    server_artifact: server.as_deref(),
                    private_artifact: private.as_deref(),
                })
                .collect();
            let options = KVMap::new();
            let mut admission = SourceOleanImportLimits::new(OleanCheckLimits::new(
                BYTES,
                Budget::for_stack_bytes(STACK),
            ));
            admission.jobs = OleanFrontierJobs {
                threads: NonZeroUsize::new(1).unwrap(),
                worker_stack_bytes: STACK,
            };
            let imported = Engine::from_environment(Environment::new())
                .import_olean_modules_for_source(&modules, &[root_module], &options, admission)
                .unwrap()
                .into_complete()
                .unwrap();
            let logical_root = imported.engine.logical_root(&options);
            let entry = name("Main");
            let mut execution = EngineExecutionLimits::new(Budget::for_stack_bytes(STACK));
            execution.vm.max_steps = 5000;
            execution.vm.max_stack_depth = 128;
            let limits = SourceProgramLimits::new(execution);
            let source = b"prelude\nimport PartialRuntime\n\
#eval PartialRuntime.count 0\n\
#eval PartialRuntime.count 4\n\
#eval PartialRuntime.choose Nat 53 3\n\
#eval PartialRuntime.choose Bool true 2\n\
#eval PartialRuntime.first 0\n\
#eval PartialRuntime.first 3\n\
#eval PartialRuntime.second 2\n\
#eval PartialRuntime.lazy 0\n";
            let run = || {
                imported
                    .execute_source_modules(
                        &[SourceModuleInput {
                            name: &entry,
                            source,
                        }],
                        &entry,
                        &options,
                        limits,
                        None,
                    )
                    .unwrap()
                    .into_complete()
                    .unwrap()
            };
            let first = run();
            let executions = &first.modules[0].commands.batch.executions;
            assert_eq!(
                executions
                    .iter()
                    .map(|execution| fln::closed_vm_value(&execution.exit).unwrap())
                    .collect::<Vec<_>>(),
                [42, 42, 53, 1, 17, 42, 42, 42].map(|value| Some(ClosedVmValue::Scalar(value)))
            );
            let spin = b"prelude\nimport PartialRuntime\n#eval PartialRuntime.lazy 1";
            assert!(matches!(
                imported
                    .execute_source_modules(
                        &[SourceModuleInput {
                            name: &entry,
                            source: spin
                        }],
                        &entry,
                        &options,
                        limits,
                        None
                    )
                    .unwrap(),
                Outcome::Inconclusive(_)
            ));
            let retry = run();
            assert_eq!(
                executions
                    .iter()
                    .map(|execution| &execution.flbc_artifact)
                    .collect::<Vec<_>>(),
                retry.modules[0]
                    .commands
                    .batch
                    .executions
                    .iter()
                    .map(|execution| &execution.flbc_artifact)
                    .collect::<Vec<_>>()
            );
            assert_eq!(imported.engine.logical_root(&options), logical_root);
        })
        .unwrap()
        .join()
        .unwrap();
}
