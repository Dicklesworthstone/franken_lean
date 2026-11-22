//! Generated builtin parser operands reach macro expansion, kernel admission,
//! and the ordinary native VM. The pinned Lean fixture prints 42, 17, and 23.
#![forbid(unsafe_code)]

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionLimits, KVMap, Name, OleanCheckLimits,
    OleanModuleInput,
};
use std::collections::{BTreeMap, BTreeSet};
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

const SOURCE: &str = include_str!("../../fln-parse/tests/fixtures/native_generated_aliases.lean");
const STACK: usize = 256 * 1024 * 1024;
// Repr supplies the Nat printer and Id monad; Meta.Defs supplies the typed
// syntax coercions used by the shared quotation templates. Both producers use
// these same checked declarations rather than assuming the seed provides them.
const IMPORTS: [&str; 2] = ["Init.Data.Repr", "Init.Meta.Defs"];

fn admission() -> EngineAdmissionLimits {
    EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))
}

struct Reference {
    binary: PathBuf,
    library: PathBuf,
}

fn reference() -> Option<Reference> {
    let library = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from);
    let binary = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            library
                .as_ref()?
                .parent()?
                .parent()
                .map(|root| root.join("bin/lean"))
        });
    let Some(binary) = binary else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "FLN_REQUIRE_REFERENCE requires the pinned Lean binary and library"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LEAN or FLN_REFERENCE_LIB for parser source execution");
        return None;
    };
    let pin = include_str!("../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference leanprover/lean4 "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|word| word.strip_prefix("commit="))
        })
        .expect("SUITE.lock Reference commit");
    let identity = Command::new(&binary)
        .arg("--githash")
        .output()
        .expect("configured Reference identity");
    assert!(identity.status.success());
    assert_eq!(
        String::from_utf8_lossy(&identity.stdout).trim(),
        pin,
        "configured Reference differs from SUITE.lock"
    );
    let location = Command::new(&binary)
        .arg("--print-libdir")
        .output()
        .expect("configured Reference library");
    assert!(location.status.success());
    let actual = PathBuf::from(String::from_utf8(location.stdout).unwrap().trim());
    let actual = std::fs::canonicalize(actual).expect("Reference library exists");
    if let Some(library) = library {
        assert_eq!(
            std::fs::canonicalize(library).expect("configured Reference library exists"),
            actual,
            "Reference binary and imported library must belong to the same pinned installation"
        );
    }
    Some(Reference {
        binary,
        library: actual,
    })
}

fn engine(library: &Path) -> Engine {
    let roots: Vec<_> = IMPORTS
        .iter()
        .map(|name| Name::from_components(name.split('.')))
        .collect();
    let mut pending: Vec<_> = roots.iter().cloned().map(|name| (name, false)).collect();
    let mut seen = BTreeSet::new();
    let mut ordered = Vec::new();
    let mut artifacts = BTreeMap::new();
    while let Some((name, finished)) = pending.pop() {
        if finished {
            ordered.push(name);
            continue;
        }
        if !seen.insert(name.clone()) {
            continue;
        }
        assert!(
            seen.len() <= 256,
            "bounded actual parser fixture import closure"
        );
        let path = library
            .join(name.to_display_string().replace('.', "/"))
            .with_extension("olean");
        let parts = [
            std::fs::read(&path).unwrap(),
            std::fs::read(path.with_extension("olean.server")).unwrap(),
            std::fs::read(path.with_extension("olean.private")).unwrap(),
        ];
        let imports =
            fln::olean_module_imports(&parts[0], fln::OleanDecodeLimits::new(STACK)).unwrap();
        artifacts.insert(name.clone(), parts);
        pending.push((name, true));
        pending.extend(imports.into_iter().rev().map(|name| (name, false)));
    }
    let inputs: Vec<_> = ordered
        .iter()
        .map(|name| {
            let [exported, server, private] = &artifacts[name];
            OleanModuleInput {
                name,
                artifact: exported,
                server_artifact: Some(server),
                private_artifact: Some(private),
            }
        })
        .collect();
    let jobs = fln::OleanFrontierJobs {
        threads: std::num::NonZeroUsize::new(1).unwrap(),
        worker_stack_bytes: STACK,
    };
    let imported = Engine::builder()
        .build_empty()
        .import_olean_modules_for_source(
            &inputs,
            &roots,
            &KVMap::new(),
            SourceOleanImportLimits {
                jobs,
                read_jobs: jobs,
                ..SourceOleanImportLimits::new(OleanCheckLimits::new(STACK, admission().kernel))
            },
        )
        .expect("actual parser fixture import admission")
        .into_complete()
        .expect("actual parser fixture import admission completes");
    assert_eq!(imported.modules.len(), ordered.len());
    imported.engine
}

fn oracle(reference: &Reference, source: &str) -> Output {
    let mut child = Command::new(&reference.binary)
        .args(["-j1", "--stdin"])
        .env("LEAN_PATH", &reference.library)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("pinned parser fixture oracle");
    let mut input = child.stdin.take().unwrap();
    writeln!(input, "prelude").unwrap();
    for module in IMPORTS {
        writeln!(input, "import {module}").unwrap();
    }
    input.write_all(source.as_bytes()).unwrap();
    drop(input);
    child.wait_with_output().unwrap()
}

fn check(reference: Reference) {
    let engine = engine(&reference.library);
    let before = engine.logical_root(&KVMap::new());
    let result = engine
        .execute_source_commands_with_checks(
            SOURCE.as_bytes(),
            &KVMap::new(),
            EngineExecutionLimits::new(admission().kernel),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    let values: Vec<_> = result
        .batch
        .source_evaluation_indices
        .iter()
        .map(|&index| {
            let execution = &result.batch.executions[index];
            let fln::VmExit::Returned(value) = &execution.exit else {
                panic!("VM did not return")
            };
            fln_vm::interpreter::nat_decimal(&value.value).unwrap()
        })
        .collect();
    assert_eq!(values, ["42", "17", "23"]);
    let expected = oracle(&reference, SOURCE);
    assert!(
        expected.status.success(),
        "{}{}",
        String::from_utf8_lossy(&expected.stdout),
        String::from_utf8_lossy(&expected.stderr)
    );
    assert_eq!(String::from_utf8(expected.stdout).unwrap(), "42\n17\n23\n");
    assert!(expected.stderr.is_empty());
    for (before, after) in [
        ("composed = 42", "composed = 43"),
        ("fromSignature = 17", "fromSignature = 18"),
        ("fromSequence = 23", "fromSequence = 24"),
    ] {
        let mutant = SOURCE.replace(before, after);
        assert_ne!(mutant, SOURCE, "the false-proof fixture must change");
        assert!(
            engine
                .execute_source_commands_with_checks(
                    mutant.as_bytes(),
                    &KVMap::new(),
                    EngineExecutionLimits::new(admission().kernel),
                )
                .is_err(),
            "accepted false generated declaration: {after}"
        );
        let expected = oracle(&reference, &mutant);
        assert!(
            !expected.status.success(),
            "the pinned Reference accepted false generated declaration: {after}"
        );
    }
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}

#[test]
fn rich_parser_alias_macros_execute_and_check_their_generated_declarations() {
    let Some(reference) = reference() else {
        return;
    };
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(move || check(reference))
        .expect("source parser fixture worker")
        .join()
        .expect("source parser fixture completed");
}
