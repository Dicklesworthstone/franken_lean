//! Actual pin-compiled named globals, shared references and initialized dependencies.
//! The Reference runs only as the test oracle; Golem executes the decoded IR.

use crate::imported_ir::{
    EntryArgument, IrExecutionLimits, IrExecutionOptions, VerifiedPartition, compile_with_options,
    native_row,
};
use fln_comp::flbc;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir::IrDecl;
use fln_olean::ir_archive::CensusPartition;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};
use std::cell::Cell;
use std::collections::BTreeSet;
use std::path::PathBuf;
use std::process::Command;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn assert_io_nat(outcome: Outcome<VmExit>, expected: &str) -> u64 {
    let Outcome::Complete(VmExit::Returned(completed)) = outcome else {
        panic!("expected returned IO Nat, got {outcome:?}");
    };
    assert!(!completed.value.is_scalar());
    assert_eq!(
        (completed.value.header().tag, completed.value.header().other),
        (0, 1),
        "the real entry returns the Reference IO.Result.ok representation"
    );
    let value = completed.value.try_ctor_child(0).unwrap();
    assert_eq!(nat_decimal(&value).as_deref(), Some(expected));
    completed.usage.steps
}

#[test]
fn live_pinned_named_globals_share_state_replay_and_recover_after_resource_stops() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let lib = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(lib.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required for live initialized-global IR"
        );
        eprintln!("SKIP: live initialized-global IR requires the pinned Reference");
        return;
    };
    let pin = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../SUITE.lock"))
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .unwrap();
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);

    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!(
        "initialized-globals-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("InitializedGlobalsModule.lean"),
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../fln-olean/fixtures/ir/InitializedGlobalsModule.lean"
        )),
    )
    .unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-o",
            "InitializedGlobalsModule.olean",
            "InitializedGlobalsModule.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "Reference compilation failed in {dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let bytes = std::fs::read(dir.join("InitializedGlobalsModule.ir")).unwrap();
    let module = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024).unwrap();
    assert_eq!(module.initializers.len(), 2);
    assert!(
        module
            .initializers
            .iter()
            .all(|entry| entry.initializer.is_some())
    );

    // Importing the artifact runs its actual named initializers. Each fresh
    // oracle process, like each Golem execution below, starts a fresh session.
    std::fs::write(
        dir.join("Oracle.lean"),
        "import InitializedGlobalsModule\n#eval initializedGlobalsAnswer\n",
    )
    .unwrap();
    for index in 0..2 {
        let oracle = Command::new(&reference)
            .current_dir(&dir)
            .env("LEAN_PATH", &dir)
            .arg("Oracle.lean")
            .output()
            .unwrap();
        std::fs::write(dir.join(format!("oracle-{index}.stdout")), &oracle.stdout).unwrap();
        std::fs::write(dir.join(format!("oracle-{index}.stderr")), &oracle.stderr).unwrap();
        assert!(
            oracle.status.success(),
            "Reference oracle failed in {dir:?}: {}{}",
            String::from_utf8_lossy(&oracle.stdout),
            String::from_utf8_lossy(&oracle.stderr)
        );
        assert_eq!(oracle.stdout, b"167\n", "actual Reference result; {dir:?}");
    }

    // This bounded unit-test partition classifies only the actual fixture's
    // user definitions. It does not bypass or qualify public census verification.
    let partition = VerifiedPartition {
        partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default())
            .unwrap(),
    };
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            IrDecl::Function { name, .. } if native_row(name).is_none() => Some(name.clone()),
            _ => None,
        })
        .collect();
    let compiled = compile_with_options(
        std::slice::from_ref(&module),
        &name("initializedGlobalsAnswer"),
        &[EntryArgument::Erased],
        &partition,
        &users,
        IrExecutionOptions {
            limits: IrExecutionLimits::default(),
            capture_output_bytes: None,
            initialize_globals: true,
        },
    )
    .unwrap_or_else(|error| panic!("actual initialized globals: {error:?}; {dir:?}"));

    let mut steps = 0;
    for _ in 0..2 {
        let report = compiled.execute(ExecutionLimits::default(), None);
        assert!(report.initialization_failure.is_none());
        steps = assert_io_nat(report.outcome, "167");
    }
    assert!(steps > 1);
    for initialized in ["initializeSharedCounter", "initializeRememberedCounter"] {
        assert!(compiled.reference_functions().iter().any(|function| {
            function.name == name(initialized) && function.producer() == "reference"
        }));
    }
    for row in ["extern:ST.Prim.mkRef", "extern:ST.Prim.Ref.get"] {
        assert!(
            compiled
                .native_externs()
                .iter()
                .any(|observed| observed == row)
        );
    }

    let canonical =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&canonical, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        canonical
    );
    for _ in 0..2 {
        let (outcome, failure) = super::super::finish(
            execute(&replay, ExecutionLimits::default(), None),
            compiled.initialization.as_ref().unwrap(),
        );
        assert!(failure.is_none());
        assert_io_nat(outcome, "167");
    }

    for budget in [0, 1, steps / 2, steps - 1] {
        let report = compiled.execute(
            ExecutionLimits {
                max_steps: budget,
                ..ExecutionLimits::default()
            },
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Inconclusive(_)),
            "budget {budget}: {report:?}"
        );
        assert!(report.initialization_failure.is_none());
        assert_io_nat(
            compiled.execute(ExecutionLimits::default(), None).outcome,
            "167",
        );
    }
    let polls = Cell::new(0u64);
    let cancel = || {
        let seen = polls.get();
        polls.set(seen + 1);
        seen >= steps / 2
    };
    let report = compiled.execute(ExecutionLimits::default(), Some(&cancel));
    assert!(matches!(report.outcome, Outcome::Inconclusive(_)));
    assert!(report.initialization_failure.is_none());
    assert_io_nat(
        compiled.execute(ExecutionLimits::default(), None).outcome,
        "167",
    );
}
