//! Live pinned-compiler oracle for recursive reset/reuse, not hand-authored IR.
//! All subprocess execution is confined to this test-only module.

use super::*;
use crate::imported_ir::{EntryArgument, VerifiedPartition, compile};
use fln_comp::flbc;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir::IrNat;
use fln_olean::ir_archive::CensusPartition;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_pinned_recursive_updates_match_reference_and_canonical_replay() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let lib = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(lib.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "the pinned Reference is required for live imported IR"
        );
        eprintln!("SKIP: live imported IR requires FLN_REFERENCE_LEAN or FLN_REFERENCE_LIB");
        return;
    };
    let lock = include_str!(concat!(env!("CARGO_MANIFEST_DIR"), "/../../SUITE.lock"));
    let pin = lock
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| line.split_whitespace().find_map(|s| s.strip_prefix("commit=")))
        .expect("SUITE.lock Reference commit");
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);

    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    std::fs::create_dir_all(&root).unwrap();
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("reset-reference-{}-{unique}", std::process::id()));
    std::fs::create_dir(&dir).unwrap();
    // Retain source, raw IR, decoded IR and the live oracle output on failure.
    // A unique directory prevents a previous run's artifact being mistaken for
    // a successful compilation. No fixture is regenerated over tracked bytes.
    let source = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../fln-olean/fixtures/ir/ResetModule.lean"
    ));
    std::fs::write(dir.join("ResetModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "ResetModule.olean", "ResetModule.lean"])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "Reference compilation failed in {dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr),
    );
    let bytes = std::fs::read(dir.join("ResetModule.ir")).unwrap();
    let module = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024).unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    // This is a real test of the new form, not an oracle case optimized into a
    // constant that never exercises reset/reuse or the recursive call.
    let mut expanded = 0;
    for decl in &module.decls {
        if let IrDecl::Function { body, .. } = decl {
            for body in body.bodies() {
                if matches!(body.stmts.as_slice(), [.., IrStmt::JDecl { params, .. },
                    IrStmt::VDecl { expr: IrExpr::IsShared { .. }, .. }]
                    if params.len() == 2)
                {
                    expanded += 1;
                }
            }
        }
    }
    assert!(expanded > 0, "the pin emitted no expanded reset region; inspect {dir:?}");

    let cases = [
        ("resetAnswer", 0),
        ("resetAnswer", 7),
        ("resetAnswer", u64::MAX),
        ("resetSharedAnswer", 7),
        ("resetClosureAnswer", 5),
        ("resetEmptyAnswer", 99),
    ];
    let mut oracle_source = source.to_owned();
    for (entry, value) in cases {
        oracle_source.push_str(&format!("\n#eval {entry} {value}\n"));
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("Oracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(oracle.status.success(), "Reference oracle failed: {}{}",
        String::from_utf8_lossy(&oracle.stdout), String::from_utf8_lossy(&oracle.stderr));
    let output = String::from_utf8(oracle.stdout).unwrap();
    let expected: Vec<_> = output.lines().collect();
    assert_eq!(expected.len(), cases.len(), "unexpected oracle output: {output}");
    assert!(expected.iter().all(|s| !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit())));

    let users = module.decls.iter().filter_map(|decl| match decl {
        IrDecl::Function { name, .. } => Some(name.clone()),
        _ => None,
    }).collect();
    let partition = VerifiedPartition {
        partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default()).unwrap(),
    };
    for ((entry, value), expected) in cases.into_iter().zip(expected) {
        let compiled = compile(
            std::slice::from_ref(&module),
            &Name::from_components(entry.split('.')),
            &[EntryArgument::Nat(IrNat::Small(value))],
            &partition,
            &users,
            IrExecutionLimits::default(),
        ).unwrap_or_else(|error| panic!("{entry} {value}: {error:?}; artifacts {dir:?}"));
        let encoded = flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
        let replay = flbc::decode_canonical(&encoded, flbc::CodecLimits::default()).unwrap();
        for program in [compiled.program.program(), &replay] {
            let outcome = execute(program, ExecutionLimits::default(), None);
            let Outcome::Complete(VmExit::Returned(result)) = outcome else {
                panic!("{entry} {value}: {outcome:?}");
            };
            assert_eq!(nat_decimal(&result.value).as_deref(), Some(expected), "{entry} {value}");
        }
        assert!(compiled.reference_functions().iter().all(|f| f.producer() == "reference"));
        eprintln!("live Reference and Golem: {entry} {value} = {expected}");
    }
}
