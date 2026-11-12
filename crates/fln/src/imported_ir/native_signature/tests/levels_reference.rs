//! Real pinned user IR calls the native universe primitives directly and as
//! captured closures. Imported toolchain bodies are never granted execution.

use super::arrays_reference::assert_nat_replay;
use super::*;
use crate::imported_ir::EntryArgument;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_pinned_level_primitives_preserve_structure_data_and_boxed_calls() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native universe primitives"
        );
        eprintln!("SKIP: native universe primitives require FLN_REFERENCE_LEAN");
        return;
    };
    let pin = include_str!("../../../../../../SUITE.lock")
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
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            reference
                .parent()
                .unwrap()
                .parent()
                .unwrap()
                .join("lib/lean")
        });
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "native-level-reference-{}-{stamp}",
        std::process::id()
    ));
    std::fs::create_dir(&dir).unwrap();
    let source = include_str!("../../../../../fln-olean/fixtures/ir/NativeLevelModule.lean");
    std::fs::write(dir.join("NativeLevelModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "NativeLevelModule.olean", "NativeLevelModule.lean"])
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeLevelModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .map(|declaration| declaration.name().clone())
        .collect();
    assert!(
        users
            .iter()
            .all(|declaration| !declaration.to_display_string().starts_with("Lean."))
    );

    let wanted = ["Lean.Level.beq", "Lean.Level.mkData"];
    let bytes = std::fs::read(library.join("Lean/Level.ir")).unwrap();
    fln_olean::pin::check_pinned_header(&bytes).unwrap();
    let prototypes = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024).unwrap();
    let mut native = IrModule::default();
    for target in wanted {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let external = prototypes
            .decls
            .iter()
            .find(|declaration| declaration.name() == &name(target))
            .unwrap();
        let IrDecl::Extern { params, result, .. } = external else {
            panic!("{target} must be an extern")
        };
        validate_extern_signature(row, params, result).unwrap();
        let boxed = Name::str(name(target), "_boxed");
        let wrapper = prototypes
            .decls
            .iter()
            .find(|declaration| declaration.name() == &boxed)
            .unwrap();
        BoxedNative::from_row(row)
            .unwrap()
            .unwrap()
            .validate_declaration(wrapper)
            .unwrap();
        native.decls.extend([external.clone(), wrapper.clone()]);
        assert!(module.decls.iter().any(|declaration| match declaration {
            IrDecl::Function { body, .. } => body.bodies().into_iter().any(|body| body.stmts.iter().any(|statement|
                matches!(statement, IrStmt::VDecl { expr: IrExpr::Pap { function, .. }, .. } if function == &boxed))),
            IrDecl::Extern { .. } => false,
        }), "{target} captured call was optimized away");
    }

    let mut cases = Vec::new();
    for entry in ["levelDataDirect", "levelDataCaptured"] {
        for hash in [0, 42, u64::MAX] {
            for depth in [0, 1, 65536, 16_777_215] {
                cases.push((entry, vec![hash, depth]));
            }
        }
    }
    for entry in ["levelCompareDirect", "levelCompareCaptured"] {
        for (a, b) in [
            (0, 0),
            (0, 1),
            (1, 7),
            (2, 2),
            (2, 3),
            (4, 4),
            (4, 5),
            (4, 6),
            (6, 6),
            (8, 8),
        ] {
            cases.push((entry, vec![a, b]));
        }
    }
    let mut oracle_source = source.to_owned();
    for (entry, args) in &cases {
        oracle_source.push_str(&format!("\n#eval {entry}"));
        for value in args {
            oracle_source.push_str(&format!(" {value}"));
        }
        oracle_source.push('\n');
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("Oracle.lean")
        .output()
        .unwrap();
    assert!(
        oracle.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    assert!(oracle.stderr.is_empty());
    let output = String::from_utf8(oracle.stdout).unwrap();
    let expected: Vec<_> = output.lines().collect();
    assert_eq!(expected.len(), cases.len(), "{output}");
    let modules = [module, native];
    let mut seen = BTreeSet::new();
    for ((entry, args), expected) in cases.into_iter().zip(expected) {
        let arguments: Vec<_> = args
            .into_iter()
            .map(|value| EntryArgument::Nat(IrNat::Small(value)))
            .collect();
        let compiled = compile(
            &modules,
            &name(entry),
            &arguments,
            &VerifiedPartition::user_fixture(),
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {arguments:?}: {error:?}; {dir:?}"));
        assert_nat_replay(&compiled, expected);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(|function| users.contains(&function.name))
        );
        seen.extend(compiled.native_externs().iter().cloned());
        assert!(matches!(
            compiled
                .execute(
                    ExecutionLimits {
                        max_steps: 0,
                        ..ExecutionLimits::default()
                    },
                    None
                )
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert!(matches!(
            compiled
                .execute(ExecutionLimits::default(), Some(&|| true))
                .outcome,
            Outcome::Inconclusive(_)
        ));
        assert_nat_replay(&compiled, expected);
    }
    for target in wanted {
        assert!(seen.contains(&format!("extern:{target}")));
    }
}
