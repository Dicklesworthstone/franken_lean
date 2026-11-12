//! Actual pinned expression IR, including scalar/boxed native prototypes.

use super::arrays_reference::assert_nat_replay;
use super::*;
use crate::imported_ir::EntryArgument;
use std::path::PathBuf;
use std::process::Command;

const TARGETS: [&str; 9] = [
    "Lean.Expr.data",
    "Lean.Expr.mkData",
    "Lean.Expr.mkAppData",
    "Lean.Expr.equal",
    "Lean.Expr.hasLooseBVar",
    "Lean.Expr.liftLooseBVars",
    "Lean.Expr.instantiate1",
    "Lean.Expr.instantiate",
    "Lean.Expr.instantiateRev",
];

#[test]
fn live_pinned_expr_primitives_preserve_binders_arrays_data_and_boxed_calls() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native expression primitives"
        );
        eprintln!("SKIP: native expression primitives require FLN_REFERENCE_LEAN");
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
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let dir = root.join(format!(
        "native-expr-reference-{}-{stamp}",
        std::process::id()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    let source = include_str!("../../../../../fln-olean/fixtures/ir/NativeExprModule.lean");
    std::fs::write(dir.join("NativeExprModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args(["-o", "NativeExprModule.olean", "NativeExprModule.lean"])
        .output()
        .unwrap();
    assert!(
        generated.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeExprModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .map(|declaration| declaration.name().clone())
        .collect();
    assert!(
        users
            .iter()
            .all(|declaration| declaration.to_display_string().starts_with("NativeExpr."))
    );

    let bytes = std::fs::read(library.join("Lean/Expr.ir")).unwrap();
    fln_olean::pin::check_pinned_header(&bytes).unwrap();
    let prototypes = crate::decode_ir_artifact(&bytes, 32 * 1024 * 1024).unwrap();
    let mut native = IrModule::default();
    for target in TARGETS {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let external = prototypes
            .decls
            .iter()
            .find(|declaration| declaration.name() == &name(target))
            .unwrap();
        let IrDecl::Extern { params, result, .. } = external else {
            panic!("{target} must be an extern")
        };
        validate_extern_signature(row, params, result)
            .unwrap_or_else(|error| panic!("{target}: {error:?}; {external:?}"));
        // Raw prototype borrowing is exact even for rows whose generated VM
        // lifetime rule differs. Neither direction is an admission shortcut.
        for index in 0..params.len() {
            let mut changed = params.clone();
            changed[index].borrow = !changed[index].borrow;
            assert!(
                matches!(
                    validate_extern_signature(row, &changed, result),
                    Err(IrExecutionError::NativeContract { .. })
                ),
                "{target} parameter {index}"
            );
        }
        let mut changed = params.clone();
        changed[0].ty = IrType::Void;
        assert!(matches!(
            validate_extern_signature(row, &changed, result),
            Err(IrExecutionError::NativeContract { .. })
        ));
        assert!(matches!(
            validate_extern_signature(row, params, &IrType::Void),
            Err(IrExecutionError::NativeContract { .. })
        ));
        native.decls.push(external.clone());
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
            .unwrap_or_else(|error| panic!("{target}: {error:?}; {wrapper:?}"));
        native.decls.push(wrapper.clone());
    }
    let cases: Vec<(&str, Vec<u64>)> = vec![
        ("single", vec![0]),
        ("single", vec![3]),
        ("single", vec![42]),
        ("arrayOrder", vec![0, 0]),
        ("arrayOrder", vec![0, 1]),
        ("arrayOrder", vec![37, 0]),
        ("arrayOrder", vec![37, 1]),
        ("lift", vec![0, 0]),
        ("lift", vec![0, 4]),
        ("lift", vec![1, 4]),
        ("lift", vec![1_u64 << 32, (1_u64 << 32) + 4]),
        ("lift", vec![u64::MAX, 7]),
        ("contains", vec![0]),
        ("contains", vec![1]),
        ("contains", vec![2]),
        ("contains", vec![3]),
        ("contains", vec![1_u64 << 32]),
        ("contains", vec![u64::MAX]),
        ("strictEquality", vec![0]),
        ("strictEquality", vec![1]),
        ("data", vec![0]),
        ("data", vec![41]),
        ("packData", vec![u64::MAX, 103, 256, 15]),
        (
            "packData",
            vec![0x1234_5678_9abc_def0, 1_048_575, u32::MAX as u64, 10],
        ),
        ("packAppData", vec![0, u64::MAX]),
        (
            "packAppData",
            vec![0x1234_5678_9abc_def0, 0xfedc_ba98_7654_3210],
        ),
    ];
    let mut oracle_source = source.to_owned();
    for (entry, args) in &cases {
        oracle_source.push_str(&format!("\n#eval NativeExpr.{entry}"));
        for value in args {
            oracle_source.push_str(&format!(" {value}"));
        }
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .arg("Oracle.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(
        oracle.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    let output = String::from_utf8(oracle.stdout).unwrap();
    let expected: Vec<_> = output.lines().collect();
    assert_eq!(expected.len(), cases.len(), "{output}");
    let modules = [module, native];
    let partition = VerifiedPartition::user_fixture();
    let mut observed = BTreeSet::new();
    for ((entry, args), expected) in cases.iter().zip(expected) {
        let arguments: Vec<_> = args
            .iter()
            .map(|value| EntryArgument::Nat(IrNat::Small(*value)))
            .collect();
        let compiled = compile(
            &modules,
            &name(&format!("NativeExpr.{entry}")),
            &arguments,
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {args:?}: {error:?}; {dir:?}"));
        assert_nat_replay(&compiled, expected);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(
                    |function| function.producer() == "reference" && users.contains(&function.name)
                )
        );
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
        observed.extend(compiled.native_externs().iter().cloned());
    }
    for target in TARGETS {
        assert!(
            observed.contains(&format!("extern:{target}")),
            "{target} not linked by actual user IR"
        );
    }
}

#[test]
fn reviewed_expr_native_contracts_reject_forged_signatures_and_authority() {
    for target in TARGETS {
        let original = crate::imported_ir::native_row(&name(target)).unwrap();
        assert!(BoxedNative::from_row(original).unwrap().is_some());
        for changed in [
            GeneratedExternRow {
                symbol: "foreign",
                ..*original
            },
            GeneratedExternRow {
                module: "Foreign",
                ..*original
            },
            GeneratedExternRow {
                kind: "axiom",
                ..*original
            },
            GeneratedExternRow {
                arity: original.arity + 1,
                ..*original
            },
            GeneratedExternRow {
                ownership: "rule(scalar)",
                ..*original
            },
            GeneratedExternRow {
                effect: "io",
                ..*original
            },
            GeneratedExternRow {
                partition: "library-code",
                ..*original
            },
        ] {
            assert!(matches!(
                BoxedNative::from_row(&changed),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
}
