//! Actual pin-produced user functions call Name equality directly and through
//! captured native predicates. Toolchain function bodies never execute.

use super::arrays_reference::assert_nat_replay;
use super::*;
use crate::imported_ir::EntryArgument;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn live_pinned_name_equality_preserves_captures_and_native_scalar_abi() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for native Name equality"
        );
        eprintln!("SKIP: native Name equality requires FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        fln_olean::format::PIN_COMMIT
    );
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
    let mut prototypes = crate::decode_ir_artifact(
        &std::fs::read(library.join("Init/Prelude.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    let equality = name("Lean.Name.beq");
    let boxed = Name::str(equality.clone(), "_boxed");
    let numeric_constructor = name("Lean.Name.num._override");
    prototypes.decls.retain(|declaration| {
        declaration.name() == &equality
            || declaration.name() == &boxed
            || declaration.name() == &name("Lean.Name.str._override")
            || declaration.name() == &numeric_constructor
    });
    let Some(IrDecl::Function { params, result, .. }) = prototypes
        .decls
        .iter()
        .find(|declaration| declaration.name() == &numeric_constructor)
    else {
        panic!("the exact pin must contain the computed numeric Name constructor");
    };
    assert_eq!(params.len(), 2);
    assert!(
        params
            .iter()
            .all(|param| !param.borrow && param.ty == IrType::TObject)
    );
    assert_eq!(*result, IrType::TObject);
    let Some(IrDecl::Extern { params, result, .. }) = prototypes
        .decls
        .iter()
        .find(|declaration| declaration.name() == &equality)
    else {
        panic!("the exact pin must contain the native Name equality extern");
    };
    assert_eq!(params.len(), 2);
    assert!(
        params
            .iter()
            .all(|param| param.borrow && param.ty == IrType::TObject)
    );
    assert_eq!(*result, IrType::UInt8);
    let row = crate::imported_ir::native_row(&equality).unwrap();
    assert_eq!(
        row.ownership,
        "abi((n1: borrowed_arg, n2: borrowed_arg) -> value)"
    );
    let signature = primitives::signature(row).unwrap().unwrap();
    assert_eq!(signature.parameters, &[IrType::TObject, IrType::TObject]);
    assert_eq!(*signature.result, IrType::UInt8);
    let mut forged = *row;
    forged.ownership = "rule(borrowed-args,owned-result)";
    assert!(matches!(
        primitives::signature(&forged),
        Err(IrExecutionError::NativeContract { .. })
    ));

    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!(
        "name-equality-reference-{}-{unique}",
        std::process::id()
    ));
    std::fs::create_dir(&dir).unwrap();
    let source = include_str!("../../../../../fln-olean/fixtures/ir/NativeNameModule.lean");
    std::fs::write(dir.join("NativeNameModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-j1",
            "-o",
            "NativeNameModule.olean",
            "NativeNameModule.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeNameModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(dir.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    assert!(module.decls.iter().any(|declaration| {
        let IrDecl::Function { body, .. } = declaration else { return false; };
        body.bodies().into_iter().flat_map(|body| &body.stmts).any(|statement| matches!(
            statement,
            IrStmt::VDecl { expr: IrExpr::Pap { function, args }, .. } if function == &boxed && args.len() == 1
        ))
    }), "the actual fixture must retain the native predicate capture: {dir:?}");
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let partition_path = std::env::var_os("FLN_REFERENCE_PARTITION")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            fln_core::checked_workspace_root!().join("contracts/builtin_partition.tsv")
        });
    let partition =
        VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(partition_path).unwrap())
            .unwrap();

    let mut cases = Vec::new();
    let mut oracle_source = source.to_owned();
    for entry in ["nativeNameEqual", "nativeNamePartial"] {
        for (left, right) in [
            ("", ""),
            ("fixed", "fixed"),
            ("fixed", "other"),
            ("A.B", "A.B"),
            ("λ\0🙂", "λ\0🙂"),
            ("λ\0🙂", "λ\0🙃"),
            ("é", "e\u{301}"),
        ] {
            let quote = |text: &str| {
                format!(
                    "\"{}\"",
                    text.replace('\\', "\\\\")
                        .replace('"', "\\\"")
                        .replace('\0', "\\x00")
                )
            };
            oracle_source.push_str(&format!(
                "\n#eval {entry} {} {}\n",
                quote(left),
                quote(right)
            ));
            cases.push((
                entry,
                vec![
                    EntryArgument::String(left.to_owned()),
                    EntryArgument::String(right.to_owned()),
                ],
            ));
        }
    }
    for value in [0, 1, u64::MAX] {
        oracle_source.push_str(&format!("\n#eval nativeNameShape {value}\n"));
        cases.push((
            "nativeNameShape",
            vec![EntryArgument::Nat(IrNat::Small(value))],
        ));
    }
    let natural = |value: u128| {
        EntryArgument::Nat(if value <= u128::from(u64::MAX) {
            IrNat::Small(value as u64)
        } else {
            IrNat::Big(vec![value as u64, (value >> 64) as u64])
        })
    };
    let numeric_pairs = [
        (0, 0),
        (7, u128::from(u64::MAX)),
        (7, 1_u128 << 64),
        (7, (1_u128 << 64) + 17),
        ((1_u128 << 64) + 5, (1_u128 << 100) + 17),
        (u128::MAX, u128::MAX),
    ];
    for (parent, component) in numeric_pairs {
        // The source-level hash observer is oracle-only. Native execution
        // returns the actual constructed object; its pinned cached field is
        // inspected below, without admitting a toolchain getter body.
        oracle_source.push_str(&format!(
            "\n#eval (nativeNameNumeric {parent} {component}).hash.toNat\n"
        ));
        cases.push((
            "nativeNameNumeric",
            vec![natural(parent), natural(component)],
        ));
        oracle_source.push_str(&format!(
            "\n#eval nativeNameNumericFields {parent} {component}\n"
        ));
        cases.push((
            "nativeNameNumericFields",
            vec![natural(parent), natural(component)],
        ));
    }
    for (parent, left, right) in [
        (7, u128::from(u64::MAX), u128::from(u64::MAX)),
        (7, 1_u128 << 64, 1_u128 << 64),
        (7, 17, (1_u128 << 64) + 17),
        (7, (1_u128 << 64) + 17, (2_u128 << 64) + 17),
        (
            (1_u128 << 100) + 5,
            (1_u128 << 100) + 17,
            (1_u128 << 100) + 17,
        ),
        (
            (1_u128 << 100) + 5,
            (1_u128 << 100) + 17,
            (1_u128 << 100) + 19,
        ),
    ] {
        oracle_source.push_str(&format!(
            "\n#eval nativeNameNumericEqual {parent} {left} {right}\n"
        ));
        cases.push((
            "nativeNameNumericEqual",
            vec![natural(parent), natural(left), natural(right)],
        ));
    }
    std::fs::write(dir.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "Oracle.lean"])
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
    let modules = [module, prototypes];
    for ((entry, arguments), expected) in cases.into_iter().zip(expected) {
        let compiled = compile(
            &modules,
            &name(entry),
            &arguments,
            &partition,
            &users,
            IrExecutionLimits::default(),
        )
        .unwrap_or_else(|error| panic!("{entry} {arguments:?}: {error:?}; {dir:?}"));
        if entry == "nativeNameNumeric" {
            assert_numeric_hash_replay(&compiled, expected);
        } else {
            assert_nat_replay(&compiled, expected);
            assert!(compiled.native_externs().iter().any(|id| id == row.id));
        }
        if entry.starts_with("nativeNameNumeric") {
            assert!(
                compiled
                    .native_externs()
                    .iter()
                    .any(|id| id == "mirror:Lean.Name.num._override")
            );
        }
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(|function| users.contains(&function.name)),
            "toolchain Name functions must remain native"
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
        if entry == "nativeNameNumeric" {
            assert_numeric_hash_replay(&compiled, expected);
        } else {
            assert_nat_replay(&compiled, expected);
        }
    }
}

fn assert_numeric_hash_replay(compiled: &CompiledIr, expected: &str) {
    let expected: u64 = expected.parse().unwrap();
    let bytes =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    let layout = fln_rt::syntax_abi_generated::NAME_NUM_CTOR;
    for program in [compiled.program.program(), &replay] {
        let outcome = execute(program, ExecutionLimits::default(), None);
        let Outcome::Complete(VmExit::Returned(value)) = outcome else {
            panic!("{outcome:?}")
        };
        assert!(!value.value.is_scalar());
        assert_eq!(value.value.obj_tag(), usize::from(layout.tag));
        assert_eq!(
            usize::from(value.value.header().other),
            layout.object_fields
        );
        assert_eq!(
            value
                .value
                .try_ctor_scalar_u64(layout.object_fields * std::mem::size_of::<usize>()),
            Some(expected)
        );
    }
}
