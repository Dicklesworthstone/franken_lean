use super::*;
use fln_vm::interpreter::VmRefusal;

const CHARACTERS: [&str; 3] = ["String.decodeChar", "String.Pos.Raw.get'", "String.get'"];
const BYTES: [&str; 3] = [
    "String.Internal.getUTF8Byte",
    "String.getUTF8Byte",
    "String.getUtf8Byte",
];
const NEXT: [&str; 3] = ["String.Pos.Raw.next'", "String.Pos.next", "String.next'"];

fn targets() -> impl Iterator<Item = &'static str> {
    CHARACTERS.into_iter().chain(BYTES).chain(NEXT)
}

fn result_type(target: &str) -> IrType {
    if CHARACTERS.contains(&target) {
        IrType::UInt32
    } else if BYTES.contains(&target) {
        IrType::UInt8
    } else if target == "String.next'" {
        IrType::TObject
    } else {
        IrType::Tagged
    }
}

fn invocation(target: &str, index: u64, boxed: bool, captured_index: bool) -> IrDecl {
    let mut statements = vec![
        IrStmt::VDecl {
            x: 1,
            ty: IrType::Object,
            expr: IrExpr::Lit(IrLit::Str("aλ🦀\0z".to_owned())),
        },
        num(2, index),
    ];
    let result = result_type(target);
    if boxed {
        statements.push(bind(
            3,
            IrExpr::Pap {
                function: Name::str(name(target), "_boxed"),
                args: if captured_index {
                    vec![var(1), var(2)]
                } else {
                    vec![var(1)]
                },
            },
        ));
        let args = if captured_index {
            vec![IrArg::Erased]
        } else {
            vec![var(2), IrArg::Erased]
        };
        // Reuse the same capture and leave the original string live. The
        // proof slot is still pending even after both data values are bound.
        for x in [4, 5] {
            statements.push(bind(
                x,
                IrExpr::Ap {
                    x: 3,
                    args: args.clone(),
                },
            ));
        }
        statements.push(call(6, "Nat.add", &[4, 5]));
    } else {
        statements.push(IrStmt::VDecl {
            x: 4,
            ty: result.clone(),
            expr: IrExpr::Fap {
                function: name(target),
                args: vec![var(1), var(2), IrArg::Erased],
            },
        });
        if result == IrType::UInt32 {
            statements.push(call(5, "UInt32.toNat", &[4]));
        } else if result == IrType::UInt8 {
            statements.push(call(5, "UInt8.toNat", &[4]));
        } else {
            statements.push(num(3, 0));
            statements.push(call(5, "Nat.add", &[4, 3]));
        }
        statements.push(call(6, "Nat.add", &[5, 5]));
    }
    statements.push(call(7, "String.utf8ByteSize", &[1]));
    statements.push(call(8, "Nat.add", &[6, 7]));
    entry(statements, 8)
}

#[test]
fn string_proof_calls_and_reused_boxed_closures_preserve_utf8_values() {
    for target in targets() {
        let cases: &[(u64, u64)] = if CHARACTERS.contains(&target) {
            &[(0, 97), (1, 955), (3, 129408), (7, 0), (8, 122)]
        } else if BYTES.contains(&target) {
            &[(0, 97), (1, 206), (2, 187), (3, 240), (4, 159), (7, 0)]
        } else {
            &[(0, 1), (1, 3), (3, 7), (7, 8), (8, 9)]
        };
        for &(index, value) in cases {
            for (boxed, captured_index) in [(false, false), (true, false), (true, true)] {
                let compiled =
                    compile_declarations(vec![invocation(target, index, boxed, captured_index)])
                        .unwrap_or_else(|error| {
                            panic!("{target}, index={index}, boxed={boxed}: {error}")
                        });
                assert_nat(&compiled, &(value * 2 + 9).to_string());
                assert!(
                    compiled
                        .native_externs()
                        .contains(&format!("extern:{target}"))
                );
            }
        }
    }
}

#[test]
fn erased_string_proofs_do_not_remove_runtime_bounds_checks() {
    for target in targets() {
        for (boxed, captured_index) in [(false, false), (true, false), (true, true)] {
            let compiled =
                compile_declarations(vec![invocation(target, 999, boxed, captured_index)]).unwrap();
            assert!(matches!(
                compiled.execute(ExecutionLimits::default(), None).outcome,
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::ArrayIndexOutOfBounds { .. },
                    ..
                })
            ));
        }
    }
}

#[test]
fn string_proof_slots_cannot_erase_data_or_change_raw_partial_application_arity() {
    for target in targets() {
        for replacement in [var(1), var(2), var(999)] {
            let mut declaration = invocation(target, 0, false, false);
            let IrDecl::Function { body, .. } = &mut declaration else {
                unreachable!()
            };
            let IrStmt::VDecl {
                expr: IrExpr::Fap { args, .. },
                ..
            } = &mut body.stmts[2]
            else {
                unreachable!()
            };
            args[2] = replacement;
            assert!(matches!(
                compile_declarations(vec![declaration]),
                Err(IrExecutionError::Unsupported { .. })
            ));
        }
        let mut declaration = invocation(target, 0, true, true);
        let IrDecl::Function { body, .. } = &mut declaration else {
            unreachable!()
        };
        let IrStmt::VDecl {
            expr: IrExpr::Pap { function, args },
            ..
        } = &mut body.stmts[2]
        else {
            unreachable!()
        };
        *function = name(target);
        args.push(IrArg::Erased);
        assert!(matches!(
            compile_declarations(vec![declaration]),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
}

#[test]
fn string_prototypes_keep_proof_slots_borrowing_and_tagged_results_distinct() {
    for target in targets() {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        assert_eq!(bridge.arity(), 3);
        assert_eq!(bridge.runtime_parameters(), 0..2);
        let params = vec![
            IrParam {
                x: 0,
                ty: IrType::Object,
                borrow: target != "String.getUtf8Byte",
            },
            IrParam {
                x: 1,
                ty: IrType::TObject,
                borrow: !BYTES.contains(&target),
            },
            IrParam {
                x: 2,
                ty: IrType::Erased,
                borrow: false,
            },
        ];
        let result = result_type(target);
        validate_extern_signature(row, &params, &result).unwrap();
        for index in 0..params.len() {
            let mut wrong = params.clone();
            wrong[index].borrow = !wrong[index].borrow;
            assert!(matches!(
                validate_extern_signature(row, &wrong, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
            wrong = params.clone();
            wrong[index].ty = if index == 2 {
                IrType::TObject
            } else {
                IrType::Erased
            };
            assert!(matches!(
                validate_extern_signature(row, &wrong, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
        let boxed = IrDecl::Extern {
            name: Name::str(name(target), "_boxed"),
            params: vec![
                IrParam {
                    x: 0,
                    ty: IrType::Object,
                    borrow: false,
                },
                IrParam {
                    x: 1,
                    ty: IrType::TObject,
                    borrow: false,
                },
                IrParam {
                    x: 2,
                    ty: IrType::TObject,
                    borrow: false,
                },
            ],
            result: if matches!(result, IrType::UInt8 | IrType::Tagged) {
                IrType::Tagged
            } else {
                IrType::TObject
            },
            entries: vec![],
        };
        bridge.validate_declaration(&boxed).unwrap();
        for drop_proof in [false, true] {
            let mut wrong = boxed.clone();
            let IrDecl::Extern { params, .. } = &mut wrong else {
                unreachable!()
            };
            if drop_proof {
                params.pop();
            } else {
                params[2].ty = IrType::Erased;
            }
            assert!(matches!(
                bridge.validate_declaration(&wrong),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
        for changed in [
            GeneratedExternRow {
                symbol: "foreign_string",
                ..*row
            },
            GeneratedExternRow { arity: 2, ..*row },
            GeneratedExternRow { levels: 1, ..*row },
            GeneratedExternRow {
                effect: "io",
                ..*row
            },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,owned-result)",
                ..*row
            },
            GeneratedExternRow {
                profile: "frontier",
                ..*row
            },
        ] {
            assert!(matches!(
                BoxedNative::from_row(&changed),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
}

#[test]
fn pinned_string_artifacts_agree_with_native_and_boxed_proof_telescopes() {
    use std::path::PathBuf;
    use std::process::Command;

    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let library = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| Some(reference.as_ref()?.parent()?.parent()?.join("lib/lean")));
    let Some(library) = library else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for string proof prototypes"
        );
        eprintln!("SKIP: string proof prototypes require FLN_REFERENCE_LIB");
        return;
    };
    let reference =
        reference.unwrap_or_else(|| library.parent().unwrap().parent().unwrap().join("bin/lean"));
    let version = Command::new(reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    let pin = include_str!("../../../../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .unwrap();
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);
    let mut found = BTreeSet::new();
    for file in [
        "Init/Data/String/Bootstrap.ir",
        "Init/Data/String/PosRaw.ir",
        "Init/Data/String/Basic.ir",
    ] {
        let module = crate::decode_ir_artifact(
            &std::fs::read(library.join(file)).unwrap(),
            32 * 1024 * 1024,
        )
        .unwrap();
        for declaration in &module.decls {
            for target in targets() {
                let native = name(target);
                let row = crate::imported_ir::native_row(&native).unwrap();
                if declaration.name() == &native {
                    let IrDecl::Extern { params, result, .. } = declaration else {
                        panic!("{target} is not a pinned extern")
                    };
                    validate_extern_signature(row, params, result)
                        .unwrap_or_else(|error| panic!("{target}: {error}; {declaration:?}"));
                    found.insert(native);
                } else if *declaration.name() == Name::str(native, "_boxed") {
                    BoxedNative::from_row(row)
                        .unwrap()
                        .unwrap()
                        .validate_declaration(declaration)
                        .unwrap_or_else(|error| panic!("{target}: {error}; {declaration:?}"));
                    found.insert(declaration.name().clone());
                }
            }
        }
    }
    for target in targets() {
        for expected in [name(target), Name::str(name(target), "_boxed")] {
            assert!(
                found.contains(&expected),
                "pin does not contain {expected:?}"
            );
        }
    }
}
