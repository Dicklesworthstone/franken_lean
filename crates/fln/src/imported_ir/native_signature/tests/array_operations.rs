//! List/Array conversion and mutation boundaries, including swap's two proofs.
use super::*;
use fln_vm::interpreter::VmRefusal;

#[test]
fn remaining_array_telescopes_authenticate_types_borrowing_and_boxed_proofs() {
    for (target, parameters, result) in [
        (
            "Array.mk",
            vec![(IrType::Erased, false), (IrType::TObject, false)],
            IrType::Object,
        ),
        (
            "Array.toList",
            vec![(IrType::Erased, false), (IrType::Object, false)],
            IrType::TObject,
        ),
        (
            "Array.pop",
            vec![(IrType::Erased, false), (IrType::Object, false)],
            IrType::Object,
        ),
        (
            "Array.swapIfInBounds",
            vec![
                (IrType::Erased, false),
                (IrType::Object, false),
                (IrType::TObject, true),
                (IrType::TObject, true),
            ],
            IrType::Object,
        ),
        (
            "Array.swap",
            vec![
                (IrType::Erased, false),
                (IrType::Object, false),
                (IrType::TObject, true),
                (IrType::TObject, true),
                (IrType::Erased, false),
                (IrType::Erased, false),
            ],
            IrType::Object,
        ),
    ] {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        let params: Vec<_> = parameters
            .into_iter()
            .enumerate()
            .map(|(x, (ty, borrow))| IrParam {
                x: x as u64,
                ty,
                borrow,
            })
            .collect();
        assert_eq!(bridge.arity(), params.len());
        validate_extern_signature(row, &params, &result).unwrap();
        assert_eq!(
            validated_ir_arity(row, params.len()).unwrap(),
            bridge.runtime_parameters().len()
        );
        for index in 0..params.len() {
            for change_type in [false, true] {
                let mut wrong = params.clone();
                if change_type {
                    wrong[index].ty = if wrong[index].ty == IrType::Erased {
                        IrType::TObject
                    } else {
                        IrType::Erased
                    };
                } else {
                    wrong[index].borrow = !wrong[index].borrow;
                }
                assert!(
                    matches!(
                        validate_extern_signature(row, &wrong, &result),
                        Err(IrExecutionError::NativeContract { .. })
                    ),
                    "{target}, parameter {index}, type={change_type}"
                );
            }
        }
        assert!(matches!(
            validate_extern_signature(row, &params, &IrType::Void),
            Err(IrExecutionError::NativeContract { .. })
        ));
        let boxed = IrDecl::Extern {
            name: Name::str(name(target), "_boxed"),
            params: params
                .iter()
                .map(|p| IrParam {
                    x: p.x,
                    borrow: false,
                    ty: if p.ty == IrType::Erased {
                        IrType::TObject
                    } else {
                        p.ty.clone()
                    },
                })
                .collect(),
            result,
            entries: Vec::new(),
        };
        bridge.validate_declaration(&boxed).unwrap();
        for index in 0..params.len() {
            for remove in [false, true] {
                let mut wrong = boxed.clone();
                let IrDecl::Extern { params, .. } = &mut wrong else {
                    unreachable!()
                };
                if remove {
                    params.remove(index);
                } else {
                    params[index].borrow = true;
                }
                assert!(matches!(
                    bridge.validate_declaration(&wrong),
                    Err(IrExecutionError::NativeContract { .. })
                ));
            }
        }
    }
}

fn setup(first: IrNat, second: IrNat) -> Vec<IrStmt> {
    vec![
        num(1, 0),
        call(2, "Array.emptyWithCapacity", &[1]),
        num(3, 11),
        call(4, "Array.push", &[2, 3]),
        num(5, 23),
        call(6, "Array.push", &[4, 5]),
        bind(7, IrExpr::Lit(IrLit::Num(first))),
        bind(8, IrExpr::Lit(IrLit::Num(second))),
    ]
}

fn direct_swap(args: Vec<IrArg>) -> Result<CompiledIr, IrExecutionError> {
    let mut stmts = setup(IrNat::Small(0), IrNat::Small(1));
    stmts.extend([
        bind(
            9,
            IrExpr::Fap {
                function: name("Array.swap"),
                args,
            },
        ),
        call(10, "Array.get!Internal", &[1, 9, 1]),
        call(11, "Array.get!Internal", &[1, 6, 1]),
        num(12, 100),
        call(13, "Nat.mul", &[10, 12]),
        call(14, "Nat.add", &[13, 11]),
    ]);
    compile_declarations(vec![entry(stmts, 14)])
}

#[test]
fn swap_erases_both_literal_proofs_and_preserves_shared_predecessors() {
    for args in [
        vec![var(6), var(7), var(8)],
        vec![
            IrArg::Erased,
            var(6),
            var(7),
            var(8),
            IrArg::Erased,
            IrArg::Erased,
        ],
    ] {
        assert_nat(&direct_swap(args).unwrap(), "2311");
    }
    let mut stmts = setup(IrNat::Small(0), IrNat::Small(1));
    stmts.extend([
        bind(
            9,
            IrExpr::Pap {
                function: name("Array.swap._boxed"),
                args: vec![IrArg::Erased, var(6), var(7), var(8)],
            },
        ),
        bind(
            10,
            IrExpr::Ap {
                x: 9,
                args: vec![IrArg::Erased, IrArg::Erased],
            },
        ),
        bind(
            11,
            IrExpr::Ap {
                x: 9,
                args: vec![IrArg::Erased, IrArg::Erased],
            },
        ),
        call(12, "Array.get!Internal", &[1, 6, 1]),
        call(13, "Array.get!Internal", &[1, 10, 1]),
        call(14, "Array.get!Internal", &[1, 11, 1]),
        num(15, 100),
        num(16, 10_000),
        call(17, "Nat.mul", &[13, 15]),
        call(18, "Nat.mul", &[14, 16]),
        call(19, "Nat.add", &[12, 17]),
        call(20, "Nat.add", &[19, 18]),
    ]);
    let compiled = compile_declarations(vec![entry(stmts, 20)]).unwrap();
    assert_nat(&compiled, "232311");
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
    assert_nat(&compiled, "232311");
}

#[test]
fn swap_erasure_never_hides_data_or_an_incomplete_proof_suffix() {
    let original = vec![
        IrArg::Erased,
        var(6),
        var(7),
        var(8),
        IrArg::Erased,
        IrArg::Erased,
    ];
    for index in [0, 4, 5] {
        for replacement in [var(1), var(999)] {
            let mut wrong = original.clone();
            wrong[index] = replacement;
            assert!(matches!(
                direct_swap(wrong),
                Err(IrExecutionError::Unsupported { .. })
            ));
        }
        let mut missing = original.clone();
        missing.remove(index);
        assert!(matches!(
            direct_swap(missing),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
    let mut extra = original.clone();
    extra.push(IrArg::Erased);
    assert!(matches!(
        direct_swap(extra),
        Err(IrExecutionError::Unsupported { .. })
    ));
    for index in [1, 2, 3] {
        let mut wrong = original.clone();
        wrong[index] = var(999);
        assert!(matches!(
            direct_swap(wrong),
            Err(IrExecutionError::IrValidation(_))
        ));
    }
    for target in ["Array.swap", "Array.swap._boxed"] {
        let mut stmts = setup(IrNat::Small(0), IrNat::Small(1));
        stmts.push(bind(
            9,
            IrExpr::Pap {
                function: name(target),
                args: vec![IrArg::Erased, var(6), var(7), var(8), var(999)],
            },
        ));
        let result = compile_declarations(vec![entry(stmts, 9)]);
        if target.ends_with("_boxed") {
            assert!(matches!(result, Err(IrExecutionError::IrValidation(_))));
        } else {
            assert!(matches!(result, Err(IrExecutionError::Unsupported { .. })));
        }
    }
}

#[test]
fn swaps_check_each_index_without_truncating_large_naturals() {
    for bad in [
        IrNat::Small(2),
        IrNat::Small(u64::MAX),
        IrNat::Big(vec![0, 1]),
    ] {
        for second_is_bad in [false, true] {
            for boxed in [false, true] {
                for safe in [false, true] {
                    let (first, second) = if second_is_bad {
                        (IrNat::Small(0), bad.clone())
                    } else {
                        (bad.clone(), IrNat::Small(0))
                    };
                    let mut stmts = setup(first, second);
                    let target = if safe {
                        "Array.swapIfInBounds"
                    } else {
                        "Array.swap"
                    };
                    let mut args = vec![IrArg::Erased, var(6), var(7), var(8)];
                    if !safe {
                        args.extend([IrArg::Erased, IrArg::Erased]);
                    }
                    if boxed {
                        stmts.push(bind(
                            9,
                            IrExpr::Pap {
                                function: name(&format!("{target}._boxed")),
                                args: vec![IrArg::Erased, var(6)],
                            },
                        ));
                        stmts.push(bind(
                            10,
                            IrExpr::Ap {
                                x: 9,
                                args: args[2..].to_vec(),
                            },
                        ));
                    } else {
                        stmts.push(bind(
                            10,
                            IrExpr::Fap {
                                function: name(target),
                                args,
                            },
                        ));
                    }
                    stmts.push(call(11, "Array.get!Internal", &[1, 10, 1]));
                    let compiled = compile_declarations(vec![entry(stmts, 11)]).unwrap();
                    if safe {
                        assert_nat(&compiled, "11");
                    } else {
                        let outcome = compiled.execute(ExecutionLimits::default(), None).outcome;
                        assert!(
                            matches!(
                                outcome,
                                Outcome::Complete(VmExit::Refused {
                                    refusal: VmRefusal::ArrayIndexOutOfBounds { size: 2, .. },
                                    ..
                                })
                            ),
                            "index={bad:?}, second={second_is_bad}, boxed={boxed}: {outcome:?}"
                        );
                    }
                }
            }
        }
    }
    assert_nat(&direct_swap(vec![var(6), var(7), var(8)]).unwrap(), "2311");
}

pub(super) const BYTE_ARRAY_NAMES: [&str; 13] = [
    "ByteArray.mk",
    "ByteArray.data",
    "ByteArray.emptyWithCapacity",
    "ByteArray.push",
    "ByteArray.size",
    "ByteArray.usize",
    "ByteArray.get!",
    "ByteArray.set!",
    "ByteArray.beq",
    "ByteArray.decEq",
    "ByteArray.hash",
    "ByteArray.copySlice",
    "ByteArray.validateUTF8",
];

#[test]
fn byte_array_telescopes_authenticate_native_borrowing_and_boxed_scalars() {
    let mut observed = BTreeSet::new();
    for (target, parameters, result) in [
        (
            "ByteArray.mk",
            vec![(IrType::Object, false)],
            IrType::Object,
        ),
        (
            "ByteArray.data",
            vec![(IrType::Object, false)],
            IrType::Object,
        ),
        (
            "ByteArray.emptyWithCapacity",
            vec![(IrType::TObject, true)],
            IrType::Object,
        ),
        (
            "ByteArray.push",
            vec![(IrType::Object, false), (IrType::UInt8, false)],
            IrType::Object,
        ),
        (
            "ByteArray.size",
            vec![(IrType::Object, true)],
            IrType::Tagged,
        ),
        (
            "ByteArray.usize",
            vec![(IrType::Object, true)],
            IrType::USize,
        ),
        (
            "ByteArray.get!",
            vec![(IrType::Object, true), (IrType::TObject, true)],
            IrType::UInt8,
        ),
        (
            "ByteArray.set!",
            vec![
                (IrType::Object, false),
                (IrType::TObject, true),
                (IrType::UInt8, false),
            ],
            IrType::Object,
        ),
        (
            "ByteArray.beq",
            vec![(IrType::Object, true), (IrType::Object, true)],
            IrType::UInt8,
        ),
        (
            "ByteArray.decEq",
            vec![(IrType::Object, true), (IrType::Object, true)],
            IrType::UInt8,
        ),
        (
            "ByteArray.hash",
            vec![(IrType::Object, true)],
            IrType::UInt64,
        ),
        (
            "ByteArray.copySlice",
            vec![
                (IrType::Object, true),
                (IrType::TObject, false),
                (IrType::Object, false),
                (IrType::TObject, false),
                (IrType::TObject, false),
                (IrType::UInt8, false),
            ],
            IrType::Object,
        ),
        (
            "ByteArray.validateUTF8",
            vec![(IrType::Object, true)],
            IrType::UInt8,
        ),
    ] {
        assert!(observed.insert(target));
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        let params: Vec<_> = parameters
            .into_iter()
            .enumerate()
            .map(|(x, (ty, borrow))| IrParam {
                x: x as u64,
                ty,
                borrow,
            })
            .collect();
        assert_eq!(bridge.arity(), params.len());
        validate_extern_signature(row, &params, &result).unwrap();
        for index in 0..params.len() {
            let mut wrong = params.clone();
            wrong[index].ty = IrType::Erased;
            assert!(matches!(
                validate_extern_signature(row, &wrong, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
            wrong = params.clone();
            wrong[index].borrow = !wrong[index].borrow;
            assert!(matches!(
                validate_extern_signature(row, &wrong, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
        assert!(matches!(
            validate_extern_signature(row, &params, &IrType::Void),
            Err(IrExecutionError::NativeContract { .. })
        ));
        for changed in [
            GeneratedExternRow {
                symbol: "foreign_byte_array",
                ..*row
            },
            GeneratedExternRow {
                arity: row.arity + 1,
                ..*row
            },
            GeneratedExternRow {
                ownership: if row.ownership == "rule(borrowed-args,owned-result)" {
                    "abi((a: borrowed_arg) -> owned_res)"
                } else {
                    "rule(borrowed-args,owned-result)"
                },
                ..*row
            },
            GeneratedExternRow {
                partition: "library-code",
                ..*row
            },
        ] {
            assert!(matches!(
                BoxedNative::from_row(&changed),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
    assert_eq!(observed, BYTE_ARRAY_NAMES.into_iter().collect());
}

fn byte_typed(x: u64, ty: IrType, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl { x, ty, expr }
}

fn byte_call(x: u64, ty: IrType, target: &str, args: &[u64]) -> IrStmt {
    byte_typed(
        x,
        ty,
        IrExpr::Fap {
            function: name(target),
            args: args.iter().copied().map(var).collect(),
        },
    )
}

fn byte_setup(value: u64) -> Vec<IrStmt> {
    vec![
        num(1, 0),
        byte_call(2, IrType::Object, "ByteArray.emptyWithCapacity", &[1]),
        num(3, value),
        byte_call(4, IrType::UInt8, "UInt8.ofNat", &[3]),
        byte_call(5, IrType::Object, "ByteArray.push", &[2, 4]),
    ]
}

#[test]
fn byte_array_boxed_updates_reuse_consuming_captures_and_staged_arguments() {
    for target in ["ByteArray.push", "ByteArray.set!"] {
        let mut stmts = byte_setup(65);
        stmts.extend([
            byte_typed(
                6,
                IrType::Object,
                IrExpr::Pap {
                    function: name(&format!("{target}._boxed")),
                    args: vec![var(5)],
                },
            ),
            num(7, 255),
            byte_call(8, IrType::UInt8, "UInt8.ofNat", &[7]),
            byte_typed(
                9,
                IrType::Tagged,
                IrExpr::Box {
                    ty: IrType::UInt8,
                    x: 8,
                },
            ),
        ]);
        let function = if target == "ByteArray.set!" {
            stmts.push(byte_typed(
                10,
                IrType::Object,
                IrExpr::Ap {
                    x: 6,
                    args: vec![var(1)],
                },
            ));
            10
        } else {
            6
        };
        stmts.extend([
            byte_typed(
                11,
                IrType::Object,
                IrExpr::Ap {
                    x: function,
                    args: vec![var(9)],
                },
            ),
            num(12, 66),
            byte_call(13, IrType::UInt8, "UInt8.ofNat", &[12]),
            byte_typed(
                14,
                IrType::Tagged,
                IrExpr::Box {
                    ty: IrType::UInt8,
                    x: 13,
                },
            ),
            byte_typed(
                15,
                IrType::Object,
                IrExpr::Ap {
                    x: function,
                    args: vec![var(14)],
                },
            ),
            num(16, u64::from(target == "ByteArray.push")),
            byte_call(17, IrType::UInt8, "ByteArray.get!", &[11, 16]),
            byte_call(18, IrType::UInt8, "ByteArray.get!", &[15, 16]),
            byte_call(19, IrType::UInt8, "ByteArray.get!", &[5, 1]),
            byte_call(20, IrType::Tagged, "ByteArray.size", &[5]),
            call(21, "UInt8.toNat", &[17]),
            call(22, "UInt8.toNat", &[18]),
            call(23, "UInt8.toNat", &[19]),
            call(24, "Nat.add", &[21, 22]),
            call(25, "Nat.add", &[24, 23]),
            call(26, "Nat.add", &[25, 20]),
        ]);
        let compiled = compile_declarations(vec![entry(stmts, 26)]).unwrap();
        assert_nat(&compiled, "387");
        assert!(
            compiled
                .native_externs()
                .contains(&format!("extern:{target}"))
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
        assert_nat(&compiled, "387");
    }
}

#[test]
fn byte_array_boxed_copy_slice_preserves_aliased_inputs_and_boolean_suffix() {
    let mut stmts = byte_setup(65);
    stmts.extend([
        num(6, 66),
        byte_call(7, IrType::UInt8, "UInt8.ofNat", &[6]),
        byte_call(8, IrType::Object, "ByteArray.push", &[5, 7]),
        num(9, 1),
        byte_typed(
            10,
            IrType::Object,
            IrExpr::Pap {
                function: name("ByteArray.copySlice._boxed"),
                args: vec![var(8), var(1), var(8), var(9)],
            },
        ),
        byte_typed(
            11,
            IrType::Object,
            IrExpr::Ap {
                x: 10,
                args: vec![var(9)],
            },
        ),
        byte_typed(
            12,
            IrType::Object,
            IrExpr::Ap {
                x: 11,
                args: vec![var(9)],
            },
        ),
        byte_typed(
            13,
            IrType::Object,
            IrExpr::Ap {
                x: 11,
                args: vec![var(1)],
            },
        ),
        byte_call(14, IrType::UInt8, "ByteArray.get!", &[12, 9]),
        byte_call(15, IrType::UInt8, "ByteArray.get!", &[13, 9]),
        byte_call(16, IrType::UInt8, "ByteArray.get!", &[8, 9]),
        call(17, "UInt8.toNat", &[14]),
        call(18, "UInt8.toNat", &[15]),
        call(19, "UInt8.toNat", &[16]),
        call(20, "Nat.add", &[17, 18]),
        call(21, "Nat.add", &[20, 19]),
    ]);
    assert_nat(
        &compile_declarations(vec![entry(stmts, 21)]).unwrap(),
        "196",
    );
}

#[test]
fn byte_array_boxed_predicates_and_hash_preserve_scalar_results() {
    let mut saw_high_bit = false;
    for byte in [0u8, 65, 127, 128, 192, 255] {
        for target in [
            "ByteArray.beq",
            "ByteArray.decEq",
            "ByteArray.validateUTF8",
            "ByteArray.hash",
        ] {
            let mut stmts = byte_setup(u64::from(byte));
            let captured = matches!(target, "ByteArray.beq" | "ByteArray.decEq");
            let hash = target == "ByteArray.hash";
            stmts.extend([
                byte_typed(
                    6,
                    IrType::Object,
                    IrExpr::Pap {
                        function: name(&format!("{target}._boxed")),
                        args: if captured { vec![var(5)] } else { Vec::new() },
                    },
                ),
                byte_typed(
                    7,
                    if hash { IrType::Object } else { IrType::Tagged },
                    IrExpr::Ap {
                        x: 6,
                        args: vec![var(5)],
                    },
                ),
                byte_typed(
                    8,
                    if hash { IrType::UInt64 } else { IrType::UInt8 },
                    IrExpr::Unbox { x: 7 },
                ),
                call(9, if hash { "UInt64.toNat" } else { "UInt8.toNat" }, &[8]),
            ]);
            let expected = if hash {
                let hash = fln_core::lean_hash::murmur_hash_64a(&[byte], 11);
                saw_high_bit |= hash > u64::MAX / 2;
                hash
            } else if target == "ByteArray.validateUTF8" {
                u64::from(byte < 128)
            } else {
                1
            };
            assert_nat(
                &compile_declarations(vec![entry(stmts, 9)]).unwrap(),
                &expected.to_string(),
            );
        }
    }
    assert!(
        saw_high_bit,
        "boxed hashes must exercise the full UInt64 width"
    );
}

#[test]
fn byte_array_boxed_getter_refuses_foreign_objects_before_returning_data() {
    let stmts = vec![
        byte_typed(
            1,
            IrType::Object,
            IrExpr::Lit(IrLit::Str("not bytes".to_owned())),
        ),
        byte_typed(
            2,
            IrType::Object,
            IrExpr::Pap {
                function: name("ByteArray.get!._boxed"),
                args: vec![var(1)],
            },
        ),
        num(3, 0),
        byte_typed(
            4,
            IrType::Tagged,
            IrExpr::Ap {
                x: 2,
                args: vec![var(3)],
            },
        ),
        byte_typed(5, IrType::UInt8, IrExpr::Unbox { x: 4 }),
        call(6, "UInt8.toNat", &[5]),
    ];
    let compiled = compile_declarations(vec![entry(stmts, 6)]).unwrap();
    assert!(matches!(
        compiled.execute(ExecutionLimits::default(), None).outcome,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch { .. },
            ..
        })
    ));
}
