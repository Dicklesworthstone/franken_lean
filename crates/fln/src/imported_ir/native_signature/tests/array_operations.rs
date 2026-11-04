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
    for bad in [IrNat::Small(2), IrNat::Small(u64::MAX), IrNat::Big(vec![0, 1])] {
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
