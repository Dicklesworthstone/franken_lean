use super::*;
use fln_vm::interpreter::VmRefusal;

fn typed_call(x: u64, ty: IrType, target: &str, args: Vec<IrArg>) -> IrStmt {
    IrStmt::VDecl {
        x,
        ty,
        expr: IrExpr::Fap {
            function: name(target),
            args,
        },
    }
}

fn array_setup(unsigned: bool, index: u64) -> Vec<IrStmt> {
    vec![
        num(1, 1),
        call(2, "Array.emptyWithCapacity", &[1]),
        num(3, 19),
        call(4, "Array.push", &[2, 3]),
        num(5, index),
        num(6, 42),
        if unsigned {
            typed_call(7, IrType::USize, "USize.ofNat", vec![var(5)])
        } else {
            num(7, index)
        },
    ]
}

fn array_call(x: u64, target: &str, array: u64, value: Option<u64>) -> IrStmt {
    let mut args = vec![IrArg::Erased, var(array), var(7)];
    args.extend(value.map(var));
    args.push(IrArg::Erased);
    typed_call(x, IrType::TObject, target, args)
}

fn byte_setup(unsigned: bool, index: u64) -> Vec<IrStmt> {
    vec![
        num(1, 1),
        call(2, "ByteArray.emptyWithCapacity", &[1]),
        num(3, 19),
        typed_call(4, IrType::UInt8, "UInt8.ofNat", vec![var(3)]),
        call(5, "ByteArray.push", &[2, 4]),
        num(6, index),
        if unsigned {
            typed_call(7, IrType::USize, "USize.ofNat", vec![var(6)])
        } else {
            num(7, index)
        },
        num(8, 42),
        typed_call(9, IrType::UInt8, "UInt8.ofNat", vec![var(8)]),
    ]
}

fn byte_call(x: u64, target: &str, array: u64, value: Option<u64>) -> IrStmt {
    let mut args = vec![var(array), var(7)];
    args.extend(value.map(var));
    args.push(IrArg::Erased);
    typed_call(
        x,
        if value.is_some() {
            IrType::TObject
        } else {
            IrType::UInt8
        },
        target,
        args,
    )
}

#[test]
fn proof_erased_array_updates_preserve_reads_and_shared_predecessors() {
    for (getter, setter, unsigned) in [
        ("Array.getInternal", "Array.set", false),
        ("Array.getInternalBorrowed", "Array.set", false),
        ("Array.uget", "Array.uset", true),
        ("Array.ugetBorrowed", "Array.uset", true),
    ] {
        let mut stmts = array_setup(unsigned, 0);
        stmts.extend([
            array_call(8, setter, 4, Some(6)),
            array_call(9, getter, 8, None),
            array_call(10, getter, 4, None),
            call(11, "Nat.add", &[9, 10]),
        ]);
        let compiled = compile_declarations(vec![entry(stmts, 11)]).unwrap();
        assert_nat(&compiled, "61"); // updated 42 plus retained predecessor 19
        for target in [getter, setter] {
            assert!(
                compiled
                    .native_externs()
                    .contains(&format!("extern:{target}"))
            );
        }
    }
    for (getter, setter, unsigned) in [
        ("ByteArray.get", "ByteArray.set", false),
        ("ByteArray.uget", "ByteArray.uset", true),
    ] {
        let mut stmts = byte_setup(unsigned, 0);
        stmts.extend([
            byte_call(10, setter, 5, Some(9)),
            byte_call(11, getter, 10, None),
            byte_call(12, getter, 5, None),
            call(13, "UInt8.toNat", &[11]),
            call(14, "UInt8.toNat", &[12]),
            call(15, "Nat.add", &[13, 14]),
        ]);
        assert_nat(&compile_declarations(vec![entry(stmts, 15)]).unwrap(), "61");
    }
}

#[test]
fn erased_proof_slots_never_hide_data_undefined_variables_or_partial_telescopes() {
    let read = |args| {
        let mut stmts = array_setup(false, 0);
        stmts.push(typed_call(8, IrType::TObject, "Array.getInternal", args));
        compile_declarations(vec![entry(stmts, 8)])
    };
    assert_nat(&read(vec![var(4), var(7)]).unwrap(), "19");
    for args in [
        vec![var(1), var(4), var(7), IrArg::Erased],
        vec![IrArg::Erased, var(4), var(7), var(1)],
        vec![var(999), var(4), var(7), IrArg::Erased],
        vec![IrArg::Erased, var(4), var(7), var(999)],
        vec![var(4), var(7), IrArg::Erased],
        vec![IrArg::Erased, var(4), var(7)],
    ] {
        assert!(matches!(
            read(args),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
    for args in [
        vec![IrArg::Erased, var(999), var(7), IrArg::Erased],
        vec![IrArg::Erased, var(4), var(999), IrArg::Erased],
    ] {
        assert!(matches!(read(args), Err(IrExecutionError::IrValidation(_))));
    }
    for args in [
        vec![var(5), var(7), var(1)],
        vec![var(5), var(7), var(999)],
        vec![IrArg::Erased, var(5), var(7), IrArg::Erased],
    ] {
        let mut stmts = byte_setup(false, 0);
        stmts.push(typed_call(10, IrType::UInt8, "ByteArray.get", args));
        assert!(matches!(
            compile_declarations(vec![entry(stmts, 10)]),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
}

#[test]
fn native_array_partial_applications_remain_valid_but_erased_captures_are_refused() {
    let read = |captures| {
        let mut stmts = array_setup(false, 0);
        stmts.extend([
            bind(
                8,
                IrExpr::Pap {
                    function: name("Array.getInternal"),
                    args: captures,
                },
            ),
            bind(
                9,
                IrExpr::Ap {
                    x: 8,
                    args: vec![var(7)],
                },
            ),
        ]);
        compile_declarations(vec![entry(stmts, 9)])
    };
    assert_nat(&read(vec![var(4)]).unwrap(), "19");
    for captures in [
        vec![IrArg::Erased],
        vec![IrArg::Erased, var(4)],
        vec![var(4), var(7), var(1)],
    ] {
        assert!(matches!(
            read(captures),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
    assert!(matches!(
        read(vec![var(999)]),
        Err(IrExecutionError::IrValidation(_))
    ));
    for captures in [vec![IrArg::Erased], vec![var(5), IrArg::Erased]] {
        let mut stmts = byte_setup(false, 0);
        stmts.push(bind(
            10,
            IrExpr::Pap {
                function: name("ByteArray.get"),
                args: captures,
            },
        ));
        assert!(matches!(
            compile_declarations(vec![entry(stmts, 10)]),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
}

#[test]
fn discarded_array_proofs_never_authorize_out_of_bounds_access() {
    for (target, unsigned, write) in [
        ("Array.getInternal", false, false),
        ("Array.getInternalBorrowed", false, false),
        ("Array.set", false, true),
        ("Array.uget", true, false),
        ("Array.ugetBorrowed", true, false),
        ("Array.uset", true, true),
        ("ByteArray.get", false, false),
        ("ByteArray.set", false, true),
        ("ByteArray.uget", true, false),
        ("ByteArray.uset", true, true),
    ] {
        let mut stmts = if target.starts_with("ByteArray.") {
            let mut stmts = byte_setup(unsigned, 1);
            stmts.push(byte_call(10, target, 5, write.then_some(9)));
            stmts
        } else {
            let mut stmts = array_setup(unsigned, 1);
            stmts.push(array_call(10, target, 4, write.then_some(6)));
            stmts
        };
        let result = if target.starts_with("ByteArray.") && !write {
            stmts.push(call(11, "UInt8.toNat", &[10]));
            11
        } else {
            10
        };
        let compiled = compile_declarations(vec![entry(stmts, result)]).unwrap();
        let outcome = compiled.execute(ExecutionLimits::default(), None).outcome;
        assert!(
            matches!(
                outcome,
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::ArrayIndexOutOfBounds { index: 1, size: 1 },
                    ..
                })
            ),
            "{target}: {outcome:?}"
        );
    }
}

#[test]
fn proof_bridges_bind_generated_metadata_and_keep_explicit_externs_native() {
    use super::super::array_proofs::erased_operands;

    for id in [
        "extern:Array.getInternal",
        "extern:Array.ugetBorrowed",
        "extern:ByteArray.set",
    ] {
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == id)
            .unwrap();
        assert!(erased_operands(row).unwrap().is_some());
        for changed in [
            GeneratedExternRow {
                name: "Foreign.get",
                ..*row
            },
            GeneratedExternRow {
                symbol: "foreign_array",
                ..*row
            },
            GeneratedExternRow {
                module: "Foreign",
                ..*row
            },
            GeneratedExternRow {
                arity: row.arity + 1,
                ..*row
            },
            GeneratedExternRow {
                levels: row.levels + 1,
                ..*row
            },
            GeneratedExternRow {
                effect: "state",
                ..*row
            },
            GeneratedExternRow {
                safety: "unreviewed",
                ..*row
            },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,owned-result)",
                ..*row
            },
            GeneratedExternRow {
                partition: "pure-library",
                ..*row
            },
        ] {
            assert!(matches!(
                erased_operands(&changed),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
    for arity in [2, 4] {
        let mut stmts = array_setup(false, 0);
        stmts.push(array_call(8, "Array.getInternal", 4, None));
        let declared = IrDecl::Extern {
            name: name("Array.getInternal"),
            params: (0..arity)
                .map(|x| IrParam {
                    x,
                    borrow: true,
                    ty: IrType::TObject,
                })
                .collect(),
            result: IrType::TObject,
            entries: vec![],
        };
        let result = compile_declarations(vec![entry(stmts, 8), declared]);
        if arity == 2 {
            assert_nat(&result.unwrap(), "19");
        } else {
            assert!(matches!(
                result,
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
}
