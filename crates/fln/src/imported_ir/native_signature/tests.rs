use super::*;
use crate::imported_ir::{CompiledIr, IrExecutionLimits, VerifiedPartition, compile};
use fln_comp::flbc;
use fln_core::outcome::Outcome;
use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir::{
    IrArg, IrBody, IrDecl, IrExpr, IrLit, IrModule, IrNat, IrParam, IrStmt, IrTerminal, IrType,
};
use fln_olean::ir_archive::CensusPartition;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};
use std::collections::BTreeSet;

#[path = "tests/arrays_reference.rs"]
mod arrays_reference;

#[path = "tests/array_proofs.rs"]
mod array_proofs;

#[path = "tests/array_operations.rs"]
mod array_operations;

#[path = "tests/float_arrays.rs"]
mod float_arrays;

#[path = "tests/boxed_primitives.rs"]
mod boxed_primitives;

#[path = "tests/boxed_floats.rs"]
mod boxed_floats;

#[path = "tests/primitives_reference.rs"]
mod primitives_reference;

#[path = "tests/integers.rs"]
mod integers;

#[path = "tests/levels_reference.rs"]
mod levels_reference;

#[path = "tests/expressions_reference.rs"]
mod expressions_reference;

#[path = "tests/names_reference.rs"]
mod names_reference;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn var(x: u64) -> IrArg {
    IrArg::Var(x)
}

fn bind(x: u64, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl {
        x,
        ty: IrType::TObject,
        expr,
    }
}

fn num(x: u64, value: u64) -> IrStmt {
    bind(x, IrExpr::Lit(IrLit::Num(IrNat::Small(value))))
}

fn call(x: u64, target: &str, args: &[u64]) -> IrStmt {
    bind(
        x,
        IrExpr::Fap {
            function: name(target),
            args: args.iter().copied().map(var).collect(),
        },
    )
}

fn entry(stmts: Vec<IrStmt>, result: u64) -> IrDecl {
    IrDecl::Function {
        name: name("Arity.main"),
        params: vec![],
        result: IrType::TObject,
        body: IrBody {
            stmts,
            terminal: Box::new(IrTerminal::Ret(var(result))),
        },
        sorry_dep: None,
    }
}

fn array_entry() -> IrDecl {
    entry(
        vec![
            num(1, 4),
            call(2, "Array.emptyWithCapacity", &[1]),
            num(3, 42),
            call(4, "Array.push", &[2, 3]),
            call(5, "Array.size", &[4]),
        ],
        5,
    )
}

fn compile_declarations(decls: Vec<IrDecl>) -> Result<CompiledIr, IrExecutionError> {
    let partition = VerifiedPartition {
        partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default())
            .unwrap(),
    };
    compile(
        &[IrModule {
            decls,
            ..IrModule::default()
        }],
        &name("Arity.main"),
        &[],
        &partition,
        &BTreeSet::from([name("Arity.main")]),
        IrExecutionLimits::default(),
    )
}

fn assert_nat(compiled: &CompiledIr, expected: &str) {
    let bytes =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    for program in [compiled.program.program(), &replay] {
        let result = execute(program, ExecutionLimits::default(), None);
        let Outcome::Complete(VmExit::Returned(value)) = result else {
            panic!("{result:?}");
        };
        assert_eq!(nat_decimal(&value.value).as_deref(), Some(expected));
    }
    assert_eq!(compiled.reference_functions().len(), 1);
    assert_eq!(compiled.reference_functions()[0].producer(), "reference");
}

#[test]
fn generated_abi_arity_is_independent_of_erased_source_binders() {
    for (signature, expected) in [
        ("() -> owned_res", 0),
        ("(()) -> owned_res", 0),
        ("(value) -> value", 1),
        ("(xs: borrowed_arg, x: owned_arg) -> owned_res", 2),
    ] {
        let contract = Ownership::AbiSignature(signature.to_owned());
        assert_eq!(executable_arity(&contract, 17).unwrap(), expected);
    }
    assert_eq!(
        executable_arity(&Ownership::DefaultRuleOwnedResult, 3).unwrap(),
        3
    );
    assert_eq!(executable_arity(&Ownership::ScalarRule, 2).unwrap(), 2);
}

#[test]
fn arity_inference_never_bypasses_ownership_contract_validation() {
    for signature in [
        "owned_arg -> owned_res",
        "(owned_arg)",
        "(raw_object) -> owned_res",
        "(borrowed_arg, ) -> owned_res",
        "(borrowed_arg) -> unknown_result",
        "(unknown_argument) -> owned_res",
    ] {
        let contract = Ownership::AbiSignature(signature.to_owned());
        assert!(executable_arity(&contract, 1).is_err());
    }
    assert!(executable_arity(&Ownership::LlvmCApi, 0).is_err());
}

#[test]
fn imported_array_calls_link_without_repeated_extern_declarations() {
    let compiled = compile_declarations(vec![array_entry()]).unwrap();
    assert_nat(&compiled, "1");
    assert!(
        compiled
            .native_externs()
            .iter()
            .any(|row| row == "extern:Array.push")
    );
}

#[test]
fn native_partial_application_uses_the_runtime_suffix_and_preserves_its_capture() {
    let compiled = compile_declarations(vec![entry(
        vec![
            num(1, 4),
            call(2, "Array.emptyWithCapacity", &[1]),
            bind(
                3,
                IrExpr::Pap {
                    function: name("Array.push"),
                    args: vec![var(2)],
                },
            ),
            num(4, 19),
            bind(
                5,
                IrExpr::Ap {
                    x: 3,
                    args: vec![var(4)],
                },
            ),
            num(6, 23),
            bind(
                7,
                IrExpr::Ap {
                    x: 3,
                    args: vec![var(6)],
                },
            ),
            call(8, "Array.size", &[2]),
            call(9, "Array.size", &[5]),
            call(10, "Array.size", &[7]),
            call(11, "Nat.add", &[8, 9]),
            call(12, "Nat.add", &[11, 10]),
        ],
        12,
    )])
    .unwrap();
    // The captured empty array remains empty. Each invocation returns its
    // own one-element array, rather than consuming the reusable capture.
    assert_nat(&compiled, "2");
}

#[test]
fn native_boxed_partial_application_retains_type_capture_and_reusable_arrays() {
    let compiled = compile_declarations(vec![entry(
        vec![
            num(1, 4),
            call(2, "Array.emptyWithCapacity", &[1]),
            bind(
                3,
                IrExpr::Pap {
                    function: name("Array.push._boxed"),
                    args: vec![IrArg::Erased, var(2)],
                },
            ),
            num(4, 19),
            bind(
                5,
                IrExpr::Ap {
                    x: 3,
                    args: vec![var(4)],
                },
            ),
            num(6, 23),
            bind(
                7,
                IrExpr::Ap {
                    x: 3,
                    args: vec![var(6)],
                },
            ),
            call(8, "Array.size", &[2]),
            call(9, "Array.size", &[5]),
            call(10, "Array.size", &[7]),
            call(11, "Nat.add", &[8, 9]),
            call(12, "Nat.add", &[11, 10]),
        ],
        12,
    )])
    .unwrap();
    assert_nat(&compiled, "2");
    assert_eq!(
        compiled
            .native_externs()
            .iter()
            .filter(|id| *id == "extern:Array.push")
            .count(),
        1,
        "the boxed adapter shares the primitive's canonical native row"
    );
}

#[test]
fn native_boxed_partial_application_keeps_its_arity_after_constructor_normalization() {
    let compiled = compile_declarations(vec![entry(
        vec![
            num(1, 1),
            call(2, "Array.emptyWithCapacity", &[1]),
            bind(
                3,
                IrExpr::Pap {
                    function: name("Array.push._boxed"),
                    args: vec![IrArg::Erased, var(2)],
                },
            ),
            num(4, 42),
            bind(
                5,
                IrExpr::Ctor {
                    info: fln_olean::ir::IrCtorInfo {
                        name: name("Arity.box"),
                        cidx: 0,
                        size: 1,
                        usize: 0,
                        ssize: 0,
                    },
                    args: vec![IrArg::Erased],
                },
            ),
            IrStmt::Set {
                x: 5,
                i: 0,
                y: var(4),
            },
            bind(6, IrExpr::Proj { i: 0, x: 5 }),
            bind(
                7,
                IrExpr::Ap {
                    x: 3,
                    args: vec![var(6)],
                },
            ),
            num(8, 0),
            call(9, "Array.get!Internal", &[8, 7, 8]),
        ],
        9,
    )])
    .unwrap();
    // Fresh-constructor stores force a second type-validation pass. The
    // captured erased type still leaves one data argument pending there.
    assert_nat(&compiled, "42");
}

#[test]
fn native_boxed_telescope_and_reserved_names_cannot_be_supplied_by_user_ir() {
    let declaration = || {
        entry(
            vec![
                num(1, 1),
                call(2, "Array.emptyWithCapacity", &[1]),
                num(3, 42),
                bind(
                    4,
                    IrExpr::Fap {
                        function: name("Array.push._boxed"),
                        args: vec![IrArg::Erased, var(2), var(3)],
                    },
                ),
                call(5, "Array.size", &[4]),
            ],
            5,
        )
    };
    let prototype = || IrDecl::Extern {
        name: name("Array.push._boxed"),
        params: [IrType::TObject, IrType::Object, IrType::TObject]
            .into_iter()
            .enumerate()
            .map(|(x, ty)| IrParam {
                x: x as u64,
                borrow: false,
                ty,
            })
            .collect(),
        result: IrType::Object,
        entries: vec![],
    };
    assert_nat(
        &compile_declarations(vec![declaration(), prototype()]).unwrap(),
        "1",
    );
    for mutation in 0..8 {
        let mut wrong = prototype();
        let IrDecl::Extern { params, result, .. } = &mut wrong else {
            unreachable!()
        };
        match mutation {
            0 => {
                params.pop();
            }
            1 => params[0].ty = IrType::Erased,
            2 => params[1].borrow = true,
            3 => params[2].ty = IrType::UInt8,
            4 => *result = IrType::UInt8,
            5 => *result = IrType::Void,
            6 => params[1].ty = IrType::Tagged,
            _ => *result = IrType::TObject,
        }
        assert!(matches!(
            compile_declarations(vec![declaration(), wrong]),
            Err(IrExecutionError::NativeContract { .. })
        ));
    }
    let module = IrModule {
        decls: vec![declaration(), prototype()],
        ..IrModule::default()
    };
    assert!(matches!(compile(
        &[module],
        &name("Arity.main"),
        &[],
        &VerifiedPartition::user_fixture(),
        &BTreeSet::from([name("Arity.main"), name("Array.push._boxed")]),
        IrExecutionLimits::default(),
    ), Err(IrExecutionError::UserOverridesCensus(found)) if found == name("Array.push._boxed")));
    for target in [
        "Int.divExact._boxed",
        "Void.mk._boxed",
        "ST.Prim.Ref.ptrEq._boxed",
    ] {
        let unsupported = entry(
            vec![bind(
                1,
                IrExpr::Pap {
                    function: name(target),
                    args: vec![],
                },
            )],
            1,
        );
        assert!(matches!(
            compile_declarations(vec![unsupported]),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
    assert!(boxed_row(&Name::str(Name::anonymous(), "Array.push._boxed")).is_none());
    assert!(boxed_row(&name("Array.push._boxed.other")).is_none());
}

#[test]
fn supplied_extern_telescope_must_still_match_the_native_abi() {
    for arity in [2, 3] {
        let declaration = IrDecl::Extern {
            name: name("Array.push"),
            params: (0..arity)
                .map(|x| IrParam {
                    x,
                    borrow: false,
                    ty: IrType::TObject,
                })
                .collect(),
            result: IrType::TObject,
            entries: vec![],
        };
        let compiled = compile_declarations(vec![array_entry(), declaration]);
        if arity == 2 {
            assert_nat(&compiled.unwrap(), "1");
        } else {
            assert!(matches!(
                compiled,
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
    }
}

#[test]
fn malformed_call_does_not_determine_a_native_callees_arity() {
    let mut declaration = array_entry();
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!();
    };
    let IrStmt::VDecl {
        expr: IrExpr::Fap { args, .. },
        ..
    } = &mut body.stmts[3]
    else {
        unreachable!();
    };
    // A data-bearing operand cannot impersonate the pin's erased type slot.
    args.insert(0, var(1));
    assert!(matches!(
        compile_declarations(vec![declaration]),
        Err(IrExecutionError::Unsupported { .. })
    ));
}

#[test]
fn pinned_array_type_slots_are_erased_without_hiding_bad_data_or_authority() {
    let declaration = || {
        entry(
            vec![
                num(1, 2),
                bind(
                    2,
                    IrExpr::Fap {
                        function: name("Array.mkEmpty"),
                        args: vec![IrArg::Erased, var(1)],
                    },
                ),
                num(3, 42),
                bind(
                    4,
                    IrExpr::Fap {
                        function: name("Array.push"),
                        args: vec![IrArg::Erased, var(2), var(3)],
                    },
                ),
                bind(
                    5,
                    IrExpr::Fap {
                        function: name("Array.size"),
                        args: vec![IrArg::Erased, var(4)],
                    },
                ),
            ],
            5,
        )
    };
    assert_nat(&compile_declarations(vec![declaration()]).unwrap(), "1");
    for (statement, operand, replacement) in [
        (1, 0, var(1)),
        (3, 0, var(1)),
        (1, 1, var(999)),
        (3, 1, var(999)),
        (3, 2, var(999)),
        (4, 0, var(1)),
        (4, 1, var(999)),
    ] {
        let mut mutated = declaration();
        let IrDecl::Function { body, .. } = &mut mutated else {
            unreachable!()
        };
        let IrStmt::VDecl {
            expr: IrExpr::Fap { args, .. },
            ..
        } = &mut body.stmts[statement]
        else {
            unreachable!()
        };
        args[operand] = replacement;
        assert!(compile_declarations(vec![mutated]).is_err());
    }
    let first_class = entry(
        vec![bind(
            1,
            IrExpr::Pap {
                function: name("Array.push"),
                args: vec![IrArg::Erased],
            },
        )],
        1,
    );
    assert!(matches!(
        compile_declarations(vec![first_class]),
        Err(IrExecutionError::Unsupported { .. })
    ));
    for id in [
        "extern:Array.mk",
        "extern:Array.toList",
        "extern:Array.pop",
        "extern:Array.swapIfInBounds",
        "extern:Array.emptyWithCapacity",
        "extern:Array.mkEmpty",
        "extern:Array.push",
        "extern:Array.size",
        "extern:Array.replicate",
        "extern:Array.set!",
        "extern:Array.get!Internal",
        "extern:Array.get!InternalBorrowed",
        "extern:Array.usize",
        "extern:Void.mk",
    ] {
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == id)
            .unwrap();
        assert!(erased_type_runtime_arity(row).unwrap().is_some());
        for changed in [
            GeneratedExternRow {
                symbol: "foreign_array",
                ..*row
            },
            GeneratedExternRow {
                arity: row.arity + 1,
                ..*row
            },
            GeneratedExternRow {
                effect: "state",
                ..*row
            },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,owned-result)",
                ..*row
            },
        ] {
            assert!(erased_type_runtime_arity(&changed).is_err());
        }
    }
}

#[test]
fn empty_with_capacity_keeps_its_full_native_telescope_and_boxed_capture() {
    let prototype = |boxed: bool| IrDecl::Extern {
        name: name(if boxed {
            "Array.emptyWithCapacity._boxed"
        } else {
            "Array.emptyWithCapacity"
        }),
        params: vec![
            IrParam {
                x: 1,
                ty: if boxed {
                    IrType::TObject
                } else {
                    IrType::Erased
                },
                borrow: false,
            },
            IrParam {
                x: 2,
                ty: IrType::TObject,
                borrow: !boxed,
            },
        ],
        result: IrType::Object,
        entries: vec![],
    };
    let caller = |boxed: bool| {
        let mut stmts = vec![num(1, 4)];
        if boxed {
            stmts.push(bind(
                2,
                IrExpr::Pap {
                    function: name("Array.emptyWithCapacity._boxed"),
                    args: vec![IrArg::Erased],
                },
            ));
            stmts.push(bind(
                3,
                IrExpr::Ap {
                    x: 2,
                    args: vec![var(1)],
                },
            ));
        } else {
            stmts.push(bind(
                3,
                IrExpr::Fap {
                    function: name("Array.emptyWithCapacity"),
                    args: vec![IrArg::Erased, var(1)],
                },
            ));
        }
        stmts.extend([
            num(4, 42),
            call(5, "Array.push", &[3, 4]),
            call(6, "Array.size", &[5]),
        ]);
        entry(stmts, 6)
    };
    for boxed in [false, true] {
        let compiled =
            compile_declarations(vec![caller(boxed), prototype(false), prototype(true)]).unwrap();
        assert_nat(&compiled, "1");
        assert!(
            compiled
                .native_externs()
                .iter()
                .any(|row| row == "extern:Array.emptyWithCapacity")
        );
        for mutation in 0..7 {
            let mut changed = prototype(boxed);
            let IrDecl::Extern { params, result, .. } = &mut changed else {
                unreachable!()
            };
            match mutation {
                0 => params[0].ty = IrType::UInt8,
                1 => params[0].borrow = true,
                2 => params[1].ty = IrType::Object,
                3 => params[1].borrow = !params[1].borrow,
                4 => *result = IrType::TObject,
                5 => *result = IrType::Void,
                _ => {
                    params.clear();
                }
            }
            assert!(
                matches!(
                    compile_declarations(vec![caller(boxed), changed, prototype(!boxed)]),
                    Err(IrExecutionError::NativeContract { .. })
                ),
                "boxed={boxed}, mutation={mutation}"
            );
        }
    }
    // The existing runtime-only extern form is intentionally still accepted;
    // its one capacity operand is fixed by the generated ABI.
    let mut native_form = prototype(false);
    let IrDecl::Extern { params, .. } = &mut native_form else {
        unreachable!()
    };
    params.remove(0);
    assert_nat(
        &compile_declarations(vec![caller(false), native_form]).unwrap(),
        "1",
    );
    // Only the exact erased literal may disappear from a raw call. A data
    // operand in that position and an out-of-scope capacity both refuse.
    for (operand, replacement) in [(0, var(1)), (1, var(999))] {
        let mut changed = caller(false);
        let IrDecl::Function { body, .. } = &mut changed else {
            unreachable!()
        };
        let IrStmt::VDecl {
            expr: IrExpr::Fap { args, .. },
            ..
        } = &mut body.stmts[1]
        else {
            unreachable!()
        };
        args[operand] = replacement;
        assert!(compile_declarations(vec![changed, prototype(false)]).is_err());
    }
}

#[test]
fn replicated_arrays_keep_their_erased_type_and_default_value_slots_distinct() {
    for getter in ["Array.get!Internal", "Array.get!InternalBorrowed"] {
        let declaration = || {
            entry(
                vec![
                    num(1, 3),
                    num(2, 19),
                    bind(
                        3,
                        IrExpr::Fap {
                            function: name("Array.replicate"),
                            args: vec![IrArg::Erased, var(1), var(2)],
                        },
                    ),
                    num(4, 1),
                    num(5, 42),
                    bind(
                        6,
                        IrExpr::Fap {
                            function: name("Array.set!"),
                            args: vec![IrArg::Erased, var(3), var(4), var(5)],
                        },
                    ),
                    num(7, 0),
                    bind(
                        8,
                        IrExpr::Fap {
                            function: name(getter),
                            args: vec![IrArg::Erased, var(7), var(6), var(4)],
                        },
                    ),
                ],
                8,
            )
        };
        let compiled = compile_declarations(vec![declaration()]).unwrap();
        assert_nat(&compiled, "42");
        for target in ["Array.replicate", "Array.set!", getter] {
            assert!(
                compiled
                    .native_externs()
                    .iter()
                    .any(|row| row == &format!("extern:{target}"))
            );
        }
        for statement in [2, 5, 7] {
            let mut mutated = declaration();
            let IrDecl::Function { body, .. } = &mut mutated else {
                unreachable!()
            };
            let IrStmt::VDecl {
                expr: IrExpr::Fap { args, .. },
                ..
            } = &mut body.stmts[statement]
            else {
                unreachable!()
            };
            args[0] = var(1);
            assert!(compile_declarations(vec![mutated]).is_err());
        }
    }
}

#[test]
fn void_token_type_erasure_keeps_its_generated_signature_and_real_native_call() {
    let producer = || {
        entry(
            vec![
                num(1, 7),
                IrStmt::VDecl {
                    x: 2,
                    ty: IrType::Void,
                    expr: IrExpr::Fap {
                        function: name("Void.mk"),
                        args: vec![IrArg::Erased, var(1)],
                    },
                },
            ],
            2,
        )
    };
    assert_nat(&compile_declarations(vec![producer()]).unwrap(), "0");
    let declaration = IrDecl::Extern {
        name: name("Void.mk"),
        params: vec![
            IrParam {
                x: 1,
                borrow: false,
                ty: IrType::Erased,
            },
            IrParam {
                x: 2,
                borrow: false,
                ty: IrType::TObject,
            },
        ],
        result: IrType::Void,
        entries: vec![],
    };
    assert_nat(
        &compile_declarations(vec![producer(), declaration.clone()]).unwrap(),
        "0",
    );
    for mutation in 0..4 {
        let mut changed = declaration.clone();
        let IrDecl::Extern { params, result, .. } = &mut changed else {
            unreachable!()
        };
        match mutation {
            0 => params[0].ty = IrType::TObject,
            1 => params[1].borrow = true,
            2 => params[1].ty = IrType::Void,
            3 => *result = IrType::TObject,
            _ => unreachable!(),
        }
        assert!(matches!(
            compile_declarations(vec![producer(), changed]),
            Err(IrExecutionError::NativeContract { .. })
        ));
    }
    let mut bad = producer();
    let IrDecl::Function { body, .. } = &mut bad else {
        unreachable!()
    };
    let IrStmt::VDecl {
        expr: IrExpr::Fap { args, .. },
        ..
    } = &mut body.stmts[1]
    else {
        unreachable!()
    };
    args[0] = var(1);
    assert!(compile_declarations(vec![bad]).is_err());
}

#[test]
fn a_forged_native_body_cannot_replace_its_published_runtime_signature() {
    let mut forged = entry(vec![num(1, 999)], 1);
    let IrDecl::Function { name: target, .. } = &mut forged else {
        unreachable!();
    };
    *target = name("Array.push");
    let compiled = compile_declarations(vec![array_entry(), forged]).unwrap();
    assert_nat(&compiled, "1");
}

#[test]
fn imported_thunk_calls_accept_erased_types_and_boxed_partial_applications() {
    for boxed in [false, true] {
        let mut statements = vec![num(1, 42)];
        for (target, input, output) in [("Thunk.pure", 1, 3), ("Thunk.get", 3, 5)] {
            if boxed {
                statements.push(bind(
                    output - 1,
                    IrExpr::Pap {
                        function: Name::str(name(target), "_boxed"),
                        args: vec![IrArg::Erased],
                    },
                ));
                statements.push(bind(
                    output,
                    IrExpr::Ap {
                        x: output - 1,
                        args: vec![var(input)],
                    },
                ));
            } else {
                statements.push(bind(
                    output,
                    IrExpr::Fap {
                        function: name(target),
                        args: vec![IrArg::Erased, var(input)],
                    },
                ));
            }
        }
        let compiled = compile_declarations(vec![entry(statements, 5)]).unwrap();
        assert_nat(&compiled, "42");
        assert_eq!(
            compiled.native_externs(),
            ["extern:Thunk.get", "extern:Thunk.pure"],
            "boxed wrappers retain the same native primitives"
        );
    }
}

#[test]
fn imported_thunk_creation_stays_lazy_and_boxed_forcing_caches_once() {
    let body = IrDecl::Function {
        name: name("Arity.force"),
        params: (1..=2)
            .map(|x| IrParam {
                x,
                borrow: false,
                ty: IrType::TObject,
            })
            .collect(),
        result: IrType::TObject,
        body: IrBody {
            stmts: vec![
                call(3, "ST.Prim.Ref.get", &[1]),
                num(4, 1),
                call(5, "Nat.add", &[3, 4]),
                call(6, "ST.Prim.Ref.set", &[1, 5]),
            ],
            terminal: Box::new(IrTerminal::Ret(var(5))),
        },
        sorry_dep: None,
    };
    for boxed in [false, true] {
        let mut statements = vec![
            num(1, 0),
            call(2, "ST.Prim.mkRef", &[1]),
            bind(
                3,
                IrExpr::Pap {
                    function: name("Arity.force"),
                    args: vec![var(2)],
                },
            ),
        ];
        if boxed {
            statements.extend([
                bind(
                    4,
                    IrExpr::Pap {
                        function: name("Thunk.mk._boxed"),
                        args: vec![IrArg::Erased],
                    },
                ),
                bind(
                    5,
                    IrExpr::Ap {
                        x: 4,
                        args: vec![var(3)],
                    },
                ),
            ]);
        } else {
            statements.push(bind(
                5,
                IrExpr::Fap {
                    function: name("Thunk.mk"),
                    args: vec![IrArg::Erased, var(3)],
                },
            ));
        }
        statements.extend([
            call(6, "ST.Prim.Ref.get", &[2]),
            bind(
                7,
                IrExpr::Pap {
                    function: name("Thunk.get._boxed"),
                    args: vec![IrArg::Erased],
                },
            ),
            bind(
                8,
                IrExpr::Ap {
                    x: 7,
                    args: vec![var(5)],
                },
            ),
            bind(
                9,
                IrExpr::Ap {
                    x: 7,
                    args: vec![var(5)],
                },
            ),
            call(10, "ST.Prim.Ref.get", &[2]),
            num(11, 10),
            call(12, "Nat.mul", &[6, 11]),
            call(13, "Nat.add", &[12, 8]),
            call(14, "Nat.mul", &[13, 11]),
            call(15, "Nat.add", &[14, 9]),
            call(16, "Nat.mul", &[15, 11]),
            call(17, "Nat.add", &[16, 10]),
        ]);
        let compiled = compile(
            &[IrModule {
                decls: vec![entry(statements, 17), body.clone()],
                ..IrModule::default()
            }],
            &name("Arity.main"),
            &[],
            &VerifiedPartition::user_fixture(),
            &BTreeSet::from([name("Arity.main"), name("Arity.force")]),
            IrExecutionLimits::default(),
        )
        .unwrap();
        // Digits encode the captured cell before forcing, first and second
        // results, and the cell afterwards. Eager construction gives 1111;
        // repeated execution gives 122. Only lazy, cached forcing gives 111.
        arrays_reference::assert_nat_replay(&compiled, "111");
        assert_eq!(compiled.reference_functions().len(), 2);
        assert!(
            compiled
                .reference_functions()
                .iter()
                .all(|function| function.producer() == "reference")
        );
    }
}

#[test]
fn thunk_native_and_boxed_telescopes_remain_bound_to_the_generated_contract() {
    for (target, parameter, result, borrowed) in [
        ("Thunk.pure", IrType::TObject, IrType::Object, false),
        ("Thunk.mk", IrType::TObject, IrType::Object, false),
        ("Thunk.get", IrType::Object, IrType::TObject, true),
    ] {
        let row = crate::imported_ir::native_row(&name(target)).unwrap();
        let bridge = BoxedNative::from_row(row).unwrap().unwrap();
        assert_eq!(bridge.arity(), 2);
        assert_eq!(bridge.runtime_parameters(), 1..2);
        let params = vec![
            IrParam {
                x: 0,
                ty: IrType::Erased,
                borrow: false,
            },
            IrParam {
                x: 1,
                ty: parameter,
                borrow: borrowed,
            },
        ];
        validate_extern_signature(row, &params, &result).unwrap();
        let boxed = IrDecl::Extern {
            name: Name::str(name(target), "_boxed"),
            params: vec![
                IrParam {
                    x: 0,
                    ty: IrType::TObject,
                    borrow: false,
                },
                IrParam {
                    borrow: false,
                    ..params[1].clone()
                },
            ],
            result: result.clone(),
            entries: vec![],
        };
        bridge.validate_declaration(&boxed).unwrap();
        for index in 0..params.len() {
            let mut wrong = params.clone();
            wrong[index].borrow = !wrong[index].borrow;
            assert!(matches!(
                validate_extern_signature(row, &wrong, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
            wrong = params.clone();
            wrong[index].ty = IrType::UInt64;
            assert!(matches!(
                validate_extern_signature(row, &wrong, &result),
                Err(IrExecutionError::NativeContract { .. })
            ));
        }
        for changed in [
            GeneratedExternRow {
                symbol: "foreign_thunk",
                ..*row
            },
            GeneratedExternRow { arity: 1, ..*row },
            GeneratedExternRow { levels: 0, ..*row },
            GeneratedExternRow {
                effect: "task",
                ..*row
            },
            GeneratedExternRow {
                ownership: "rule(borrowed-args,owned-result)",
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
fn thunk_erasure_cannot_hide_runtime_operands_or_rebind_native_wrappers() {
    let produce = |type_arg| {
        entry(
            vec![
                num(1, 42),
                bind(
                    2,
                    IrExpr::Fap {
                        function: name("Thunk.pure"),
                        args: vec![type_arg, var(1)],
                    },
                ),
                call(3, "Thunk.get", &[2]),
            ],
            3,
        )
    };
    for type_arg in [var(1), var(999)] {
        assert!(matches!(
            compile_declarations(vec![produce(type_arg)]),
            Err(IrExecutionError::Unsupported { .. })
        ));
    }
    let mut forged = entry(vec![num(1, 999)], 1);
    let IrDecl::Function {
        name: target,
        params,
        result,
        ..
    } = &mut forged
    else {
        unreachable!()
    };
    *target = name("Thunk.pure._boxed");
    *params = (2..=3)
        .map(|x| IrParam {
            x,
            ty: IrType::TObject,
            borrow: false,
        })
        .collect();
    *result = IrType::Object;
    let caller = entry(
        vec![
            num(1, 42),
            bind(
                2,
                IrExpr::Fap {
                    function: name("Thunk.pure._boxed"),
                    args: vec![IrArg::Erased, var(1)],
                },
            ),
            call(3, "Thunk.get", &[2]),
        ],
        3,
    );
    assert_nat(
        &compile_declarations(vec![caller.clone(), forged.clone()]).unwrap(),
        "42",
    );
    assert!(matches!(compile(
        &[IrModule { decls: vec![caller, forged], ..IrModule::default() }],
        &name("Arity.main"),
        &[],
        &VerifiedPartition::user_fixture(),
        &BTreeSet::from([name("Arity.main"), name("Thunk.pure._boxed")]),
        IrExecutionLimits::default(),
    ), Err(IrExecutionError::UserOverridesCensus(found)) if found == name("Thunk.pure._boxed")));
}

#[test]
fn live_pinned_thunk_ir_preserves_native_prototypes_laziness_and_boxed_calls() {
    use crate::imported_ir::EntryArgument;
    use fln_core::diag::ResourceReason;
    use fln_core::outcome::InconclusiveCause;
    use std::path::PathBuf;
    use std::process::Command;

    let reference = std::env::var_os("FLN_REFERENCE_LEAN")
        .map(PathBuf::from)
        .or_else(|| {
            let library = PathBuf::from(std::env::var_os("FLN_REFERENCE_LIB")?);
            Some(library.parent()?.parent()?.join("bin/lean"))
        });
    let Some(reference) = reference else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for imported Thunk execution"
        );
        eprintln!("SKIP: imported Thunk execution requires FLN_REFERENCE_LEAN");
        return;
    };
    let pin = include_str!("../../../../../SUITE.lock")
        .lines()
        .find(|line| line.starts_with("reference "))
        .and_then(|line| {
            line.split_whitespace()
                .find_map(|part| part.strip_prefix("commit="))
        })
        .expect("SUITE.lock Reference commit");
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(String::from_utf8(version.stdout).unwrap().trim(), pin);
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let stamp = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let directory = root.join(format!("thunk-reference-{}-{stamp}", std::process::id()));
    std::fs::create_dir_all(&directory).unwrap();
    let source = include_str!("../../../../fln-olean/fixtures/ir/NativeThunkModule.lean");
    std::fs::write(directory.join("NativeThunkModule.lean"), source).unwrap();
    let generated = Command::new(&reference)
        .current_dir(&directory)
        .args([
            "-j1",
            "-o",
            "NativeThunkModule.olean",
            "NativeThunkModule.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(directory.join("compile.stdout"), &generated.stdout).unwrap();
    std::fs::write(directory.join("compile.stderr"), &generated.stderr).unwrap();
    assert!(
        generated.status.success(),
        "{directory:?}: {}{}",
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr)
    );
    let module = crate::decode_ir_artifact(
        &std::fs::read(directory.join("NativeThunkModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    std::fs::write(directory.join("decoded-ir.txt"), format!("{module:#?}")).unwrap();
    let users: BTreeSet<_> = module
        .decls
        .iter()
        .filter(|declaration| matches!(declaration, IrDecl::Function { .. }))
        .map(|declaration| declaration.name().clone())
        .collect();
    let partials: BTreeSet<_> = module
        .decls
        .iter()
        .flat_map(|declaration| match declaration {
            IrDecl::Function { body, .. } => body.bodies(),
            IrDecl::Extern { .. } => Vec::new(),
        })
        .flat_map(|body| &body.stmts)
        .filter_map(|statement| match statement {
            IrStmt::VDecl {
                expr: IrExpr::Pap { function, .. },
                ..
            } => Some(function.clone()),
            _ => None,
        })
        .collect();
    for target in ["Thunk.pure._boxed", "Thunk.get._boxed"] {
        assert!(partials.contains(&name(target)), "{target} optimized away");
    }

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
    let core = crate::decode_ir_artifact(
        &std::fs::read(library.join("Init/Core.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap();
    let targets = ["Thunk.pure", "Thunk.mk", "Thunk.get"].map(name);
    let prototypes = IrModule {
        decls: core
            .decls
            .into_iter()
            .filter(|declaration| {
                targets.iter().any(|target| {
                    declaration.name() == target
                        || *declaration.name() == Name::str(target.clone(), "_boxed")
                })
            })
            .collect(),
        ..IrModule::default()
    };
    for target in &targets {
        assert!(
            prototypes
                .decls
                .iter()
                .any(|declaration| declaration.name() == target)
        );
        assert!(!users.contains(target));
    }
    let cases: Vec<_> = [
        "thunkDirect",
        "thunkConstructor",
        "thunkPure",
        "thunkGet",
        "thunkCaptured",
    ]
    .into_iter()
    .flat_map(|target| {
        [0, 42, u64::MAX]
            .into_iter()
            .map(move |value| (target, value))
    })
    .chain(std::iter::once(("thunkLazy", 0)))
    .collect();
    let mut oracle_source = source.to_owned();
    for (target, value) in &cases {
        oracle_source.push_str(&format!("\n#eval {target} {value}\n"));
    }
    std::fs::write(directory.join("Oracle.lean"), oracle_source).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&directory)
        .args(["-j1", "Oracle.lean"])
        .output()
        .unwrap();
    std::fs::write(directory.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(directory.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(
        oracle.status.success(),
        "{directory:?}: {}{}",
        String::from_utf8_lossy(&oracle.stdout),
        String::from_utf8_lossy(&oracle.stderr)
    );
    let output = String::from_utf8(oracle.stdout).unwrap();
    let expected: Vec<_> = output.lines().collect();
    assert_eq!(expected.len(), cases.len(), "{output}");
    for ((target, value), expected) in cases.into_iter().zip(expected) {
        for include_prototypes in [false, true] {
            let modules = if include_prototypes {
                vec![module.clone(), prototypes.clone()]
            } else {
                vec![module.clone()]
            };
            let compiled = compile(
                &modules,
                &name(target),
                &[EntryArgument::Nat(IrNat::Small(value))],
                &VerifiedPartition::user_fixture(),
                &users,
                IrExecutionLimits::default(),
            )
            .unwrap_or_else(|error| {
                panic!("{target} {value}, prototypes={include_prototypes}: {error}; {directory:?}")
            });
            let constructor = if matches!(target, "thunkDirect" | "thunkPure") {
                "extern:Thunk.pure"
            } else {
                "extern:Thunk.mk"
            };
            for native in [constructor, "extern:Thunk.get"] {
                assert!(
                    compiled.native_externs().iter().any(|row| row == native),
                    "{target} no longer exercises {native}"
                );
            }
            arrays_reference::assert_nat_replay(&compiled, expected);
            assert!(
                compiled
                    .reference_functions()
                    .iter()
                    .all(|function| users.contains(&function.name))
            );
        }
    }
    let divergent = compile(
        &[module, prototypes],
        &name("thunkLazy"),
        &[EntryArgument::Nat(IrNat::Small(1))],
        &VerifiedPartition::user_fixture(),
        &users,
        IrExecutionLimits::default(),
    )
    .unwrap();
    // Selecting the other branch forces the same diverging callback. It
    // must stop under the VM budget; the unforced branch above returns 0.
    let stopped = divergent.execute(
        ExecutionLimits {
            max_steps: 1_000,
            ..ExecutionLimits::default()
        },
        None,
    );
    let Outcome::Inconclusive(inconclusive) = stopped.outcome else {
        panic!("forcing the diverging thunk did not exhaust its budget");
    };
    let InconclusiveCause::ResourceExhausted { usage } = &inconclusive.cause else {
        panic!("forcing the diverging thunk refused without running: {inconclusive:?}");
    };
    assert_eq!(usage.reason, ResourceReason::ExecutionSteps);
    assert_eq!(usage.allowed, 1_000);
    assert!(usage.observed > usage.allowed);
    eprintln!("Thunk Reference differential retained in {directory:?}");
}
