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
                call(5, "Array.size", &[4]),
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
    for id in ["extern:Array.mkEmpty", "extern:Array.push"] {
        let row = fln_vm::extern_table_generated::EXTERN_ROWS
            .iter()
            .find(|row| row.id == id)
            .unwrap();
        assert!(array_runtime_arity(row).unwrap().is_some());
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
            assert!(array_runtime_arity(&changed).is_err());
        }
    }
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
