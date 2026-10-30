use super::super::{CompiledIr, EntryArgument, VerifiedPartition, compile};
use super::*;
use fln_comp::flbc;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir::{IrLit, IrNat, IrParam};
use fln_olean::ir_archive::CensusPartition;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, nat_decimal};

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn body(stmts: Vec<IrStmt>, terminal: IrTerminal) -> IrBody {
    IrBody {
        stmts,
        terminal: Box::new(terminal),
    }
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

fn num(x: u64, n: u64) -> IrStmt {
    bind(x, IrExpr::Lit(IrLit::Num(IrNat::Small(n))))
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

fn info(tag: u64, fields: u64) -> IrCtorInfo {
    IrCtorInfo {
        name: name("Updates.Node"),
        cidx: tag,
        size: fields,
        usize: 0,
        ssize: 0,
    }
}

fn function(text: &str, params: &[u64], value: IrBody) -> IrDecl {
    IrDecl::Function {
        name: name(text),
        params: params
            .iter()
            .map(|x| IrParam {
                x: *x,
                borrow: true,
                ty: IrType::TObject,
            })
            .collect(),
        result: IrType::TObject,
        body: value,
        sorry_dep: None,
    }
}

fn update_region() -> IrBody {
    body(
        vec![
            bind(3, IrExpr::Proj { i: 1, x: 1 }),
            IrStmt::VDecl {
                x: 4,
                ty: IrType::UInt8,
                expr: IrExpr::IsShared { x: 1 },
            },
        ],
        IrTerminal::Case {
            type_name: name("Bool"),
            x: 4,
            x_type: IrType::UInt8,
            alts: vec![
                IrAlt::Ctor {
                    info: info(0, 0),
                    body: body(
                        vec![IrStmt::Set {
                            x: 1,
                            i: 0,
                            y: var(2),
                        }],
                        IrTerminal::Ret(var(1)),
                    ),
                },
                IrAlt::Ctor {
                    info: info(1, 0),
                    body: body(
                        vec![bind(
                            5,
                            IrExpr::Ctor {
                                info: info(1, 2),
                                args: vec![var(2), var(3)],
                            },
                        )],
                        IrTerminal::Ret(var(5)),
                    ),
                },
            ],
        },
    )
}

fn update(region: IrBody) -> IrDecl {
    function(
        "Updates.replaceHead",
        &[1, 2],
        body(
            vec![],
            IrTerminal::Case {
                type_name: name("Updates.Node"),
                x: 1,
                x_type: IrType::TObject,
                alts: vec![IrAlt::Ctor {
                    info: info(1, 2),
                    body: region,
                }],
            },
        ),
    )
}

fn entry(return_record: bool) -> IrDecl {
    let mut stmts = vec![
        num(1, 19),
        num(2, 23),
        bind(
            3,
            IrExpr::Ctor {
                info: info(1, 2),
                args: vec![var(1), var(2)],
            },
        ),
        num(4, 42),
        call(5, "Updates.replaceHead", &[3, 4]),
    ];
    if return_record {
        return function("Updates.main", &[], body(stmts, IrTerminal::Ret(var(5))));
    }
    stmts.extend([
        bind(6, IrExpr::Proj { i: 0, x: 5 }),
        bind(7, IrExpr::Proj { i: 0, x: 3 }),
        call(8, "Nat.add", &[6, 7]),
        bind(9, IrExpr::Proj { i: 1, x: 5 }),
        call(10, "Nat.add", &[8, 9]),
        num(11, 7),
        call(12, "Updates.replaceHead", &[3, 11]),
        bind(13, IrExpr::Proj { i: 0, x: 12 }),
        call(14, "Nat.add", &[10, 13]),
    ]);
    function("Updates.main", &[], body(stmts, IrTerminal::Ret(var(14))))
}

fn compile_fixture(
    region: IrBody,
    return_record: bool,
    limits: IrExecutionLimits,
) -> Result<CompiledIr> {
    let module = IrModule {
        decls: vec![update(region), entry(return_record)],
        ..IrModule::default()
    };
    let users = BTreeSet::from([name("Updates.replaceHead"), name("Updates.main")]);
    let partition = VerifiedPartition {
        partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default())
            .unwrap(),
    };
    compile(
        &[module],
        &name("Updates.main"),
        &[],
        &partition,
        &users,
        limits,
    )
}

fn assert_nat_and_replay(compiled: &CompiledIr, expected: &str) {
    let bytes =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    for program in [compiled.program.program(), &replay] {
        let outcome = execute(program, ExecutionLimits::default(), None);
        let Outcome::Complete(VmExit::Returned(value)) = outcome else {
            panic!("{outcome:?}");
        };
        assert_eq!(nat_decimal(&value.value).as_deref(), Some(expected));
    }
    assert!(
        compiled
            .reference_functions()
            .iter()
            .all(|f| f.producer() == "reference")
    );
}

fn alternatives(region: &mut IrBody) -> &mut Vec<IrAlt> {
    let IrTerminal::Case { alts, .. } = region.terminal.as_mut() else {
        panic!("case fixture");
    };
    alts
}

fn branch(region: &mut IrBody, index: usize) -> &mut IrBody {
    let IrAlt::Ctor { body, .. } = &mut alternatives(region)[index] else {
        panic!("constructor fixture");
    };
    body
}

#[test]
fn updates_allocate_fresh_and_preserve_both_old_and_new_shared_values() {
    for reverse in [false, true] {
        let mut region = update_region();
        if reverse {
            alternatives(&mut region).reverse();
        }
        let compiled = compile_fixture(region, false, IrExecutionLimits::default()).unwrap();
        // Updated head 42 + unchanged original head 19 + preserved tail 23 +
        // the head from a second update of the same original input, 7.
        assert_nat_and_replay(&compiled, "91");
        assert_eq!(compiled.reference_functions().len(), 2);
    }
}

#[test]
fn retagged_update_preserves_the_verified_new_header_and_object_fields() {
    let mut region = update_region();
    branch(&mut region, 0)
        .stmts
        .insert(0, IrStmt::SetTag { x: 1, cidx: 2 });
    let IrStmt::VDecl {
        expr: IrExpr::Ctor { info, .. },
        ..
    } = &mut branch(&mut region, 1).stmts[0]
    else {
        panic!("constructor");
    };
    info.cidx = 2;
    let compiled = compile_fixture(region, true, IrExecutionLimits::default()).unwrap();
    let outcome = compiled.execute(ExecutionLimits::default(), None).outcome;
    let Outcome::Complete(VmExit::Returned(value)) = outcome else {
        panic!("{outcome:?}");
    };
    assert_eq!(value.value.header().tag, 2);
    assert_eq!(
        nat_decimal(&value.value.ctor_child(0)).as_deref(),
        Some("42")
    );
    assert_eq!(
        nat_decimal(&value.value.ctor_child(1)).as_deref(),
        Some("23")
    );
}

#[test]
fn tail_join_continuations_receive_the_same_fresh_value_without_capturing_the_receiver() {
    let mut region = update_region();
    region.stmts.insert(
        0,
        IrStmt::JDecl {
            j: 10,
            params: vec![IrParam {
                x: 11,
                borrow: true,
                ty: IrType::TObject,
            }],
            value: body(vec![], IrTerminal::Ret(var(11))),
        },
    );
    branch(&mut region, 0).terminal = Box::new(IrTerminal::Jmp {
        j: 10,
        args: vec![var(1)],
    });
    branch(&mut region, 1).terminal = Box::new(IrTerminal::Jmp {
        j: 10,
        args: vec![var(5)],
    });
    let compiled = compile_fixture(region, false, IrExecutionLimits::default()).unwrap();
    assert_nat_and_replay(&compiled, "91");
}

#[test]
fn branch_mismatches_and_observable_sharing_are_never_specialized() {
    for mutation in 0..8 {
        let mut region = update_region();
        match mutation {
            0 => {
                let IrStmt::VDecl {
                    expr: IrExpr::Ctor { args, .. },
                    ..
                } = &mut branch(&mut region, 1).stmts[0]
                else {
                    panic!("constructor");
                };
                args[1] = var(2); // An unchanged field is not its original projection.
            }
            1 => branch(&mut region, 0).stmts.push(IrStmt::Set {
                x: 1,
                i: 0,
                y: var(2),
            }),
            2 => branch(&mut region, 0)
                .stmts
                .push(IrStmt::SetTag { x: 1, cidx: 3 }),
            3 => branch(&mut region, 0)
                .stmts
                .insert(0, call(6, "Nat.add", &[2, 3])),
            4 => branch(&mut region, 0).terminal = Box::new(IrTerminal::Ret(var(4))),
            5 => {
                branch(&mut region, 0).stmts[0] = IrStmt::Set {
                    x: 1,
                    i: 2,
                    y: var(2),
                };
            }
            6 => {
                branch(&mut region, 0).stmts[0] = IrStmt::Set {
                    x: 1,
                    i: 0,
                    y: var(1),
                };
                let IrStmt::VDecl {
                    expr: IrExpr::Ctor { args, .. },
                    ..
                } = &mut branch(&mut region, 1).stmts[0]
                else {
                    panic!("constructor");
                };
                // A self-reference is not a fresh object's reference to its input.
                args[0] = var(1);
            }
            _ => {
                region.stmts[0] = bind(3, IrExpr::Proj { i: 0, x: 1 });
            }
        }
        let error = compile_fixture(region, false, IrExecutionLimits::default()).unwrap_err();
        assert!(!error.is_resource(), "{error:?}");
        assert!(
            matches!(
                error,
                IrExecutionError::Unsupported { .. } | IrExecutionError::IrValidation(_)
            ),
            "{error:?}"
        );
    }
    assert_nat_and_replay(
        &compile_fixture(update_region(), false, IrExecutionLimits::default()).unwrap(),
        "91",
    );
}

#[test]
fn join_capture_of_the_original_object_prevents_branch_elimination() {
    let mut region = update_region();
    region.stmts.insert(
        0,
        IrStmt::JDecl {
            j: 10,
            params: vec![IrParam {
                x: 11,
                borrow: true,
                ty: IrType::TObject,
            }],
            value: body(
                vec![bind(12, IrExpr::Proj { i: 0, x: 1 })],
                IrTerminal::Ret(var(12)),
            ),
        },
    );
    branch(&mut region, 0).terminal = Box::new(IrTerminal::Jmp {
        j: 10,
        args: vec![var(1)],
    });
    branch(&mut region, 1).terminal = Box::new(IrTerminal::Jmp {
        j: 10,
        args: vec![var(5)],
    });
    assert!(matches!(
        compile_fixture(region, true, IrExecutionLimits::default()),
        Err(IrExecutionError::Unsupported { .. })
    ));
}

#[test]
fn original_ir_types_are_checked_before_discarding_an_allocation_branch() {
    let mut region = update_region();
    let IrStmt::VDecl { ty, .. } = region.stmts.last_mut().unwrap() else {
        panic!("flag");
    };
    *ty = IrType::UInt16;
    assert!(matches!(
        compile_fixture(region, false, IrExecutionLimits::default()),
        Err(IrExecutionError::IrValidation(_))
    ));
}

#[test]
fn update_normalization_is_bounded_and_a_refusal_does_not_mutate_the_inputs() {
    let input = IrModule {
        decls: vec![update(update_region()), entry(false)],
        ..IrModule::default()
    };
    let mut copy = input.clone();
    let mut limits = IrExecutionLimits::default();
    limits.ir.max_work = 0;
    let error = normalize(&mut copy, limits).unwrap_err();
    assert!(error.is_resource());
    assert_eq!(copy, input);
    assert!(normalize(&mut copy, IrExecutionLimits::default()).unwrap());
    for declaration in &copy.decls {
        if let IrDecl::Function { body, .. } = declaration {
            for body in body.bodies() {
                assert!(body.stmts.iter().all(|stmt| !matches!(
                    stmt,
                    IrStmt::Set { .. }
                        | IrStmt::SetTag { .. }
                        | IrStmt::VDecl {
                            expr: IrExpr::IsShared { .. },
                            ..
                        }
                )));
            }
        }
    }
    let first = copy.clone();
    assert!(!normalize(&mut copy, IrExecutionLimits::default()).unwrap());
    assert_eq!(copy, first, "normalization is deterministic and idempotent");
    assert_nat_and_replay(
        &compile_fixture(update_region(), false, IrExecutionLimits::default()).unwrap(),
        "91",
    );
}

#[test]
fn unknown_input_shapes_do_not_authorize_object_mutation() {
    let partition = VerifiedPartition {
        partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default())
            .unwrap(),
    };
    let input = IrModule {
        decls: vec![function("Updates.unknown", &[1, 2], update_region())],
        ..IrModule::default()
    };
    let error = compile(
        &[input],
        &name("Updates.unknown"),
        &[
            EntryArgument::Nat(IrNat::Small(0)),
            EntryArgument::Nat(IrNat::Small(1)),
        ],
        &partition,
        &BTreeSet::from([name("Updates.unknown")]),
        IrExecutionLimits::default(),
    )
    .unwrap_err();
    assert!(matches!(error, IrExecutionError::Unsupported { .. }));
}

mod fresh_initialization;
