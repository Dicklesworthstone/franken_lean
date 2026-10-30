use super::*;
use crate::imported_ir::{
    CompiledIr, EntryArgument, IrExecutionError, IrExecutionLimits, Native, VerifiedPartition,
    compile, compile_with_captured_output, native_row, native_signature,
};
use fln_comp::flbc;
use fln_core::name::Name;
use fln_core::outcome::InconclusiveCause;
use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir::{
    IrArg, IrBody, IrDecl, IrExpr, IrLit, IrModule, IrNat, IrParam, IrStmt, IrTerminal, IrType,
};
use fln_olean::ir_archive::CensusPartition;
use fln_rt::obj::Obj;
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{VmRefusal, nat_decimal};
use std::collections::BTreeSet;

mod reference;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn partition() -> VerifiedPartition {
    VerifiedPartition {
        partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default())
            .unwrap(),
    }
}

fn bind(x: u64, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl {
        x,
        ty: IrType::TObject,
        expr,
    }
}

fn output_module(read: bool) -> IrModule {
    let mut stmts = vec![
        bind(
            0,
            IrExpr::Fap {
                function: name("IO.getStdout"),
                args: vec![IrArg::Erased],
            },
        ),
        bind(
            1,
            IrExpr::Proj {
                i: if read { 3 } else { 4 },
                x: 0,
            },
        ),
        bind(2, IrExpr::Lit(IrLit::Str("aλ\0".to_owned()))),
        bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
        bind(
            4,
            IrExpr::Ap {
                x: 1,
                args: if read {
                    vec![IrArg::Var(3)]
                } else {
                    vec![IrArg::Var(2), IrArg::Var(3)]
                },
            },
        ),
    ];
    if !read {
        stmts.extend([
            bind(5, IrExpr::Lit(IrLit::Str("🙂\n".to_owned()))),
            bind(
                6,
                IrExpr::Ap {
                    x: 1,
                    args: vec![IrArg::Var(5), IrArg::Var(3)],
                },
            ),
            bind(7, IrExpr::Proj { i: 0, x: 6 }),
        ]);
    }
    IrModule {
        decls: vec![IrDecl::Function {
            name: name("LocalOutput.main"),
            params: vec![],
            result: IrType::TObject,
            body: IrBody {
                stmts,
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(if read { 4 } else { 7 }))),
            },
            sorry_dep: None,
        }],
        ..IrModule::default()
    }
}

fn prepare(module: &IrModule, max_bytes: usize) -> CompiledIr {
    compile_with_captured_output(
        std::slice::from_ref(module),
        &name("LocalOutput.main"),
        &[],
        &partition(),
        &BTreeSet::from([name("LocalOutput.main")]),
        IrExecutionLimits::default(),
        max_bytes,
    )
    .unwrap()
}

#[test]
fn output_capability_admits_only_the_exact_stdout_row_and_default_stays_closed() {
    let module = output_module(false);
    assert!(matches!(
        compile(
            std::slice::from_ref(&module),
            &name("LocalOutput.main"),
            &[],
            &partition(),
            &BTreeSet::from([name("LocalOutput.main")]),
            IrExecutionLimits::default(),
        ),
        Err(IrExecutionError::Unsupported {
            form: "effectful native call",
            ..
        })
    ));
    for row in EXTERN_ROWS.iter().filter(|row| row.effect != "pure") {
        let allowed = native_signature::ir_arity(row)
            .and_then(|arity| Native::with_output(row, arity, true))
            .is_ok();
        assert_eq!(
            allowed,
            matches!(
                row.id,
                "extern:IO.getStdout"
                    | "extern:ST.Prim.mkRef"
                    | "extern:ST.Prim.Ref.get"
                    | "extern:ST.Prim.Ref.set"
                    | "extern:ST.Prim.Ref.swap"
                    | "extern:ST.Prim.Ref.take"
            ),
            "{}",
            row.id
        );
    }
}

#[test]
fn stdout_world_bridge_validates_original_ir_and_refuses_data_or_getter_closures() {
    let compile = |module: &IrModule| {
        compile_with_captured_output(
            std::slice::from_ref(module),
            &name("LocalOutput.main"),
            &[],
            &partition(),
            &BTreeSet::from([name("LocalOutput.main")]),
            IrExecutionLimits::default(),
            9,
        )
    };
    let mut module = output_module(false);
    module.decls.push(IrDecl::Extern {
        name: name("IO.getStdout"),
        params: vec![IrParam {
            x: 0,
            borrow: true,
            ty: IrType::Erased,
        }],
        result: IrType::TObject,
        entries: vec![],
    });
    assert!(
        compile(&module).is_ok(),
        "explicit Reference world telescope"
    );
    let IrDecl::Extern { params, .. } = &mut module.decls[1] else {
        unreachable!()
    };
    params.clear();
    assert!(matches!(
        compile(&module),
        Err(IrExecutionError::NativeContract { .. })
    ));

    let mut module = output_module(false);
    let IrDecl::Function { body, .. } = &mut module.decls[0] else {
        unreachable!()
    };
    let IrStmt::VDecl {
        expr: IrExpr::Fap { args, .. },
        ..
    } = &mut body.stmts[0]
    else {
        unreachable!()
    };
    args.clear();
    assert!(
        matches!(compile(&module), Err(IrExecutionError::IrValidation(_))),
        "zero-argument input IR must not be mistaken for the pin's world call"
    );

    for closure in [false, true] {
        let mut module = output_module(false);
        let IrDecl::Function { body, .. } = &mut module.decls[0] else {
            unreachable!()
        };
        let IrStmt::VDecl { expr, .. } = &mut body.stmts[0] else {
            unreachable!()
        };
        *expr = if closure {
            IrExpr::Pap {
                function: name("IO.getStdout"),
                args: vec![],
            }
        } else {
            IrExpr::Fap {
                function: name("IO.getStdout"),
                args: vec![IrArg::Var(8)],
            }
        };
        body.stmts
            .insert(0, bind(8, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))));
        assert!(
            matches!(compile(&module), Err(IrExecutionError::Unsupported { form, .. })
            if form == if closure { "first-class native stdout getter" } else { "non-erased native stdout world" })
        );
    }
}

#[test]
fn captured_output_preserves_unicode_nuls_native_result_provenance_and_replay() {
    let expected = "aλ\0🙂\n".as_bytes();
    let compiled = prepare(&output_module(false), expected.len());
    assert_eq!(compiled.output_byte_limit(), Some(expected.len()));
    assert!(
        compiled
            .native_externs()
            .iter()
            .any(|row| row == "extern:IO.getStdout")
    );
    assert!(
        compiled
            .reference_functions()
            .iter()
            .all(|item| item.producer() == "reference")
    );
    let canonical =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&canonical, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        canonical
    );
    for _ in 0..2 {
        for program in [compiled.program.program(), &replay] {
            let (outcome, output) =
                execute(program, ExecutionLimits::default(), None, expected.len());
            let Outcome::Complete(VmExit::Returned(result)) = outcome else {
                panic!("{outcome:?}")
            };
            assert_eq!(
                nat_decimal(&result.value).as_deref(),
                Some("0"),
                "compiled IO.Result Unit"
            );
            assert_eq!(output.bytes, expected);
        }
    }
}

#[test]
fn void_world_parameters_require_erased_entry_values_and_cannot_be_observed() {
    let mut module = output_module(false);
    let IrDecl::Function { params, .. } = &mut module.decls[0] else {
        unreachable!()
    };
    params.push(IrParam {
        x: 9,
        borrow: true,
        ty: IrType::Void,
    });
    let prepare = |module: &IrModule, argument| {
        compile_with_captured_output(
            std::slice::from_ref(module),
            &name("LocalOutput.main"),
            &[argument],
            &partition(),
            &BTreeSet::from([name("LocalOutput.main")]),
            IrExecutionLimits::default(),
            9,
        )
    };
    let compiled = prepare(&module, EntryArgument::Erased).unwrap();
    assert!(matches!(
        compiled.execute(ExecutionLimits::default(), None).outcome,
        Outcome::Complete(VmExit::Returned(_))
    ));
    assert!(matches!(
        prepare(&module, EntryArgument::Nat(IrNat::Small(0))),
        Err(IrExecutionError::Unsupported {
            form: "non-erased entry world",
            ..
        })
    ));

    let mut observed = module.clone();
    let IrDecl::Function { body, .. } = &mut observed.decls[0] else {
        unreachable!()
    };
    body.terminal = Box::new(IrTerminal::Ret(IrArg::Var(9)));
    assert!(matches!(
        prepare(&observed, EntryArgument::Erased),
        Err(IrExecutionError::Unsupported {
            form: "access to an erased world parameter",
            ..
        })
    ));

    let IrDecl::Function { result, .. } = &mut module.decls[0] else {
        unreachable!()
    };
    *result = IrType::Void;
    assert!(matches!(
        prepare(&module, EntryArgument::Erased),
        Err(IrExecutionError::Unsupported {
            form: "packed/unboxed IR representation",
            ..
        })
    ));
}

#[test]
fn exhausted_capture_retains_only_accepted_prefix_and_retry_is_fresh() {
    let module = output_module(false);
    let report = prepare(&module, 8).execute(ExecutionLimits::default(), None);
    let Outcome::Inconclusive(stop) = report.outcome else {
        panic!("{report:?}")
    };
    assert!(
        matches!(stop.cause, InconclusiveCause::ResourceExhausted { usage }
        if usage.allowed == 8 && usage.observed == 9)
    );
    assert_eq!(report.captured_output.unwrap().bytes, "aλ\0".as_bytes());
    let report = prepare(&module, 9).execute(ExecutionLimits::default(), None);
    assert!(matches!(
        report.outcome,
        Outcome::Complete(VmExit::Returned(_))
    ));
    assert_eq!(report.captured_output.unwrap().bytes, "aλ\0🙂\n".as_bytes());
}

#[test]
fn zero_output_allowance_accepts_empty_writes_and_preserves_work_limits() {
    let mut module = output_module(false);
    let IrDecl::Function { body, .. } = &mut module.decls[0] else {
        unreachable!()
    };
    for stmt in &mut body.stmts {
        if let IrStmt::VDecl {
            expr: IrExpr::Lit(IrLit::Str(text)),
            ..
        } = stmt
        {
            text.clear();
        }
    }
    let compiled = prepare(&module, 0);
    let report = compiled.execute(ExecutionLimits::default(), None);
    assert!(matches!(
        report.outcome,
        Outcome::Complete(VmExit::Returned(_))
    ));
    assert!(report.captured_output.unwrap().bytes.is_empty());
    let limits = ExecutionLimits {
        max_steps: 0,
        ..ExecutionLimits::default()
    };
    let report = compiled.execute(limits, None);
    assert!(matches!(
        report.outcome,
        Outcome::Inconclusive(Inconclusive {
            cause: InconclusiveCause::ResourceExhausted { .. },
            ..
        })
    ));
    assert!(report.captured_output.unwrap().bytes.is_empty());
}

#[test]
fn captured_output_refuses_reads_and_cancellation_before_any_write() {
    let report = prepare(&output_module(true), 100).execute(ExecutionLimits::default(), None);
    assert!(matches!(
        report.outcome,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::NativeStdoutContract {
                reason: "captured Reference output does not authorize stream reads"
            },
            ..
        })
    ));
    assert!(report.captured_output.unwrap().bytes.is_empty());
    let report =
        prepare(&output_module(false), 100).execute(ExecutionLimits::default(), Some(&|| true));
    assert!(matches!(
        report.outcome,
        Outcome::Inconclusive(Inconclusive {
            cause: InconclusiveCause::Cancelled { .. },
            ..
        })
    ));
    assert!(report.captured_output.unwrap().bytes.is_empty());
}

#[test]
fn nested_capture_restores_outer_scope_and_cannot_hide_its_failure() {
    let outer = StdoutCapture::begin_isolated(10, true).unwrap();
    StdoutCapture::append_current("outer").unwrap();
    let report = prepare(&output_module(false), 9).execute(ExecutionLimits::default(), None);
    assert_eq!(report.captured_output.unwrap().bytes, "aλ\0🙂\n".as_bytes());
    StdoutCapture::append_current("tail").unwrap();
    assert_eq!(outer.finish().bytes, b"outertail");

    let outer = StdoutCapture::begin_isolated(1, true).unwrap();
    assert!(StdoutCapture::append_current("no").is_err());
    let report = prepare(&output_module(false), 9).execute(ExecutionLimits::default(), None);
    assert!(matches!(report.outcome, Outcome::Inconclusive(_)));
    assert!(report.captured_output.unwrap().bytes.is_empty());
    assert!(outer.finish().error.is_some());
}

#[test]
fn captured_reference_context_requires_an_installed_sink() {
    let compiled = prepare(&output_module(false), 9);
    let outcome = execute_with_context(
        compiled.program.program(),
        ExecutionLimits::default(),
        CommandExecutionContext::UNLIMITED.with_captured_reference_output(),
        None,
    );
    assert!(matches!(outcome, Outcome::InternalFault(_)));
    // The same exact callback cannot write through the safe boundary without
    // an installed sink, even when invoked outside the interpreter.
    let callback = Obj::stdio_stdout().unwrap().try_ctor_child(4).unwrap();
    assert!(
        callback
            .try_captured_stdio_put_str(&Obj::mk_string("must not escape"), &Obj::mk_nat(0))
            .is_err()
    );
}

#[test]
fn native_diagnostic_capture_failure_cannot_publish_its_continuation_result() {
    let continuation = name("LocalOutput.continue");
    let module = IrModule {
        decls: vec![
            IrDecl::Function {
                name: name("LocalOutput.main"),
                params: vec![],
                result: IrType::TObject,
                body: IrBody {
                    stmts: vec![
                        bind(0, IrExpr::Lit(IrLit::Str("λ".to_owned()))),
                        bind(
                            1,
                            IrExpr::Pap {
                                function: continuation.clone(),
                                args: vec![],
                            },
                        ),
                        bind(
                            2,
                            IrExpr::Fap {
                                function: name("dbgTrace"),
                                args: vec![IrArg::Var(0), IrArg::Var(1)],
                            },
                        ),
                    ],
                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(2))),
                },
                sorry_dep: None,
            },
            IrDecl::Function {
                name: continuation.clone(),
                params: vec![IrParam {
                    x: 0,
                    borrow: true,
                    ty: IrType::TObject,
                }],
                result: IrType::TObject,
                body: IrBody {
                    stmts: vec![bind(1, IrExpr::Lit(IrLit::Num(IrNat::Small(42))))],
                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(1))),
                },
                sorry_dep: None,
            },
            IrDecl::Extern {
                name: name("dbgTrace"),
                params: (0..2)
                    .map(|x| IrParam {
                        x,
                        borrow: false,
                        ty: IrType::TObject,
                    })
                    .collect(),
                result: IrType::TObject,
                entries: vec![],
            },
        ],
        ..IrModule::default()
    };
    for max_bytes in [2, 3] {
        let compiled = compile_with_captured_output(
            std::slice::from_ref(&module),
            &name("LocalOutput.main"),
            &[],
            &partition(),
            &BTreeSet::from([name("LocalOutput.main"), continuation.clone()]),
            IrExecutionLimits::default(),
            max_bytes,
        )
        .unwrap();
        let report = compiled.execute(ExecutionLimits::default(), None);
        if max_bytes == 2 {
            assert!(matches!(report.outcome, Outcome::Inconclusive(_)));
            assert!(report.captured_output.unwrap().bytes.is_empty());
        } else {
            let Outcome::Complete(VmExit::Returned(value)) = report.outcome else {
                panic!("{report:?}")
            };
            assert_eq!(nat_decimal(&value.value).as_deref(), Some("42"));
            assert_eq!(report.captured_output.unwrap().bytes, "λ\n".as_bytes());
        }
    }
}
