use super::*;
use crate::imported_ir::{
    CompiledCallableIr, CompiledIr, EntryArgument, VerifiedPartition, compile, compile_callable,
};
use fln_comp::flbc;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_hash::ir_graph::GraphArchiveLimits;
use fln_olean::ir::{IrLit, IrNat, IrParam};
use fln_olean::ir_archive::CensusPartition;
use fln_rt::obj::Obj;
use fln_vm::interpreter::{ExecutionLimits, VmExit, execute, execute_function, nat_decimal};

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
        name: name("Reset.Node"),
        cidx: tag,
        size: fields,
        usize: 0,
        ssize: 0,
    }
}

fn param(x: u64, ty: IrType) -> IrParam {
    IrParam {
        x,
        borrow: true,
        ty,
    }
}

fn function(text: &str, params: &[u64], value: IrBody) -> IrDecl {
    IrDecl::Function {
        name: name(text),
        params: params.iter().map(|x| param(*x, IrType::TObject)).collect(),
        result: IrType::TObject,
        body: value,
        sorry_dep: None,
    }
}

fn jump(j: u64, args: Vec<IrArg>) -> IrTerminal {
    IrTerminal::Jmp { j, args }
}

fn cases(x: u64, exclusive: IrBody, shared: IrBody) -> IrTerminal {
    IrTerminal::Case {
        type_name: name("Bool"),
        x,
        x_type: IrType::UInt8,
        alts: vec![
            IrAlt::Ctor {
                info: info(0, 0),
                body: exclusive,
            },
            IrAlt::Ctor {
                info: info(1, 0),
                body: shared,
            },
        ],
    }
}

fn region() -> IrBody {
    body(
        vec![
            bind(3, IrExpr::Proj { i: 1, x: 1 }),
            IrStmt::JDecl {
                j: 10,
                params: vec![param(11, IrType::TObject), param(12, IrType::UInt8)],
                value: body(
                    vec![
                        num(13, 1),
                        call(14, "Nat.add", &[2, 13]),
                        IrStmt::JDecl {
                            j: 20,
                            params: vec![param(21, IrType::TObject)],
                            value: body(vec![], IrTerminal::Ret(var(21))),
                        },
                    ],
                    cases(
                        12,
                        body(
                            vec![IrStmt::Set {
                                x: 11,
                                i: 0,
                                y: var(14),
                            }],
                            jump(20, vec![var(11)]),
                        ),
                        body(
                            vec![bind(
                                22,
                                IrExpr::Ctor {
                                    info: info(1, 2),
                                    args: vec![var(14), var(3)],
                                },
                            )],
                            jump(20, vec![var(22)]),
                        ),
                    ),
                ),
            },
            IrStmt::VDecl {
                x: 4,
                ty: IrType::UInt8,
                expr: IrExpr::IsShared { x: 1 },
            },
        ],
        cases(
            4,
            body(
                vec![
                    bind(5, IrExpr::Proj { i: 0, x: 1 }),
                    IrStmt::Dec {
                        x: 5,
                        n: 1,
                        checked: true,
                        persistent: false,
                    },
                ],
                jump(10, vec![var(1), var(4)]),
            ),
            body(
                vec![
                    IrStmt::Inc {
                        x: 3,
                        n: 1,
                        checked: true,
                        persistent: false,
                    },
                    IrStmt::Dec {
                        x: 1,
                        n: 1,
                        checked: true,
                        persistent: false,
                    },
                ],
                jump(10, vec![IrArg::Erased, var(4)]),
            ),
        ),
    )
}

fn update(region: IrBody) -> IrDecl {
    function(
        "Reset.update",
        &[1, 2],
        body(
            vec![],
            IrTerminal::Case {
                type_name: name("Reset.Node"),
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

fn entry() -> IrDecl {
    function(
        "Reset.main",
        &[],
        body(
            vec![
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
                call(5, "Reset.update", &[3, 4]),
                bind(6, IrExpr::Proj { i: 0, x: 5 }),
                bind(7, IrExpr::Proj { i: 1, x: 5 }),
                bind(8, IrExpr::Proj { i: 0, x: 3 }),
                num(9, 7),
                call(10, "Reset.update", &[3, 9]),
                bind(11, IrExpr::Proj { i: 0, x: 10 }),
                call(12, "Nat.add", &[6, 7]),
                call(13, "Nat.add", &[8, 11]),
                call(14, "Nat.add", &[12, 13]),
            ],
            IrTerminal::Ret(var(14)),
        ),
    )
}

fn compile_module(
    module: &IrModule,
    entry: &str,
    arguments: &[EntryArgument],
    limits: IrExecutionLimits,
) -> Result<CompiledIr> {
    let users = module
        .decls
        .iter()
        .filter_map(|d| match d {
            IrDecl::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    let partition = VerifiedPartition {
        partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default())
            .unwrap(),
    };
    compile(
        std::slice::from_ref(module),
        &name(entry),
        arguments,
        &partition,
        &users,
        limits,
    )
}

fn fixture(region: IrBody) -> IrModule {
    IrModule {
        decls: vec![update(region), entry()],
        ..IrModule::default()
    }
}

fn unshaped_fixture(region: IrBody) -> IrModule {
    IrModule {
        decls: vec![function("Reset.update", &[1, 2], region), entry()],
        ..IrModule::default()
    }
}

fn callable(module: &IrModule) -> CompiledCallableIr {
    let users = module
        .decls
        .iter()
        .filter_map(|declaration| match declaration {
            IrDecl::Function { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect();
    compile_callable(
        std::slice::from_ref(module),
        &name("Reset.update"),
        &VerifiedPartition::user_fixture(),
        &users,
        IrExecutionLimits::default(),
    )
    .unwrap()
}

fn refused_with_or_without_incoming_shape(region: IrBody, label: &str) {
    for module in [fixture(region.clone()), unshaped_fixture(region)] {
        assert!(
            compile_module(&module, "Reset.main", &[], IrExecutionLimits::default()).is_err(),
            "{label}"
        );
    }
}

fn compile_region(region: IrBody) -> Result<CompiledIr> {
    compile_module(
        &fixture(region),
        "Reset.main",
        &[],
        IrExecutionLimits::default(),
    )
}

fn assert_replay(compiled: &CompiledIr, expected: &str) {
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

fn continuation(region: &mut IrBody) -> &mut IrBody {
    let IrStmt::JDecl { value, .. } = &mut region.stmts[1] else {
        panic!("reset join");
    };
    value
}

fn arms(body: &mut IrBody) -> &mut Vec<IrAlt> {
    let IrTerminal::Case { alts, .. } = body.terminal.as_mut() else {
        panic!("case");
    };
    alts
}

fn arm(body: &mut IrBody, index: usize) -> &mut IrBody {
    match &mut arms(body)[index] {
        IrAlt::Ctor { body, .. } | IrAlt::Default { body } => body,
    }
}

#[test]
fn expanded_reset_reuse_preserves_shared_originals_and_strict_common_work() {
    for module in [fixture(region()), unshaped_fixture(region())] {
        let original = module.clone();
        let compiled =
            compile_module(&module, "Reset.main", &[], IrExecutionLimits::default()).unwrap();
        // Two updates (42+1 and 7+1), retained tail 23, unchanged original head 19.
        assert_replay(&compiled, "93");
        assert_eq!(module, original);
        assert_eq!(compiled.reference_functions().len(), 3); // main, update, reuse join
    }
}

#[test]
fn inferred_record_shape_is_checked_for_raw_calls_and_canonical_replay() {
    let compiled = callable(&unshaped_fixture(region()));
    let bytes = flbc::encode_canonical(compiled.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    let entry = compiled
        .reference_functions()
        .iter()
        .find(|function| function.name == name("Reset.update"))
        .unwrap()
        .function;
    for program in [compiled.program(), &replay] {
        assert!(
            program
                .functions()
                .iter()
                .flat_map(|f| &f.code)
                .any(|instruction| matches!(
                    instruction,
                    flbc::Instruction::CtorLayoutTest {
                        expected_tag: 1,
                        expected_fields: 2,
                        expected_scalar_bytes: 0,
                        ..
                    }
                ))
        );
        let original = Obj::mk_ctor(1, vec![Obj::mk_nat(19), Obj::mk_nat(23)], &[]);
        let outcome = execute_function(
            program,
            entry,
            vec![original.clone_ref(), Obj::mk_nat(42)],
            ExecutionLimits::default(),
            None,
        );
        let Outcome::Complete(VmExit::Returned(result)) = outcome else {
            panic!("{outcome:?}")
        };
        assert_eq!(
            nat_decimal(&result.value.ctor_child(0)).as_deref(),
            Some("43")
        );
        assert_eq!(
            nat_decimal(&result.value.ctor_child(1)).as_deref(),
            Some("23")
        );
        assert_eq!(nat_decimal(&original.ctor_child(0)).as_deref(), Some("19"));
        for malformed in [
            Obj::mk_ctor(2, vec![Obj::mk_nat(19), Obj::mk_nat(23)], &[]),
            Obj::mk_ctor(
                1,
                vec![Obj::mk_nat(19), Obj::mk_nat(23), Obj::mk_nat(0)],
                &[],
            ),
            Obj::mk_ctor(1, vec![Obj::mk_nat(19), Obj::mk_nat(23)], &[0]),
            Obj::mk_ctor(1, vec![Obj::mk_nat(19), Obj::mk_nat(23)], &[0; 16]),
        ] {
            let outcome = execute_function(
                program,
                entry,
                vec![malformed, Obj::mk_nat(42)],
                ExecutionLimits::default(),
                None,
            );
            assert!(
                matches!(outcome, Outcome::Complete(VmExit::Panicked { .. })),
                "{outcome:?}"
            );
        }
    }
}

#[test]
fn inferred_guard_preserves_the_original_strict_effect_checkpoint() {
    use fln_rt::obj::StdoutCapture;
    let mut region = region();
    continuation(&mut region).stmts.splice(
        2..2,
        [
            bind(50, IrExpr::Lit(IrLit::Str("after guard".into()))),
            bind(
                51,
                IrExpr::Pap {
                    function: name("Reset.traceCont"),
                    args: vec![],
                },
            ),
            call(52, "dbgTrace", &[50, 51]),
        ],
    );
    region.stmts.splice(
        1..1,
        [
            bind(40, IrExpr::Lit(IrLit::Str("before guard".into()))),
            bind(
                41,
                IrExpr::Pap {
                    function: name("Reset.traceCont"),
                    args: vec![],
                },
            ),
            call(42, "dbgTrace", &[40, 41]),
        ],
    );
    let mut module = unshaped_fixture(region);
    module.decls.push(function(
        "Reset.traceCont",
        &[1],
        body(vec![num(2, 0)], IrTerminal::Ret(var(2))),
    ));
    module.decls.push(IrDecl::Extern {
        name: name("dbgTrace"),
        params: vec![param(1, IrType::TObject), param(2, IrType::TObject)],
        result: IrType::TObject,
        entries: vec![],
    });
    let compiled = callable(&module);
    let bytes = flbc::encode_canonical(compiled.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    let entry = compiled
        .reference_functions()
        .iter()
        .find(|f| f.name == name("Reset.update"))
        .unwrap()
        .function;
    for program in [compiled.program(), &replay] {
        for (tag, expected) in [(1, "before guard\nafter guard\n"), (2, "before guard\n")] {
            let capture = StdoutCapture::begin_evaluation(1024).unwrap();
            let outcome = execute_function(
                program,
                entry,
                vec![
                    Obj::mk_ctor(tag, vec![Obj::mk_nat(19), Obj::mk_nat(23)], &[]),
                    Obj::mk_nat(42),
                ],
                ExecutionLimits::default(),
                None,
            );
            let captured = capture.finish();
            assert_eq!(captured.error, None);
            assert_eq!(captured.bytes, expected.as_bytes());
            if tag == 1 {
                assert!(
                    matches!(outcome, Outcome::Complete(VmExit::Returned(_))),
                    "{outcome:?}"
                );
            } else {
                assert!(
                    matches!(outcome, Outcome::Complete(VmExit::Panicked { .. })),
                    "{outcome:?}"
                );
            }
        }
    }
}

#[test]
fn an_unknown_packed_layout_is_not_inferred_from_allocation_padding() {
    let mut region = region();
    let value = continuation(&mut region);
    value.stmts.insert(
        0,
        IrStmt::VDecl {
            x: 15,
            ty: IrType::UInt8,
            expr: IrExpr::Lit(IrLit::Num(IrNat::Small(7))),
        },
    );
    arm(value, 0).stmts.push(IrStmt::SSet {
        x: 11,
        i: 2,
        offset: 0,
        y: 15,
        ty: IrType::UInt8,
    });
    let cold = arm(value, 1);
    let IrStmt::VDecl {
        expr: IrExpr::Ctor { info, .. },
        ..
    } = &mut cold.stmts[0]
    else {
        panic!("cold allocation")
    };
    info.ssize = 1;
    cold.stmts.push(IrStmt::SSet {
        x: 22,
        i: 2,
        offset: 0,
        y: 15,
        ty: IrType::UInt8,
    });
    let mut known = update(region.clone());
    let IrDecl::Function { body, .. } = &mut known else {
        panic!("update function")
    };
    let IrAlt::Ctor { info, .. } = &mut arms(body)[0] else {
        panic!("known incoming shape")
    };
    info.ssize = 1;
    let compiled = callable(&IrModule {
        decls: vec![known],
        ..IrModule::default()
    });
    let result = compiled.execute(
        vec![
            Obj::mk_ctor(1, vec![Obj::mk_nat(19), Obj::mk_nat(23)], &[3]),
            Obj::mk_nat(42),
        ],
        ExecutionLimits::default(),
        None,
    );
    let Outcome::Complete(VmExit::Returned(result)) = result.outcome else {
        panic!("{result:?}")
    };
    assert_eq!(
        nat_decimal(&result.value.ctor_child(0)).as_deref(),
        Some("43")
    );
    assert_eq!(result.value.try_ctor_scalar_u32(16), Some(7));
    assert!(
        compile_module(
            &unshaped_fixture(region),
            "Reset.main",
            &[],
            IrExecutionLimits::default(),
        )
        .is_err()
    );
}

#[test]
fn reset_and_reuse_guards_accept_either_boolean_default_and_order() {
    for outer_default in [0, 1] {
        for inner_default in [0, 1] {
            let mut region = region();
            let inner = continuation(&mut region);
            let value = arm(inner, inner_default).clone();
            arms(inner)[inner_default] = IrAlt::Default { body: value };
            arms(inner).reverse();
            let value = arm(&mut region, outer_default).clone();
            arms(&mut region)[outer_default] = IrAlt::Default { body: value };
            arms(&mut region).reverse();
            assert_replay(&compile_region(region).unwrap(), "93");
        }
    }
}

#[test]
fn reset_prefix_effects_run_once_per_update_including_bytecode_replay() {
    use fln_rt::obj::StdoutCapture;
    let mut region = region();
    continuation(&mut region).stmts.splice(
        2..2,
        [
            bind(
                30,
                IrExpr::Lit(IrLit::Str("between reset and reuse".to_owned())),
            ),
            bind(
                31,
                IrExpr::Pap {
                    function: name("Reset.traceCont"),
                    args: vec![],
                },
            ),
            call(32, "dbgTrace", &[30, 31]),
        ],
    );
    let mut module = fixture(region);
    module.decls.push(function(
        "Reset.traceCont",
        &[1],
        body(vec![num(2, 0)], IrTerminal::Ret(var(2))),
    ));
    module.decls.push(IrDecl::Extern {
        name: name("dbgTrace"),
        params: vec![param(1, IrType::TObject), param(2, IrType::TObject)],
        result: IrType::TObject,
        entries: vec![],
    });
    let compiled =
        compile_module(&module, "Reset.main", &[], IrExecutionLimits::default()).unwrap();
    let bytes =
        flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    for program in [compiled.program.program(), &replay] {
        let capture = StdoutCapture::begin_evaluation(1024).unwrap();
        let outcome = execute(program, ExecutionLimits::default(), None);
        let captured = capture.finish();
        assert_eq!(captured.error, None);
        assert_eq!(
            captured.bytes,
            b"between reset and reuse\nbetween reset and reuse\n"
        );
        let Outcome::Complete(VmExit::Returned(value)) = outcome else {
            panic!("{outcome:?}");
        };
        assert_eq!(nat_decimal(&value.value).as_deref(), Some("93"));
    }
}

#[test]
fn discarded_reset_arms_cannot_hide_calls_bad_projections_or_changed_operands() {
    for kind in 0..5 {
        let mut region = region();
        match kind {
            0 => arm(&mut region, 0).stmts.push(call(40, "Nat.add", &[2, 3])),
            1 => arm(&mut region, 0).stmts[0] = bind(5, IrExpr::Proj { i: 2, x: 1 }),
            2 => arm(&mut region, 0).stmts[0] = bind(5, IrExpr::Proj { i: 0, x: 2 }),
            3 => *arm(&mut region, 1).terminal = jump(10, vec![var(1), var(4)]),
            _ => *arm(&mut region, 0).terminal = jump(10, vec![var(1), IrArg::Erased]),
        }
        refused_with_or_without_incoming_shape(region, &format!("reset mismatch {kind}"));
    }
}

#[test]
fn reuse_field_tag_and_continuation_mismatches_never_authorize_sharing() {
    for kind in 0..5 {
        let mut region = region();
        let value = continuation(&mut region);
        match kind {
            0 => {
                arm(value, 0).stmts[0] = IrStmt::Set {
                    x: 11,
                    i: 1,
                    y: var(14),
                }
            }
            1 => arm(value, 0).stmts.push(IrStmt::SetTag { x: 11, cidx: 2 }),
            2 => arm(value, 1).stmts.push(call(40, "Nat.add", &[2, 3])),
            3 => *arm(value, 0).terminal = IrTerminal::Ret(var(11)),
            _ => *arm(value, 1).terminal = jump(20, vec![var(3)]),
        }
        refused_with_or_without_incoming_shape(region, &format!("reuse mismatch {kind}"));
    }
}

#[test]
fn reset_parameters_and_receiver_cannot_escape_through_common_code_or_captures() {
    for (source, nested) in [
        (11, false),
        (12, false),
        (1, false),
        (11, true),
        (12, true),
        (1, true),
    ] {
        let mut region = region();
        let read = if source == 12 {
            bind(
                40,
                IrExpr::Box {
                    ty: IrType::UInt8,
                    x: source,
                },
            )
        } else {
            bind(40, IrExpr::Proj { i: 0, x: source })
        };
        let value = continuation(&mut region);
        if nested {
            let IrStmt::JDecl { value, .. } = &mut value.stmts[2] else {
                panic!("reuse join");
            };
            value.stmts.push(read);
        } else {
            value.stmts.insert(2, read);
        }
        refused_with_or_without_incoming_shape(region, &format!("read {source}, nested={nested}"));
    }
}

#[test]
fn original_ir_is_validated_even_in_reset_branches_that_would_be_discarded() {
    let mut region = region();
    // An invalid object projection result must not disappear behind the proof.
    let IrStmt::VDecl { ty, .. } = &mut arm(&mut region, 0).stmts[0] else {
        panic!("projection");
    };
    *ty = IrType::UInt8;
    let error = compile_region(region).unwrap_err();
    assert!(
        matches!(error, IrExecutionError::IrValidation(_)),
        "{error:?}"
    );
}

#[test]
fn reset_normalization_is_bounded_and_failed_preparation_leaves_inputs_unchanged() {
    for module in [fixture(region()), unshaped_fixture(region())] {
        let original = module.clone();
        let mut limits = IrExecutionLimits::default();
        limits.ir.max_work = 1;
        let error = compile_module(&module, "Reset.main", &[], limits).unwrap_err();
        assert!(error.is_resource(), "{error:?}");
        assert_eq!(module, original);
        let first =
            compile_module(&module, "Reset.main", &[], IrExecutionLimits::default()).unwrap();
        let second =
            compile_module(&module, "Reset.main", &[], IrExecutionLimits::default()).unwrap();
        assert_replay(&first, "93");
        assert_eq!(
            flbc::encode_canonical(first.program.program(), flbc::CodecLimits::default()).unwrap(),
            flbc::encode_canonical(second.program.program(), flbc::CodecLimits::default()).unwrap(),
        );
    }
}
