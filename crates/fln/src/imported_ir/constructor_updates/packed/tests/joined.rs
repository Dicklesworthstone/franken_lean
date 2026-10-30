use super::*;

fn factor_store(module: &mut IrModule, updated: usize) {
    let value = region(module);
    let mut store = branch(value, 0).stmts.remove(0);
    match &mut store {
        IrStmt::USet { x, .. } | IrStmt::SSet { x, .. } => *x = 81,
        _ => panic!("scalar store"),
    }
    branch(value, 1).stmts.remove(updated + 1);
    *branch(value, 0).terminal = IrTerminal::Jmp {
        j: 80,
        args: vec![var(1)],
    };
    *branch(value, 1).terminal = IrTerminal::Jmp {
        j: 80,
        args: vec![var(51)],
    };
    let join = IrStmt::JDecl {
        j: 80,
        params: vec![param(81, IrType::TObject)],
        value: body(vec![store], IrTerminal::Ret(var(81))),
    };
    value.stmts.insert(value.stmts.len() - 1, join);
}

fn continuation(module: &mut IrModule) -> &mut IrBody {
    region(module)
        .stmts
        .iter_mut()
        .find_map(|stmt| match stmt {
            IrStmt::JDecl { j: 80, value, .. } => Some(value),
            _ => None,
        })
        .unwrap()
}

fn expand_reset(module: &mut IrModule) {
    let value = region(module);
    let join_index = value
        .stmts
        .iter()
        .position(|stmt| matches!(stmt, IrStmt::JDecl { j: 80, .. }))
        .unwrap();
    let continuation = value.stmts.remove(join_index);
    let mut reuse = value.terminal.as_ref().clone();
    let IrTerminal::Case { x, alts, .. } = &mut reuse else {
        panic!("reuse")
    };
    *x = 61;
    let IrAlt::Ctor { body: hot, .. } = &mut alts[0] else {
        panic!("hot")
    };
    *hot.terminal = IrTerminal::Jmp {
        j: 80,
        args: vec![var(60)],
    };
    // The factored scalar store leaves no direct hot-path mutation.
    assert!(hot.stmts.is_empty());
    value.stmts.insert(
        value.stmts.len() - 1,
        IrStmt::JDecl {
            j: 70,
            params: vec![param(60, IrType::TObject), param(61, IrType::UInt8)],
            value: body(vec![continuation], reuse),
        },
    );
    *value.terminal = IrTerminal::Case {
        type_name: name("Bool"),
        x: 50,
        x_type: IrType::UInt8,
        alts: vec![
            boolean(
                0,
                body(
                    vec![],
                    IrTerminal::Jmp {
                        j: 70,
                        args: vec![var(1), var(50)],
                    },
                ),
            ),
            boolean(
                1,
                body(
                    vec![],
                    IrTerminal::Jmp {
                        j: 70,
                        args: vec![IrArg::Erased, var(50)],
                    },
                ),
            ),
        ],
    };
}

#[test]
fn factored_initialization_executes_for_every_scalar_representation() {
    for layout in [
        Layout::integers(true),
        Layout::integers(false),
        Layout::floats(),
    ] {
        for updated in 0..layout.fields.len() {
            let mut module = layout.module(updated);
            factor_store(&mut module, updated);
            let replacement = layout.original[updated] ^ 1;
            let compiled = compile_module(
                &module,
                &layout.arguments(updated, replacement),
                IrExecutionLimits::default(),
            )
            .unwrap();
            check(&compiled, &layout.expected(replacement));
        }
    }
}

#[test]
fn expanded_reset_reuse_initializes_the_common_packed_continuation() {
    for layout in [Layout::integers(true), Layout::floats()] {
        let mut module = layout.module(1);
        factor_store(&mut module, 1);
        expand_reset(&mut module);
        let replacement = layout.original[1] ^ 1;
        let compiled = compile_module(
            &module,
            &layout.arguments(1, replacement),
            IrExecutionLimits::default(),
        )
        .unwrap();
        check(&compiled, &layout.expected(replacement));
    }
}

#[test]
fn common_object_and_scalar_stores_construct_one_complete_mixed_record() {
    let layout = Layout::integers(true);
    let mut module = layout.module(1);
    factor_store(&mut module, 1);
    let value = region(&mut module);
    let index = value
        .stmts
        .iter()
        .position(|stmt| matches!(stmt, IrStmt::JDecl { j: 80, .. }))
        .unwrap();
    value.stmts.insert(index, num(90, 23));
    continuation(&mut module).stmts.push(IrStmt::Set {
        x: 81,
        i: 0,
        y: var(90),
    });
    let compiled = compile_module(
        &module,
        &layout.arguments(1, 42),
        IrExecutionLimits::default(),
    )
    .unwrap();
    let expected = (layout.expected(42).parse::<u128>().unwrap() + 12).to_string();
    check(&compiled, &expected);
}

#[test]
fn continued_reads_cases_and_nested_join_captures_use_the_fresh_record() {
    let layout = Layout::integers(true);
    for nested in [false, true] {
        let mut module = layout.module(1);
        factor_store(&mut module, 1);
        let tail = continuation(&mut module);
        tail.stmts
            .push(bind(82, IrType::UInt64, layout.projection(1, 81)));
        if nested {
            tail.stmts.push(IrStmt::JDecl {
                j: 90,
                params: vec![],
                value: body(vec![], IrTerminal::Ret(var(81))),
            });
            *tail.terminal = IrTerminal::Jmp {
                j: 90,
                args: vec![],
            };
        } else {
            *tail.terminal = IrTerminal::Case {
                type_name: layout.info.name.clone(),
                x: 81,
                x_type: IrType::TObject,
                alts: vec![IrAlt::Ctor {
                    info: layout.info.clone(),
                    body: body(vec![], IrTerminal::Ret(var(81))),
                }],
            };
        }
        let compiled = compile_module(
            &module,
            &layout.arguments(1, 42),
            IrExecutionLimits::default(),
        )
        .unwrap();
        check(&compiled, &layout.expected(42));
    }
}

#[test]
fn unused_continuation_work_is_not_dropped_after_initialization() {
    let layout = Layout::integers(true);
    for valid in [false, true] {
        let mut module = layout.module(1);
        factor_store(&mut module, 1);
        continuation(&mut module).stmts.push(bind(
            82,
            IrType::UInt64,
            IrExpr::SProj {
                n: if valid { 2 } else { 99 },
                offset: 0,
                x: 81,
            },
        ));
        let compiled = compile_module(
            &module,
            &layout.arguments(1, 42),
            IrExecutionLimits::default(),
        )
        .unwrap();
        if valid {
            check(&compiled, &layout.expected(42));
        } else {
            let encoded =
                flbc::encode_canonical(compiled.program.program(), flbc::CodecLimits::default())
                    .unwrap();
            let replay = flbc::decode_canonical(&encoded, flbc::CodecLimits::default()).unwrap();
            for program in [compiled.program.program(), &replay] {
                assert!(!matches!(
                    execute(program, ExecutionLimits::default(), None),
                    Outcome::Complete(VmExit::Returned(_))
                ));
            }
        }
    }
}

#[test]
fn unsafe_continuation_regions_remain_refusals() {
    let layout = Layout::integers(true);
    for mutant in 0..7 {
        let mut module = layout.module(1);
        factor_store(&mut module, 1);
        match mutant {
            0 => {
                continuation(&mut module)
                    .stmts
                    .insert(0, bind(82, IrType::TObject, IrExpr::Proj { i: 0, x: 81 }));
            }
            1 => {
                continuation(&mut module).stmts.insert(
                    0,
                    IrStmt::Set {
                        x: 81,
                        i: 0,
                        y: var(81),
                    },
                );
            }
            2 => {
                if let IrStmt::SSet { offset, .. } = &mut continuation(&mut module).stmts[0] {
                    *offset = u64::MAX;
                }
            }
            3 => {
                *continuation(&mut module).terminal = IrTerminal::Jmp {
                    j: 80,
                    args: vec![var(81)],
                };
            }
            4 => {
                *branch(region(&mut module), 1).terminal = IrTerminal::Jmp {
                    j: 80,
                    args: vec![var(1)],
                };
            }
            5 => {
                continuation(&mut module).stmts.push(bind(
                    82,
                    IrType::TObject,
                    IrExpr::Proj { i: 0, x: 1 },
                ));
            }
            6 => {
                branch(region(&mut module), 0)
                    .stmts
                    .push(call(99, "Nat.succ", vec![var(3)]));
            }
            _ => unreachable!(),
        }
        assert!(
            compile_module(
                &module,
                &layout.arguments(1, 42),
                IrExecutionLimits::default()
            )
            .is_err(),
            "mutant {mutant}"
        );
    }
}
