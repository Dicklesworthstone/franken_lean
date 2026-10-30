use super::*;

fn compile_fresh(value: IrBody, arguments: &[EntryArgument]) -> Result<CompiledIr> {
    let input = IrModule {
        decls: vec![
            function(
                "Updates.fresh",
                &(1..=arguments.len() as u64).collect::<Vec<_>>(),
                value,
            ),
            function(
                "Updates.identity",
                &[1, 2],
                body(vec![], IrTerminal::Ret(var(1))),
            ),
        ],
        ..IrModule::default()
    };
    let partition = VerifiedPartition {
        partition: CensusPartition::parse("constant_count\t0\n", GraphArchiveLimits::default())
            .unwrap(),
    };
    compile(
        &[input],
        &name("Updates.fresh"),
        arguments,
        &partition,
        &BTreeSet::from([name("Updates.fresh"), name("Updates.identity")]),
        IrExecutionLimits::default(),
    )
}

#[test]
fn fresh_constructor_stores_preserve_computation_order_and_repeated_writes() {
    let compiled = compile_fresh(
        body(
            vec![
                num(1, 19),
                num(2, 23),
                bind(
                    3,
                    IrExpr::Ctor {
                        info: info(1, 2),
                        args: vec![var(1), IrArg::Erased],
                    },
                ),
                call(4, "Nat.add", &[1, 2]),
                IrStmt::Set {
                    x: 3,
                    i: 0,
                    y: var(4),
                },
                call(5, "Nat.add", &[4, 2]),
                IrStmt::Set {
                    x: 3,
                    i: 0,
                    y: var(5),
                },
                IrStmt::Set {
                    x: 3,
                    i: 1,
                    y: var(4),
                },
                bind(6, IrExpr::Proj { i: 0, x: 3 }),
                bind(7, IrExpr::Proj { i: 1, x: 3 }),
                call(8, "Nat.add", &[6, 7]),
            ],
            IrTerminal::Ret(var(8)),
        ),
        &[],
    )
    .unwrap();
    assert_nat_and_replay(&compiled, "107");
    let entry = compiled
        .reference_functions()
        .iter()
        .find(|f| f.name == name("Updates.fresh"))
        .unwrap()
        .function;
    let code = &compiled.program.program().functions()[entry.get() as usize].code;
    assert_eq!(
        code.iter()
            .filter(|i| {
                matches!(i, flbc::Instruction::Intrinsic { row, .. } if row == "extern:Nat.add")
            })
            .count(),
        3,
        "overwriting a field does not erase its operand's computation"
    );
    assert_eq!(
        code.iter()
            .filter(|i| matches!(i, flbc::Instruction::Ctor { tag: 1, .. }))
            .count(),
        1,
        "the initialized record is one immutable allocation"
    );
}

#[test]
fn initialized_object_fields_keep_shared_strings_alive_across_consuming_calls() {
    let compiled = compile_fresh(
        body(
            vec![
                bind(
                    2,
                    IrExpr::Ctor {
                        info: info(1, 2),
                        args: vec![var(1), IrArg::Erased],
                    },
                ),
                call(3, "String.append", &[1, 1]),
                IrStmt::Set {
                    x: 2,
                    i: 1,
                    y: var(3),
                },
                bind(4, IrExpr::Proj { i: 0, x: 2 }),
                bind(5, IrExpr::Proj { i: 1, x: 2 }),
                call(6, "String.length", &[4]),
                call(7, "String.length", &[5]),
                call(8, "Nat.add", &[6, 7]),
                call(9, "String.length", &[1]),
                call(10, "Nat.add", &[8, 9]),
            ],
            IrTerminal::Ret(var(10)),
        ),
        &[EntryArgument::String("λ🦀".to_owned())],
    )
    .unwrap();
    assert_nat_and_replay(&compiled, "8");
}

#[test]
fn dependent_fresh_allocations_materialize_before_becoming_object_fields() {
    let compiled = compile_fresh(
        body(
            vec![
                num(1, 19),
                num(2, 23),
                bind(
                    10,
                    IrExpr::Ctor {
                        info: info(1, 2),
                        args: vec![var(1), var(2)],
                    },
                ),
                bind(
                    20,
                    IrExpr::Ctor {
                        info: info(1, 2),
                        args: vec![var(1), var(2)],
                    },
                ),
                num(3, 42),
                IrStmt::Set {
                    x: 20,
                    i: 0,
                    y: var(3),
                },
                IrStmt::Set {
                    x: 10,
                    i: 1,
                    y: var(20),
                },
                bind(30, IrExpr::Proj { i: 1, x: 10 }),
                bind(31, IrExpr::Proj { i: 0, x: 30 }),
                bind(32, IrExpr::Proj { i: 0, x: 10 }),
                call(33, "Nat.add", &[31, 32]),
            ],
            IrTerminal::Ret(var(33)),
        ),
        &[],
    )
    .unwrap();
    assert_nat_and_replay(&compiled, "61");
}

#[test]
fn fresh_construction_composes_with_guarded_updates_and_rc_annotations() {
    let mut region = update_region();
    let shared = branch(&mut region, 1);
    shared.stmts = vec![
        bind(
            5,
            IrExpr::Ctor {
                info: info(1, 2),
                args: vec![IrArg::Erased, var(3)],
            },
        ),
        IrStmt::Inc {
            x: 5,
            n: 1,
            checked: false,
            persistent: false,
        },
        IrStmt::Set {
            x: 5,
            i: 0,
            y: var(2),
        },
        IrStmt::Dec {
            x: 5,
            n: 1,
            checked: false,
            persistent: false,
        },
    ];
    let compiled = compile_fixture(region, false, IrExecutionLimits::default()).unwrap();
    assert_nat_and_replay(&compiled, "91");
}

#[test]
fn fresh_constructor_updates_do_not_cross_reads_calls_closures_or_join_captures() {
    for escape in [
        bind(4, IrExpr::Proj { i: 0, x: 3 }),
        call(4, "Updates.identity", &[3, 1]),
        bind(
            4,
            IrExpr::Pap {
                function: name("Updates.identity"),
                args: vec![var(3)],
            },
        ),
        bind(
            4,
            IrExpr::Ctor {
                info: info(0, 1),
                args: vec![var(3)],
            },
        ),
        IrStmt::JDecl {
            j: 4,
            params: vec![],
            value: body(vec![], IrTerminal::Ret(var(3))),
        },
    ] {
        let error = compile_fresh(
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
                    escape,
                    IrStmt::Set {
                        x: 3,
                        i: 0,
                        y: var(2),
                    },
                ],
                IrTerminal::Ret(var(3)),
            ),
            &[],
        )
        .unwrap_err();
        assert!(matches!(error, IrExecutionError::Unsupported { .. }), "{error:?}");
    }
}

#[test]
fn fresh_constructor_initialization_checks_bounds_and_rejects_self_cycles() {
    for store in [
        IrStmt::Set {
            x: 3,
            i: 2,
            y: var(1),
        },
        IrStmt::Set {
            x: 3,
            i: u64::MAX,
            y: var(1),
        },
        IrStmt::SetTag {
            x: 3,
            cidx: u64::from(fln_rt::abi::TAG_MAX_CTOR_TAG) + 1,
        },
        IrStmt::Set {
            x: 3,
            i: 0,
            y: var(3),
        },
    ] {
        let error = compile_fresh(
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
                    store,
                ],
                IrTerminal::Ret(var(3)),
            ),
            &[],
        )
        .unwrap_err();
        assert!(!error.is_resource(), "{error:?}");
        assert!(matches!(
            error,
            IrExecutionError::Unsupported { .. } | IrExecutionError::IrValidation(_)
        ));
    }
    let compiled = compile_fresh(
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
                IrStmt::SetTag { x: 3, cidx: 7 },
            ],
            IrTerminal::Ret(var(3)),
        ),
        &[],
    )
    .unwrap();
    let outcome = compiled.execute(ExecutionLimits::default(), None).outcome;
    let Outcome::Complete(VmExit::Returned(value)) = outcome else {
        panic!("{outcome:?}");
    };
    assert_eq!(value.value.header().tag, 7);
    assert_eq!(nat_decimal(&value.value.ctor_child(0)).as_deref(), Some("19"));
    assert_eq!(nat_decimal(&value.value.ctor_child(1)).as_deref(), Some("23"));
}

#[test]
fn sharing_guards_accept_a_default_for_exactly_the_missing_boolean_alternative() {
    for default_index in [0, 1] {
        for reverse in [false, true] {
            let mut region = update_region();
            let IrAlt::Ctor { body, .. } = alternatives(&mut region)[default_index].clone() else {
                panic!("constructor alternative");
            };
            alternatives(&mut region)[default_index] = IrAlt::Default { body };
            if reverse {
                alternatives(&mut region).reverse();
            }
            let compiled = compile_fixture(region, false, IrExecutionLimits::default()).unwrap();
            assert_nat_and_replay(&compiled, "91");
        }
    }
    let mut region = update_region();
    let IrAlt::Ctor { body, .. } = alternatives(&mut region)[1].clone() else {
        panic!("constructor alternative");
    };
    alternatives(&mut region)[1] = IrAlt::Default { body };
    let IrAlt::Ctor { info, .. } = &mut alternatives(&mut region)[0] else {
        panic!("constructor alternative");
    };
    info.cidx = 2;
    assert!(matches!(
        compile_fixture(region, false, IrExecutionLimits::default()),
        Err(IrExecutionError::Unsupported { .. })
    ));
}
