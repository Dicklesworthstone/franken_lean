use super::*;
use fln_olean::initializers::InitEntry;
use fln_olean::ir::{IrArg, IrCtorInfo, IrExpr, IrLit, IrParam};
use fln_rt::obj::Obj;

mod policy;
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

fn binding(x: u64, ty: IrType, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl { x, ty, expr }
}

fn global(n: &str) -> IrDecl {
    IrDecl::Function {
        name: name(n),
        params: vec![],
        result: IrType::TObject,
        body: IrBody {
            stmts: vec![],
            terminal: Box::new(IrTerminal::Unreachable),
        },
        sorry_dep: None,
    }
}

fn initializer(n: &str, source: Option<&str>, tag: u64) -> IrDecl {
    let value = source.map_or_else(
        || IrExpr::Lit(IrLit::Num(IrNat::Small(42))),
        |source| IrExpr::Fap {
            function: name(source),
            args: vec![],
        },
    );
    IrDecl::Function {
        name: name(n),
        params: vec![IrParam {
            x: 0,
            borrow: false,
            ty: IrType::Void,
        }],
        result: IrType::Object,
        body: IrBody {
            stmts: vec![
                binding(1, IrType::TObject, value),
                binding(
                    2,
                    IrType::Object,
                    IrExpr::Ctor {
                        info: IrCtorInfo {
                            name: Name::anonymous(),
                            cidx: tag,
                            size: 1,
                            usize: 0,
                            ssize: 0,
                        },
                        args: vec![IrArg::Var(1)],
                    },
                ),
            ],
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(2))),
        },
        sorry_dep: None,
    }
}

fn module() -> IrModule {
    IrModule {
        decls: vec![global("g"), initializer("initG", None, 0)],
        initializers: vec![InitEntry {
            declaration: name("g"),
            initializer: Some(name("initG")),
        }],
        ..IrModule::default()
    }
}

fn prepare(module: &IrModule, limits: IrExecutionLimits) -> Result<CompiledIr, IrExecutionError> {
    compile_with_options(
        std::slice::from_ref(module),
        &name("g"),
        &[],
        &partition(),
        &module
            .decls
            .iter()
            .map(|decl| decl.name().clone())
            .collect(),
        IrExecutionOptions {
            limits,
            initialize_globals: true,
            capture_output_bytes: None,
        },
    )
}

#[test]
fn named_global_requires_capability_and_returns_its_initialized_value() {
    let module = module();
    let users = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    assert!(matches!(
        compile(
            std::slice::from_ref(&module),
            &name("g"),
            &[],
            &partition(),
            &users,
            IrExecutionLimits::default()
        ),
        Err(IrExecutionError::InitializerContract {
            detail: "requires explicit initialized-global capability",
            ..
        })
    ));
    let compiled = prepare(&module, IrExecutionLimits::default()).unwrap();
    for _ in 0..2 {
        let report = compiled.execute(ExecutionLimits::default(), None);
        assert!(report.initialization_failure.is_none());
        let Outcome::Complete(VmExit::Returned(result)) = report.outcome else {
            panic!("{report:?}")
        };
        assert_eq!(crate::nat_decimal(&result.value).as_deref(), Some("42"));
    }
}

#[test]
fn initializer_dependencies_override_reversed_journal_order() {
    let mut module = module();
    module.decls[1] = initializer("initG", Some("dependency"), 0);
    module
        .decls
        .extend([global("dependency"), initializer("initDependency", None, 0)]);
    module.initializers.push(InitEntry {
        declaration: name("dependency"),
        initializer: Some(name("initDependency")),
    });
    let compiled = prepare(&module, IrExecutionLimits::default()).unwrap();
    assert_eq!(
        compiled
            .initialization
            .as_ref()
            .unwrap()
            .globals
            .iter()
            .map(|global| global.declaration.clone())
            .collect::<Vec<_>>(),
        vec![name("dependency"), name("g")]
    );
    let report = compiled.execute(ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(result)) = report.outcome else {
        panic!("{report:?}")
    };
    assert_eq!(crate::nat_decimal(&result.value).as_deref(), Some("42"));
}

#[test]
fn dependency_cycles_and_missing_initializers_refuse_before_execution() {
    let mut module = module();
    module.decls[1] = initializer("initG", Some("g"), 0);
    assert!(matches!(
        prepare(&module, IrExecutionLimits::default()),
        Err(IrExecutionError::InitializerContract {
            detail: "cyclic initialized-global dependency",
            ..
        })
    ));
    module.decls.pop();
    assert!(
        matches!(prepare(&module, IrExecutionLimits::default()), Err(IrExecutionError::MissingDeclaration(n)) if n == name("initG"))
    );
}

#[test]
fn duplicate_journals_and_standalone_actions_cannot_be_silently_ignored() {
    let mut module = module();
    module.initializers.push(module.initializers[0].clone());
    assert!(matches!(
        prepare(&module, IrExecutionLimits::default()),
        Err(IrExecutionError::InitializerContract {
            detail: "anonymous or repeated initialized declaration",
            ..
        })
    ));
    module.initializers[1] = InitEntry {
        declaration: name("moduleAction"),
        initializer: None,
    };
    assert!(matches!(
        prepare(&module, IrExecutionLimits::default()),
        Err(IrExecutionError::InitializerContract {
            detail: "supplied modules also require standalone initialization actions",
            ..
        })
    ));
}

#[test]
fn initializer_signature_and_original_world_uses_are_checked() {
    let mut module = module();
    let IrDecl::Function { params, .. } = &mut module.decls[1] else {
        unreachable!()
    };
    params.clear();
    assert!(matches!(
        prepare(&module, IrExecutionLimits::default()),
        Err(IrExecutionError::InitializerContract { .. })
    ));
    let mut module = self::module();
    let IrDecl::Function { body, .. } = &mut module.decls[1] else {
        unreachable!()
    };
    body.stmts.push(IrStmt::Inc {
        x: 0,
        n: 1,
        checked: false,
        persistent: false,
    });
    assert!(prepare(&module, IrExecutionLimits::default()).is_err());
}

#[test]
fn journal_entries_and_dependency_walks_use_preparation_budgets() {
    let module = module();
    let mut limits = IrExecutionLimits::default();
    limits.ir.max_declarations = module.decls.len();
    let error = prepare(&module, limits).unwrap_err();
    assert!(error.is_resource());
    assert!(matches!(
        error,
        IrExecutionError::Limit("input declarations")
    ));
    let selected = module
        .decls
        .iter()
        .map(|decl| (decl.name().clone(), decl))
        .collect();
    let index = index(std::slice::from_ref(&module), IrExecutionLimits::default()).unwrap();
    let mut limits = IrExecutionLimits::default();
    limits.ir.max_work = 0;
    assert!(matches!(
        plan(&index, &selected, limits),
        Err(IrExecutionError::Limit("initializer dependency graph"))
    ));
}

#[test]
fn global_placeholder_depth_is_bounded_before_selected_module_cloning() {
    let mut module = module();
    let IrDecl::Function { body, .. } = &mut module.decls[0] else {
        unreachable!()
    };
    body.stmts.push(IrStmt::JDecl {
        j: 0,
        params: vec![],
        value: IrBody {
            stmts: vec![],
            terminal: Box::new(IrTerminal::Unreachable),
        },
    });
    prepare(&module, IrExecutionLimits::default()).unwrap();

    let mut limits = IrExecutionLimits::default();
    limits.ir.max_depth = 1;
    let error = prepare(&module, limits).unwrap_err();
    assert!(error.is_resource());
    // This is the selection preflight, not the later validation of an
    // already-cloned body. The unused placeholder still consumes this budget.
    assert!(matches!(error, IrExecutionError::Limit("IR body depth")));
}

#[test]
fn global_placeholder_work_is_bounded_before_selected_module_cloning() {
    let mut module = module();
    let IrDecl::Function { body, .. } = &mut module.decls[0] else {
        unreachable!()
    };
    body.stmts = (0..4)
        .map(|x| binding(x, IrType::TObject, IrExpr::Lit(IrLit::Num(IrNat::Small(x)))))
        .collect();
    prepare(&module, IrExecutionLimits::default()).unwrap();

    let mut limits = IrExecutionLimits::default();
    // The initializer has two statements plus its terminal and fits this
    // allowance. The larger placeholder must fail before either is cloned.
    limits.ir.max_work = 3;
    let error = prepare(&module, limits).unwrap_err();
    assert!(error.is_resource());
    assert!(matches!(
        error,
        IrExecutionError::Limit("IR selection work")
    ));
}

#[test]
fn io_failure_retains_the_original_result_and_never_becomes_an_entry_value() {
    let mut module = module();
    module.decls[1] = initializer("initG", None, 1);
    let report = prepare(&module, IrExecutionLimits::default())
        .unwrap()
        .execute(ExecutionLimits::default(), None);
    assert!(matches!(
        report.outcome,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::Initialization {
                malformed_result: false,
                ..
            },
            ..
        })
    ));
    let failure = report.initialization_failure.unwrap();
    assert_eq!(failure.declaration, name("g"));
    assert_eq!(failure.initializer, name("initG"));
    assert!(!failure.malformed);
    assert_eq!(failure.result.header().tag, 1);
    assert_eq!(
        crate::nat_decimal(&failure.result.try_ctor_child(0).unwrap()).as_deref(),
        Some("42")
    );
}

#[test]
fn initialization_exhaustion_is_inconclusive_and_retry_starts_fresh() {
    let compiled = prepare(&module(), IrExecutionLimits::default()).unwrap();
    let report = compiled.execute(
        ExecutionLimits {
            max_steps: 0,
            ..ExecutionLimits::default()
        },
        None,
    );
    assert!(matches!(report.outcome, Outcome::Inconclusive(_)));
    assert!(report.initialization_failure.is_none());
    assert!(matches!(
        compiled.execute(ExecutionLimits::default(), None).outcome,
        Outcome::Complete(VmExit::Returned(_))
    ));
}

#[test]
fn initializer_failure_and_capture_exhaustion_preserve_only_accepted_output() {
    let mut module = module();
    module.decls[1] = initializer("initG", None, 1);
    let IrDecl::Function { body, .. } = &mut module.decls[1] else {
        unreachable!()
    };
    body.stmts.splice(
        0..0,
        [
            binding(
                3,
                IrType::TObject,
                IrExpr::Fap {
                    function: name("IO.getStdout"),
                    args: vec![IrArg::Erased],
                },
            ),
            binding(4, IrType::TObject, IrExpr::Proj { i: 4, x: 3 }),
            binding(
                5,
                IrType::TObject,
                IrExpr::Lit(IrLit::Str("pre".to_owned())),
            ),
            binding(6, IrType::TObject, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
            binding(
                7,
                IrType::TObject,
                IrExpr::Ap {
                    x: 4,
                    args: vec![IrArg::Var(5), IrArg::Var(6)],
                },
            ),
            binding(
                8,
                IrType::TObject,
                IrExpr::Lit(IrLit::Str("tail".to_owned())),
            ),
            binding(
                9,
                IrType::TObject,
                IrExpr::Ap {
                    x: 4,
                    args: vec![IrArg::Var(8), IrArg::Var(6)],
                },
            ),
        ],
    );
    for (limit, expected, failed) in [
        (7, b"pretail".as_slice(), true),
        (3, b"pre".as_slice(), false),
    ] {
        let compiled = compile_with_options(
            std::slice::from_ref(&module),
            &name("g"),
            &[],
            &partition(),
            &module
                .decls
                .iter()
                .map(|decl| decl.name().clone())
                .collect(),
            IrExecutionOptions {
                capture_output_bytes: Some(limit),
                initialize_globals: true,
                ..IrExecutionOptions::default()
            },
        )
        .unwrap();
        for _ in 0..2 {
            let report = compiled.execute(ExecutionLimits::default(), None);
            assert_eq!(report.captured_output.unwrap().bytes, expected);
            assert_eq!(report.initialization_failure.is_some(), failed);
            if failed {
                assert!(matches!(
                    report.outcome,
                    Outcome::Complete(VmExit::Refused {
                        refusal: VmRefusal::Initialization {
                            malformed_result: false,
                            ..
                        },
                        ..
                    })
                ));
            } else {
                assert!(matches!(report.outcome, Outcome::Inconclusive(_)));
            }
        }
    }
}

fn callable_module() -> IrModule {
    let mut module = module();
    module.decls.push(IrDecl::Function {
        name: name("callable"),
        params: vec![IrParam {
            x: 0,
            borrow: true,
            ty: IrType::TObject,
        }],
        result: IrType::TObject,
        body: IrBody {
            stmts: vec![
                binding(
                    1,
                    IrType::TObject,
                    IrExpr::Fap {
                        function: name("g"),
                        args: vec![],
                    },
                ),
                binding(
                    2,
                    IrType::TObject,
                    IrExpr::Fap {
                        function: name("Nat.add"),
                        args: vec![IrArg::Var(0), IrArg::Var(1)],
                    },
                ),
            ],
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(2))),
        },
        sorry_dep: None,
    });
    module
}

fn prepare_callable(module: &IrModule, max_output: Option<usize>) -> CompiledCallableIr {
    compile_callable_with_options(
        std::slice::from_ref(module),
        &name("callable"),
        &partition(),
        &module
            .decls
            .iter()
            .map(|decl| decl.name().clone())
            .collect(),
        IrExecutionOptions {
            capture_output_bytes: max_output,
            initialize_globals: true,
            ..IrExecutionOptions::default()
        },
    )
    .unwrap()
}

#[test]
fn initialized_callable_preserves_capability_boundary_and_one_execution_budget() {
    let module = callable_module();
    assert!(matches!(
        compile_callable(
            std::slice::from_ref(&module),
            &name("callable"),
            &partition(),
            &module
                .decls
                .iter()
                .map(|decl| decl.name().clone())
                .collect(),
            IrExecutionLimits::default(),
        ),
        Err(IrExecutionError::InitializerContract {
            detail: "requires explicit initialized-global capability",
            ..
        })
    ));
    let compiled = prepare_callable(&module, None);
    let success = || {
        let report = compiled.execute(vec![Obj::mk_nat(7)], ExecutionLimits::default(), None);
        assert!(report.initialization_failure.is_none());
        let Outcome::Complete(VmExit::Returned(result)) = report.outcome else {
            panic!("{report:?}")
        };
        assert_eq!(crate::nat_decimal(&result.value).as_deref(), Some("49"));
        result.usage.steps
    };
    let steps = success();
    for max_steps in [0, 1, steps / 2, steps - 1] {
        let report = compiled.execute(
            vec![Obj::mk_nat(7)],
            ExecutionLimits {
                max_steps,
                ..ExecutionLimits::default()
            },
            None,
        );
        assert!(
            matches!(report.outcome, Outcome::Inconclusive(_)),
            "{report:?}"
        );
        assert!(report.initialization_failure.is_none());
        success();
    }
    let polls = std::cell::Cell::new(0u64);
    let cancel = || {
        let count = polls.get();
        polls.set(count + 1);
        count >= steps / 2
    };
    let report = compiled.execute(
        vec![Obj::mk_nat(7)],
        ExecutionLimits::default(),
        Some(&cancel),
    );
    assert!(
        matches!(report.outcome, Outcome::Inconclusive(_)),
        "{report:?}"
    );
    assert!(report.initialization_failure.is_none());
    success();
}

fn output_statements(text: &str) -> Vec<IrStmt> {
    vec![
        binding(
            10,
            IrType::TObject,
            IrExpr::Fap {
                function: name("IO.getStdout"),
                args: vec![IrArg::Erased],
            },
        ),
        binding(11, IrType::TObject, IrExpr::Proj { i: 4, x: 10 }),
        binding(12, IrType::TObject, IrExpr::Lit(IrLit::Str(text.into()))),
        binding(
            13,
            IrType::TObject,
            IrExpr::Lit(IrLit::Num(IrNat::Small(0))),
        ),
        binding(
            14,
            IrType::TObject,
            IrExpr::Ap {
                x: 11,
                args: vec![IrArg::Var(12), IrArg::Var(13)],
            },
        ),
    ]
}

#[test]
fn initialized_callable_shares_capture_and_stops_before_entry_on_failure() {
    for (tag, max_bytes, expected, malformed) in [
        (0, 8, b"initbody".as_slice(), None),
        (0, 4, b"init".as_slice(), None),
        (1, 8, b"init".as_slice(), Some(false)),
        (2, 8, b"init".as_slice(), Some(true)),
    ] {
        let mut module = callable_module();
        module.decls[1] = initializer("initG", None, tag);
        for (index, text) in [(1, "init"), (2, "body")] {
            let IrDecl::Function { body, .. } = &mut module.decls[index] else {
                unreachable!()
            };
            body.stmts.splice(0..0, output_statements(text));
        }
        let compiled = prepare_callable(&module, Some(max_bytes));
        let wrong_arity = compiled.execute(vec![], ExecutionLimits::default(), None);
        assert!(matches!(
            wrong_arity.outcome,
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::CallableEntry { .. },
                ..
            })
        ));
        assert!(wrong_arity.captured_output.unwrap().bytes.is_empty());
        assert!(wrong_arity.initialization_failure.is_none());
        for _ in 0..2 {
            let report = compiled.execute(vec![Obj::mk_nat(7)], ExecutionLimits::default(), None);
            assert_eq!(report.captured_output.unwrap().bytes, expected);
            if let Some(malformed) = malformed {
                assert!(matches!(
                    report.outcome,
                    Outcome::Complete(VmExit::Refused {
                        refusal: VmRefusal::Initialization { .. },
                        ..
                    })
                ));
                let failure = report.initialization_failure.unwrap();
                assert_eq!(failure.initializer, name("initG"));
                assert_eq!(failure.malformed, malformed);
                assert_eq!(failure.result.header().tag as u64, tag);
            } else if max_bytes == 4 {
                assert!(matches!(report.outcome, Outcome::Inconclusive(_)));
                assert!(report.initialization_failure.is_none());
            } else {
                let Outcome::Complete(VmExit::Returned(result)) = report.outcome else {
                    panic!("{:?}", report.outcome)
                };
                assert_eq!(crate::nat_decimal(&result.value).as_deref(), Some("49"));
                assert!(report.initialization_failure.is_none());
            }
        }
    }
}
