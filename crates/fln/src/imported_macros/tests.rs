use super::*;
use fln_comp::flbc;
use fln_core::outcome::InconclusiveCause;
use fln_olean::ir::{
    IrArg, IrBody, IrCtorInfo, IrDecl, IrExpr, IrLit, IrNat, IrParam, IrStmt, IrTerminal, IrType,
};
use fln_syntax::source::{BytePos, ByteSpan, SourceInfo};
use fln_syntax::tree::Preresolved;

mod lookup_reference;
mod reference;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}
fn span(start: usize, end: usize) -> ByteSpan {
    ByteSpan::new(BytePos(start), BytePos(end)).unwrap()
}
fn source() -> SourceText {
    SourceText::from_utf8(" α ".as_bytes()).unwrap()
}
fn leaf() -> Syntax {
    Syntax::Ident {
        info: SourceInfo::Original {
            leading: span(0, 1),
            pos: BytePos(1),
            trailing: span(3, 4),
            end_pos: BytePos(3),
        },
        raw_val: span(1, 3),
        val: Name::num(name("Main._hyg"), 17),
        preresolved: vec![
            Preresolved::Namespace { ns: name("N") },
            Preresolved::Decl {
                name: name("N.x"),
                fields: vec!["field".into()],
            },
        ],
    }
}
fn context() -> MacroContext {
    MacroContext {
        quotation_context: name("Main"),
        current_macro_scope: 17,
        current_recursion_depth: 0,
        max_recursion_depth: 512,
    }
}

fn bind(x: u64, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl {
        x,
        ty: IrType::TObject,
        expr,
    }
}
fn ctor(layout: layout::CtorLayout, label: &str, args: &[u64]) -> IrExpr {
    IrExpr::Ctor {
        info: IrCtorInfo {
            name: name(label),
            cidx: u64::from(layout.tag),
            size: layout.object_fields as u64,
            usize: 0,
            ssize: layout.scalar_bytes as u64,
        },
        args: args.iter().copied().map(IrArg::Var).collect(),
    }
}
fn module(stmts: Vec<IrStmt>, result: u64) -> IrModule {
    IrModule {
        decls: vec![IrDecl::Function {
            name: name("User.macro"),
            params: (0..3)
                .map(|x| IrParam {
                    x,
                    borrow: false,
                    ty: IrType::TObject,
                })
                .collect(),
            result: IrType::TObject,
            body: IrBody {
                stmts,
                terminal: Box::new(IrTerminal::Ret(IrArg::Var(result))),
            },
            sorry_dep: None,
        }],
        ..IrModule::default()
    }
}
fn prepared(module: &IrModule) -> CompiledMacro {
    compile(
        std::slice::from_ref(module),
        &name("User.macro"),
        &VerifiedPartition::user_fixture(),
        &BTreeSet::from([name("User.macro")]),
        IrExecutionLimits::default(),
    )
    .unwrap()
}
fn identity() -> IrModule {
    module(
        vec![bind(
            3,
            ctor(layout::RESULT_OK, "EStateM.Result.ok", &[0, 2]),
        )],
        3,
    )
}

#[test]
fn macro_state_and_syntax_survive_callable_entry_and_canonical_replay() {
    let compiled = prepared(&identity());
    let state = MacroState {
        macro_scope: u64::MAX,
        trace_messages: vec![(name("trace.test"), "λ\0🙂".into())],
        expanded_macro_declarations: vec![Name::num(name("User.macro"), 7)],
    };
    let report = compiled.execute(
        &leaf(),
        &source(),
        &context(),
        &state,
        MacroLimits::default(),
        None,
    );
    let Outcome::Complete(Ok(MacroResult::Expanded {
        syntax,
        state: observed,
    })) = report.outcome
    else {
        panic!("{report:?}")
    };
    assert_eq!(syntax, leaf());
    assert_eq!(observed, state);
    assert_eq!(report.reference_functions.len(), 1);
    assert_eq!(report.reference_functions[0].producer(), "reference");
    let bytes = flbc::encode_canonical(compiled.callable().program(), flbc::CodecLimits::default())
        .unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    // The artifact's zero-argument entry returns the actual callable closure;
    // it never executes an input-free macro with fabricated arguments.
    let outcome = fln_vm::interpreter::execute(&replay, ExecutionLimits::default(), None);
    let Outcome::Complete(VmExit::Returned(value)) = outcome else {
        panic!("{outcome:?}")
    };
    assert_eq!(
        fln_vm::interpreter::value_kind(&value.value),
        fln_vm::interpreter::ValueKind::Closure
    );
}

#[test]
fn unsupported_and_diagnostic_exceptions_preserve_their_distinct_state() {
    let unsupported = module(
        vec![
            bind(
                3,
                IrExpr::Lit(IrLit::Num(IrNat::Small(
                    layout::EXCEPTION_UNSUPPORTED_TAG as u64,
                ))),
            ),
            bind(
                4,
                ctor(layout::RESULT_ERROR, "EStateM.Result.error", &[3, 2]),
            ),
        ],
        4,
    );
    let state = MacroState {
        macro_scope: 42,
        ..MacroState::default()
    };
    let report = prepared(&unsupported).execute(
        &leaf(),
        &source(),
        &context(),
        &state,
        MacroLimits::default(),
        None,
    );
    assert!(
        matches!(report.outcome, Outcome::Complete(Ok(MacroResult::Unsupported { state: actual })) if actual == state)
    );
    let diagnostic = module(
        vec![
            bind(3, IrExpr::Lit(IrLit::Str("λ\0error".into()))),
            bind(
                4,
                ctor(
                    layout::EXCEPTION_ERROR,
                    "Lean.Macro.Exception.error",
                    &[0, 3],
                ),
            ),
            bind(
                5,
                ctor(layout::RESULT_ERROR, "EStateM.Result.error", &[4, 2]),
            ),
        ],
        5,
    );
    let report = prepared(&diagnostic).execute(
        &leaf(),
        &source(),
        &context(),
        &state,
        MacroLimits::default(),
        None,
    );
    let Outcome::Complete(Ok(MacroResult::Error {
        reference,
        message,
        state: actual,
    })) = report.outcome
    else {
        panic!("{report:?}")
    };
    assert_eq!(reference, leaf());
    assert_eq!(message, "λ\0error");
    assert_eq!(actual, state);
}

#[test]
fn malformed_macro_results_never_publish_a_partial_syntax_or_state() {
    for malformed in [
        module(vec![bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(7))))], 3),
        module(
            vec![
                bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(7)))),
                bind(4, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[0, 3])),
            ],
            4,
        ),
        module(
            vec![
                bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(7)))),
                bind(4, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[3, 2])),
            ],
            4,
        ),
    ] {
        let report = prepared(&malformed).execute(
            &leaf(),
            &source(),
            &context(),
            &MacroState::default(),
            MacroLimits::default(),
            None,
        );
        assert!(
            matches!(
                report.outcome,
                Outcome::Complete(Err(MacroExecutionError::Conversion(_)))
            ),
            "{report:?}"
        );
    }
}

#[test]
fn macro_limits_and_cancellation_leave_inputs_reusable() {
    let compiled = prepared(&identity());
    for limits in [
        MacroLimits {
            syntax: SyntaxLimits {
                max_nodes: 0,
                ..SyntaxLimits::default()
            },
            ..MacroLimits::default()
        },
        MacroLimits {
            syntax: SyntaxLimits {
                max_bytes: 0,
                ..SyntaxLimits::default()
            },
            ..MacroLimits::default()
        },
        MacroLimits {
            vm: ExecutionLimits {
                max_steps: 0,
                ..ExecutionLimits::default()
            },
            ..MacroLimits::default()
        },
    ] {
        assert!(matches!(
            compiled
                .execute(
                    &leaf(),
                    &source(),
                    &context(),
                    &MacroState::default(),
                    limits,
                    None
                )
                .outcome,
            Outcome::Inconclusive(_)
        ));
    }
    let cancelled = compiled.execute(
        &leaf(),
        &source(),
        &context(),
        &MacroState::default(),
        MacroLimits::default(),
        Some(&|| true),
    );
    assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
    let bounded = compiled.execute(
        &leaf(),
        &source(),
        &context(),
        &MacroState::default(),
        MacroLimits {
            syntax: SyntaxLimits {
                max_bytes: 0,
                ..SyntaxLimits::default()
            },
            ..MacroLimits::default()
        },
        None,
    );
    let Outcome::Inconclusive(bounded) = bounded.outcome else {
        panic!("{bounded:?}")
    };
    let InconclusiveCause::ResourceExhausted { usage } = bounded.cause else {
        panic!("{bounded:?}")
    };
    assert_eq!(
        (usage.allowed, usage.observed),
        (0, source().len_bytes() as u64)
    );
    assert!(matches!(
        compiled
            .execute(
                &leaf(),
                &source(),
                &context(),
                &MacroState::default(),
                MacroLimits::default(),
                None
            )
            .outcome,
        Outcome::Complete(Ok(MacroResult::Expanded { .. }))
    ));
    let error = SyntaxConversionError::Name(fln_rt::convert::ConvertError::NodeBudgetExhausted {
        family: "name",
        visited: 11,
        budget: 10,
    });
    assert!(
        matches!(conversion_outcome(error), Outcome::Inconclusive(reason) if matches!(reason.cause, InconclusiveCause::ResourceExhausted { .. }))
    );
}

#[test]
fn macro_selection_never_executes_toolchain_bodies_or_ambient_effects() {
    let context_observer = module(
        vec![
            bind(3, IrExpr::Proj { i: 0, x: 1 }),
            bind(4, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[0, 2])),
        ],
        4,
    );
    assert!(matches!(
        compile(
            &[context_observer],
            &name("User.macro"),
            &VerifiedPartition::user_fixture(),
            &BTreeSet::from([name("User.macro")]),
            IrExecutionLimits::default()
        ),
        Err(MacroExecutionError::Compile(
            IrExecutionError::Unsupported {
                form: "Macro.Context observation requires native Macro.Methods support",
                ..
            }
        ))
    ));
    let unknown = module(
        vec![
            bind(
                3,
                IrExpr::Fap {
                    function: name("Lean.Macro.resolveGlobalName"),
                    args: vec![IrArg::Var(0), IrArg::Var(1), IrArg::Var(2)],
                },
            ),
            bind(4, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[0, 2])),
        ],
        4,
    );
    assert!(matches!(
        compile(
            &[unknown],
            &name("User.macro"),
            &VerifiedPartition::user_fixture(),
            &BTreeSet::from([name("User.macro")]),
            IrExecutionLimits::default()
        ),
        Err(MacroExecutionError::Compile(
            IrExecutionError::Unclassified(_)
        ))
    ));
    let refs = module(
        vec![
            bind(
                3,
                IrExpr::Fap {
                    function: name("ST.Prim.mkRef"),
                    args: vec![IrArg::Var(0)],
                },
            ),
            bind(4, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[0, 2])),
        ],
        4,
    );
    assert!(
        compile(
            &[refs],
            &name("User.macro"),
            &VerifiedPartition::user_fixture(),
            &BTreeSet::from([name("User.macro")]),
            IrExecutionLimits::default()
        )
        .is_err()
    );
    let mut wrong_arity = identity();
    let IrDecl::Function { params, .. } = &mut wrong_arity.decls[0] else {
        unreachable!()
    };
    params.push(IrParam {
        x: 10,
        borrow: false,
        ty: IrType::Object,
    });
    assert!(matches!(
        compile(
            &[wrong_arity],
            &name("User.macro"),
            &VerifiedPartition::user_fixture(),
            &BTreeSet::from([name("User.macro")]),
            IrExecutionLimits::default()
        ),
        Err(MacroExecutionError::Signature { arity: 4 })
    ));
}

#[test]
fn ordinary_context_fields_are_readable_but_the_carrier_and_methods_are_confined() {
    for field in 0..layout::MACRO_CONTEXT.object_fields as u64 {
        let code = module(
            vec![
                bind(3, IrExpr::Proj { i: field, x: 1 }),
                bind(4, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[0, 2])),
            ],
            4,
        );
        let compiled = compile(
            &[code],
            &name("User.macro"),
            &VerifiedPartition::user_fixture(),
            &BTreeSet::from([name("User.macro")]),
            IrExecutionLimits::default(),
        );
        if field == layout::MACRO_CONTEXT_METHODS_FIELD {
            assert!(matches!(
                compiled,
                Err(MacroExecutionError::Compile(
                    IrExecutionError::Unsupported {
                        form: "Macro.Context observation requires native Macro.Methods support",
                        ..
                    }
                ))
            ));
        } else {
            let result = compiled.unwrap().execute(
                &leaf(),
                &source(),
                &context(),
                &MacroState::default(),
                MacroLimits::default(),
                None,
            );
            assert!(
                matches!(result.outcome, Outcome::Complete(Ok(MacroResult::Expanded { syntax, state }))
                if syntax == leaf() && state == MacroState::default())
            );
        }
    }

    // Introspection, mutation, storage and calls to unselected helpers stay
    // closed. Check the new confinement pass directly because several of
    // these deliberately adversarial operations also fail earlier validation.
    // Nested blocks must be checked alongside top-level statements.
    let assert_confined = |body: IrBody| {
        let mut code = module(vec![], 0);
        let IrDecl::Function {
            body: entry_body, ..
        } = &mut code.decls[0]
        else {
            unreachable!()
        };
        *entry_body = body;
        let selected = [ReferenceFunction {
            name: name("User.macro"),
            function: flbc::FunctionId::new(0),
        }];
        assert!(
            matches!(
                confinement::check(
                    std::slice::from_ref(&code),
                    &name("User.macro"),
                    &selected,
                    IrExecutionLimits::default().ir.max_work,
                ),
                Err(IrExecutionError::Unsupported {
                    form: "Macro.Context observation requires native Macro.Methods support",
                    ..
                })
            ),
            "{code:?}"
        );
    };
    let forbidden = [
        IrExpr::Proj {
            i: layout::MACRO_CONTEXT.object_fields as u64,
            x: 1,
        },
        IrExpr::Proj { i: u64::MAX, x: 1 },
        IrExpr::UProj { i: 1, x: 1 },
        IrExpr::SProj {
            n: 0,
            offset: 0,
            x: 1,
        },
        IrExpr::IsShared { x: 1 },
        IrExpr::Unbox { x: 1 },
        IrExpr::Box {
            ty: IrType::TObject,
            x: 1,
        },
        IrExpr::Reset { n: 0, x: 1 },
        IrExpr::Fap {
            function: name("User.helper"),
            args: vec![IrArg::Var(1)],
        },
        IrExpr::Pap {
            function: name("User.helper"),
            args: vec![IrArg::Var(1)],
        },
        IrExpr::Ap { x: 1, args: vec![] },
        ctor(layout::RESULT_OK, "EStateM.Result.ok", &[1, 2]),
    ];
    for expression in forbidden {
        let body = IrBody {
            stmts: vec![bind(3, expression)],
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(0))),
        };
        assert_confined(body.clone());
        let nested = IrBody {
            stmts: vec![IrStmt::JDecl {
                j: 10,
                params: vec![],
                value: body,
            }],
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(0))),
        };
        assert_confined(nested);
    }
    for statement in [
        IrStmt::Set {
            x: 1,
            i: 0,
            y: IrArg::Var(0),
        },
        IrStmt::USet { x: 1, i: 0, y: 0 },
        IrStmt::SSet {
            x: 1,
            i: 0,
            offset: 0,
            y: 0,
            ty: IrType::UInt8,
        },
        IrStmt::SetTag { x: 1, cidx: 0 },
    ] {
        assert_confined(IrBody {
            stmts: vec![statement],
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(0))),
        });
    }
}

#[test]
fn passing_context_to_a_user_helper_cannot_launder_the_opaque_token() {
    let mut code = module(
        vec![
            bind(
                3,
                IrExpr::Fap {
                    function: name("User.helper"),
                    args: vec![IrArg::Var(1)],
                },
            ),
            bind(4, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[3, 2])),
        ],
        4,
    );
    code.decls.push(IrDecl::Function {
        name: name("User.helper"),
        params: vec![IrParam {
            x: 0,
            borrow: false,
            ty: IrType::TObject,
        }],
        result: IrType::TObject,
        body: IrBody {
            stmts: vec![bind(
                1,
                IrExpr::Proj {
                    i: layout::MACRO_CONTEXT_METHODS_FIELD,
                    x: 0,
                },
            )],
            terminal: Box::new(IrTerminal::Ret(IrArg::Var(1))),
        },
        sorry_dep: None,
    });
    assert!(matches!(
        compile(
            &[code],
            &name("User.macro"),
            &VerifiedPartition::user_fixture(),
            &BTreeSet::from([name("User.macro"), name("User.helper")]),
            IrExecutionLimits::default(),
        ),
        Err(MacroExecutionError::Compile(
            IrExecutionError::Unsupported {
                form: "Macro.Context observation requires native Macro.Methods support",
                ..
            }
        ))
    ));
}
