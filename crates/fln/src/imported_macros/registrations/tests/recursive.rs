//! Native `Macro.expandMacro?` re-enters the selected registration snapshot.
//! These are constructed caller ownership and compiler-IR inputs, as in the
//! parent tests; they test runtime behavior, not artifact admission or pin parity.
use super::*;
use fln_core::outcome::InconclusiveCause;
use fln_olean::ir::IrAlt;
use fln_rt::macro_expansion_abi_generated as expansion_layout;
use fln_vm::interpreter::VmRefusal;
use fln_vm::macro_native::MacroLookup;
use std::cell::Cell;

fn alternative(shape: layout::CtorLayout, label: &str, body: IrBody) -> IrAlt {
    IrAlt::Ctor {
        info: IrCtorInfo {
            name: name(label),
            cidx: shape.tag as u64,
            size: shape.object_fields as u64,
            usize: 0,
            ssize: shape.scalar_bytes as u64,
        },
        body,
    }
}

/// Expand either one child or the unchanged input root. Preserve a diagnostic
/// EStateM result; unwrap `some`, and return the original query for `none`.
fn recursive_function(text: &str, child: Option<u64>) -> IrDecl {
    let mut declaration = function(text, Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    body.stmts.clear();
    let query = if let Some(index) = child {
        body.stmts.extend([
            bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(index)))),
            bind(
                4,
                IrExpr::Fap {
                    function: name("Lean.Syntax.getArg"),
                    args: vec![IrArg::Var(0), IrArg::Var(3)],
                },
            ),
        ]);
        4
    } else {
        0
    };
    body.stmts.push(bind(
        5,
        IrExpr::Fap {
            function: name("Lean.Macro.expandMacro?"),
            args: vec![IrArg::Var(query), IrArg::Var(1), IrArg::Var(2)],
        },
    ));
    *body.terminal = IrTerminal::Case {
        type_name: name("EStateM.Result"),
        x: 5,
        x_type: IrType::TObject,
        alts: vec![
            alternative(
                layout::RESULT_OK,
                "EStateM.Result.ok",
                IrBody {
                    stmts: vec![
                        bind(6, IrExpr::Proj { i: 0, x: 5 }),
                        bind(7, IrExpr::Proj { i: 1, x: 5 }),
                    ],
                    terminal: Box::new(IrTerminal::Case {
                        type_name: name("Option"),
                        x: 6,
                        x_type: IrType::TObject,
                        alts: vec![
                            alternative(
                                expansion_layout::OPTION_SOME,
                                "Option.some",
                                IrBody {
                                    stmts: vec![
                                        bind(8, IrExpr::Proj { i: 0, x: 6 }),
                                        bind(
                                            9,
                                            ctor(layout::RESULT_OK, "EStateM.Result.ok", &[8, 7]),
                                        ),
                                    ],
                                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(9))),
                                },
                            ),
                            IrAlt::Default {
                                body: IrBody {
                                    stmts: vec![bind(
                                        10,
                                        ctor(layout::RESULT_OK, "EStateM.Result.ok", &[query, 7]),
                                    )],
                                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(10))),
                                },
                            },
                        ],
                    }),
                },
            ),
            IrAlt::Default {
                body: IrBody {
                    stmts: vec![],
                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(5))),
                },
            },
        ],
    };
    declaration
}

fn selector(text: &str, index: u64) -> IrDecl {
    let mut declaration = function(text, Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    body.stmts = vec![
        bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(index)))),
        bind(
            4,
            IrExpr::Fap {
                function: name("Lean.Syntax.getArg"),
                args: vec![IrArg::Var(0), IrArg::Var(3)],
            },
        ),
        bind(5, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[4, 2])),
    ];
    *body.terminal = IrTerminal::Ret(IrArg::Var(5));
    declaration
}

/// Repeatedly query an unregistered child, thread its returned state, and then
/// decline the outer syntax. No successful expansion is available to charge
/// against the generated-result budget.
fn unsupported_probe(text: &str, calls: u64) -> IrDecl {
    let mut declaration = function(text, Behavior::Unsupported);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    body.stmts = vec![
        bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
        bind(
            4,
            IrExpr::Fap {
                function: name("Lean.Syntax.getArg"),
                args: vec![IrArg::Var(0), IrArg::Var(3)],
            },
        ),
    ];
    let mut state = 2;
    for call in 0..calls {
        let result = 5 + call * 2;
        body.stmts.push(bind(
            result,
            IrExpr::Fap {
                function: name("Lean.Macro.expandMacro?"),
                args: vec![IrArg::Var(4), IrArg::Var(1), IrArg::Var(state)],
            },
        ));
        state = result + 1;
        body.stmts
            .push(bind(state, IrExpr::Proj { i: 1, x: result }));
    }
    let exception = 5 + calls * 2;
    body.stmts.extend([
        bind(
            exception,
            IrExpr::Lit(IrLit::Num(IrNat::Small(
                layout::EXCEPTION_UNSUPPORTED_TAG as u64,
            ))),
        ),
        bind(
            exception + 1,
            ctor(
                layout::RESULT_ERROR,
                "EStateM.Result.error",
                &[exception, state],
            ),
        ),
    ]);
    *body.terminal = IrTerminal::Ret(IrArg::Var(exception + 1));
    declaration
}

fn registry(rows: &[(&str, &str, Option<&str>)], declarations: Vec<IrDecl>) -> RegisteredMacros {
    let owners: Vec<_> = declarations
        .iter()
        .filter_map(|declaration| match declaration {
            IrDecl::Function { name, .. } => Some(owner(&name.to_display_string())),
            IrDecl::Extern { .. } => None,
        })
        .collect();
    let module = checked("User", &owners, &[]);
    let rows = journal(rows);
    prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code(declarations),
    )
}

fn recursive_registry() -> RegisteredMacros {
    registry(
        &[
            ("outer", "User.outer", None),
            ("choice", "User.select", None),
            ("choice", "User.skip", None),
        ],
        vec![
            recursive_function("User.outer", Some(0)),
            selector("User.select", 2),
            function("User.skip", Behavior::AdvanceUnsupported),
        ],
    )
}

fn choice() -> Syntax {
    Syntax::node(
        name("choice"),
        vec![
            Syntax::atom(SourceInfo::None, "left"),
            Syntax::atom(SourceInfo::None, ","),
            Syntax::atom(SourceInfo::None, "right"),
        ],
    )
}

fn outer(child: Syntax) -> Syntax {
    Syntax::node(name("outer"), vec![child])
}

fn execute(
    registry: &RegisteredMacros,
    input: &Syntax,
    limits: MacroDispatchLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> MacroDispatch {
    registry.expand_root(
        input,
        &SourceText::from_utf8(b"").unwrap(),
        &context(),
        MacroState {
            macro_scope: 17,
            ..MacroState::default()
        },
        limits,
        cancellation,
    )
}

fn expanded(report: &MacroDispatch) -> (&Syntax, &MacroState) {
    let Outcome::Complete(Ok(RegisteredExpansion::Expanded { syntax, state, .. })) =
        &report.outcome
    else {
        panic!("{report:?}")
    };
    (syntax, state)
}

fn attempted(report: &MacroDispatch) -> Vec<Name> {
    report
        .attempts
        .iter()
        .map(|attempt| attempt.declaration.clone())
        .collect()
}

#[test]
fn standalone_macros_receive_no_ambient_expansion_authority() {
    struct Lookup(Name);
    impl MacroLookup for Lookup {
        fn current_namespace(&self) -> &Name {
            &self.0
        }
        fn has_decl(&self, _: &Name) -> bool {
            true
        }
    }

    let code = code(vec![recursive_function("User.outer", Some(0))]);
    let compiled = compile(
        &code,
        &name("User.outer"),
        &VerifiedPartition::user_fixture(),
        &users(&code),
        IrExecutionLimits::default(),
    )
    .unwrap();
    let input = outer(choice());
    let source = SourceText::from_utf8(b"").unwrap();
    let context = context();
    let state = MacroState::default();
    let refused = |report: crate::imported_macros::MacroExecution| {
        assert!(
            matches!(
                report.outcome,
                Outcome::Complete(Err(MacroExecutionError::Runtime(
                    VmRefusal::MacroExpansionUnavailable
                )))
            ),
            "a missing registry capability must expose no syntax or state: {report:?}"
        );
        assert!(report.vm_usage.is_some(), "the native callback was reached");
    };
    refused(compiled.execute(
        &input,
        &source,
        &context,
        &state,
        MacroLimits::default(),
        None,
    ));
    let lookup = Lookup(name("Client"));
    for lookup in [None, Some(&lookup as &dyn MacroLookup)] {
        refused(compiled.execute_with_context(
            &input,
            MacroInvocation {
                source: &source,
                context: &context,
                state: &state,
                lookup,
            },
            MacroLimits::default(),
            None,
        ));
    }
}

#[test]
fn nested_dispatch_preserves_priority_state_history_and_provenance() {
    let registry = recursive_registry();
    let input = outer(choice());
    let report = execute(&registry, &input, MacroDispatchLimits::default(), None);
    let (syntax, state) = expanded(&report);
    assert_eq!(syntax, &Syntax::atom(SourceInfo::None, "right"));
    assert_eq!(state.macro_scope, 41);
    assert_eq!(
        state.expanded_macro_declarations,
        vec![name("User.outer"), name("User.select")]
    );
    assert_eq!(
        attempted(&report),
        vec![name("User.outer"), name("User.skip"), name("User.select")]
    );
    assert!(
        report.attempts[0]
            .native_functions
            .iter()
            .any(|function| function == "mirror:Lean.Macro.expandMacro?")
    );
    for attempt in &report.attempts {
        assert!(attempt.reference_functions.iter().any(|function| {
            function.name == attempt.declaration && function.producer() == "reference"
        }));
    }
    // The caller includes the nested executions in its own usage. The batch
    // total must charge that work once, not add the same child steps again.
    assert_eq!(
        report.completed_vm_usage.steps,
        report.attempts[0].vm_usage.unwrap().steps
    );

    // `expandMacro?` itself does not introduce `withIncRecDepth` at the pin.
    let zero_depth = MacroContext {
        max_recursion_depth: 0,
        ..context()
    };
    let report = registry.expand_root(
        &input,
        &SourceText::from_utf8(b"").unwrap(),
        &zero_depth,
        MacroState {
            macro_scope: 17,
            ..MacroState::default()
        },
        MacroDispatchLimits::default(),
        None,
    );
    assert_eq!(expanded(&report).0, syntax);
}

#[test]
fn nested_none_and_success_expand_only_the_requested_root() {
    let registry = registry(
        &[
            ("outer", "User.outer", None),
            ("declined", "User.skip", None),
            ("choice", "User.select", None),
            ("peel", "User.peel", None),
        ],
        vec![
            recursive_function("User.outer", Some(0)),
            function("User.skip", Behavior::Unsupported),
            selector("User.select", 0),
            selector("User.peel", 0),
        ],
    );
    for (child, attempts, scope) in [
        (Syntax::atom(SourceInfo::None, "unregistered"), 1, 18),
        (Syntax::node(name("declined"), vec![]), 2, 19),
    ] {
        let report = execute(
            &registry,
            &outer(child.clone()),
            MacroDispatchLimits::default(),
            None,
        );
        let (syntax, state) = expanded(&report);
        assert_eq!(syntax, &child, "none must preserve the queried syntax");
        assert_eq!(report.attempts.len(), attempts);
        assert_eq!(state.macro_scope, scope);
        assert_eq!(state.expanded_macro_declarations, vec![name("User.outer")]);
    }
    let retained = peel(Syntax::atom(SourceInfo::None, "leaf"));
    let input = outer(Syntax::node(name("choice"), vec![retained.clone()]));
    let report = execute(&registry, &input, MacroDispatchLimits::default(), None);
    assert_eq!(expanded(&report).0, &retained);
    assert_eq!(
        attempted(&report),
        vec![name("User.outer"), name("User.select")]
    );
}

#[test]
fn nested_callbacks_preserve_the_callers_reference_and_source_metadata() {
    use fln_syntax::source::{BytePos, ByteSpan};
    use fln_syntax::tree::Preresolved;

    let mut reference = function("User.reference", Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut reference else {
        unreachable!()
    };
    body.stmts = vec![
        bind(
            3,
            IrExpr::Proj {
                i: expansion_layout::MACRO_CONTEXT_REF_FIELD as u64,
                x: 1,
            },
        ),
        bind(4, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[3, 2])),
    ];
    *body.terminal = IrTerminal::Ret(IrArg::Var(4));
    let registry = registry(
        &[
            ("outer", "User.outer", None),
            ("choice", "User.reference", None),
        ],
        vec![recursive_function("User.outer", Some(0)), reference],
    );
    let source = SourceText::from_utf8(b" \tshadow\r\n").unwrap();
    let identifier = Syntax::Ident {
        info: SourceInfo::Original {
            leading: ByteSpan::new(BytePos(0), BytePos(2)).unwrap(),
            pos: BytePos(2),
            trailing: ByteSpan::new(BytePos(8), BytePos(10)).unwrap(),
            end_pos: BytePos(8),
        },
        raw_val: ByteSpan::new(BytePos(2), BytePos(8)).unwrap(),
        val: name("shadow"),
        preresolved: vec![Preresolved::Decl {
            name: name("Library.actual"),
            fields: vec!["field".to_owned()],
        }],
    };
    let queried = Syntax::node(name("choice"), vec![identifier]);
    let input = Syntax::Node {
        info: SourceInfo::Synthetic {
            pos: BytePos(2),
            end_pos: BytePos(8),
            canonical: true,
        },
        kind: name("outer"),
        args: vec![queried.clone()],
    };
    let report = registry.expand_root(
        &input,
        &source,
        &context(),
        MacroState::default(),
        MacroDispatchLimits::default(),
        None,
    );
    // `expandMacro?` does not introduce `withRef`: the child's macro observes
    // the caller's outer reference, not its own queried syntax argument.
    assert_eq!(expanded(&report).0, &input);
    assert_ne!(expanded(&report).0, &queried);
    assert_eq!(
        attempted(&report),
        vec![name("User.outer"), name("User.reference")]
    );
}

#[test]
fn nested_diagnostics_and_malformed_results_never_try_an_older_candidate() {
    for behavior in [Behavior::Diagnostic, Behavior::Malformed] {
        let diagnostic = matches!(behavior, Behavior::Diagnostic);
        let registry = registry(
            &[
                ("outer", "User.outer", None),
                ("choice", "User.older", None),
                ("choice", "User.fail", None),
            ],
            vec![
                recursive_function("User.outer", Some(0)),
                selector("User.older", 0),
                function("User.fail", behavior),
            ],
        );
        let report = execute(
            &registry,
            &outer(choice()),
            MacroDispatchLimits::default(),
            None,
        );
        assert_eq!(
            attempted(&report),
            vec![name("User.outer"), name("User.fail")]
        );
        match &report.outcome {
            Outcome::Complete(Ok(RegisteredExpansion::Error {
                reference,
                message,
                state,
                ..
            })) if diagnostic => {
                assert_eq!(reference, &choice());
                assert_eq!(message, "λ\0diagnostic");
                assert_eq!(state.macro_scope, 19);
                assert!(state.expanded_macro_declarations.is_empty());
            }
            Outcome::Complete(Err(_)) if !diagnostic => {}
            other => panic!("{other:?}"),
        }
    }
}

#[test]
fn nested_calls_share_attempt_and_instruction_limits_without_retaining_partial_state() {
    let registry = recursive_registry();
    let input = outer(choice());
    let complete = execute(&registry, &input, MacroDispatchLimits::default(), None);
    let expected = expanded(&complete);
    let mut exact = MacroDispatchLimits {
        max_attempts: complete.attempts.len() as u64,
        ..MacroDispatchLimits::default()
    };
    exact.execution.vm.max_steps = complete.completed_vm_usage.steps;
    let exact_report = execute(&registry, &input, exact, None);
    assert_eq!(expanded(&exact_report), expected);
    for limit in ["attempts", "instructions"] {
        let mut low = exact;
        if limit == "attempts" {
            low.max_attempts -= 1;
        } else {
            low.execution.vm.max_steps -= 1;
        }
        let report = execute(&registry, &input, low, None);
        assert!(
            matches!(
                report.outcome,
                Outcome::Inconclusive(Inconclusive {
                    cause: InconclusiveCause::ResourceExhausted { .. },
                    ..
                })
            ),
            "{limit}: {report:?}"
        );
    }
    let recovered = execute(&registry, &input, exact, None);
    assert_eq!(expanded(&recovered), expected);
    assert_eq!(attempted(&recovered), attempted(&complete));
}

#[test]
fn nested_results_share_the_tree_generation_allowance() {
    let registry = recursive_registry();
    let input = outer(choice());
    let execute = |limits| {
        registry.expand_tree(
            &input,
            &SourceText::from_utf8(b"").unwrap(),
            &context(),
            MacroState::default(),
            limits,
            None,
        )
    };
    let complete = execute(MacroTreeLimits::default());
    assert!(
        matches!(
            complete.outcome,
            Outcome::Complete(Ok(MacroTreeResult::Expanded { .. }))
        ),
        "{complete:?}"
    );
    // The callback produces `right`, then the outer macro returns that same
    // tree. Both successful expansions count, even though the first result is
    // not independently visited by the outer tree traversal.
    assert_eq!(complete.usage.generated_nodes, 4);
    assert_eq!(complete.usage.generated_bytes, 10);
    let mut exact = MacroTreeLimits::default();
    exact.generation.max_nodes = 4;
    exact.generation.max_bytes = 10;
    assert!(matches!(
        execute(exact).outcome,
        Outcome::Complete(Ok(MacroTreeResult::Expanded { .. }))
    ));
    for dimension in ["nodes", "bytes"] {
        let mut low = exact;
        if dimension == "nodes" {
            low.generation.max_nodes -= 1;
        } else {
            low.generation.max_bytes -= 1;
        }
        let report = execute(low);
        assert!(
            matches!(
                report.outcome,
                Outcome::Inconclusive(Inconclusive {
                    cause: InconclusiveCause::ResourceExhausted { .. },
                    ..
                })
            ),
            "{dimension}: {report:?}"
        );
    }
}

#[test]
fn repeated_no_handler_queries_share_conversion_budgets_without_generated_results() {
    let make_registry = |calls| {
        registry(
            &[("probe", "User.probe", None)],
            vec![unsupported_probe("User.probe", calls)],
        )
    };
    let once = make_registry(1);
    let repeated = make_registry(32);
    let input = Syntax::node(
        name("probe"),
        vec![Syntax::atom(SourceInfo::None, "x".repeat(600))],
    );
    let completed = |report: &MacroDispatch| {
        let Outcome::Complete(Ok(RegisteredExpansion::Unsupported { state })) = &report.outcome
        else {
            panic!("the no-handler query must finish without any expansion: {report:?}")
        };
        assert_eq!(state.macro_scope, 18);
        assert!(state.expanded_macro_declarations.is_empty());
        assert_eq!(attempted(report), vec![name("User.probe")]);
    };
    for (dimension, allowance) in [("nodes", 128), ("bytes", 2048)] {
        let mut limits = MacroDispatchLimits {
            max_attempts: 1,
            ..MacroDispatchLimits::default()
        };
        if dimension == "nodes" {
            limits.execution.syntax.max_nodes = allowance;
        } else {
            limits.execution.syntax.max_bytes = allowance;
        }
        completed(&execute(&once, &input, limits, None));
        let report = execute(&repeated, &input, limits, None);
        let Outcome::Inconclusive(reason) = &report.outcome else {
            panic!("repeated callback {dimension} must consume one shared pool: {report:?}")
        };
        let InconclusiveCause::ResourceExhausted { usage } = &reason.cause else {
            panic!("{report:?}")
        };
        assert_eq!(usage.allowed, allowance as u64);
        assert!(usage.observed > usage.allowed);
        assert!(
            reason.progress.as_deref().is_some_and(|progress| {
                progress
                    .text()
                    .contains(&format!("macro callback conversion {dimension}"))
            }),
            "{report:?}"
        );
        assert_eq!(attempted(&report), vec![name("User.probe")]);
    }
    let roomy = MacroDispatchLimits {
        max_attempts: 1,
        ..MacroDispatchLimits::default()
    };
    completed(&execute(&repeated, &input, roomy, None));
}

#[test]
fn nested_dispatch_uses_the_active_scopes_and_the_current_lookup_capability() {
    struct Lookup {
        namespace: Name,
        present: bool,
        calls: Cell<usize>,
    }
    impl MacroLookup for Lookup {
        fn current_namespace(&self) -> &Name {
            &self.namespace
        }
        fn has_decl(&self, declaration: &Name) -> bool {
            self.calls.set(self.calls.get() + 1);
            self.present && *declaration == name("available")
        }
    }
    let registry = registry(
        &[
            ("outer", "User.outer", None),
            ("choice", "User.right", None),
            ("choice", "User.lookup", Some("Scoped")),
        ],
        vec![
            recursive_function("User.outer", Some(0)),
            selector("User.right", 2),
            super::lookup::has_decl_selector("User.lookup"),
        ],
    );
    let active = registry.activate_scoped(&name("Scoped")).unwrap();
    let input = outer(choice());
    let source = SourceText::from_utf8(b"").unwrap();
    let context = context();
    for present in [true, false] {
        let lookup = Lookup {
            namespace: name("Client"),
            present,
            calls: Cell::new(0),
        };
        let report = active.expand_root_with_context(
            &input,
            MacroDispatchInvocation {
                source: &source,
                context: &context,
                state: MacroState::default(),
                lookup: Some(&lookup),
            },
            MacroDispatchLimits::default(),
            None,
        );
        assert_eq!(
            expanded(&report).0,
            &Syntax::atom(SourceInfo::None, if present { "left" } else { "right" })
        );
        assert_eq!(lookup.calls.get(), 1);
        assert_eq!(
            attempted(&report),
            vec![name("User.outer"), name("User.lookup")]
        );
    }
    let absent = execute(&active, &input, MacroDispatchLimits::default(), None);
    assert!(
        matches!(
            absent.outcome,
            Outcome::Complete(Err(MacroExecutionError::Runtime(
                VmRefusal::MacroLookupUnavailable { .. }
            )))
        ),
        "{absent:?}"
    );
    let original = execute(&registry, &input, MacroDispatchLimits::default(), None);
    assert_eq!(
        expanded(&original).0,
        &Syntax::atom(SourceInfo::None, "right")
    );
    assert_eq!(
        attempted(&original),
        vec![name("User.outer"), name("User.right")]
    );
}

#[test]
fn recursive_cycles_and_mid_call_cancellation_are_typed_nonanswers() {
    let cycle = registry(
        &[("loop", "User.loop", None)],
        vec![recursive_function("User.loop", None)],
    );
    let report = execute(
        &cycle,
        &Syntax::node(name("loop"), vec![]),
        MacroDispatchLimits::default(),
        None,
    );
    assert!(
        matches!(
            report.outcome,
            Outcome::Inconclusive(Inconclusive {
                cause: InconclusiveCause::ResourceExhausted { .. },
                ..
            })
        ),
        "{report:?}"
    );
    assert!(report.attempts.len() > 1 && report.attempts.len() <= 17);

    struct StopAfter {
        calls: Cell<usize>,
        allowed: usize,
    }
    impl CancellationProbe for StopAfter {
        fn is_cancelled(&self) -> bool {
            let calls = self.calls.get();
            self.calls.set(calls + 1);
            calls >= self.allowed
        }
    }
    let registry = recursive_registry();
    let input = outer(choice());
    let probe = StopAfter {
        calls: Cell::new(0),
        allowed: usize::MAX,
    };
    let full = execute(
        &registry,
        &input,
        MacroDispatchLimits::default(),
        Some(&probe),
    );
    let expected = expanded(&full);
    assert!(probe.calls.get() > 2);
    let cancelled = StopAfter {
        calls: Cell::new(0),
        allowed: probe.calls.get() / 2,
    };
    let report = execute(
        &registry,
        &input,
        MacroDispatchLimits::default(),
        Some(&cancelled),
    );
    assert!(
        matches!(
            report.outcome,
            Outcome::Inconclusive(Inconclusive {
                cause: InconclusiveCause::Cancelled { .. },
                ..
            })
        ),
        "{report:?}"
    );
    assert!(
        !report.attempts.is_empty(),
        "cancellation must interrupt a started call"
    );
    let recovered = execute(&registry, &input, MacroDispatchLimits::default(), None);
    assert_eq!(expanded(&recovered), expected);
}
