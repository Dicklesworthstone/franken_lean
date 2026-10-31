//! The capability must reach every registered candidate and tree visit without
//! being retained by reusable registry snapshots.
use super::*;
use fln_olean::ir::IrAlt;
use fln_vm::interpreter::VmRefusal;
use fln_vm::macro_native::MacroLookup;
use std::cell::{Cell, RefCell};

struct Lookup {
    namespace: Name,
    present: bool,
    namespace_calls: Cell<u64>,
    declarations: RefCell<Vec<Name>>,
}

impl Lookup {
    fn new(namespace: &str, present: bool) -> Self {
        Self {
            namespace: name(namespace),
            present,
            namespace_calls: Cell::new(0),
            declarations: RefCell::new(Vec::new()),
        }
    }
}

impl MacroLookup for Lookup {
    fn current_namespace(&self) -> &Name {
        self.namespace_calls.set(self.namespace_calls.get() + 1);
        &self.namespace
    }

    fn has_decl(&self, declaration: &Name) -> bool {
        self.declarations.borrow_mut().push(declaration.clone());
        self.present && *declaration == name("available")
    }
}

/// Also used by the source adapter's test: choose the first or third existing
/// subtree from the actual parser result, preserving its complete source data.
pub(super) fn has_decl_selector(text: &str) -> IrDecl {
    let branch = |first, index| IrBody {
        stmts: vec![
            bind(first, IrExpr::Lit(IrLit::Num(IrNat::Small(index)))),
            bind(
                first + 1,
                IrExpr::Fap {
                    function: name("Lean.Syntax.getArg"),
                    args: vec![IrArg::Var(0), IrArg::Var(first)],
                },
            ),
            bind(
                first + 2,
                ctor(layout::RESULT_OK, "EStateM.Result.ok", &[first + 1, 7]),
            ),
        ],
        terminal: Box::new(IrTerminal::Ret(IrArg::Var(first + 2))),
    };
    let mut declaration = function(text, Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    body.stmts = vec![
        bind(3, IrExpr::Lit(IrLit::Str("available".into()))),
        bind(
            4,
            IrExpr::Fap {
                function: name("Lean.Name.mkStr1"),
                args: vec![IrArg::Var(3)],
            },
        ),
        bind(
            5,
            IrExpr::Fap {
                function: name("Lean.Macro.hasDecl"),
                args: vec![IrArg::Var(4), IrArg::Var(1), IrArg::Var(2)],
            },
        ),
        bind(6, IrExpr::Proj { i: 0, x: 5 }),
        bind(7, IrExpr::Proj { i: 1, x: 5 }),
    ];
    *body.terminal = IrTerminal::Case {
        type_name: name("Bool"),
        x: 6,
        x_type: IrType::TObject,
        alts: vec![
            IrAlt::Ctor {
                info: IrCtorInfo {
                    name: name("Bool.true"),
                    cidx: 1,
                    size: 0,
                    usize: 0,
                    ssize: 0,
                },
                body: branch(8, 0),
            },
            IrAlt::Default {
                body: branch(11, 2),
            },
        ],
    };
    declaration
}

fn namespace_unsupported(text: &str) -> IrDecl {
    let mut declaration = function(text, Behavior::Unsupported);
    let IrDecl::Function { body, .. } = &mut declaration else {
        unreachable!()
    };
    body.stmts = vec![
        bind(
            3,
            IrExpr::Fap {
                function: name("Lean.Macro.getCurrNamespace"),
                args: vec![IrArg::Var(1), IrArg::Var(2)],
            },
        ),
        bind(4, IrExpr::Proj { i: 1, x: 3 }),
        bind(
            5,
            IrExpr::Lit(IrLit::Num(IrNat::Small(
                layout::EXCEPTION_UNSUPPORTED_TAG as u64,
            ))),
        ),
        bind(
            6,
            ctor(layout::RESULT_ERROR, "EStateM.Result.error", &[5, 4]),
        ),
    ];
    *body.terminal = IrTerminal::Ret(IrArg::Var(6));
    declaration
}

fn registry() -> RegisteredMacros {
    let module = checked("User", &[owner("User.select"), owner("User.fallback")], &[]);
    let rows = journal(&[
        ("choice", "User.select", None),
        ("choice", "User.fallback", None),
    ]);
    prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code(vec![
            has_decl_selector("User.select"),
            namespace_unsupported("User.fallback"),
        ]),
    )
}

fn choice() -> Syntax {
    Syntax::node(
        name("choice"),
        vec![
            Syntax::atom(SourceInfo::None, "present"),
            Syntax::atom(SourceInfo::None, ","),
            Syntax::atom(SourceInfo::None, "absent"),
        ],
    )
}

fn invocation<'a>(
    source: &'a SourceText,
    context: &'a MacroContext,
    lookup: &'a dyn MacroLookup,
) -> MacroDispatchInvocation<'a> {
    MacroDispatchInvocation {
        source,
        context,
        state: MacroState::default(),
        lookup: Some(lookup),
    }
}

#[test]
fn lookup_reaches_candidate_fallback_and_registry_reuse_does_not_retain_authority() {
    let registry = registry();
    let source = SourceText::from_utf8(b"").unwrap();
    let context = context();
    let input = choice();
    let absent_capability = || {
        registry.expand_root(
            &input,
            &source,
            &context,
            MacroState::default(),
            MacroDispatchLimits::default(),
            None,
        )
    };
    assert!(matches!(
        absent_capability().outcome,
        Outcome::Complete(Err(MacroExecutionError::Runtime(
            VmRefusal::MacroLookupUnavailable { .. }
        )))
    ));
    let present = Lookup::new("First", true);
    let absent = Lookup::new("Second", false);
    for (lookup, expected) in [
        (&present, Syntax::atom(SourceInfo::None, "present")),
        (&absent, Syntax::atom(SourceInfo::None, "absent")),
    ] {
        let result = registry.expand_root_with_context(
            &input,
            invocation(&source, &context, lookup),
            MacroDispatchLimits::default(),
            None,
        );
        assert_eq!(result.attempts.len(), 2);
        assert_eq!(result.attempts[0].declaration, name("User.fallback"));
        assert_eq!(result.attempts[1].declaration, name("User.select"));
        let Outcome::Complete(Ok(RegisteredExpansion::Expanded { syntax, state, .. })) =
            result.outcome
        else {
            panic!("{result:?}")
        };
        assert_eq!(syntax, expected);
        assert_eq!(state.macro_scope, 2);
        assert_eq!(state.expanded_macro_declarations, vec![name("User.select")]);
        assert_eq!(lookup.namespace_calls.get(), 1);
        assert_eq!(*lookup.declarations.borrow(), vec![name("available")]);
    }
    assert_eq!(present.namespace_calls.get(), 1);
    assert_eq!(absent.namespace_calls.get(), 1);
    assert!(matches!(
        absent_capability().outcome,
        Outcome::Complete(Err(MacroExecutionError::Runtime(
            VmRefusal::MacroLookupUnavailable { .. }
        )))
    ));
}

#[test]
fn lookup_follows_tree_visits_with_one_state_and_work_budget() {
    let registry = registry();
    let source = SourceText::from_utf8(b"").unwrap();
    let context = context();
    let lookup = Lookup::new("Tree", true);
    let input = Syntax::node(name("container"), vec![choice(), choice()]);
    let result = registry.expand_tree_with_context(
        &input,
        invocation(&source, &context, &lookup),
        MacroTreeLimits::default(),
        None,
    );
    assert_eq!(result.attempts.len(), 4);
    assert!(result.completed_vm_usage.steps > 0);
    let Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, state })) = result.outcome else {
        panic!("{result:?}")
    };
    assert_eq!(
        syntax,
        Syntax::node(
            name("container"),
            vec![
                Syntax::atom(SourceInfo::None, "present"),
                Syntax::atom(SourceInfo::None, "present"),
            ]
        )
    );
    assert_eq!(state.macro_scope, 4);
    assert_eq!(
        state.expanded_macro_declarations,
        vec![name("User.select"), name("User.select")]
    );
    assert_eq!(lookup.namespace_calls.get(), 2);
    assert_eq!(
        *lookup.declarations.borrow(),
        vec![name("available"), name("available")]
    );

    let stopped = Lookup::new("Stopped", true);
    let result = registry.expand_tree_with_context(
        &input,
        invocation(&source, &context, &stopped),
        MacroTreeLimits {
            dispatch: MacroDispatchLimits {
                max_attempts: 1,
                ..MacroDispatchLimits::default()
            },
            ..MacroTreeLimits::default()
        },
        None,
    );
    assert!(matches!(result.outcome, Outcome::Inconclusive(_)));
    assert_eq!(result.attempts.len(), 1);
    assert_eq!(stopped.namespace_calls.get(), 1);
    assert!(stopped.declarations.borrow().is_empty());
}

#[test]
fn cancellation_and_zero_steps_do_not_invoke_the_lookup_provider() {
    let registry = registry();
    let source = SourceText::from_utf8(b"").unwrap();
    let context = context();
    let lookup = Lookup::new("Stopped", true);
    let input = choice();
    let cancelled = registry.expand_root_with_context(
        &input,
        invocation(&source, &context, &lookup),
        MacroDispatchLimits::default(),
        Some(&|| true),
    );
    assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
    assert!(cancelled.attempts.is_empty());
    let mut limits = MacroDispatchLimits::default();
    limits.execution.vm.max_steps = 0;
    let exhausted = registry.expand_root_with_context(
        &input,
        invocation(&source, &context, &lookup),
        limits,
        None,
    );
    assert!(matches!(exhausted.outcome, Outcome::Inconclusive(_)));
    assert_eq!(exhausted.attempts.len(), 1);
    assert_eq!(lookup.namespace_calls.get(), 0);
    assert!(lookup.declarations.borrow().is_empty());
}
