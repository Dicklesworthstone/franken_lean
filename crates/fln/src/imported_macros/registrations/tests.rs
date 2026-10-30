use super::*;
use crate::imported_ir::IrExecutionError;
use crate::{OleanDecodeLimits, decode_olean_artifact};
use fln_core::expr::{Expr, Literal, NatLit};
use fln_core::options::KVMap;
use fln_env::constants::{ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints};
use fln_olean::format;
use fln_olean::ir::{
    IrArg, IrBody, IrCtorInfo, IrDecl, IrExpr, IrLit, IrNat, IrParam, IrStmt, IrTerminal, IrType,
};
use fln_olean::region::ModuleImport;
use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};
use fln_rt::convert::inject_name;
use fln_rt::obj::Obj;
use fln_rt::region::compact;
use fln_rt::syntax_abi_generated as layout;
use fln_syntax::source::SourceInfo;

#[path = "tests/reference.rs"]
mod reference;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn owner(text: &str) -> ConstantInfo {
    ConstantInfo::Defn(DefinitionVal {
        base: ConstantVal {
            name: name(text),
            level_params: Vec::new(),
            type_: Expr::const_(name("Lean.Macro"), vec![]),
        },
        value: Expr::lit(Literal::Nat(NatLit::from_u64(0))),
        hints: ReducibilityHints::Abbrev,
        safety: DefinitionSafety::Safe,
        all: vec![name(text)],
    })
}

/// Synthetic caller ownership inputs, not an admission test. Runtime behavior
/// comes from independently built IR; negative cells mutate the ownership bind.
fn checked(text: &str, constants: &[ConstantInfo], imports: &[&str]) -> CheckedOleanModule {
    let imports: Vec<_> = imports
        .iter()
        .map(|module| ModuleImport {
            module: name(module),
            import_all: false,
            is_exported: false,
            is_meta: false,
        })
        .collect();
    let bytes = encode_module(
        ModuleWriteInput {
            is_module: false,
            imports: &imports,
            constants,
            extra_const_names: &[],
        },
        OleanWriteHeader {
            version: format::OLEAN_ACCEPTED_VERSIONS[0],
            flags: 1,
            lean_version: format::PIN_TAG.strip_prefix('v').unwrap(),
            githash: format::PIN_COMMIT,
            base_addr: (format::REGION_ALIGN * 2) as u64,
        },
        WriteBudget::default(),
    )
    .unwrap()
    .bytes;
    let decoded = decode_olean_artifact(&bytes, OleanDecodeLimits::new(bytes.len())).unwrap();
    let root = Environment::new().logical_root(&KVMap::new());
    CheckedOleanModule {
        name: name(text),
        decoded,
        base_logical_root: root,
        result_logical_root: root,
        declarations: Vec::new(),
    }
}

fn environment(modules: &[&CheckedOleanModule]) -> Environment {
    modules
        .iter()
        .flat_map(|module| &module.decoded.constants)
        .fold(Environment::new(), |environment, declaration| {
            environment.add_decl(declaration.clone()).unwrap()
        })
}

fn journal(rows: &[(&str, &str, Option<&str>)]) -> Vec<OpaqueExtensionBlock> {
    vec![OpaqueExtensionBlock {
        name: name(macros::MACRO_EXTENSION),
        entries: rows
            .iter()
            .map(|(key, declaration, scope)| {
                let pair = Obj::mk_ctor(
                    0,
                    vec![inject_name(&name(key)), inject_name(&name(declaration))],
                    &[],
                );
                let entry = match scope {
                    Some(namespace) => {
                        Obj::mk_ctor(1, vec![inject_name(&name(namespace)), pair], &[])
                    }
                    None => Obj::mk_ctor(0, vec![pair], &[]),
                };
                compact(&entry, 0).unwrap()
            })
            .collect(),
    }]
}

fn bind(x: u64, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl {
        x,
        ty: IrType::TObject,
        expr,
    }
}

fn ctor(shape: layout::CtorLayout, label: &str, args: &[u64]) -> IrExpr {
    IrExpr::Ctor {
        info: IrCtorInfo {
            name: name(label),
            cidx: shape.tag as u64,
            size: shape.object_fields as u64,
            usize: 0,
            ssize: shape.scalar_bytes as u64,
        },
        args: args.iter().copied().map(IrArg::Var).collect(),
    }
}

enum Behavior {
    Identity,
    Unsupported,
    AdvanceUnsupported,
    Diagnostic,
    Malformed,
}

fn function(text: &str, behavior: Behavior) -> IrDecl {
    let (stmts, result) = match behavior {
        Behavior::Identity => (
            vec![bind(
                3,
                ctor(layout::RESULT_OK, "EStateM.Result.ok", &[0, 2]),
            )],
            3,
        ),
        Behavior::Unsupported => (
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
        ),
        Behavior::AdvanceUnsupported => (
            vec![
                bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(40)))),
                bind(4, IrExpr::Lit(IrLit::Num(IrNat::Small(0)))),
                bind(
                    5,
                    ctor(layout::MACRO_STATE, "Lean.Macro.State.mk", &[3, 4, 4]),
                ),
                bind(
                    6,
                    IrExpr::Lit(IrLit::Num(IrNat::Small(
                        layout::EXCEPTION_UNSUPPORTED_TAG as u64,
                    ))),
                ),
                bind(
                    7,
                    ctor(layout::RESULT_ERROR, "EStateM.Result.error", &[6, 5]),
                ),
            ],
            7,
        ),
        Behavior::Diagnostic => (
            vec![
                bind(3, IrExpr::Lit(IrLit::Str("λ\0diagnostic".into()))),
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
        ),
        Behavior::Malformed => (vec![bind(3, IrExpr::Lit(IrLit::Num(IrNat::Small(7))))], 3),
    };
    IrDecl::Function {
        name: name(text),
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
    }
}

fn code(decls: Vec<IrDecl>) -> Vec<IrModule> {
    vec![IrModule {
        decls,
        ..IrModule::default()
    }]
}

fn users(code: &[IrModule]) -> BTreeSet<Name> {
    code.iter()
        .flat_map(|module| &module.decls)
        .filter_map(|decl| match decl {
            IrDecl::Function { name, .. } => Some(name.clone()),
            IrDecl::Extern { .. } => None,
        })
        .collect()
}

fn prepare(modules: &[MacroRegistrationModule<'_>], code: &[IrModule]) -> RegisteredMacros {
    let admitted = environment(
        &modules
            .iter()
            .map(|module| module.checked)
            .collect::<Vec<_>>(),
    );
    RegisteredMacros::prepare(
        modules,
        &admitted,
        code,
        &VerifiedPartition::user_fixture(),
        &users(code),
        MacroRegistryLimits::default(),
    )
    .unwrap()
}

fn input() -> Syntax {
    Syntax::node(name("choice"), vec![Syntax::atom(SourceInfo::None, "α")])
}

fn peeling_registry() -> RegisteredMacros {
    let module = checked("User", &[owner("User.peel")], &[]);
    let rows = journal(&[("peel", "User.peel", None)]);
    let mut peel = function("User.peel", Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut peel else {
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
        bind(5, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[4, 2])),
    ];
    *body.terminal = IrTerminal::Ret(IrArg::Var(5));
    prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code(vec![peel]),
    )
}

fn peel(child: Syntax) -> Syntax {
    Syntax::node(name("peel"), vec![child])
}

#[test]
fn tree_expands_roots_before_children_revisits_results_and_threads_sibling_state() {
    let registry = peeling_registry();
    let source = SourceText::from_utf8(b"x").unwrap();
    let position = fln_syntax::source::BytePos(0);
    let info = SourceInfo::Synthetic {
        pos: position,
        end_pos: fln_syntax::source::BytePos(1),
        canonical: true,
    };
    let atom = Syntax::atom(info, "x");
    let tree = Syntax::Node {
        info,
        kind: name("container"),
        args: vec![peel(peel(atom.clone())), peel(atom.clone())],
    };
    let expected = Syntax::Node {
        info,
        kind: name("container"),
        args: vec![atom.clone(), atom],
    };
    let execute = |limits| {
        registry.expand_tree(
            &tree,
            &source,
            &context(),
            MacroState {
                macro_scope: 17,
                ..MacroState::default()
            },
            limits,
            None,
        )
    };
    let report = execute(MacroTreeLimits::default());
    let Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, state })) = &report.outcome else {
        panic!("{report:?}")
    };
    assert_eq!(syntax, &expected);
    assert_ne!(
        syntax, &tree,
        "an unchanged or one-root-only result is wrong"
    );
    assert_eq!(state.macro_scope, 20);
    assert_eq!(
        state.expanded_macro_declarations,
        vec![name("User.peel"); 3]
    );
    assert_eq!(report.attempts.len(), 3);
    assert!(report.attempts.iter().all(|attempt| {
        attempt
            .native_functions
            .iter()
            .any(|id| id == "mirror:Lean.Syntax.getArg")
    }));
    let steps = report.completed_vm_usage.steps;
    assert_eq!(
        steps,
        report
            .attempts
            .iter()
            .map(|attempt| attempt.vm_usage.unwrap().steps)
            .sum()
    );
    let mut exact = MacroTreeLimits::default();
    exact.dispatch.execution.vm.max_steps = steps;
    assert!(matches!(
        execute(exact).outcome,
        Outcome::Complete(Ok(MacroTreeResult::Expanded { .. }))
    ));
    exact.dispatch.execution.vm.max_steps -= 1;
    let short = execute(exact);
    assert!(
        matches!(short.outcome, Outcome::Inconclusive(_)),
        "{short:?}"
    );
    let mut short = MacroTreeLimits::default();
    short.dispatch.max_attempts = 2;
    let stopped = execute(short);
    assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)));
    assert_eq!(stopped.attempts.len(), 2);
    assert!(
        matches!(execute(MacroTreeLimits::default()).outcome, Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, .. })) if syntax == expected)
    );
}

#[test]
fn tree_skips_tactic_blocks_and_leaves_and_checks_macro_free_depth_and_visits() {
    let registry = peeling_registry();
    let source = SourceText::from_utf8(b"").unwrap();
    let tactic = Syntax::node(
        name("Lean.Parser.Term.byTactic"),
        vec![peel(Syntax::Missing)],
    );
    let execute = |tree: &Syntax, context: &MacroContext, limits| {
        registry.expand_tree(tree, &source, context, MacroState::default(), limits, None)
    };
    let report = execute(&tactic, &context(), MacroTreeLimits::default());
    assert!(
        matches!(report.outcome, Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, .. })) if syntax == tactic)
    );
    assert!(report.attempts.is_empty());
    let tree = Syntax::node(
        name("outer"),
        vec![Syntax::node(name("inner"), vec![Syntax::Missing])],
    );
    let shallow = MacroContext {
        max_recursion_depth: 1,
        ..context()
    };
    assert!(matches!(
        execute(&tree, &shallow, MacroTreeLimits::default()).outcome,
        Outcome::Inconclusive(_)
    ));
    let short = MacroTreeLimits {
        max_visits: 2,
        ..MacroTreeLimits::default()
    };
    assert!(matches!(
        execute(&tree, &context(), short).outcome,
        Outcome::Inconclusive(_)
    ));
    assert!(
        matches!(execute(&tree, &context(), MacroTreeLimits::default()).outcome, Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, .. })) if syntax == tree)
    );
}

#[test]
fn tree_self_expansion_diagnostics_malformed_output_and_cancellation_do_not_return_partial_results()
{
    let source = SourceText::from_utf8(b"").unwrap();
    struct Cancel;
    impl CancellationProbe for Cancel {
        fn is_cancelled(&self) -> bool {
            true
        }
    }
    for (behavior, expected) in [
        (Behavior::Identity, "budget"),
        (Behavior::Diagnostic, "diagnostic"),
        (Behavior::Malformed, "malformed"),
    ] {
        let module = checked("User", &[owner("User.rule")], &[]);
        let rows = journal(&[("choice", "User.rule", None)]);
        let registry = prepare(
            &[MacroRegistrationModule {
                checked: &module,
                extensions: &rows,
            }],
            &code(vec![function("User.rule", behavior)]),
        );
        let limits = MacroTreeLimits {
            dispatch: MacroDispatchLimits {
                max_attempts: 3,
                ..MacroDispatchLimits::default()
            },
            ..MacroTreeLimits::default()
        };
        let report = registry.expand_tree(
            &input(),
            &source,
            &context(),
            MacroState::default(),
            limits,
            None,
        );
        match report.outcome {
            Outcome::Inconclusive(_) if expected == "budget" => {
                assert_eq!(report.attempts.len(), 3)
            }
            Outcome::Complete(Ok(MacroTreeResult::Error {
                reference, message, ..
            })) if expected == "diagnostic" => {
                assert_eq!(reference, input());
                assert_eq!(message, "λ\0diagnostic");
                assert_eq!(report.attempts.len(), 1);
            }
            Outcome::Complete(Err(MacroExecutionError::Conversion(_)))
                if expected == "malformed" =>
            {
                assert_eq!(report.attempts.len(), 1)
            }
            other => panic!("{other:?}"),
        }
        let cancelled = registry.expand_tree(
            &input(),
            &source,
            &context(),
            MacroState::default(),
            limits,
            Some(&Cancel),
        );
        assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
        assert!(cancelled.attempts.is_empty());
    }
}

#[test]
fn tree_assembled_siblings_share_the_output_size_limit_and_deep_trees_use_no_host_recursion() {
    let module = checked("User", &[owner("User.grow")], &[]);
    let rows = journal(&[("grow", "User.grow", None)]);
    let mut grow = function("User.grow", Behavior::Identity);
    let IrDecl::Function { body, .. } = &mut grow else {
        unreachable!()
    };
    body.stmts = vec![
        bind(
            3,
            IrExpr::Lit(IrLit::Num(IrNat::Small(layout::SOURCE_NONE_TAG as u64))),
        ),
        bind(4, IrExpr::Lit(IrLit::Str("x".repeat(60)))),
        bind(5, ctor(layout::SYNTAX_ATOM, "Lean.Syntax.atom", &[3, 4])),
        bind(6, ctor(layout::RESULT_OK, "EStateM.Result.ok", &[5, 2])),
    ];
    *body.terminal = IrTerminal::Ret(IrArg::Var(6));
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code(vec![grow]),
    );
    let source = SourceText::from_utf8(b"").unwrap();
    let input = Syntax::node(
        name("container"),
        vec![
            Syntax::node(name("grow"), vec![]),
            Syntax::node(name("grow"), vec![]),
        ],
    );
    let execute = |limits| {
        registry.expand_tree(
            &input,
            &source,
            &context(),
            MacroState::default(),
            limits,
            None,
        )
    };
    assert!(matches!(
        execute(MacroTreeLimits::default()).outcome,
        Outcome::Complete(Ok(MacroTreeResult::Expanded { .. }))
    ));
    let mut small = MacroTreeLimits::default();
    small.dispatch.execution.syntax.max_bytes = 100;
    let report = execute(small);
    assert_eq!(
        report.attempts.len(),
        2,
        "both individual results fit before the assembled tree exhausts its allowance"
    );
    assert!(
        matches!(report.outcome, Outcome::Inconclusive(_)),
        "{report:?}"
    );
    let mut generated = MacroTreeLimits::default();
    generated.generation.max_bytes = 120;
    assert!(matches!(
        execute(generated).outcome,
        Outcome::Complete(Ok(MacroTreeResult::Expanded { .. }))
    ));
    generated.generation.max_bytes = 119;
    let stopped = execute(generated);
    assert_eq!(stopped.attempts.len(), 2);
    assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)));
    generated.generation.max_bytes = 120;
    generated.generation.max_nodes = 3;
    assert!(matches!(
        execute(generated).outcome,
        Outcome::Inconclusive(_)
    ));
    generated.generation.max_nodes = 4;
    assert!(matches!(
        execute(generated).outcome,
        Outcome::Complete(Ok(MacroTreeResult::Expanded { .. }))
    ));

    let mut deep = Syntax::Missing;
    for _ in 0..5000 {
        deep = Syntax::node(name("layer"), vec![deep]);
    }
    let deep_context = MacroContext {
        max_recursion_depth: 6000,
        ..context()
    };
    let report = registry.expand_tree(
        &deep,
        &source,
        &deep_context,
        MacroState::default(),
        MacroTreeLimits::default(),
        None,
    );
    assert!(
        matches!(report.outcome, Outcome::Complete(Ok(MacroTreeResult::Expanded { syntax, .. })) if syntax == deep)
    );
    assert!(report.attempts.is_empty());
}

fn context() -> MacroContext {
    MacroContext {
        quotation_context: name("Main"),
        current_macro_scope: 17,
        current_recursion_depth: 0,
        max_recursion_depth: 512,
    }
}

fn run(registry: &RegisteredMacros, limits: MacroDispatchLimits) -> MacroDispatch {
    registry.expand_root(
        &input(),
        &SourceText::from_utf8(b"").unwrap(),
        &context(),
        MacroState {
            macro_scope: 17,
            ..MacroState::default()
        },
        limits,
        None,
    )
}

#[test]
fn import_and_entry_order_are_semantic_not_sorted() {
    let z = checked("Z", &[owner("Z.old"), owner("Z.new")], &[]);
    let a = checked("A", &[owner("A.rule")], &["Z"]);
    let z_rows = journal(&[("choice", "Z.old", None), ("choice", "Z.new", None)]);
    let a_rows = journal(&[("choice", "A.rule", None)]);
    let code = code(vec![
        function("Z.old", Behavior::Identity),
        function("Z.new", Behavior::Identity),
        function("A.rule", Behavior::Identity),
    ]);
    let modules = [
        MacroRegistrationModule {
            checked: &z,
            extensions: &z_rows,
        },
        MacroRegistrationModule {
            checked: &a,
            extensions: &a_rows,
        },
    ];
    let registry = prepare(&modules, &code);
    assert_eq!(
        registry
            .declarations(&name("choice"))
            .cloned()
            .collect::<Vec<_>>(),
        [name("A.rule"), name("Z.new"), name("Z.old")]
    );
    let report = run(&registry, MacroDispatchLimits::default());
    let Outcome::Complete(Ok(RegisteredExpansion::Expanded {
        declaration,
        syntax,
        state,
        ..
    })) = report.outcome
    else {
        panic!("{report:?}")
    };
    assert_eq!(declaration, name("A.rule"));
    assert_eq!(syntax, input());
    assert_eq!(state.macro_scope, 18);
    assert_eq!(state.expanded_macro_declarations, [name("A.rule")]);
    assert_eq!(report.attempts.len(), 1);
    assert!(report.completed_vm_usage.steps > 0);
    let admitted = environment(&[&z, &a]);
    assert!(matches!(
        RegisteredMacros::prepare(
            &[modules[1].borrow(), modules[0].borrow()],
            &admitted,
            &code,
            &VerifiedPartition::user_fixture(),
            &users(&code),
            MacroRegistryLimits::default()
        ),
        Err(MacroRegistrationError::ImportOrder { .. })
    ));
}

#[test]
fn unsupported_keeps_changed_state_and_allocates_a_fresh_scope_per_attempt() {
    let module = checked("User", &[owner("User.old"), owner("User.skip")], &[]);
    let rows = journal(&[("choice", "User.old", None), ("choice", "User.skip", None)]);
    let code = code(vec![
        function("User.old", Behavior::Identity),
        function("User.skip", Behavior::AdvanceUnsupported),
    ]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let report = run(&registry, MacroDispatchLimits::default());
    let Outcome::Complete(Ok(RegisteredExpansion::Expanded {
        declaration, state, ..
    })) = report.outcome
    else {
        panic!("{report:?}")
    };
    assert_eq!(declaration, name("User.old"));
    assert_eq!(
        state.macro_scope, 41,
        "the unsupported candidate's state must not roll back"
    );
    assert_eq!(state.expanded_macro_declarations, [name("User.old")]);
    assert_eq!(
        report
            .attempts
            .iter()
            .map(|attempt| &attempt.declaration)
            .collect::<Vec<_>>(),
        [&name("User.skip"), &name("User.old")]
    );
    assert_eq!(
        report.completed_vm_usage.steps,
        report
            .attempts
            .iter()
            .map(|attempt| attempt.vm_usage.unwrap().steps)
            .sum::<u64>()
    );
    assert!(
        report
            .attempts
            .iter()
            .flat_map(|attempt| &attempt.reference_functions)
            .all(|function| function.producer() == "reference")
    );
}

#[test]
fn diagnostic_and_malformed_results_never_fall_back() {
    for (behavior, diagnostic) in [(Behavior::Diagnostic, true), (Behavior::Malformed, false)] {
        let module = checked("User", &[owner("User.old"), owner("User.new")], &[]);
        let rows = journal(&[("choice", "User.old", None), ("choice", "User.new", None)]);
        let code = code(vec![
            function("User.old", Behavior::Identity),
            function("User.new", behavior),
        ]);
        let registry = prepare(
            &[MacroRegistrationModule {
                checked: &module,
                extensions: &rows,
            }],
            &code,
        );
        let report = run(&registry, MacroDispatchLimits::default());
        assert_eq!(report.attempts.len(), 1);
        match report.outcome {
            Outcome::Complete(Ok(RegisteredExpansion::Error {
                declaration,
                reference,
                message,
                state,
                ..
            })) => {
                assert!(diagnostic, "malformed results must refuse conversion");
                assert_eq!(declaration, name("User.new"));
                assert_eq!(reference, input());
                assert_eq!(message, "λ\0diagnostic");
                assert_eq!(state.macro_scope, 18);
                assert!(state.expanded_macro_declarations.is_empty());
            }
            Outcome::Complete(Err(MacroExecutionError::Conversion(_))) => {
                assert!(
                    !diagnostic,
                    "well-formed diagnostics must survive conversion"
                );
            }
            other => panic!("{other:?}"),
        }
    }
}

#[test]
fn attempts_and_vm_steps_are_cumulative_exact_and_retryable() {
    let module = checked("User", &[owner("User.old"), owner("User.skip")], &[]);
    let rows = journal(&[("choice", "User.old", None), ("choice", "User.skip", None)]);
    let code = code(vec![
        function("User.old", Behavior::Identity),
        function("User.skip", Behavior::Unsupported),
    ]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let successful = run(&registry, MacroDispatchLimits::default());
    let steps = successful.completed_vm_usage.steps;
    assert!(matches!(
        successful.outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded { .. }))
    ));
    for (attempts, budget, succeeds) in [
        (2, steps, true),
        (1, steps, false),
        (2, steps - 1, false),
        (0, steps, false),
        (2, 0, false),
    ] {
        let mut limits = MacroDispatchLimits {
            max_attempts: attempts,
            ..MacroDispatchLimits::default()
        };
        limits.execution.vm.max_steps = budget;
        let report = run(&registry, limits);
        if succeeds {
            assert!(matches!(
                report.outcome,
                Outcome::Complete(Ok(RegisteredExpansion::Expanded { .. }))
            ));
            assert_eq!(report.completed_vm_usage.steps, steps);
        } else {
            assert!(
                matches!(report.outcome, Outcome::Inconclusive(_)),
                "{report:?}"
            );
            assert!(report.completed_vm_usage.steps <= budget);
        }
    }
    let retried = run(&registry, MacroDispatchLimits::default());
    assert!(matches!(
        retried.outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded {
            state: MacroState {
                macro_scope: 19,
                ..
            },
            ..
        }))
    ));
}

#[test]
fn unmatched_kind_and_cancelled_attempt_do_not_consume_state() {
    struct Cancel;
    impl CancellationProbe for Cancel {
        fn is_cancelled(&self) -> bool {
            true
        }
    }
    let module = checked("User", &[owner("User.rule")], &[]);
    let rows = journal(&[("choice", "User.rule", None)]);
    let code = code(vec![function("User.rule", Behavior::Identity)]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let source = SourceText::from_utf8(b"").unwrap();
    let state = MacroState {
        macro_scope: 99,
        ..MacroState::default()
    };
    let report = registry.expand_root(
        &Syntax::Missing,
        &source,
        &context(),
        state.clone(),
        MacroDispatchLimits {
            max_attempts: 0,
            ..MacroDispatchLimits::default()
        },
        None,
    );
    assert!(
        matches!(report.outcome, Outcome::Complete(Ok(RegisteredExpansion::Unsupported { state: actual })) if actual == state)
    );
    assert!(report.attempts.is_empty());
    let report = registry.expand_root(
        &input(),
        &source,
        &context(),
        state,
        MacroDispatchLimits::default(),
        Some(&Cancel),
    );
    assert!(matches!(report.outcome, Outcome::Inconclusive(_)));
    assert!(report.attempts.is_empty());
}

#[test]
fn scoped_foreign_changed_and_missing_owners_refuse_before_execution() {
    let module = checked("User", &[owner("User.rule")], &[]);
    let foreign = checked("Other", &[owner("Other.rule")], &[]);
    let admitted = environment(&[&module, &foreign]);
    let code = code(vec![
        function("User.rule", Behavior::Identity),
        function("Other.rule", Behavior::Identity),
    ]);
    for (declaration, scope) in [
        ("Other.rule", None),
        ("Missing.rule", None),
        ("Other.rule", Some("Scope")),
        ("Missing.rule", Some("Scope")),
    ] {
        let rows = journal(&[("choice", declaration, scope)]);
        let result = RegisteredMacros::prepare(
            &[MacroRegistrationModule {
                checked: &module,
                extensions: &rows,
            }],
            &admitted,
            &code,
            &VerifiedPartition::user_fixture(),
            &users(&code),
            MacroRegistryLimits::default(),
        );
        assert!(matches!(result, Err(MacroRegistrationError::Owner { .. })));
    }
    let mut altered = owner("User.rule");
    if let ConstantInfo::Defn(info) = &mut altered {
        info.value = Expr::lit(Literal::Nat(NatLit::from_u64(1)));
    }
    let altered = checked("User", &[altered], &[]);
    let rows = journal(&[("choice", "User.rule", None)]);
    assert!(matches!(
        RegisteredMacros::prepare(
            &[MacroRegistrationModule {
                checked: &altered,
                extensions: &rows
            }],
            &admitted,
            &code,
            &VerifiedPartition::user_fixture(),
            &users(&code),
            MacroRegistryLimits::default()
        ),
        Err(MacroRegistrationError::Owner { .. })
    ));
    assert!(matches!(
        RegisteredMacros::prepare(
            &[MacroRegistrationModule {
                checked: &module,
                extensions: &rows
            }],
            &Environment::new(),
            &code,
            &VerifiedPartition::user_fixture(),
            &users(&code),
            MacroRegistryLimits::default()
        ),
        Err(MacroRegistrationError::Owner { .. })
    ));
}

#[test]
fn metadata_never_grants_user_or_native_execution_authority() {
    for declaration in ["User.rule", "Lean.Syntax.getArg"] {
        let module = checked("User", &[owner(declaration)], &[]);
        let rows = journal(&[("choice", declaration, None)]);
        let admitted = environment(&[&module]);
        let code = code(vec![function(declaration, Behavior::Identity)]);
        let users = if declaration == "User.rule" {
            BTreeSet::new()
        } else {
            users(&code)
        };
        let result = RegisteredMacros::prepare(
            &[MacroRegistrationModule {
                checked: &module,
                extensions: &rows,
            }],
            &admitted,
            &code,
            &VerifiedPartition::user_fixture(),
            &users,
            MacroRegistryLimits::default(),
        );
        assert!(
            matches!(
                result,
                Err(MacroRegistrationError::Compile {
                    ref error,
                    ..
                }) if matches!(error.as_ref(), MacroExecutionError::Compile(
                        IrExecutionError::Unclassified(_)
                            | IrExecutionError::UserOverridesCensus(_)
                    ))
            ),
            "{result:?}"
        );
    }
}

impl<'a> MacroRegistrationModule<'a> {
    fn borrow(&self) -> Self {
        Self {
            checked: self.checked,
            extensions: self.extensions,
        }
    }
}

#[test]
fn duplicate_rows_share_compilation_and_preparation_limits_are_cumulative() {
    let module = checked("User", &[owner("User.rule")], &[]);
    let rows = journal(&[("choice", "User.rule", None), ("choice", "User.rule", None)]);
    let code = code(vec![function("User.rule", Behavior::Identity)]);
    let admitted = environment(&[&module]);
    let modules = [MacroRegistrationModule {
        checked: &module,
        extensions: &rows,
    }];
    let base = MacroRegistryLimits {
        max_macros: 1,
        ..MacroRegistryLimits::default()
    };
    let prepared = RegisteredMacros::prepare(
        &modules,
        &admitted,
        &code,
        &VerifiedPartition::user_fixture(),
        &users(&code),
        base,
    )
    .unwrap();
    assert_eq!(prepared.declarations(&name("choice")).count(), 2);
    for limits in [
        MacroRegistryLimits {
            max_modules: 0,
            ..base
        },
        MacroRegistryLimits {
            max_declarations: 0,
            ..base
        },
        MacroRegistryLimits {
            max_macros: 0,
            ..base
        },
        MacroRegistryLimits {
            metadata: DecodeLimits {
                max_entries: 1,
                ..base.metadata
            },
            ..base
        },
    ] {
        assert!(
            RegisteredMacros::prepare(
                &modules,
                &admitted,
                &code,
                &VerifiedPartition::user_fixture(),
                &users(&code),
                limits
            )
            .unwrap_err()
            .is_resource()
        );
    }
    assert!(matches!(
        RegisteredMacros::prepare(
            &[modules[0].borrow(), modules[0].borrow()],
            &admitted,
            &code,
            &VerifiedPartition::user_fixture(),
            &users(&code),
            base
        ),
        Err(MacroRegistrationError::DuplicateModule(_))
    ));
}

#[test]
fn scope_overflow_stops_before_vm_and_all_unsupported_keeps_state() {
    let module = checked("User", &[owner("User.skip")], &[]);
    let rows = journal(&[("choice", "User.skip", None)]);
    let code = code(vec![function("User.skip", Behavior::AdvanceUnsupported)]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let result = run(&registry, MacroDispatchLimits::default());
    assert!(matches!(
        result.outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Unsupported {
            state: MacroState {
                macro_scope: 40,
                ..
            }
        }))
    ));
    assert_eq!(result.attempts.len(), 1);
    let stopped = registry.expand_root(
        &input(),
        &SourceText::from_utf8(b"").unwrap(),
        &context(),
        MacroState {
            macro_scope: u64::MAX,
            ..MacroState::default()
        },
        MacroDispatchLimits::default(),
        None,
    );
    assert!(matches!(stopped.outcome, Outcome::Inconclusive(_)));
    assert!(stopped.attempts.is_empty());
}

fn selecting_function(text: &str, index: u64) -> IrDecl {
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

#[test]
fn scoped_activation_preserves_import_order_precedence_and_parent_snapshots() {
    let z = checked(
        "Z",
        &[
            owner("Z.base"),
            owner("Z.firstOld"),
            owner("Z.firstNew"),
            owner("Z.second"),
        ],
        &[],
    );
    let a = checked("A", &[owner("A.first"), owner("A.base")], &["Z"]);
    let z_rows = journal(&[
        ("choice", "Z.base", None),
        ("choice", "Z.firstOld", Some("First")),
        ("choice", "Z.firstNew", Some("First")),
        ("choice", "Z.second", Some("Second")),
    ]);
    let a_rows = journal(&[
        ("choice", "A.first", Some("First")),
        ("choice", "A.base", None),
    ]);
    let code = code(vec![
        selecting_function("Z.base", 0),
        selecting_function("Z.firstOld", 0),
        selecting_function("Z.firstNew", 1),
        selecting_function("Z.second", 1),
        selecting_function("A.first", 2),
        selecting_function("A.base", 0),
    ]);
    let registry = prepare(
        &[
            MacroRegistrationModule {
                checked: &z,
                extensions: &z_rows,
            },
            MacroRegistrationModule {
                checked: &a,
                extensions: &a_rows,
            },
        ],
        &code,
    );
    let first = registry.activate_scoped(&name("First")).unwrap();
    let both = first.activate_scoped(&name("Second")).unwrap();
    let reopened = both.activate_scoped(&name("First")).unwrap();
    let reversed = registry
        .activate_scoped(&name("Second"))
        .unwrap()
        .activate_scoped(&name("First"))
        .unwrap();
    let declarations = |registry: &RegisteredMacros| {
        registry
            .declarations(&name("choice"))
            .cloned()
            .collect::<Vec<_>>()
    };
    assert_eq!(declarations(&registry), [name("A.base"), name("Z.base")]);
    assert_eq!(
        declarations(&first),
        [
            name("A.first"),
            name("Z.firstNew"),
            name("Z.firstOld"),
            name("A.base"),
            name("Z.base"),
        ]
    );
    assert_eq!(
        declarations(&both),
        [
            name("Z.second"),
            name("A.first"),
            name("Z.firstNew"),
            name("Z.firstOld"),
            name("A.base"),
            name("Z.base"),
        ]
    );
    assert_eq!(declarations(&reopened), declarations(&both));
    let input = Syntax::node(
        name("choice"),
        ["left", "middle", "right"]
            .map(|text| Syntax::atom(SourceInfo::None, text))
            .to_vec(),
    );
    let source = SourceText::from_utf8(b"").unwrap();
    for (registry, selected, text) in [
        (&registry, "A.base", "left"),
        (&first, "A.first", "right"),
        (&both, "Z.second", "middle"),
        (&reopened, "Z.second", "middle"),
        (&reversed, "A.first", "right"),
        // Returning from a lexical scope uses the unchanged parent snapshot.
        (&registry, "A.base", "left"),
    ] {
        let report = registry.expand_root(
            &input,
            &source,
            &context(),
            MacroState::default(),
            MacroDispatchLimits::default(),
            None,
        );
        assert!(
            matches!(&report.outcome,
                Outcome::Complete(Ok(RegisteredExpansion::Expanded {
                    declaration, syntax, state, ..
                })) if declaration == &name(selected)
                    && syntax == &Syntax::atom(SourceInfo::None, text)
                    && state.macro_scope == 1),
            "{report:?}"
        );
        assert_eq!(report.attempts.len(), 1);
        assert!(report.completed_vm_usage.steps > 0);
    }
}

#[test]
fn scoped_activation_requires_the_exact_structural_namespace() {
    let module = checked("User", &[owner("User.rule")], &[]);
    let rows = journal(&[("choice", "User.rule", Some("Scope.Inner"))]);
    let registry = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code(vec![function("User.rule", Behavior::Identity)]),
    );
    for candidate in [
        registry.clone(),
        registry.activate_scoped(&name("Scope")).unwrap(),
        registry
            .activate_scoped(&Name::str(Name::anonymous(), "Scope.Inner"))
            .unwrap(),
        registry.activate_scoped(&name("Scope.InnerExtra")).unwrap(),
    ] {
        let report = run(&candidate, MacroDispatchLimits::default());
        assert!(matches!(
            report.outcome,
            Outcome::Complete(Ok(RegisteredExpansion::Unsupported {
                state: MacroState {
                    macro_scope: 17,
                    ..
                }
            }))
        ));
        assert!(report.attempts.is_empty());
    }
    let active = registry.activate_scoped(&name("Scope.Inner")).unwrap();
    let report = run(&active, MacroDispatchLimits::default());
    assert!(matches!(
        report.outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded { .. }))
    ));
    assert_eq!(report.attempts.len(), 1);
    assert!(registry.declarations(&name("choice")).next().is_none());
}

#[test]
fn inactive_scoped_candidates_still_require_owners_authority_and_shared_limits() {
    let module = checked("User", &[owner("User.base"), owner("User.scoped")], &[]);
    let rows = journal(&[
        ("choice", "User.base", None),
        ("choice", "User.scoped", Some("Scope")),
    ]);
    let code = code(vec![
        function("User.base", Behavior::Identity),
        function("User.scoped", Behavior::Identity),
    ]);
    let modules = [MacroRegistrationModule {
        checked: &module,
        extensions: &rows,
    }];
    let admitted = environment(&[&module]);
    let partition = VerifiedPartition::user_fixture();
    assert!(matches!(
        RegisteredMacros::prepare(
            &modules,
            &admitted,
            &code,
            &partition,
            &users(&code),
            MacroRegistryLimits {
                max_macros: 1,
                ..MacroRegistryLimits::default()
            }
        ),
        Err(MacroRegistrationError::Limit("compiled macros"))
    ));
    assert!(matches!(
        RegisteredMacros::prepare(
            &modules,
            &admitted,
            &code,
            &partition,
            &BTreeSet::from([name("User.base")]),
            MacroRegistryLimits::default()
        ),
        Err(MacroRegistrationError::Compile { declaration, .. })
            if declaration == name("User.scoped")
    ));
    let incomplete = environment(&[&checked("User", &[owner("User.base")], &[])]);
    assert!(matches!(
        RegisteredMacros::prepare(
            &modules,
            &incomplete,
            &code,
            &partition,
            &users(&code),
            MacroRegistryLimits::default()
        ),
        Err(MacroRegistrationError::Owner { declaration, .. })
            if declaration == name("User.scoped")
    ));
    // Recovery uses the original, unchanged inputs and validates both candidates.
    let recovered = RegisteredMacros::prepare(
        &modules,
        &admitted,
        &code,
        &partition,
        &users(&code),
        MacroRegistryLimits::default(),
    )
    .unwrap()
    .activate_scoped(&name("Scope"))
    .unwrap();
    assert!(matches!(
        run(&recovered, MacroDispatchLimits::default()).outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded { declaration, .. }))
            if declaration == name("User.scoped")
    ));
}

#[test]
fn scoped_fallbacks_share_steps_and_attempts_and_reactivation_is_idempotent() {
    let module = checked("User", &[owner("User.base"), owner("User.skip")], &[]);
    let rows = journal(&[
        ("choice", "User.base", None),
        ("choice", "User.skip", Some("Scope")),
    ]);
    let code = code(vec![
        function("User.base", Behavior::Identity),
        function("User.skip", Behavior::AdvanceUnsupported),
    ]);
    let base = prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &rows,
        }],
        &code,
    );
    let active = base.activate_scoped(&name("Scope")).unwrap();
    let reopened = active.activate_scoped(&name("Scope")).unwrap();
    let report = run(&reopened, MacroDispatchLimits::default());
    assert!(matches!(
        &report.outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded {
            declaration,
            state: MacroState {
                macro_scope: 41,
                ..
            },
            ..
        })) if declaration == &name("User.base")
    ));
    assert_eq!(
        report
            .attempts
            .iter()
            .map(|attempt| attempt.declaration.clone())
            .collect::<Vec<_>>(),
        [name("User.skip"), name("User.base")]
    );
    let mut exact = MacroDispatchLimits::default();
    exact.execution.vm.max_steps = report.completed_vm_usage.steps;
    assert!(matches!(
        run(&active, exact).outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded { .. }))
    ));
    exact.execution.vm.max_steps -= 1;
    assert!(matches!(
        run(&active, exact).outcome,
        Outcome::Inconclusive(_)
    ));
    assert!(matches!(
        run(
            &active,
            MacroDispatchLimits {
                max_attempts: 1,
                ..MacroDispatchLimits::default()
            }
        )
        .outcome,
        Outcome::Inconclusive(_)
    ));
    let parent = run(&base, MacroDispatchLimits::default());
    assert_eq!(parent.attempts.len(), 1);
    assert!(matches!(
        parent.outcome,
        Outcome::Complete(Ok(RegisteredExpansion::Expanded { .. }))
    ));
}
