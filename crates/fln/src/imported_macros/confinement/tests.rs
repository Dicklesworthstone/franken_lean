use super::*;
use crate::imported_ir::{IrExecutionLimits, VerifiedPartition};
use crate::imported_macros::{MacroContext, MacroLimits, MacroResult, MacroState, compile};
use fln_comp::flbc::FunctionId;
use fln_core::outcome::Outcome;
use fln_olean::ir::{IrAlt, IrCtorInfo, IrType};
use fln_syntax::source::SourceText;
use fln_syntax::tree::Syntax;

mod reference;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn params(indices: &[u64]) -> Vec<IrParam> {
    indices
        .iter()
        .map(|&x| IrParam {
            x,
            borrow: false,
            ty: IrType::TObject,
        })
        .collect()
}

fn bind(x: u64, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl {
        x,
        ty: IrType::TObject,
        expr,
    }
}

fn call(function: &str, arguments: &[u64]) -> IrExpr {
    IrExpr::Fap {
        function: name(function),
        args: arguments.iter().copied().map(IrArg::Var).collect(),
    }
}

fn partial(function: &str, arguments: &[u64]) -> IrExpr {
    IrExpr::Pap {
        function: name(function),
        args: arguments.iter().copied().map(IrArg::Var).collect(),
    }
}

fn ok(syntax: u64, state: u64) -> IrExpr {
    IrExpr::Ctor {
        info: IrCtorInfo {
            name: name("EStateM.Result.ok"),
            cidx: layout::RESULT_OK.tag as u64,
            size: layout::RESULT_OK.object_fields as u64,
            usize: 0,
            ssize: layout::RESULT_OK.scalar_bytes as u64,
        },
        args: vec![IrArg::Var(syntax), IrArg::Var(state)],
    }
}

fn function(label: &str, indices: &[u64], statements: Vec<IrStmt>, terminal: IrTerminal) -> IrDecl {
    IrDecl::Function {
        name: name(label),
        params: params(indices),
        result: IrType::TObject,
        body: IrBody {
            stmts: statements,
            terminal: Box::new(terminal),
        },
        sorry_dep: None,
    }
}

fn entry(statements: Vec<IrStmt>, result: u64) -> IrDecl {
    function(
        "User.macro",
        &[0, 1, 2],
        statements,
        IrTerminal::Ret(IrArg::Var(result)),
    )
}

fn helper() -> IrDecl {
    function(
        "User.helper",
        &[10, 11],
        vec![bind(12, IrExpr::Proj { i: 5, x: 10 }), bind(13, ok(12, 11))],
        IrTerminal::Ret(IrArg::Var(13)),
    )
}

fn module(declarations: Vec<IrDecl>) -> IrModule {
    IrModule {
        decls: declarations,
        ..IrModule::default()
    }
}

fn checked(module: &IrModule, max_work: u64) -> Result<(), IrExecutionError> {
    let selected: Vec<_> = module
        .decls
        .iter()
        .enumerate()
        .map(|(index, declaration)| ReferenceFunction {
            name: declaration.name().clone(),
            function: FunctionId::new(index as u32),
        })
        .collect();
    check(
        std::slice::from_ref(module),
        &name("User.macro"),
        &selected,
        max_work,
    )
}

fn assert_executes(module: &IrModule) {
    let users = module
        .decls
        .iter()
        .map(|decl| decl.name().clone())
        .collect();
    let compiled = compile(
        std::slice::from_ref(module),
        &name("User.macro"),
        &VerifiedPartition::user_fixture(),
        &users,
        IrExecutionLimits::default(),
    )
    .unwrap();
    let input = Syntax::node(name("input"), vec![Syntax::Missing]);
    let state = MacroState {
        macro_scope: 29,
        ..MacroState::default()
    };
    let report = compiled.execute(
        &input,
        &SourceText::from_utf8(b"").unwrap(),
        &MacroContext {
            quotation_context: name("Test"),
            current_macro_scope: 17,
            current_recursion_depth: 3,
            max_recursion_depth: 512,
        },
        &state,
        MacroLimits::default(),
        None,
    );
    assert!(
        matches!(report.outcome,
            Outcome::Complete(Ok(MacroResult::Expanded { syntax, state: actual }))
                if syntax == input && actual == state),
        "confined helper did not preserve the complete input and state"
    );
}

#[test]
fn direct_helpers_and_known_partial_applications_preserve_context_and_state() {
    assert_executes(&module(vec![
        entry(vec![bind(3, call("User.helper", &[1, 2]))], 3),
        helper(),
    ]));
    assert_executes(&module(vec![
        entry(
            vec![
                bind(3, partial("User.helper", &[1])),
                bind(
                    4,
                    IrExpr::Ap {
                        x: 3,
                        args: vec![IrArg::Var(2)],
                    },
                ),
            ],
            4,
        ),
        helper(),
    ]));
}

#[test]
fn known_callbacks_remain_confined_across_helper_boundaries() {
    assert_executes(&module(vec![
        entry(
            vec![
                bind(3, partial("User.helper", &[])),
                bind(4, call("User.invoke", &[3, 1, 2])),
            ],
            4,
        ),
        function(
            "User.invoke",
            &[10, 11, 12],
            vec![bind(
                13,
                IrExpr::Ap {
                    x: 10,
                    args: vec![IrArg::Var(11), IrArg::Var(12)],
                },
            )],
            IrTerminal::Ret(IrArg::Var(13)),
        ),
        helper(),
    ]));
    assert_executes(&module(vec![
        entry(
            vec![
                bind(3, partial("User.helper", &[1])),
                bind(4, call("User.invoke", &[3, 2])),
            ],
            4,
        ),
        function(
            "User.invoke",
            &[10, 11],
            vec![bind(
                12,
                IrExpr::Ap {
                    x: 10,
                    args: vec![IrArg::Var(11)],
                },
            )],
            IrTerminal::Ret(IrArg::Var(12)),
        ),
        helper(),
    ]));
}

#[test]
fn join_parameters_propagate_context_and_refuse_methods_observation() {
    let joined = |field| {
        module(vec![function(
            "User.macro",
            &[0, 1, 2],
            vec![IrStmt::JDecl {
                j: 3,
                params: params(&[4, 5]),
                value: IrBody {
                    stmts: vec![bind(6, IrExpr::Proj { i: field, x: 4 }), bind(7, ok(6, 5))],
                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(7))),
                },
            }],
            IrTerminal::Jmp {
                j: 3,
                args: vec![IrArg::Var(1), IrArg::Var(2)],
            },
        )])
    };
    assert_executes(&joined(5));
    assert!(matches!(
        checked(&joined(layout::MACRO_CONTEXT_METHODS_FIELD), 10_000),
        Err(IrExecutionError::Unsupported {
            form: OBSERVATION,
            ..
        })
    ));
}

#[test]
fn helpers_cannot_inspect_reinterpret_store_mutate_or_return_the_carrier() {
    let expressions = [
        IrExpr::Proj {
            i: layout::MACRO_CONTEXT_METHODS_FIELD,
            x: 10,
        },
        IrExpr::Proj {
            i: layout::MACRO_CONTEXT.object_fields as u64,
            x: 10,
        },
        IrExpr::UProj { i: 1, x: 10 },
        IrExpr::SProj {
            n: 0,
            offset: 0,
            x: 10,
        },
        IrExpr::Box {
            ty: IrType::TObject,
            x: 10,
        },
        IrExpr::Unbox { x: 10 },
        IrExpr::Reset { n: 1, x: 10 },
        IrExpr::IsShared { x: 10 },
        call("Nat.add", &[10, 11]),
        partial("Lean.Macro.getMethods", &[10]),
        IrExpr::Ap {
            x: 10,
            args: vec![],
        },
        ok(10, 11),
    ];
    for expression in expressions {
        let module = module(vec![
            entry(vec![bind(3, call("User.helper", &[1, 2]))], 3),
            function(
                "User.helper",
                &[10, 11],
                vec![bind(12, expression.clone())],
                IrTerminal::Ret(IrArg::Var(12)),
            ),
        ]);
        assert!(checked(&module, 10_000).is_err(), "accepted {expression:?}");
    }
    let statements = [
        IrStmt::Set {
            x: 10,
            i: 1,
            y: IrArg::Var(11),
        },
        IrStmt::Set {
            x: 11,
            i: 0,
            y: IrArg::Var(10),
        },
        IrStmt::SetTag { x: 10, cidx: 0 },
        IrStmt::USet { x: 10, i: 0, y: 11 },
        IrStmt::SSet {
            x: 11,
            i: 0,
            offset: 0,
            y: 10,
            ty: IrType::USize,
        },
    ];
    for statement in statements {
        let module = module(vec![
            entry(vec![bind(3, call("User.helper", &[1, 2]))], 3),
            function(
                "User.helper",
                &[10, 11],
                vec![statement.clone()],
                IrTerminal::Ret(IrArg::Var(11)),
            ),
        ]);
        assert!(checked(&module, 10_000).is_err(), "accepted {statement:?}");
    }
    let terminals = [
        IrTerminal::Ret(IrArg::Var(10)),
        IrTerminal::Case {
            type_name: name("Lean.Macro.Context"),
            x: 10,
            x_type: IrType::TObject,
            alts: vec![IrAlt::Default {
                body: IrBody {
                    stmts: vec![],
                    terminal: Box::new(IrTerminal::Ret(IrArg::Var(11))),
                },
            }],
        },
    ];
    for terminal in terminals {
        let module = module(vec![
            entry(vec![bind(3, call("User.helper", &[1, 2]))], 3),
            function("User.helper", &[10, 11], vec![], terminal.clone()),
        ]);
        assert!(checked(&module, 10_000).is_err(), "accepted {terminal:?}");
    }
}

#[test]
fn closures_cannot_hide_context_from_return_or_unknown_indirect_calls() {
    let escaping = module(vec![
        entry(vec![bind(3, partial("User.helper", &[1]))], 3),
        helper(),
    ]);
    assert!(checked(&escaping, 10_000).is_err());
    let unknown = module(vec![entry(
        vec![bind(
            3,
            IrExpr::Ap {
                x: 0,
                args: vec![IrArg::Var(1), IrArg::Var(2)],
            },
        )],
        3,
    )]);
    assert!(checked(&unknown, 10_000).is_err());
    let callback = module(vec![
        entry(vec![bind(3, call("User.invoke", &[0, 1, 2]))], 3),
        function(
            "User.invoke",
            &[10, 11, 12],
            vec![bind(
                13,
                IrExpr::Ap {
                    x: 10,
                    args: vec![IrArg::Var(11), IrArg::Var(12)],
                },
            )],
            IrTerminal::Ret(IrArg::Var(13)),
        ),
    ]);
    assert!(checked(&callback, 10_000).is_err());
    let hidden = module(vec![
        entry(
            vec![bind(3, partial("User.helper", &[1])), bind(4, ok(3, 2))],
            4,
        ),
        helper(),
    ]);
    assert!(checked(&hidden, 10_000).is_err());
}

#[test]
fn recursive_function_signatures_are_cached_and_work_exhaustion_is_explicit() {
    let module = module(vec![
        entry(vec![bind(3, call("User.first", &[1, 2]))], 3),
        function(
            "User.first",
            &[10, 11],
            vec![bind(12, call("User.second", &[10, 11]))],
            IrTerminal::Ret(IrArg::Var(12)),
        ),
        function(
            "User.second",
            &[10, 11],
            vec![bind(12, call("User.first", &[10, 11]))],
            IrTerminal::Ret(IrArg::Var(12)),
        ),
    ]);
    checked(&module, 1_000).unwrap();
    let error = checked(&module, 0).unwrap_err();
    assert!(matches!(
        error,
        IrExecutionError::Limit("macro context confinement work")
    ));
    assert!(error.is_resource());
}

#[test]
fn native_context_method_policy_is_exact_and_position_specific() {
    let analyzer = Analyzer {
        declarations: BTreeMap::new(),
        closures: Vec::new(),
        closure_ids: BTreeMap::new(),
        pending: Vec::new(),
        seen: BTreeSet::new(),
        remaining: 1_000,
    };
    let owner = name("User.macro");
    // Printed dots are not structural Name component boundaries.
    assert!(
        analyzer
            .native_arguments(
                &owner,
                &Name::from_components(["Lean.Macro.getCurrNamespace"]),
                &[Value::Context, Value::Plain],
            )
            .is_err()
    );
    for (function, arguments) in [
        (
            "Lean.Macro.getCurrNamespace",
            vec![Value::Context, Value::Plain],
        ),
        (
            "Lean.Macro.hasDecl",
            vec![Value::Plain, Value::Context, Value::Plain],
        ),
    ] {
        analyzer
            .native_arguments(&owner, &name(function), &arguments)
            .unwrap();
    }
    for (function, arguments) in [
        (
            "Lean.Macro.getCurrNamespace",
            vec![Value::Plain, Value::Context],
        ),
        (
            "Lean.Macro.hasDecl",
            vec![Value::Context, Value::Plain, Value::Plain],
        ),
        (
            "Lean.Macro.hasDecl",
            vec![Value::Plain, Value::Plain, Value::Context],
        ),
        (
            "Lean.Macro.hasDecl",
            vec![Value::Context, Value::Context, Value::Plain],
        ),
        (
            "Lean.Macro.hasDecl",
            vec![Value::Plain, Value::Mixed, Value::Plain],
        ),
        ("Lean.Macro.getMethods", vec![Value::Context, Value::Plain]),
        ("Lean.Macro.mkMethods", vec![Value::Context, Value::Plain]),
        (
            "Lean.Macro.hasDecl._redArg",
            vec![Value::Plain, Value::Context],
        ),
        ("User.hasDecl", vec![Value::Plain, Value::Context]),
    ] {
        assert!(
            analyzer
                .native_arguments(&owner, &name(function), &arguments)
                .is_err(),
            "accepted {function} {arguments:?}"
        );
    }
}

#[test]
fn only_selected_reference_declarations_can_receive_context() {
    let module = module(vec![
        entry(vec![bind(3, call("User.helper", &[1, 2]))], 3),
        helper(),
    ]);
    let selected = [ReferenceFunction {
        name: name("User.macro"),
        function: FunctionId::new(0),
    }];
    assert!(check(&[module], &name("User.macro"), &selected, 10_000).is_err());
}
