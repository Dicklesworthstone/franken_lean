//! Structural IR validation. These tests do not claim IR type checking or
//! permission to execute Reference-produced code.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_olean::ir::{
    IrAlt, IrArg, IrBody, IrCtorInfo, IrDecl, IrExpr, IrExternEntry, IrLit, IrModule, IrNat,
    IrParam, IrStmt, IrTerminal, IrType,
};
use fln_olean::ir_validate::{
    IrCallTarget, IrValidationError, IrValidationErrorKind as Kind, IrValidationLimits,
    IrValidationSummary, validate_ir,
};
use std::collections::BTreeMap;

fn name(text: &str) -> Name { Name::from_components(text.split('.')) }
fn var(x: u64) -> IrArg { IrArg::Var(x) }
fn params(ids: &[u64]) -> Vec<IrParam> {
    ids.iter().map(|&x| IrParam { x, borrow: false, ty: IrType::Object }).collect()
}
fn body(stmts: Vec<IrStmt>, terminal: IrTerminal) -> IrBody {
    IrBody { stmts, terminal: Box::new(terminal) }
}
fn function(n: &str, ids: &[u64], value: IrBody) -> IrDecl {
    IrDecl::Function {
        name: name(n), params: params(ids), result: IrType::Object,
        body: value, sorry_dep: None,
    }
}
fn external(n: &str, ids: &[u64]) -> IrDecl {
    IrDecl::Extern {
        name: name(n), params: params(ids), result: IrType::Object,
        entries: vec![IrExternEntry::Opaque],
    }
}
fn constant(x: u64) -> IrStmt {
    bind(x, IrExpr::Lit(IrLit::Num(IrNat::Small(7))))
}
fn bind(x: u64, expr: IrExpr) -> IrStmt { IrStmt::VDecl { x, ty: IrType::Object, expr } }
fn module(decls: Vec<IrDecl>) -> IrModule { IrModule { decls, uninterpreted: vec![] } }
fn run(decls: Vec<IrDecl>) -> Result<IrValidationSummary, IrValidationError> {
    validate_ir(&[module(decls)], &BTreeMap::new(), IrValidationLimits::default())
}
fn main_body(stmts: Vec<IrStmt>, terminal: IrTerminal) -> IrDecl {
    function("Main", &[0], body(stmts, terminal))
}
fn target() -> IrDecl { function("Target", &[0, 1], body(vec![], IrTerminal::Ret(var(0)))) }
fn ctor() -> IrCtorInfo {
    IrCtorInfo { name: name("Pair.mk"), cidx: 0, size: 2, usize: 0, ssize: 0 }
}
fn case(arms: Vec<IrBody>) -> IrTerminal {
    IrTerminal::Case {
        type_name: name("Choice"), x: 0, x_type: IrType::Object,
        alts: arms.into_iter().enumerate().map(|(i, body)| {
            let mut info = ctor(); info.cidx = i as u64;
            IrAlt::Ctor { info, body }
        }).collect(),
    }
}
fn assert_kind(decls: Vec<IrDecl>, expected: Kind) {
    let failure = run(decls).expect_err("malformed IR must be refused");
    assert!(failure.declaration.is_some(), "refusal must identify its declaration");
    assert_eq!(failure.kind, expected);
}

#[test]
fn definition_must_precede_use_and_its_initializer_cannot_see_it() {
    assert_kind(
        vec![main_body(vec![bind(1, IrExpr::Proj { i: 0, x: 1 })], IrTerminal::Ret(var(1)))],
        Kind::UnknownVariable { index: 1 },
    );
    assert_kind(
        vec![main_body(vec![bind(1, IrExpr::Proj { i: 0, x: 2 }), constant(2)], IrTerminal::Ret(var(1)))],
        Kind::UnknownVariable { index: 2 },
    );
    run(vec![main_body(vec![constant(1)], IrTerminal::Ret(var(1)))]).unwrap();
}

#[test]
fn all_expression_variable_operands_are_checked() {
    let expressions = vec![
        IrExpr::Ctor { info: ctor(), args: vec![var(99)] },
        IrExpr::Reset { n: 1, x: 99 },
        IrExpr::Reuse { x: 99, info: ctor(), update_header: true, args: vec![] },
        IrExpr::Reuse { x: 0, info: ctor(), update_header: false, args: vec![var(99)] },
        IrExpr::Proj { i: 0, x: 99 },
        IrExpr::UProj { i: 0, x: 99 },
        IrExpr::SProj { n: 0, offset: 0, x: 99 },
        IrExpr::Fap { function: name("Target"), args: vec![var(0), var(99)] },
        IrExpr::Pap { function: name("Target"), args: vec![var(99)] },
        IrExpr::Ap { x: 99, args: vec![] },
        IrExpr::Ap { x: 0, args: vec![var(99)] },
        IrExpr::Box { ty: IrType::UInt64, x: 99 },
        IrExpr::Unbox { x: 99 },
        IrExpr::IsShared { x: 99 },
    ];
    for expr in expressions {
        assert_kind(
            vec![main_body(vec![bind(1, expr)], IrTerminal::Ret(var(1))), target()],
            Kind::UnknownVariable { index: 99 },
        );
    }
}

#[test]
fn all_statement_variable_operands_are_checked() {
    let statements = vec![
        IrStmt::Set { x: 99, i: 0, y: var(0) },
        IrStmt::Set { x: 0, i: 0, y: var(99) },
        IrStmt::USet { x: 99, i: 0, y: 0 },
        IrStmt::USet { x: 0, i: 0, y: 99 },
        IrStmt::SSet { x: 99, i: 0, offset: 0, y: 0, ty: IrType::UInt8 },
        IrStmt::SSet { x: 0, i: 0, offset: 0, y: 99, ty: IrType::UInt8 },
        IrStmt::SetTag { x: 99, cidx: 0 },
        IrStmt::Inc { x: 99, n: 1, checked: true, persistent: false },
        IrStmt::Dec { x: 99, n: 1, checked: false, persistent: true },
        IrStmt::Del { x: 99 },
    ];
    for stmt in statements {
        assert_kind(vec![main_body(vec![stmt], IrTerminal::Ret(var(0)))], Kind::UnknownVariable { index: 99 });
    }
}

#[test]
fn all_expression_and_statement_forms_have_positive_scope_controls() {
    let expressions = vec![
        IrExpr::Ctor { info: ctor(), args: vec![var(0), IrArg::Erased] },
        IrExpr::Reset { n: 1, x: 0 },
        IrExpr::Reuse { x: 0, info: ctor(), update_header: true, args: vec![var(0)] },
        IrExpr::Proj { i: 0, x: 0 }, IrExpr::UProj { i: 0, x: 0 },
        IrExpr::SProj { n: 0, offset: 0, x: 0 },
        IrExpr::Fap { function: name("Target"), args: vec![var(0), IrArg::Erased] },
        IrExpr::Pap { function: name("Target"), args: vec![var(0)] },
        IrExpr::Ap { x: 0, args: vec![var(0)] },
        IrExpr::Box { ty: IrType::UInt8, x: 0 }, IrExpr::Unbox { x: 0 },
        IrExpr::IsShared { x: 0 }, IrExpr::Lit(IrLit::Str("text".into())),
    ];
    let mut stmts: Vec<_> = expressions.into_iter().enumerate().map(|(i, e)| bind(i as u64 + 1, e)).collect();
    stmts.extend([
        IrStmt::Set { x: 0, i: 0, y: IrArg::Erased },
        IrStmt::SetTag { x: 0, cidx: 0 },
        IrStmt::USet { x: 0, i: 0, y: 0 },
        IrStmt::SSet { x: 0, i: 0, offset: 0, y: 0, ty: IrType::UInt8 },
        IrStmt::Inc { x: 0, n: 1, checked: true, persistent: true },
        IrStmt::Dec { x: 0, n: 1, checked: false, persistent: false },
        IrStmt::Del { x: 0 },
    ]);
    let report = run(vec![main_body(stmts, IrTerminal::Ret(IrArg::Erased)), target()]).unwrap();
    assert_eq!(report.dynamic_calls, 1);
    assert_eq!(report.declarations, 2);
}

#[test]
fn terminals_check_their_variables() {
    assert_kind(vec![main_body(vec![], IrTerminal::Ret(var(99)))], Kind::UnknownVariable { index: 99 });
    assert_kind(vec![main_body(vec![], IrTerminal::Case {
        type_name: name("Choice"), x: 99, x_type: IrType::Object, alts: vec![],
    })], Kind::UnknownVariable { index: 99 });
    run(vec![main_body(vec![], IrTerminal::Unreachable)]).unwrap();
}

#[test]
fn join_scope_is_value_then_continuation_not_recursive() {
    let join = IrStmt::JDecl { j: 10, params: params(&[1]), value: body(vec![], IrTerminal::Ret(var(1))) };
    run(vec![main_body(vec![join], IrTerminal::Jmp { j: 10, args: vec![var(0)] })]).unwrap();
    let recursive = IrStmt::JDecl {
        j: 10, params: params(&[1]),
        value: body(vec![], IrTerminal::Jmp { j: 10, args: vec![var(1)] }),
    };
    assert_kind(vec![main_body(vec![recursive], IrTerminal::Ret(var(0)))], Kind::UnknownJoinPoint { index: 10 });
}

#[test]
fn joins_capture_outer_variables_and_previously_declared_joins() {
    let first = IrStmt::JDecl { j: 10, params: params(&[1]), value: body(vec![], IrTerminal::Ret(var(0))) };
    let second = IrStmt::JDecl {
        j: 11, params: params(&[2]), value: body(vec![], IrTerminal::Jmp { j: 10, args: vec![var(2)] }),
    };
    run(vec![main_body(vec![first, second], IrTerminal::Jmp { j: 11, args: vec![var(0)] })]).unwrap();
}

#[test]
fn join_parameters_and_locals_do_not_escape() {
    for index in [1, 2] {
        let join = IrStmt::JDecl {
            j: 10, params: params(&[1]), value: body(vec![constant(2)], IrTerminal::Ret(var(2))),
        };
        assert_kind(vec![main_body(vec![join], IrTerminal::Ret(var(index)))], Kind::UnknownVariable { index });
    }
}

#[test]
fn nested_and_forward_joins_do_not_escape_scope() {
    let inner = IrStmt::JDecl { j: 20, params: vec![], value: body(vec![], IrTerminal::Ret(var(0))) };
    let outer = IrStmt::JDecl {
        j: 10, params: vec![], value: body(vec![inner], IrTerminal::Jmp { j: 20, args: vec![] }),
    };
    assert_kind(vec![main_body(vec![outer], IrTerminal::Jmp { j: 20, args: vec![] })], Kind::UnknownJoinPoint { index: 20 });
    let first = IrStmt::JDecl {
        j: 10, params: vec![], value: body(vec![], IrTerminal::Jmp { j: 11, args: vec![] }),
    };
    let later = IrStmt::JDecl { j: 11, params: vec![], value: body(vec![], IrTerminal::Ret(var(0))) };
    assert_kind(vec![main_body(vec![first, later], IrTerminal::Ret(var(0)))], Kind::UnknownJoinPoint { index: 11 });
}

#[test]
fn variable_and_join_namespaces_are_distinct_but_indices_globally_unique() {
    assert_kind(vec![main_body(vec![], IrTerminal::Jmp { j: 0, args: vec![] })], Kind::UnknownJoinPoint { index: 0 });
    let join = IrStmt::JDecl { j: 10, params: vec![], value: body(vec![], IrTerminal::Ret(var(0))) };
    assert_kind(vec![main_body(vec![join], IrTerminal::Ret(var(10)))], Kind::UnknownVariable { index: 10 });
    let collision = IrStmt::JDecl { j: 0, params: vec![], value: body(vec![], IrTerminal::Ret(IrArg::Erased)) };
    assert_kind(vec![main_body(vec![collision], IrTerminal::Ret(var(0)))], Kind::DuplicateIndex { index: 0 });
}

#[test]
fn case_arms_restore_locals_but_not_global_index_uniqueness() {
    let first = body(vec![constant(1)], IrTerminal::Ret(var(1)));
    let second = body(vec![constant(2)], IrTerminal::Ret(var(2)));
    run(vec![main_body(vec![], case(vec![first.clone(), second]))]).unwrap();
    assert_kind(vec![main_body(vec![], case(vec![first.clone(), body(vec![], IrTerminal::Ret(var(1)))]))], Kind::UnknownVariable { index: 1 });
    assert_kind(vec![main_body(vec![], case(vec![first.clone(), first]))], Kind::DuplicateIndex { index: 1 });
}

#[test]
fn case_arms_can_jump_to_enclosing_join_with_capture() {
    let join = IrStmt::JDecl { j: 10, params: params(&[1]), value: body(vec![], IrTerminal::Ret(var(1))) };
    let arm = body(vec![], IrTerminal::Jmp { j: 10, args: vec![var(0)] });
    run(vec![main_body(vec![join], case(vec![arm.clone(), arm]))]).unwrap();
}

#[test]
fn default_arm_is_validated_and_cannot_leak_into_a_sibling() {
    let terminal = IrTerminal::Case {
        type_name: name("Choice"), x: 0, x_type: IrType::Object,
        alts: vec![
            IrAlt::Default { body: body(vec![constant(1)], IrTerminal::Ret(var(1))) },
            IrAlt::Ctor { info: ctor(), body: body(vec![], IrTerminal::Ret(var(1))) },
        ],
    };
    assert_kind(vec![main_body(vec![], terminal)], Kind::UnknownVariable { index: 1 });
}

#[test]
fn jump_arity_and_arguments_are_checked() {
    for args in [vec![], vec![var(0), var(0)]] {
        let provided = args.len();
        let join = IrStmt::JDecl { j: 10, params: params(&[1]), value: body(vec![], IrTerminal::Ret(var(1))) };
        assert_kind(vec![main_body(vec![join], IrTerminal::Jmp { j: 10, args })], Kind::Arity {
            target: IrCallTarget::JoinPoint(10), provided, expected: 1, partial: false,
        });
    }
    let join = IrStmt::JDecl { j: 10, params: params(&[1]), value: body(vec![], IrTerminal::Ret(var(1))) };
    assert_kind(vec![main_body(vec![join], IrTerminal::Jmp { j: 10, args: vec![var(99)] })], Kind::UnknownVariable { index: 99 });
}

#[test]
fn parameters_and_binders_cannot_reuse_an_index() {
    assert_kind(vec![function("Main", &[0, 0], body(vec![], IrTerminal::Ret(var(0))))], Kind::DuplicateIndex { index: 0 });
    assert_kind(vec![main_body(vec![constant(0)], IrTerminal::Ret(var(0)))], Kind::DuplicateIndex { index: 0 });
    assert_kind(vec![external("Main", &[0, 0])], Kind::DuplicateIndex { index: 0 });
    let join = IrStmt::JDecl { j: 10, params: params(&[10]), value: body(vec![], IrTerminal::Ret(var(10))) };
    assert_kind(vec![main_body(vec![join], IrTerminal::Ret(var(0)))], Kind::DuplicateIndex { index: 10 });
}

#[test]
fn function_recursion_and_cross_module_forward_references_are_legal() {
    let f = function("F", &[0], body(vec![bind(1, IrExpr::Fap { function: name("G"), args: vec![var(0)] })], IrTerminal::Ret(var(1))));
    let g = function("G", &[0], body(vec![bind(1, IrExpr::Fap { function: name("F"), args: vec![var(0)] })], IrTerminal::Ret(var(1))));
    let modules = [module(vec![g]), module(vec![f])];
    assert_eq!(validate_ir(&modules, &BTreeMap::new(), IrValidationLimits::default()).unwrap().declarations, 2);
}

#[test]
fn duplicate_declarations_are_not_resolved_by_last_writer_wins() {
    let f = main_body(vec![], IrTerminal::Ret(var(0)));
    let modules = [module(vec![f.clone()]), module(vec![f])];
    assert_eq!(validate_ir(&modules, &BTreeMap::new(), IrValidationLimits::default()).unwrap_err().kind, Kind::DuplicateDeclaration { name: name("Main") });
}

#[test]
fn unknown_callees_fail_for_both_full_and_partial_applications() {
    for expr in [
        IrExpr::Fap { function: name("Absent"), args: vec![] },
        IrExpr::Pap { function: name("Absent"), args: vec![] },
    ] {
        assert_kind(vec![main_body(vec![bind(1, expr)], IrTerminal::Ret(var(1)))], Kind::UnknownCallee { name: name("Absent") });
    }
}

#[test]
fn full_calls_require_exact_arity_partial_calls_require_strictly_less() {
    for (partial, provided) in [(false, 1), (false, 3), (true, 2), (true, 3)] {
        let args = vec![IrArg::Erased; provided];
        let expr = if partial { IrExpr::Pap { function: name("Target"), args } } else { IrExpr::Fap { function: name("Target"), args } };
        assert_kind(vec![main_body(vec![bind(1, expr)], IrTerminal::Ret(var(1))), target()], Kind::Arity {
            target: IrCallTarget::Declaration(name("Target")), provided, expected: 2, partial,
        });
    }
}

#[test]
fn zero_arity_full_call_is_legal_but_partial_call_is_not() {
    let zero = external("Zero", &[]);
    let full = IrExpr::Fap { function: name("Zero"), args: vec![] };
    run(vec![main_body(vec![bind(1, full)], IrTerminal::Ret(var(1))), zero.clone()]).unwrap();
    let partial = IrExpr::Pap { function: name("Zero"), args: vec![] };
    assert_kind(vec![main_body(vec![bind(1, partial)], IrTerminal::Ret(var(1))), zero], Kind::Arity {
        target: IrCallTarget::Declaration(name("Zero")), provided: 0, expected: 0, partial: true,
    });
}

#[test]
fn explicit_census_signature_closes_an_external_call() {
    let call = IrExpr::Fap { function: name("Native.foo"), args: vec![var(0)] };
    let modules = [module(vec![main_body(vec![bind(1, call)], IrTerminal::Ret(var(1)))])];
    let census = BTreeMap::from([(name("Native.foo"), 1)]);
    let report = validate_ir(&modules, &census, IrValidationLimits::default()).unwrap();
    assert_eq!(report.census_signatures, 1);
    assert_eq!(report.extern_declarations, 0);
    let wrong = BTreeMap::from([(name("Native.foo"), 2)]);
    assert!(matches!(validate_ir(&modules, &wrong, IrValidationLimits::default()).unwrap_err().kind, Kind::Arity { .. }));
}

#[test]
fn census_cannot_shadow_functions_or_disagree_with_ir_extern_arity() {
    let census = BTreeMap::from([(name("Main"), 1)]);
    let modules = [module(vec![main_body(vec![], IrTerminal::Ret(var(0)))])];
    assert_eq!(validate_ir(&modules, &census, IrValidationLimits::default()).unwrap_err().kind, Kind::ExternalShadowsFunction { name: name("Main") });
    let modules = [module(vec![external("Main", &[0])])];
    validate_ir(&modules, &census, IrValidationLimits::default()).unwrap();
    let wrong = BTreeMap::from([(name("Main"), 2)]);
    assert_eq!(validate_ir(&modules, &wrong, IrValidationLimits::default()).unwrap_err().kind, Kind::ConflictingExternalArity { name: name("Main"), ir: 1, census: 2 });
}

#[test]
fn failure_order_for_distinct_bodies_is_independent_of_module_order() {
    let a = module(vec![function("A", &[], body(vec![], IrTerminal::Ret(var(99))))]);
    let b = module(vec![function("B", &[], body(vec![], IrTerminal::Jmp { j: 88, args: vec![] }))]);
    let first = validate_ir(&[a.clone(), b.clone()], &BTreeMap::new(), IrValidationLimits::default()).unwrap_err();
    let second = validate_ir(&[b, a], &BTreeMap::new(), IrValidationLimits::default()).unwrap_err();
    assert_eq!(first, second);
    assert_eq!(first.declaration, Some(std::cmp::min(name("A"), name("B"))));
}

#[test]
fn work_budget_accepts_exact_boundary_and_refuses_one_less_without_mutation() {
    let modules = [module(vec![main_body(vec![constant(1), constant(2)], IrTerminal::Ret(var(2)))])];
    let original = modules.clone();
    let work = validate_ir(&modules, &BTreeMap::new(), IrValidationLimits::default()).unwrap().work;
    let exact = IrValidationLimits { max_work: work, ..IrValidationLimits::default() };
    validate_ir(&modules, &BTreeMap::new(), exact).unwrap();
    let below = IrValidationLimits { max_work: work - 1, ..exact };
    let failure = validate_ir(&modules, &BTreeMap::new(), below).unwrap_err();
    assert!(failure.is_resource());
    assert_eq!(failure.kind, Kind::Limit { resource: "work" });
    assert_eq!(modules, original);
}

#[test]
fn declarations_and_census_entries_share_the_index_budget() {
    let modules = [module(vec![external("Main", &[0])])];
    let census = BTreeMap::from([(name("Main"), 1)]);
    let exact = IrValidationLimits { max_declarations: 2, ..IrValidationLimits::default() };
    validate_ir(&modules, &census, exact).unwrap();
    let below = IrValidationLimits { max_declarations: 1, ..exact };
    assert_eq!(validate_ir(&modules, &census, below).unwrap_err().kind, Kind::Limit { resource: "declarations" });
}

#[test]
fn empty_modules_still_consume_budget() {
    let modules = [IrModule::default(), IrModule::default()];
    let limits = IrValidationLimits { max_work: 1, ..IrValidationLimits::default() };
    let failure = validate_ir(&modules, &BTreeMap::new(), limits).unwrap_err();
    assert!(failure.is_resource());
    assert!(failure.declaration.is_none());
}

#[test]
fn nesting_limit_includes_root_and_is_exact() {
    let join = IrStmt::JDecl { j: 10, params: vec![], value: body(vec![], IrTerminal::Ret(var(0))) };
    let modules = [module(vec![main_body(vec![join], IrTerminal::Ret(var(0)))])];
    let exact = IrValidationLimits { max_depth: 2, ..IrValidationLimits::default() };
    validate_ir(&modules, &BTreeMap::new(), exact).unwrap();
    let below = IrValidationLimits { max_depth: 1, ..exact };
    assert_eq!(validate_ir(&modules, &BTreeMap::new(), below).unwrap_err().kind, Kind::Limit { resource: "depth" });
    let root = [module(vec![main_body(vec![], IrTerminal::Ret(var(0)))])];
    let none = IrValidationLimits { max_depth: 0, ..exact };
    assert_eq!(validate_ir(&root, &BTreeMap::new(), none).unwrap_err().kind, Kind::Limit { resource: "depth" });
}

#[test]
fn long_flat_bodies_and_wide_cases_do_not_consume_recursive_depth() {
    let stmts = (1..=10_000).map(constant).collect();
    let modules = [module(vec![main_body(stmts, IrTerminal::Ret(var(10_000)))])];
    let limits = IrValidationLimits { max_depth: 1, ..IrValidationLimits::default() };
    assert_eq!(validate_ir(&modules, &BTreeMap::new(), limits).unwrap().statements, 10_000);
    let arms = (0..5_000).map(|_| body(vec![], IrTerminal::Ret(var(0)))).collect();
    let modules = [module(vec![main_body(vec![], case(arms))])];
    let limits = IrValidationLimits { max_depth: 2, ..limits };
    assert_eq!(validate_ir(&modules, &BTreeMap::new(), limits).unwrap().bodies, 5_001);
}

#[test]
fn sparse_maximum_index_does_not_size_an_array_from_the_index() {
    let declaration = function("Sparse", &[u64::MAX], body(vec![], IrTerminal::Ret(var(u64::MAX))));
    run(vec![declaration]).unwrap();
}

#[test]
fn borrow_flags_and_uninterpreted_extensions_are_not_mutated_or_promoted() {
    let mut declaration = external("External", &[0]);
    if let IrDecl::Extern { params, .. } = &mut declaration { params[0].borrow = true; }
    let modules = [IrModule { decls: vec![declaration], uninterpreted: vec![name("opaque.extension")] }];
    let original = modules.clone();
    let report = validate_ir(&modules, &BTreeMap::new(), IrValidationLimits::default()).unwrap();
    assert_eq!(report.extern_declarations, 1);
    assert_eq!(modules, original);
}

#[test]
fn real_nat_blt_fixture_refuses_its_missing_import_instead_of_inventing_a_signature() {
    use fln_olean::ir::{IrDecodeLimits, decode_ir};
    use fln_olean::region::{OleanView, WalkBudget};

    // Same committed Reference bytes and independent printout used by tests/ir.rs.
    // The printout starts Nat.blt with an application of Nat.add. This tests the
    // decode -> validation boundary, not the whole stdlib or a fabricated census.
    let bytes = include_bytes!("../fixtures/ir/Init.Data.Nat.Basic.ir");
    let view = OleanView::parse(bytes).unwrap();
    let blocks = view.extension_payloads(WalkBudget::default(), 1 << 30).unwrap();
    let decoded = decode_ir(&blocks, IrDecodeLimits::default()).unwrap();
    let declaration = decoded.decls.into_iter().find(|d| d.name() == &name("Nat.blt"))
        .expect("the pinned fixture contains Nat.blt");
    let failure = run(vec![declaration]).unwrap_err();
    assert_eq!(failure.declaration, Some(name("Nat.blt")));
    assert_eq!(failure.kind, Kind::UnknownCallee { name: name("Nat.add") });
}
