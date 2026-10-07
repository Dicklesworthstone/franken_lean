//! The structural validator feeds the existing IR graph, not a duplicate engine.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_olean::ir::{
    IrArg, IrBody, IrDecl, IrExpr, IrModule, IrParam, IrStmt, IrTerminal, IrType,
};
use fln_olean::ir::graph::IrNodeKind;
use fln_olean::ir_validate::{
    IrValidatedGraphError, IrValidationErrorKind, IrValidationLimits,
    build_validated_ir_call_graph,
};
use std::collections::BTreeMap;

fn name(text: &str) -> Name {
    Name::from_components(text.split('.'))
}

fn function(text: &str, arity: u64, stmts: Vec<IrStmt>, result: IrArg) -> IrDecl {
    IrDecl::Function {
        name: name(text),
        params: (0..arity)
            .map(|x| IrParam { x, borrow: false, ty: IrType::Object })
            .collect(),
        result: IrType::Object,
        body: IrBody { stmts, terminal: Box::new(IrTerminal::Ret(result)) },
        sorry_dep: None,
    }
}

fn bind(x: u64, expr: IrExpr) -> IrStmt {
    IrStmt::VDecl { x, ty: IrType::Object, expr }
}

fn module(decls: Vec<IrDecl>) -> IrModule {
    IrModule { decls, uninterpreted: vec![] }
}

#[test]
fn validated_graph_preserves_module_labels_and_reports_indirect_calls() {
    let app = module(vec![function(
        "App.main",
        1,
        vec![
            bind(1, IrExpr::Pap { function: name("Library.run"), args: vec![IrArg::Var(0)] }),
            bind(2, IrExpr::Ap { x: 1, args: vec![IrArg::Var(0)] }),
        ],
        IrArg::Var(2),
    )]);
    let library = module(vec![function("Library.run", 2, vec![], IrArg::Var(0))]);
    let checked = build_validated_ir_call_graph(
        &[("App", &app), ("Library", &library)],
        &BTreeMap::new(),
        IrValidationLimits::default(),
    ).unwrap();
    let graph = checked.graph();
    let caller = graph.node(&name("App.main")).unwrap();
    let callee = graph.node(&name("Library.run")).unwrap();
    assert_eq!(graph.module(caller), Some("App"));
    assert_eq!(graph.module(callee), Some("Library"));
    assert_eq!(graph.callees(caller), &[callee]);
    assert_eq!(graph.edge_count(), 1);
    assert_eq!(checked.summary().dynamic_calls, 1);
    assert_eq!(checked.summary().declarations, 2);
    assert_eq!(graph.duplicates().count(), 0);
}

#[test]
fn strict_entry_refuses_duplicates_instead_of_first_declaration_wins() {
    let first = module(vec![function("Main", 0, vec![], IrArg::Erased)]);
    let second = first.clone();
    let failure = build_validated_ir_call_graph(
        &[("first", &first), ("second", &second)],
        &BTreeMap::new(),
        IrValidationLimits::default(),
    ).unwrap_err();
    let IrValidatedGraphError::Validation(error) = failure else {
        panic!(/* ubs:ignore -- test-only diagnostic. */ "expected structural validation refusal");
    };
    assert_eq!(error.kind, IrValidationErrorKind::DuplicateDeclaration { name: name("Main") });
}

#[test]
fn unreachable_invalid_body_prevents_a_successful_graph_result() {
    let inputs = module(vec![
        function("Entry", 0, vec![], IrArg::Erased),
        function("Unused", 0, vec![], IrArg::Var(42)),
    ]);
    let failure = build_validated_ir_call_graph(
        &[("App", &inputs)],
        &BTreeMap::new(),
        IrValidationLimits::default(),
    ).unwrap_err();
    let IrValidatedGraphError::Validation(error) = failure else {
        panic!(/* ubs:ignore -- test-only diagnostic. */ "expected structural validation refusal");
    };
    assert_eq!(error.declaration, Some(name("Unused")));
    assert_eq!(error.kind, IrValidationErrorKind::UnknownVariable { index: 42 });
}

#[test]
fn census_signature_resolves_a_call_without_inventing_an_ir_body() {
    let inputs = module(vec![function(
        "Main",
        0,
        vec![bind(0, IrExpr::Fap { function: name("Native"), args: vec![IrArg::Erased] })],
        IrArg::Var(0),
    )]);
    let missing = build_validated_ir_call_graph(
        &[("App", &inputs)],
        &BTreeMap::new(),
        IrValidationLimits::default(),
    ).unwrap_err();
    let IrValidatedGraphError::Validation(error) = missing else {
        panic!(/* ubs:ignore -- test-only diagnostic. */ "expected missing-callee refusal");
    };
    assert_eq!(error.kind, IrValidationErrorKind::UnknownCallee { name: name("Native") });
    let checked = build_validated_ir_call_graph(
        &[("App", &inputs)],
        &BTreeMap::from([(name("Native"), 1)]),
        IrValidationLimits::default(),
    ).unwrap();
    let graph = checked.graph();
    let external = graph.node(&name("Native")).unwrap();
    assert_eq!(graph.kind(external), IrNodeKind::Undeclared);
    assert_eq!(graph.module(external), None);
    assert_eq!(checked.summary().census_signatures, 1);
}

#[test]
fn cross_module_recursive_functions_validate_before_graph_construction() {
    let make = |caller: &str, callee: &str| module(vec![function(
        caller,
        1,
        vec![bind(1, IrExpr::Fap { function: name(callee), args: vec![IrArg::Var(0)] })],
        IrArg::Var(1),
    )]);
    let a = make("A.run", "B.run");
    let b = make("B.run", "A.run");
    let checked = build_validated_ir_call_graph(
        &[("A", &a), ("B", &b)],
        &BTreeMap::new(),
        IrValidationLimits::default(),
    ).unwrap();
    let graph = checked.graph();
    let root = graph.node(&name("A.run")).unwrap();
    assert_eq!(graph.edge_count(), 2);
    assert_eq!(graph.reach([root], |_| true), vec![true, true]);
}

#[test]
fn resource_refusal_leaves_the_input_unchanged_and_returns_no_graph() {
    let inputs = module(vec![function("Main", 0, vec![], IrArg::Erased)]);
    let original = inputs.clone();
    let failure = build_validated_ir_call_graph(
        &[("App", &inputs)],
        &BTreeMap::new(),
        IrValidationLimits { max_work: 0, ..IrValidationLimits::default() },
    ).unwrap_err();
    assert!(failure.is_resource());
    assert_eq!(inputs, original);
}
