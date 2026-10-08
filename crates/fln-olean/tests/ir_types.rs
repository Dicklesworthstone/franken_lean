//! Pin-anchored expression representation rules; no ownership/execution claim.
#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_olean::ir::{
    IrAlt, IrArg, IrBody, IrCtorInfo, IrDecl, IrExpr, IrLit, IrModule, IrNat,
    IrParam, IrStmt, IrTerminal, IrType,
};
use fln_olean::ir_types::{IrTypeValidationError as Error, validate_ir_types};
use fln_olean::ir_validate::{IrValidationErrorKind, IrValidationLimits};
use std::collections::BTreeMap;

fn name(text: &str) -> Name { Name::from_components(text.split('.')) }
fn param(x: u64, ty: IrType) -> IrParam { IrParam { x, borrow: false, ty } }
fn body(stmts: Vec<IrStmt>, terminal: IrTerminal) -> IrBody {
    IrBody { stmts, terminal: Box::new(terminal) }
}
fn bind(x: u64, ty: IrType, expr: IrExpr) -> IrStmt { IrStmt::VDecl { x, ty, expr } }
fn function(params: Vec<IrParam>, body: IrBody) -> IrDecl {
    IrDecl::Function { name: name("Main"), params, result: IrType::TObject, body, sorry_dep: None }
}
fn module(decls: Vec<IrDecl>) -> IrModule { IrModule { decls, uninterpreted: vec![] } }
fn sample(source: IrType, result: IrType, expr: IrExpr) -> IrModule {
    module(vec![function(
        vec![param(0, source)],
        body(vec![bind(1, result, expr)], IrTerminal::Ret(IrArg::Var(1))),
    )])
}
fn check(source: IrType, result: IrType, expr: IrExpr) -> Result<(), Error> {
    let signatures = BTreeMap::from([(name("Target"), 2)]);
    validate_ir_types(&[sample(source, result, expr)], &signatures, IrValidationLimits::default()).map(|_| ())
}
fn rejected(source: IrType, result: IrType, expr: IrExpr, operation: &str) {
    let error = check(source, result, expr).expect_err("representation violation must be refused");
    match error {
        Error::Rule { declaration, binding, operation: found, .. } => {
            assert_eq!(declaration, name("Main"));
            assert_eq!(binding, 1);
            assert_eq!(found, operation);
        }
        other => panic!(/* ubs:ignore -- test-only diagnostic. */ "wrong refusal: {other:?}"),
    }
}
fn info(size: u64) -> IrCtorInfo {
    IrCtorInfo { name: name("C.mk"), cidx: 0, size, usize: 0, ssize: 0 }
}

#[test]
fn object_category_includes_void_but_not_erased_or_unboxed_scalars() {
    for source in [IrType::Object, IrType::TObject, IrType::Tagged, IrType::Void] {
        check(source, IrType::UInt8, IrExpr::IsShared { x: 0 }).unwrap();
    }
    for source in [IrType::Erased, IrType::UInt8, IrType::UInt64, IrType::Float, IrType::Float32] {
        rejected(source, IrType::UInt8, IrExpr::IsShared { x: 0 }, "isShared source");
    }
}

#[test]
fn boxing_accepts_every_scalar_and_preserves_the_exact_annotation() {
    for scalar in [IrType::Float, IrType::Float32, IrType::UInt8, IrType::UInt16,
        IrType::UInt32, IrType::UInt64, IrType::USize] {
        check(scalar.clone(), IrType::TObject, IrExpr::Box { ty: scalar, x: 0 }).unwrap();
    }
    rejected(IrType::UInt8, IrType::TObject, IrExpr::Box { ty: IrType::UInt64, x: 0 }, "box annotation");
    rejected(IrType::Object, IrType::TObject, IrExpr::Box { ty: IrType::Object, x: 0 }, "box source");
    rejected(IrType::UInt8, IrType::UInt8, IrExpr::Box { ty: IrType::UInt8, x: 0 }, "box result");
}

#[test]
fn unbox_requires_object_input_and_scalar_output() {
    check(IrType::Tagged, IrType::UInt64, IrExpr::Unbox { x: 0 }).unwrap();
    rejected(IrType::UInt8, IrType::UInt64, IrExpr::Unbox { x: 0 }, "unbox source");
    rejected(IrType::Object, IrType::TObject, IrExpr::Unbox { x: 0 }, "unbox result");
}

#[test]
fn closure_applications_require_boxed_source_and_result() {
    check(IrType::Object, IrType::TObject, IrExpr::Ap { x: 0, args: vec![] }).unwrap();
    rejected(IrType::UInt64, IrType::TObject, IrExpr::Ap { x: 0, args: vec![] }, "ap source");
    rejected(IrType::Object, IrType::UInt64, IrExpr::Ap { x: 0, args: vec![] }, "ap result");
    check(IrType::Object, IrType::Object, IrExpr::Pap { function: name("Target"), args: vec![] }).unwrap();
    rejected(IrType::Object, IrType::UInt8, IrExpr::Pap { function: name("Target"), args: vec![] }, "pap result");
}

#[test]
fn reset_and_reuse_enforce_object_representations_on_both_sides() {
    let expressions = [
        IrExpr::Reset { n: 1, x: 0 },
        IrExpr::Reuse { x: 0, info: info(1), update_header: true, args: vec![IrArg::Var(0)] },
    ];
    for expr in expressions {
        check(IrType::TObject, IrType::Object, expr.clone()).unwrap();
        rejected(IrType::UInt64, IrType::Object, expr.clone(), "reset/reuse source");
        rejected(IrType::Object, IrType::UInt64, expr, "reset/reuse result");
    }
}

#[test]
fn reference_constructors_require_objects_but_fieldless_forms_keep_the_pin_rule() {
    check(IrType::Object, IrType::Object, IrExpr::Ctor { info: info(1), args: vec![IrArg::Var(0)] }).unwrap();
    rejected(IrType::Object, IrType::UInt8, IrExpr::Ctor { info: info(1), args: vec![] }, "reference constructor result");
    let mut scalars = info(0);
    scalars.ssize = 8;
    rejected(IrType::Object, IrType::UInt8, IrExpr::Ctor { info: scalars, args: vec![] }, "reference constructor result");
    check(IrType::Object, IrType::Tagged, IrExpr::Ctor { info: info(0), args: vec![] }).unwrap();
}

#[test]
fn object_projection_and_tagged_projection_follow_different_rules() {
    check(IrType::Object, IrType::TObject, IrExpr::Proj { i: 0, x: 0 }).unwrap();
    check(IrType::Tagged, IrType::UInt8, IrExpr::Proj { i: 0, x: 0 }).unwrap();
    rejected(IrType::Object, IrType::UInt8, IrExpr::Proj { i: 0, x: 0 }, "proj result");
    rejected(IrType::Void, IrType::TObject, IrExpr::Proj { i: 0, x: 0 }, "proj source");
    rejected(IrType::UInt64, IrType::TObject, IrExpr::Proj { i: 0, x: 0 }, "proj source");
}

#[test]
fn aggregate_projection_checks_bounds_and_field_types_for_struct_and_union() {
    for source in [
        IrType::Struct { lean_type: None, types: vec![IrType::UInt8, IrType::USize] },
        IrType::Union { lean_type: name("Union"), types: vec![IrType::UInt8, IrType::USize] },
    ] {
        check(source.clone(), IrType::USize, IrExpr::Proj { i: 1, x: 0 }).unwrap();
        rejected(source.clone(), IrType::UInt64, IrExpr::Proj { i: 1, x: 0 }, "proj aggregate field");
        for index in [2, u64::MAX] {
            assert!(matches!(
                check(source.clone(), IrType::UInt8, IrExpr::Proj { i: index, x: 0 }),
                Err(Error::Projection { index: found, fields: 2, .. }) if found == index,
            ));
        }
    }
}

#[test]
fn aggregate_field_equality_checks_nested_types_owners_and_lengths() {
    let expected = IrType::Struct { lean_type: Some(name("Pair")), types: vec![IrType::UInt8] };
    let source = IrType::Struct { lean_type: None, types: vec![expected.clone()] };
    check(source.clone(), expected, IrExpr::Proj { i: 0, x: 0 }).unwrap();
    for result in [
        IrType::Struct { lean_type: Some(name("Other")), types: vec![IrType::UInt8] },
        IrType::Struct { lean_type: Some(name("Pair")), types: vec![IrType::UInt64] },
        IrType::Struct { lean_type: Some(name("Pair")), types: vec![] },
        IrType::Union { lean_type: name("Pair"), types: vec![IrType::UInt8] },
    ] {
        rejected(source.clone(), result, IrExpr::Proj { i: 0, x: 0 }, "proj aggregate field");
    }
}

#[test]
fn scalar_projections_and_is_shared_check_their_specific_results() {
    check(IrType::Object, IrType::USize, IrExpr::UProj { i: 0, x: 0 }).unwrap();
    rejected(IrType::Object, IrType::UInt64, IrExpr::UProj { i: 0, x: 0 }, "uproj result");
    rejected(IrType::UInt8, IrType::USize, IrExpr::UProj { i: 0, x: 0 }, "uproj source");
    check(IrType::Object, IrType::Float32, IrExpr::SProj { n: 0, offset: 0, x: 0 }).unwrap();
    rejected(IrType::Object, IrType::Object, IrExpr::SProj { n: 0, offset: 0, x: 0 }, "sproj result");
    rejected(IrType::UInt8, IrType::UInt8, IrExpr::SProj { n: 0, offset: 0, x: 0 }, "sproj source");
    rejected(IrType::Object, IrType::UInt64, IrExpr::IsShared { x: 0 }, "isShared result");
}

#[test]
fn string_literals_require_object_results_without_inventing_numeric_type_rules() {
    check(IrType::Object, IrType::Object, IrExpr::Lit(IrLit::Str("hello".into()))).unwrap();
    rejected(IrType::Object, IrType::UInt64, IrExpr::Lit(IrLit::Str("hello".into())), "string literal result");
    check(IrType::Object, IrType::UInt64, IrExpr::Lit(IrLit::Num(IrNat::Small(7)))).unwrap();
    check(IrType::Object, IrType::Tagged, IrExpr::Lit(IrLit::Num(IrNat::Small(7)))).unwrap();
}

#[test]
fn type_checks_reach_join_values_and_default_case_arms() {
    let bad = || bind(2, IrType::Object, IrExpr::Unbox { x: 0 });
    let join = IrStmt::JDecl { j: 10, params: vec![], value: body(vec![bad()], IrTerminal::Ret(IrArg::Var(2))) };
    let declaration = function(vec![param(0, IrType::Object)], body(vec![join], IrTerminal::Ret(IrArg::Var(0))));
    assert!(matches!(validate_ir_types(&[module(vec![declaration])], &BTreeMap::new(), IrValidationLimits::default()), Err(Error::Rule { binding: 2, .. })));
    let declaration = function(vec![param(0, IrType::Object)], body(vec![], IrTerminal::Case {
        type_name: name("C"), x: 0, x_type: IrType::Object,
        alts: vec![IrAlt::Default { body: body(vec![bad()], IrTerminal::Ret(IrArg::Var(2))) }],
    }));
    assert!(matches!(validate_ir_types(&[module(vec![declaration])], &BTreeMap::new(), IrValidationLimits::default()), Err(Error::Rule { binding: 2, .. })));
}

#[test]
fn structural_errors_win_and_out_of_scope_locals_are_never_rescued_by_the_type_index() {
    let join = IrStmt::JDecl { j: 10, params: vec![param(2, IrType::Object)], value: body(vec![], IrTerminal::Ret(IrArg::Var(2))) };
    let declaration = function(vec![param(0, IrType::Object)], body(
        vec![join, bind(3, IrType::UInt8, IrExpr::Unbox { x: 2 })], IrTerminal::Ret(IrArg::Var(3)),
    ));
    let error = validate_ir_types(&[module(vec![declaration])], &BTreeMap::new(), IrValidationLimits::default()).unwrap_err();
    assert!(matches!(error, Error::Structural(error) if error.kind == IrValidationErrorKind::UnknownVariable { index: 2 }));
}

#[test]
fn cumulative_work_limit_is_exact_and_failures_do_not_mutate_input() {
    let modules = [sample(IrType::Object, IrType::UInt64, IrExpr::Unbox { x: 0 })];
    let original = modules.clone();
    let measured = validate_ir_types(&modules, &BTreeMap::new(), IrValidationLimits::default()).unwrap();
    assert!(measured.work > measured.structural.work);
    assert_eq!(measured.expressions, 1);
    let exact = IrValidationLimits { max_work: measured.work, ..IrValidationLimits::default() };
    validate_ir_types(&modules, &BTreeMap::new(), exact).unwrap();
    let below = IrValidationLimits { max_work: measured.work - 1, ..exact };
    assert!(validate_ir_types(&modules, &BTreeMap::new(), below).unwrap_err().is_resource());
    assert_eq!(modules, original);
}

#[test]
fn directly_constructed_aggregate_types_have_their_own_depth_limit() {
    let mut ty = IrType::UInt8;
    for _ in 0..32 { ty = IrType::Struct { lean_type: None, types: vec![ty] }; }
    let modules = [module(vec![IrDecl::Extern { name: name("Deep"), params: vec![], result: ty, entries: vec![] }])];
    let exact = IrValidationLimits { max_depth: 33, ..IrValidationLimits::default() };
    validate_ir_types(&modules, &BTreeMap::new(), exact).unwrap();
    let below = IrValidationLimits { max_depth: 32, ..exact };
    let error = validate_ir_types(&modules, &BTreeMap::new(), below).unwrap_err();
    assert!(matches!(error, Error::Limit { resource: "type depth", .. }));
    assert!(error.is_resource());
}

#[test]
fn real_boxed_nat_wrapper_passes_and_a_wrong_box_annotation_is_refused() {
    use fln_olean::ir::{IrDecodeLimits, decode_ir};
    use fln_olean::region::{OleanView, WalkBudget};
    let view = OleanView::parse(include_bytes!("../fixtures/ir/Init.Data.Nat.Basic.ir")).unwrap();
    let blocks = view.extension_payloads(WalkBudget::default(), 1 << 30).unwrap();
    let decoded = decode_ir(&blocks, IrDecodeLimits::default()).unwrap();
    let target = decoded.decls.iter().find(|d| d.name() == &name("Nat.blt")).unwrap();
    let arity = match target { IrDecl::Function { params, .. } => params.len(), _ => unreachable!() };
    let signatures = BTreeMap::from([(target.name().clone(), arity)]);
    let wrapper = decoded.decls.iter().find(|d| d.name() == &name("Nat.blt._boxed")).unwrap().clone();
    let mut modules = [module(vec![wrapper])];
    validate_ir_types(&modules, &signatures, IrValidationLimits::default()).unwrap();
    let IrDecl::Function { body, .. } = &mut modules[0].decls[0] else { unreachable!() };
    let mut mutations = 0;
    for stmt in &mut body.stmts {
        if let IrStmt::VDecl { expr: IrExpr::Box { ty, .. }, .. } = stmt {
            assert_eq!(*ty, IrType::UInt8);
            *ty = IrType::UInt64;
            mutations += 1;
        }
    }
    assert_eq!(mutations, 1, "the real wrapper must exercise the rule");
    assert!(matches!(validate_ir_types(&modules, &signatures, IrValidationLimits::default()), Err(Error::Rule { operation: "box annotation", .. })));
}
