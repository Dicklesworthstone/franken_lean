use super::*;
use crate::interpreter::{ExecutionLimits, VmExit, execute_function};
use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, Function, Instruction as I, Pc,
    Register, ResultOwnership as R,
};
use fln_core::expr::{BinderInfo, Expr, FVarId, Literal, MVarId, NatLit};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Authority, Outcome};
use fln_rt::convert::inject_expr;
use fln_rt::native_heap::NativeHeap;
use std::cell::Cell;

const REPLACE: &str = "extern:Lean.Expr.replaceImpl";
const FIND: &str = "extern:Lean.Expr.findImpl?";
const FIND_EXT: &str = "extern:Lean.Expr.findExtImpl?";

fn r(index: u16) -> Register {
    Register::new(index)
}

fn f(index: u32) -> FunctionId {
    FunctionId::new(index)
}

fn nat(dst: u16, value: u64) -> I {
    I::Nat { dst: r(dst), value }
}

fn function(id: u32, args: Vec<A>, result: C, registers: u16, code: Vec<I>) -> Function {
    Function {
        id: f(id),
        arity: u16::try_from(args.len()).unwrap(),
        parameter_ownership: args,
        result_ownership: result,
        register_count: registers,
        code,
    }
}

fn program(row: &str, callback: Function, captured: bool) -> ValidatedProgram {
    let capture_ownership = if captured {
        vec![callback.parameter_ownership[0]]
    } else {
        vec![]
    };
    let checked = flbc::validate(flbc::Program::new(
        f(0),
        vec![
            function(
                0,
                vec![],
                C::Scalar,
                1,
                vec![nat(0, 0), I::Return { src: r(0) }],
            ),
            function(
                1,
                vec![A::Borrowed; if captured { 2 } else { 1 }],
                // Expr is always a heap object. Option Expr has the pin's
                // TObject ABI: scalar none or owned some. OwnedOrScalar is
                // specifically Nat, so it cannot represent this sum type.
                if row == REPLACE { C::Owned } else { C::Erased },
                4,
                vec![
                    I::Closure {
                        dst: r(2),
                        function: f(2),
                        captures: if captured { vec![r(1)] } else { vec![] },
                        capture_ownership,
                    },
                    I::Intrinsic {
                        dst: r(3),
                        row: row.to_owned(),
                        args: vec![r(2), r(0)],
                        argument_ownership: vec![A::Borrowed; 2],
                        result_ownership: R::Owned,
                    },
                    I::Return { src: r(3) },
                ],
            ),
            callback,
        ],
    ))
    .unwrap();
    let managed = flbc::insert_ownership(&checked, flbc::OwnershipLimits::default()).unwrap();
    let bytes = flbc::encode_canonical(managed.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        bytes,
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap()
    );
    replay
}

fn constant_callback(value: u64, ownership: A) -> Function {
    function(
        2,
        vec![ownership],
        C::Scalar,
        2,
        vec![nat(1, value), I::Return { src: r(1) }],
    )
}

fn captured_replacement(all: bool) -> Function {
    let some = I::Ctor {
        dst: r(3),
        tag: 1,
        fields: vec![r(0)],
        scalar_bytes: vec![],
    };
    let code = if all {
        vec![some, I::Return { src: r(3) }]
    } else {
        vec![
            I::CtorTest {
                dst: r(2),
                src: r(1),
                expected_tag: 0,
                expected_fields: 1,
            },
            I::JumpIfZero {
                cond: r(2),
                zero: Pc::new(4),
                nonzero: Pc::new(2),
            },
            some,
            I::Return { src: r(3) },
            nat(3, 0),
            I::Return { src: r(3) },
        ]
    };
    function(
        2,
        vec![A::Owned, A::Borrowed],
        if all { C::Owned } else { C::Erased },
        4,
        code,
    )
}

fn call(program: &ValidatedProgram, args: &[&Obj]) -> Obj {
    let result = execute_function(
        program,
        f(1),
        args.iter().map(|value| value.clone_ref()).collect(),
        ExecutionLimits::default(),
        None,
    );
    let Outcome::Complete(VmExit::Returned(result)) = result else {
        panic!("native expression traversal failed: {result:?}")
    };
    result.value
}

fn object(expr: Expr) -> Obj {
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(expr);
    inject_expr(&heap, handle).unwrap()
}

fn bvar(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn app(function: &Obj, argument: &Obj) -> Obj {
    // A children-only input is a supported checked encoding. This preserves
    // intentional distinct-equal children that whole-graph injection interns.
    Obj::mk_ctor(5, vec![function.clone_ref(), argument.clone_ref()], &[])
}

fn trace(
    intrinsic: Intrinsic,
    input: &Obj,
    allowed: usize,
    mut callback: impl FnMut(&Obj) -> Obj,
) -> Result<(Obj, Vec<usize>), Failure> {
    let row = match intrinsic {
        Intrinsic::Replace => REPLACE,
        Intrinsic::Find => FIND,
        Intrinsic::FindExt => FIND_EXT,
    };
    let program = program(row, constant_callback(0, A::Borrowed), false);
    let closure = Obj::mk_closure(2, vec![Obj::mk_nat(2)]);
    let mut step = start_bounded(
        &program,
        intrinsic,
        row,
        vec![closure, input.clone_ref()],
        allowed,
    )?;
    let mut visits = Vec::new();
    loop {
        match step {
            Step::Complete(value) => return Ok((value, visits)),
            Step::Call { args, state, .. } => {
                assert_eq!(args.len(), 1);
                visits.push(args[0].identity_token());
                step = resume(&program, state, callback(&args[0]))?;
            }
        }
    }
}

#[test]
fn native_expr_traversal_public_callbacks_preserve_root_and_shared_replacement_identity() {
    let left = object(bvar(0));
    let right = object(bvar(0));
    assert_ne!(left.identity_token(), right.identity_token());
    let input = app(&left, &right);
    for ownership in [A::Owned, A::Borrowed] {
        let unchanged = call(
            &program(REPLACE, constant_callback(0, ownership), false),
            &[&input],
        );
        assert_eq!(unchanged.identity_token(), input.identity_token());
        assert_eq!(
            unchanged.try_ctor_child(0).unwrap().identity_token(),
            left.identity_token()
        );
        assert_eq!(
            unchanged.try_ctor_child(1).unwrap().identity_token(),
            right.identity_token()
        );
    }
    let shared = app(&left, &object(bvar(1)));
    let root = app(&shared, &shared);
    let replacement = object(bvar(8));
    let rewritten = call(
        &program(REPLACE, captured_replacement(false), true),
        &[&root, &replacement],
    );
    let first = rewritten.try_ctor_child(0).unwrap();
    let second = rewritten.try_ctor_child(1).unwrap();
    assert_eq!(first.identity_token(), second.identity_token());
    assert_ne!(first.identity_token(), shared.identity_token());
    for slot in 0..2 {
        assert_eq!(
            first.try_ctor_child(slot).unwrap().identity_token(),
            replacement.identity_token()
        );
    }
    let checked = Conversion::new().check_expr(&rewritten).unwrap();
    assert_eq!(
        checked.expression(),
        &Expr::app(Expr::app(bvar(8), bvar(8)), Expr::app(bvar(8), bvar(8)))
    );
    assert_eq!(
        root.try_ctor_child(0).unwrap().identity_token(),
        shared.identity_token()
    );
    let replaced_root = call(
        &program(REPLACE, captured_replacement(true), true),
        &[&root, &replacement],
    );
    assert_eq!(replaced_root.identity_token(), replacement.identity_token());
}

#[test]
fn native_expr_traversal_callbacks_observe_preorder_and_replacement_prunes_new_subtrees() {
    let a = bvar(1);
    let b = bvar(2);
    let c = bvar(3);
    for (expr, slots) in [
        (Expr::app(a.clone(), b.clone()), vec![0, 1]),
        (
            Expr::lam(
                Name::anonymous(),
                a.clone(),
                b.clone(),
                BinderInfo::Implicit,
            ),
            vec![1, 2],
        ),
        (
            Expr::forall_e(Name::anonymous(), a.clone(), b.clone(), BinderInfo::Default),
            vec![1, 2],
        ),
        (
            Expr::let_e(Name::anonymous(), a.clone(), b.clone(), c, false),
            vec![1, 2, 3],
        ),
        (Expr::mdata(KVMap::new(), a.clone()), vec![1]),
        (Expr::proj(Name::anonymous(), 2, a), vec![2]),
    ] {
        let input = object(expr);
        let mut expected = vec![input.identity_token()];
        expected.extend(
            slots
                .iter()
                .map(|&slot| input.try_ctor_child(slot).unwrap().identity_token()),
        );
        for intrinsic in [Intrinsic::Replace, Intrinsic::Find, Intrinsic::FindExt] {
            let continue_tag = usize::from(intrinsic == Intrinsic::FindExt);
            let (_, actual) = trace(intrinsic, &input, 100, |_| Obj::mk_nat(continue_tag)).unwrap();
            assert_eq!(actual, expected);
        }
        let replacement = object(Expr::app(bvar(8), bvar(9)));
        let (result, visits) = trace(Intrinsic::Replace, &input, 100, |_| {
            Obj::mk_ctor(1, vec![replacement.clone_ref()], &[])
        })
        .unwrap();
        assert_eq!(visits, vec![input.identity_token()]);
        assert_eq!(result.identity_token(), replacement.identity_token());
    }
}

#[test]
fn native_expr_traversal_shared_cache_matches_the_pins_special_leaf_rules() {
    for (expr, repeated_find_visits) in [
        (bvar(0), 3),
        (Expr::sort(Level::zero()), 3),
        (Expr::const_(Name::anonymous(), vec![]), 3),
        (Expr::lit(Literal::Nat(NatLit::from_u64(7))), 1),
        (Expr::fvar(FVarId(Name::anonymous())), 1),
        (Expr::mvar(MVarId(Name::anonymous())), 1),
    ] {
        let shared = object(expr);
        let pair = app(&shared, &shared);
        let input = app(&pair, &shared);
        for intrinsic in [Intrinsic::Replace, Intrinsic::Find] {
            let (_, visits) = trace(intrinsic, &input, 100, |_| Obj::mk_nat(0)).unwrap();
            assert_eq!(
                visits
                    .iter()
                    .filter(|&&identity| identity == shared.identity_token())
                    .count(),
                if intrinsic == Intrinsic::Replace {
                    1
                } else {
                    repeated_find_visits
                }
            );
        }
    }
    let shared = app(&object(bvar(0)), &object(bvar(1)));
    let input = app(&shared, &shared);
    let (_, visits) = trace(Intrinsic::Find, &input, 100, |_| Obj::mk_nat(0)).unwrap();
    assert_eq!(
        visits
            .iter()
            .filter(|&&id| id == shared.identity_token())
            .count(),
        1
    );
}

fn partial_application_predicate(extended: bool) -> Function {
    function(
        2,
        vec![A::Borrowed],
        C::Scalar,
        5,
        vec![
            I::CtorTest {
                dst: r(1),
                src: r(0),
                expected_tag: 5,
                expected_fields: 2,
            },
            I::JumpIfZero {
                cond: r(1),
                zero: Pc::new(7),
                nonzero: Pc::new(2),
            },
            I::CtorField {
                dst: r(2),
                src: r(0),
                expected_tag: 5,
                expected_fields: 2,
                field: 0,
            },
            I::CtorTest {
                dst: r(3),
                src: r(2),
                expected_tag: 0,
                expected_fields: 1,
            },
            I::JumpIfZero {
                cond: r(3),
                zero: Pc::new(7),
                nonzero: Pc::new(5),
            },
            nat(4, u64::from(!extended)),
            I::Return { src: r(4) },
            nat(4, u64::from(extended)),
            I::Return { src: r(4) },
        ],
    )
}

#[test]
fn native_expr_traversal_public_find_returns_original_and_find_ext_skips_partial_apps() {
    let head = object(bvar(0));
    let a = object(bvar(1));
    let b = object(bvar(2));
    let partial = app(&head, &a);
    let root = app(&partial, &b);
    let result = call(
        &program(FIND, partial_application_predicate(false), false),
        &[&root],
    );
    assert_eq!(result.obj_tag(), 1);
    assert_eq!(
        result.try_ctor_child(0).unwrap().identity_token(),
        partial.identity_token()
    );
    let result = call(
        &program(FIND_EXT, partial_application_predicate(true), false),
        &[&root],
    );
    assert!(result.is_scalar() && result.unbox() == 0);
    let (_, visits) = trace(Intrinsic::FindExt, &root, 100, |_| Obj::mk_nat(1)).unwrap();
    assert_eq!(
        visits,
        [
            root.identity_token(),
            head.identity_token(),
            a.identity_token(),
            b.identity_token()
        ]
    );
    let (result, visits) = trace(Intrinsic::FindExt, &root, 100, |_| Obj::mk_nat(2)).unwrap();
    assert!(result.is_scalar() && result.unbox() == 0);
    assert_eq!(visits, [root.identity_token()]);
    let (result, visits) = trace(Intrinsic::Find, &root, 100, |value| {
        Obj::mk_nat(usize::from(value.identity_token() == head.identity_token()))
    })
    .unwrap();
    assert_eq!(
        result.try_ctor_child(0).unwrap().identity_token(),
        head.identity_token()
    );
    assert_eq!(
        visits,
        [
            root.identity_token(),
            partial.identity_token(),
            head.identity_token()
        ]
    );
}

#[test]
fn native_expr_traversal_rejects_bad_callbacks_results_and_forged_cached_data_then_recovers() {
    let input = object(bvar(0));
    for (row, callback) in [
        (REPLACE, constant_callback(1, A::Borrowed)),
        (FIND, constant_callback(2, A::Borrowed)),
        (FIND_EXT, constant_callback(3, A::Borrowed)),
        (REPLACE, constant_callback(0, A::Unique)),
        (FIND, constant_callback(0, A::Scalar)),
        (
            REPLACE,
            function(
                2,
                vec![A::Borrowed],
                C::Owned,
                2,
                vec![
                    I::Ctor {
                        dst: r(1),
                        tag: 1,
                        fields: vec![r(0), r(0)],
                        scalar_bytes: vec![],
                    },
                    I::Return { src: r(1) },
                ],
            ),
        ),
    ] {
        let program = program(row, callback, false);
        assert!(matches!(
            execute_function(
                &program,
                f(1),
                vec![input.clone_ref()],
                ExecutionLimits::default(),
                None
            ),
            Outcome::Complete(VmExit::Refused { .. })
        ));
    }
    let replacement_program = program(REPLACE, captured_replacement(true), true);
    for malformed in [
        Obj::mk_nat(7),
        Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &u64::MAX.to_le_bytes()),
    ] {
        let outcome = execute_function(
            &replacement_program,
            f(1),
            vec![input.clone_ref(), malformed],
            ExecutionLimits::default(),
            None,
        );
        assert!(
            matches!(
                outcome,
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::InvalidCtorObject,
                    ..
                })
            ),
            "{outcome:?}"
        );
    }
    let replacement = object(bvar(8));
    assert_eq!(
        call(&replacement_program, &[&input, &replacement]).identity_token(),
        replacement.identity_token()
    );
    let unique_capture = program(
        REPLACE,
        function(
            2,
            vec![A::Unique, A::Borrowed],
            C::Scalar,
            3,
            vec![nat(2, 0), I::Return { src: r(2) }],
        ),
        false,
    );
    let forged_capture = Obj::mk_closure(3, vec![Obj::mk_nat(2), replacement]);
    assert!(matches!(
        start(
            &unique_capture,
            Intrinsic::Replace,
            REPLACE,
            vec![forged_capture, input.clone_ref()]
        ),
        Err(Failure::Refused(VmRefusal::ApplyOwnershipMismatch {
            expected: A::Unique,
            ..
        }))
    ));
}

#[test]
fn native_expr_traversal_work_and_replacement_projection_are_aggregate_and_bounded() {
    let leaf = object(bvar(0));
    let root = app(&leaf, &leaf);
    assert!(matches!(
        trace(Intrinsic::Replace, &root, 3, |_| Obj::mk_nat(0)),
        Err(Failure::Resource {
            resource: "expression traversal work",
            allowed: 3,
            observed: 4
        })
    ));
    let replacement = app(&object(bvar(1)), &object(bvar(2)));
    assert!(matches!(
        trace(Intrinsic::Replace, &leaf, 3, |_| Obj::mk_ctor(
            1,
            vec![replacement.clone_ref()],
            &[]
        )),
        Err(Failure::Resource {
            resource: "expression traversal projection/rebuild nodes",
            allowed: 3,
            observed: 4
        })
    ));
    let left = object(bvar(1));
    let right = object(bvar(2));
    let distinct = app(&left, &right);
    let replacement = object(bvar(8));
    // Three input nodes + one shared replacement + one rebuilt parent fit
    // five units; the second callback still runs but its result is checked.
    let (result, visits) = trace(Intrinsic::Replace, &distinct, 5, |value| {
        if value.identity_token() == distinct.identity_token() {
            Obj::mk_nat(0)
        } else {
            Obj::mk_ctor(1, vec![replacement.clone_ref()], &[])
        }
    })
    .unwrap();
    assert_eq!(visits.len(), 3);
    assert_eq!(
        result.try_ctor_child(0).unwrap().identity_token(),
        replacement.identity_token()
    );
    assert_eq!(
        result.try_ctor_child(1).unwrap().identity_token(),
        replacement.identity_token()
    );
    let mut deep = leaf.clone_ref();
    for _ in 0..400 {
        deep = app(&leaf, &deep);
    }
    assert!(matches!(
        trace(Intrinsic::Find, &deep, 8, |_| Obj::mk_nat(0)),
        Err(Failure::Resource {
            allowed: 8,
            observed: 9,
            ..
        })
    ));
    assert_eq!(
        trace(Intrinsic::Replace, &root, 100, |_| Obj::mk_nat(0))
            .unwrap()
            .0
            .identity_token(),
        root.identity_token()
    );
}

#[test]
fn native_expr_traversal_uses_vm_steps_cancellation_and_bounded_callback_stack() {
    let leaf = object(bvar(0));
    let mut input = leaf.clone_ref();
    for _ in 0..400 {
        input = app(&input, &leaf);
    }
    let program = program(REPLACE, constant_callback(0, A::Borrowed), false);
    for limits in [
        ExecutionLimits {
            max_stack_depth: 1,
            ..ExecutionLimits::default()
        },
        ExecutionLimits {
            max_steps: 25,
            ..ExecutionLimits::default()
        },
    ] {
        let outcome = execute_function(&program, f(1), vec![input.clone_ref()], limits, None);
        assert_eq!(outcome.authority(), Authority::NonAuthoritative);
        assert!(matches!(outcome, Outcome::Inconclusive(_)));
    }
    let polls = Cell::new(0);
    let cancel = || {
        polls.set(polls.get() + 1);
        polls.get() >= 5
    };
    let outcome = execute_function(
        &program,
        f(1),
        vec![input.clone_ref()],
        ExecutionLimits::default(),
        Some(&cancel),
    );
    assert_eq!(outcome.authority(), Authority::NonAuthoritative);
    assert!(matches!(outcome, Outcome::Inconclusive(_)));
    let outcome = execute_function(
        &program,
        f(1),
        vec![input.clone_ref()],
        ExecutionLimits {
            max_stack_depth: 2,
            ..ExecutionLimits::default()
        },
        None,
    );
    let Outcome::Complete(VmExit::Returned(result)) = outcome else {
        panic!("{outcome:?}")
    };
    assert_eq!(result.value.identity_token(), input.identity_token());
}
