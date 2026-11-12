use super::*;
use crate::interpreter::{ExecutionLimits, VmExit, execute_function};
use fln_comp::flbc::{self, ArgumentOwnership, CallableResultOwnership, ResultOwnership};
use fln_core::expr::{BinderInfo, Literal, NatLit};
use fln_core::name::Name;
use fln_core::outcome::Outcome;

fn bvar(index: u32) -> Expr {
    Expr::bvar(index).unwrap()
}

fn literal(value: u64) -> Expr {
    Expr::lit(Literal::Nat(NatLit::from_u64(value)))
}

fn object(expr: Expr) -> Obj {
    let mut heap = NativeHeap::new();
    let handle = heap.alloc(expr);
    inject_expr(&heap, handle).unwrap()
}

fn expression(value: &Obj) -> Expr {
    let mut heap = NativeHeap::new();
    let handle = Conversion::new().project_expr(&mut heap, value).unwrap();
    heap.get(handle).unwrap().clone()
}

fn program(row: &str) -> flbc::ValidatedProgram {
    let (arity, argument_ownership, result_ownership) =
        if let Some(entry) = crate::macro_native::row_for_id(row) {
            (
                u16::try_from(entry.parameters.len()).unwrap(),
                entry.argument_ownership(),
                entry.result_ownership(),
            )
        } else {
            let entry = crate::extern_table_generated::EXTERN_ROWS
                .iter()
                .find(|entry| entry.id == row)
                .unwrap();
            let data = row == "extern:Lean.Expr.data";
            let arity = u16::try_from(entry.arity).unwrap();
            (
                arity,
                vec![
                    if data {
                        ArgumentOwnership::Owned
                    } else {
                        ArgumentOwnership::Borrowed
                    };
                    usize::from(arity)
                ],
                if data {
                    ResultOwnership::Scalar
                } else {
                    ResultOwnership::Owned
                },
            )
        };
    let r = flbc::Register::new;
    let f = flbc::FunctionId::new;
    let checked = flbc::validate(flbc::Program::new(
        f(0),
        vec![
            flbc::Function {
                id: f(0),
                arity: 0,
                parameter_ownership: vec![],
                result_ownership: CallableResultOwnership::Scalar,
                register_count: 1,
                code: vec![
                    flbc::Instruction::Nat {
                        dst: r(0),
                        value: 0,
                    },
                    flbc::Instruction::Return { src: r(0) },
                ],
            },
            flbc::Function {
                id: f(1),
                arity,
                parameter_ownership: vec![ArgumentOwnership::Borrowed; usize::from(arity)],
                result_ownership: if matches!(
                    row,
                    "extern:Lean.Expr.equal" | "extern:Lean.Expr.hasLooseBVar"
                ) {
                    CallableResultOwnership::Scalar
                } else {
                    CallableResultOwnership::Owned
                },
                register_count: arity + 1,
                code: vec![
                    flbc::Instruction::Intrinsic {
                        dst: r(arity),
                        row: row.to_owned(),
                        args: (0..arity).map(r).collect(),
                        argument_ownership,
                        result_ownership,
                    },
                    flbc::Instruction::Return { src: r(arity) },
                ],
            },
        ],
    ))
    .unwrap();
    let managed = flbc::insert_ownership(&checked, flbc::OwnershipLimits::default()).unwrap();
    let bytes = flbc::encode_canonical(managed.program(), flbc::CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, flbc::CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, flbc::CodecLimits::default()).unwrap(),
        bytes
    );
    replay
}

fn execute(row: &str, args: &[Obj]) -> Outcome<VmExit> {
    execute_function(
        &program(row),
        flbc::FunctionId::new(1),
        args.iter().map(Obj::clone_ref).collect(),
        ExecutionLimits::default(),
        None,
    )
}

fn call(row: &str, args: &[Obj]) -> Obj {
    let result = execute(row, args);
    let Outcome::Complete(VmExit::Returned(result)) = result else {
        panic!("{row}: {result:?}")
    };
    result.value
}

#[test]
fn native_expr_constructors_compute_data_and_preserve_all_binder_fields() {
    let created = call("mirror:Lean.Expr.bvar._override", &[Obj::mk_nat(3)]);
    assert_eq!(expression(&created), bvar(3));
    let applied = call(
        "mirror:Lean.Expr.app._override",
        &[created.clone_ref(), object(bvar(1))],
    );
    assert_eq!(expression(&applied), Expr::app(bvar(3), bvar(1)));
    let name = Name::num(Name::from_components(["x", "_hyg"]), 77);
    for (row, expected) in [
        (
            "mirror:Lean.Expr.lam._override",
            Expr::lam(name.clone(), bvar(3), bvar(1), BinderInfo::InstImplicit),
        ),
        (
            "mirror:Lean.Expr.forallE._override",
            Expr::forall_e(name.clone(), bvar(3), bvar(1), BinderInfo::InstImplicit),
        ),
    ] {
        let result = call(
            row,
            &[
                fln_rt::convert::inject_name(&name),
                created.clone_ref(),
                object(bvar(1)),
                Obj::mk_nat(3),
            ],
        );
        assert_eq!(expression(&result), expected);
        assert_eq!(
            call("extern:Lean.Expr.data", &[result]).try_ctor_scalar_u64(0),
            Some(expected.data().0)
        );
    }
    let result = call(
        "mirror:Lean.Expr.letE._override",
        &[
            fln_rt::convert::inject_name(&name),
            created.clone_ref(),
            object(literal(8)),
            object(bvar(1)),
            Obj::mk_nat(1),
        ],
    );
    assert_eq!(
        expression(&result),
        Expr::let_e(name, bvar(3), literal(8), bvar(1), true)
    );
    assert_eq!(expression(&created), bvar(3));
    assert!(matches!(
        execute(
            "mirror:Lean.Expr.lam._override",
            &[
                Obj::mk_nat(0),
                created.clone_ref(),
                object(bvar(0)),
                Obj::mk_nat(4)
            ]
        ),
        Outcome::Complete(VmExit::Refused { .. })
    ));
    assert!(matches!(
        execute(
            "mirror:Lean.Expr.bvar._override",
            &[Obj::mk_mpz(&[u64::MAX], false)]
        ),
        Outcome::Inconclusive(_)
    ));
}

#[test]
fn native_expr_substitution_orders_and_binder_depth_are_observable() {
    let body = Expr::app(bvar(0), Expr::app(bvar(1), bvar(2)));
    let args = [
        object(body.clone()),
        Obj::mk_array(vec![object(bvar(4)), object(bvar(8))]),
    ];
    assert_eq!(
        expression(&call("extern:Lean.Expr.instantiate", &args)),
        Expr::app(bvar(4), Expr::app(bvar(8), bvar(0)))
    );
    assert_eq!(
        expression(&call("extern:Lean.Expr.instantiateRev", &args)),
        Expr::app(bvar(8), Expr::app(bvar(4), bvar(0)))
    );
    assert_eq!(expression(&args[0]), body);
    assert_eq!(expression(&args[1].array_child(0)), bvar(4));

    let nested = Expr::lam(
        Name::from_components(["x"]),
        bvar(0),
        Expr::forall_e(
            Name::anonymous(),
            bvar(1),
            Expr::let_e(
                Name::anonymous(),
                bvar(2),
                bvar(1),
                Expr::app(bvar(0), Expr::app(bvar(3), bvar(4))),
                true,
            ),
            BinderInfo::Implicit,
        ),
        BinderInfo::Default,
    );
    let expected = Expr::lam(
        Name::from_components(["x"]),
        bvar(5),
        Expr::forall_e(
            Name::anonymous(),
            bvar(6),
            Expr::let_e(
                Name::anonymous(),
                bvar(7),
                bvar(1),
                Expr::app(bvar(0), Expr::app(bvar(8), bvar(3))),
                true,
            ),
            BinderInfo::Implicit,
        ),
        BinderInfo::Default,
    );
    assert_eq!(
        expression(&call(
            "extern:Lean.Expr.instantiate1",
            &[object(nested), object(bvar(5))]
        )),
        expected,
    );
    let closed = object(literal(17));
    for row in [
        "extern:Lean.Expr.instantiate",
        "extern:Lean.Expr.instantiateRev",
    ] {
        let result = call(row, &[closed.clone_ref(), Obj::mk_array(vec![])]);
        assert_eq!(result.identity_token(), closed.identity_token());
    }
}

#[test]
fn native_expr_lift_and_occurrence_preserve_pin_nat_boundaries() {
    let shared = bvar(1);
    let body = Expr::app(
        Expr::lam(
            Name::anonymous(),
            literal(0),
            shared.clone(),
            BinderInfo::Default,
        ),
        shared,
    );
    let carrier = object(body.clone());
    for (index, expected) in [(0, true), (1, true), (2, false), (1_u64 << 32, true)] {
        let result = call(
            "extern:Lean.Expr.hasLooseBVar",
            &[carrier.clone_ref(), Obj::mk_nat(index as usize)],
        );
        assert_eq!(result.unbox(), usize::from(expected));
    }
    let large = Obj::mk_mpz(&[0, 1], false);
    assert_eq!(
        call(
            "extern:Lean.Expr.hasLooseBVar",
            &[carrier.clone_ref(), large.clone_ref()]
        )
        .unbox(),
        0
    );
    let unchanged = call(
        "extern:Lean.Expr.liftLooseBVars",
        &[carrier.clone_ref(), large, Obj::mk_nat(2)],
    );
    assert_eq!(unchanged.identity_token(), carrier.identity_token());
    let lifted = call(
        "extern:Lean.Expr.liftLooseBVars",
        &[carrier.clone_ref(), Obj::mk_nat(0), Obj::mk_nat(3)],
    );
    assert_eq!(
        expression(&lifted),
        Expr::app(
            Expr::lam(Name::anonymous(), literal(0), bvar(4), BinderInfo::Default),
            bvar(4),
        )
    );
    let wrapped = call(
        "extern:Lean.Expr.liftLooseBVars",
        &[
            carrier.clone_ref(),
            Obj::mk_nat(1_usize << 32),
            Obj::mk_nat((1_usize << 32) + 3),
        ],
    );
    assert_eq!(expression(&wrapped), expression(&lifted));
    assert_eq!(expression(&carrier), body);
}

#[test]
fn native_expr_strict_equality_keeps_binder_names_and_annotations() {
    let original = Expr::lam(
        Name::from_components(["x"]),
        literal(0),
        bvar(0),
        BinderInfo::Default,
    );
    let carrier = object(original.clone());
    for (other, expected) in [
        (original.clone(), true),
        (
            Expr::lam(
                Name::from_components(["y"]),
                literal(0),
                bvar(0),
                BinderInfo::Default,
            ),
            false,
        ),
        (
            Expr::lam(
                Name::from_components(["x"]),
                literal(0),
                bvar(0),
                BinderInfo::Implicit,
            ),
            false,
        ),
    ] {
        assert_eq!(
            original.data(),
            other.data(),
            "same data word cannot imply equality"
        );
        assert_eq!(
            call(
                "extern:Lean.Expr.equal",
                &[carrier.clone_ref(), object(other)]
            )
            .unbox(),
            usize::from(expected)
        );
    }
}

#[test]
fn native_expr_data_packing_keeps_all_bits_and_saturates_depth() {
    for depth in [0, 7, 255, 256, u32::MAX] {
        let args = [
            wide(0xfedc_ba98_7654_3210),
            Obj::mk_nat(91),
            Obj::mk_nat(depth as usize),
            Obj::mk_nat(1),
            Obj::mk_nat(0),
            Obj::mk_nat(1),
            Obj::mk_nat(1),
        ];
        let result = call("extern:Lean.Expr.mkData", &args);
        let expected = 0x7654_3210
            | (u64::from(depth.min(255)) << 32)
            | (1_u64 << 40)
            | (1_u64 << 42)
            | (1_u64 << 43)
            | (91_u64 << 44);
        assert_eq!(result.try_ctor_scalar_u64(0), Some(expected));
    }
    let left = bvar(8);
    let right = literal(123);
    let expected = Expr::app(left.clone(), right.clone());
    let packed = call(
        "extern:Lean.Expr.mkAppData",
        &[wide(left.data().0), wide(right.data().0)],
    );
    let queried = call("extern:Lean.Expr.data", &[object(expected.clone())]);
    assert_eq!(packed.try_ctor_scalar_u64(0), Some(expected.data().0));
    assert_eq!(queried.try_ctor_scalar_u64(0), Some(expected.data().0));
}

#[test]
fn native_expr_refuses_malformed_values_and_retains_resource_nonanswers() {
    let valid = object(bvar(0));
    let forged = Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &[0; 8]);
    for args in [
        vec![Obj::mk_nat(0), valid.clone_ref()],
        vec![forged, valid.clone_ref()],
    ] {
        assert!(matches!(
            execute("extern:Lean.Expr.equal", &args),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::InvalidCtorObject,
                ..
            })
        ));
    }
    assert!(matches!(
        execute(
            "extern:Lean.Expr.instantiate",
            &[valid.clone_ref(), Obj::mk_nat(0)]
        ),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::InvalidArrayObject,
            ..
        })
    ));
    assert!(matches!(
        execute(
            "extern:Lean.Expr.instantiateRev",
            &[valid.clone_ref(), Obj::mk_array(vec![Obj::mk_nat(0)])]
        ),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::InvalidCtorObject,
            ..
        })
    ));
    assert!(matches!(
        execute(
            "extern:Lean.Expr.hasLooseBVar",
            &[valid.clone_ref(), Obj::mk_mpz(&[1], true)]
        ),
        Outcome::Complete(VmExit::Refused { .. })
    ));
    assert!(matches!(
        execute(
            "extern:Lean.Expr.mkData",
            &[
                wide(0),
                Obj::mk_nat(MAX_LOOSE_BVAR_RANGE as usize + 1),
                Obj::mk_nat(0),
                Obj::mk_nat(0),
                Obj::mk_nat(0),
                Obj::mk_nat(0),
                Obj::mk_nat(0)
            ]
        ),
        Outcome::Inconclusive(_)
    ));
    assert!(matches!(
        execute(
            "extern:Lean.Expr.liftLooseBVars",
            &[
                valid.clone_ref(),
                Obj::mk_nat(0),
                Obj::mk_nat(MAX_LOOSE_BVAR_RANGE as usize)
            ]
        ),
        Outcome::Inconclusive(_)
    ));
    assert!(matches!(
        Intrinsic::Equal.invoke_bounded(
            "extern:Lean.Expr.equal",
            &[valid.clone_ref(), valid.clone_ref()],
            1
        ),
        Err(IntrinsicFailure::MirrorResource {
            resource: "expression projection nodes",
            ..
        })
    ));
    let shared = bvar(1);
    let multiple_depths = Expr::app(
        shared.clone(),
        Expr::lam(Name::anonymous(), literal(0), shared, BinderInfo::Default),
    );
    assert!(matches!(
        check_transform(
            &multiple_depths,
            0,
            None,
            &mut WorkBudget {
                allowed: 4,
                visited: 0
            }
        ),
        Err(IntrinsicFailure::MirrorResource {
            resource: "expression traversal nodes",
            ..
        })
    ));
    assert_eq!(
        call("extern:Lean.Expr.equal", &[valid.clone_ref(), valid]).unbox(),
        1
    );
}

#[test]
fn native_expr_equal_bounds_differently_shared_pairs_before_comparison() {
    fn shared(depth: usize) -> Expr {
        let mut value = literal(0);
        for _ in 0..depth {
            value = Expr::app(value.clone(), value);
        }
        value
    }
    fn separate_prefix(depth: usize, shared_depth: usize) -> Expr {
        if depth == 0 {
            shared(shared_depth)
        } else {
            Expr::app(
                separate_prefix(depth - 1, shared_depth),
                separate_prefix(depth - 1, shared_depth),
            )
        }
    }
    // Fifteen nodes on the left and nine on the right produce 31 distinct
    // comparison pairs: the two graphs share at opposite ends of each path.
    let left = separate_prefix(2, 2);
    let mut right = separate_prefix(2, 0);
    for _ in 0..2 {
        right = Expr::app(right.clone(), right);
    }
    assert_eq!(left, right);
    assert!(matches!(
        check_equality_pairs(
            &left,
            &right,
            &mut WorkBudget {
                allowed: 24,
                visited: 0
            }
        ),
        Err(IntrinsicFailure::MirrorResource {
            resource: "expression traversal nodes",
            ..
        })
    ));
    let mut budget = WorkBudget {
        allowed: 31,
        visited: 0,
    };
    assert!(check_equality_pairs(&left, &right, &mut budget).is_ok());
    assert_eq!(budget.visited, 31);

    let mut operands = Operands {
        conversion: Conversion::new(),
        heap: NativeHeap::new(),
    };
    let first = operands
        .expr(&object(literal(0)))
        .unwrap_or_else(|_| panic!("first projection"));
    let second = operands
        .expr(&object(literal(0)))
        .unwrap_or_else(|_| panic!("second projection"));
    assert_ne!(
        first.allocation_identity(),
        second.allocation_identity(),
        "projection must not intern equal operands together before pair accounting"
    );
}

#[test]
fn native_expr_equal_charges_nested_universe_pairs_to_one_allowance() {
    fn shared(depth: usize) -> Level {
        let mut value = Level::zero();
        for _ in 0..depth {
            value = Level::max(value.clone(), value).unwrap();
        }
        value
    }
    fn separate_prefix(depth: usize, shared_depth: usize) -> Level {
        if depth == 0 {
            shared(shared_depth)
        } else {
            Level::max(
                separate_prefix(depth - 1, shared_depth),
                separate_prefix(depth - 1, shared_depth),
            )
            .unwrap()
        }
    }
    let left = separate_prefix(2, 2);
    let mut right = separate_prefix(2, 0);
    for _ in 0..2 {
        right = Level::max(right.clone(), right).unwrap();
    }
    let sorts = (Expr::sort(left.clone()), Expr::sort(right.clone()));
    let constants = (
        Expr::const_(Name::from_components(["C"]), vec![left.clone(), left]),
        Expr::const_(Name::from_components(["C"]), vec![right.clone(), right]),
    );
    for ((left, right), required) in [(sorts, 32), (constants, 63)] {
        assert_eq!(left, right);
        assert!(matches!(
            check_equality_pairs(
                &left,
                &right,
                &mut WorkBudget {
                    allowed: required - 1,
                    visited: 0
                }
            ),
            Err(IntrinsicFailure::MirrorResource {
                resource: "universe level comparison pairs",
                ..
            })
        ));
        let mut budget = WorkBudget {
            allowed: required,
            visited: 0,
        };
        assert!(check_equality_pairs(&left, &right, &mut budget).is_ok());
        assert_eq!(budget.visited, required);
        assert_eq!(
            call("extern:Lean.Expr.equal", &[object(left), object(right)]).unbox(),
            1
        );
    }
}

#[test]
fn native_expr_deep_shared_graphs_replay_and_obey_vm_stops() {
    let mut expr = bvar(0);
    for _ in 0..400 {
        expr = Expr::app(expr.clone(), expr);
    }
    let carrier = object(expr);
    let row = "extern:Lean.Expr.instantiate1";
    let program = program(row);
    for (limits, cancel) in [
        (
            ExecutionLimits {
                max_steps: 0,
                ..ExecutionLimits::default()
            },
            false,
        ),
        (ExecutionLimits::default(), true),
    ] {
        assert!(matches!(
            execute_function(
                &program,
                flbc::FunctionId::new(1),
                vec![carrier.clone_ref(), object(literal(42))],
                limits,
                Some(&|| cancel)
            ),
            Outcome::Inconclusive(_)
        ));
    }
    let result = call(row, &[carrier, object(literal(42))]);
    let result = expression(&result);
    assert!(!result.has_loose_bvars());
    assert_eq!(result.approx_depth(), 255);
}
