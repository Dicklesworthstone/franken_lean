use super::*;
use crate::interpreter::{ExecutionLimits, VmExit, execute_function};
use fln_comp::flbc::{self, ArgumentOwnership, CallableResultOwnership, ResultOwnership};
use fln_core::expr::{BinderInfo, FVarId, Literal, MVarId, NatLit};
use fln_core::name::Name;
use fln_core::outcome::Outcome;

mod ordering;

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
                    "extern:Lean.Expr.equal"
                        | "extern:Lean.Expr.eqv"
                        | "extern:Lean.Expr.lt"
                        | "extern:Lean.Expr.quickLt"
                        | "extern:Lean.Expr.hasLooseBVar"
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
fn native_expr_all_composite_constructors_retain_shared_operand_identity() {
    let name = fln_rt::convert::inject_name(&Name::from_components(["shared"]));
    let operand = object(Expr::app(bvar(1), bvar(3)));
    for (row, args, child_slots) in [
        (
            "mirror:Lean.Expr.app._override",
            vec![operand.clone_ref(), operand.clone_ref()],
            vec![0, 1],
        ),
        (
            "mirror:Lean.Expr.lam._override",
            vec![
                name.clone_ref(),
                operand.clone_ref(),
                operand.clone_ref(),
                Obj::mk_nat(3),
            ],
            vec![1, 2],
        ),
        (
            "mirror:Lean.Expr.forallE._override",
            vec![
                name.clone_ref(),
                operand.clone_ref(),
                operand.clone_ref(),
                Obj::mk_nat(2),
            ],
            vec![1, 2],
        ),
        (
            "mirror:Lean.Expr.letE._override",
            vec![
                name.clone_ref(),
                operand.clone_ref(),
                operand.clone_ref(),
                operand.clone_ref(),
                Obj::mk_nat(1),
            ],
            vec![1, 2, 3],
        ),
    ] {
        let constructed = call(row, &args);
        for slot in child_slots {
            assert_eq!(
                constructed.try_ctor_child(slot).unwrap().identity_token(),
                operand.identity_token(),
                "{row} retains the shared operand at field {slot}"
            );
        }
        if row != "mirror:Lean.Expr.app._override" {
            assert_eq!(
                constructed.try_ctor_child(0).unwrap().identity_token(),
                name.identity_token()
            );
        }
        // Projection independently validates each new cached Data word and
        // the original annotations after identity-preserving construction.
        expression(&constructed);
    }
    let equal_but_distinct = object(expression(&operand));
    assert_ne!(
        operand.identity_token(),
        equal_but_distinct.identity_token()
    );
    let constructed = call(
        "mirror:Lean.Expr.app._override",
        &[operand.clone_ref(), equal_but_distinct.clone_ref()],
    );
    assert_eq!(
        constructed.try_ctor_child(0).unwrap().identity_token(),
        operand.identity_token()
    );
    assert_eq!(
        constructed.try_ctor_child(1).unwrap().identity_token(),
        equal_but_distinct.identity_token()
    );
    let maximum = MAX_LOOSE_BVAR_RANGE - 1;
    assert_eq!(
        expression(&call(
            "mirror:Lean.Expr.bvar._override",
            &[Obj::mk_nat(maximum as usize)]
        )),
        bvar(maximum)
    );
    assert!(matches!(
        execute(
            "mirror:Lean.Expr.bvar._override",
            &[Obj::mk_nat(MAX_LOOSE_BVAR_RANGE as usize)]
        ),
        Outcome::Inconclusive(_)
    ));
}

#[test]
fn native_expr_remaining_constructors_preserve_fields_and_checked_cached_data() {
    use fln_core::expr::{FVarId, MVarId};
    use fln_core::options::{DataValue, KVMap};
    let name = Name::num(Name::from_components(["Expr", "payload"]), 91);
    let level = Level::succ(Level::param(name.clone())).unwrap();
    for (row, expected) in [
        (
            "mirror:Lean.Expr.fvar._override",
            Expr::fvar(FVarId(name.clone())),
        ),
        (
            "mirror:Lean.Expr.mvar._override",
            Expr::mvar(MVarId(name.clone())),
        ),
        ("mirror:Lean.Expr.sort._override", Expr::sort(level.clone())),
        (
            "mirror:Lean.Expr.const._override",
            Expr::const_(name.clone(), vec![level]),
        ),
        (
            "mirror:Lean.Expr.lit._override",
            Expr::lit(Literal::Str("retained λ".into())),
        ),
        (
            "mirror:Lean.Expr.mdata._override",
            Expr::mdata(
                KVMap::from_entries(vec![
                    (name.clone(), DataValue::OfString("kept".into())),
                    (name.clone(), DataValue::OfNat(7)),
                ]),
                bvar(2),
            ),
        ),
        (
            "mirror:Lean.Expr.proj._override",
            Expr::proj(name, u64::MAX, bvar(3)),
        ),
    ] {
        let source = object(expected.clone());
        let fields = (0..usize::from(source.header().other))
            .map(|slot| source.try_ctor_child(slot).unwrap())
            .collect::<Vec<_>>();
        let constructed = call(row, &fields);
        assert_eq!(expression(&constructed), expected);
        assert_eq!(constructed.obj_tag(), source.obj_tag());
        for (slot, field) in fields.iter().enumerate() {
            assert_eq!(
                constructed.try_ctor_child(slot).unwrap().identity_token(),
                field.identity_token(),
                "{row} retains original field {slot}"
            );
        }
        assert_eq!(
            call("extern:Lean.Expr.data", &[constructed]).try_ctor_scalar_u64(0),
            Some(expected.data().0)
        );
    }
}

#[test]
fn native_expr_remaining_constructors_bound_validation_and_reject_malformed_fields() {
    let level = object(Expr::sort(Level::succ(Level::one()).unwrap()))
        .try_ctor_child(0)
        .unwrap();
    assert!(matches!(
        Intrinsic::Sort.invoke_bounded("mirror:Lean.Expr.sort._override", &[level], 2),
        Err(IntrinsicFailure::MirrorResource {
            allowed: 2,
            observed: 3,
            ..
        })
    ));
    for (row, fields) in [
        (
            "mirror:Lean.Expr.fvar._override",
            vec![Obj::mk_string("not a Name")],
        ),
        (
            "mirror:Lean.Expr.const._override",
            vec![Obj::mk_nat(0), Obj::mk_nat(1)],
        ),
        ("mirror:Lean.Expr.lit._override", vec![Obj::mk_nat(0)]),
        (
            "mirror:Lean.Expr.mdata._override",
            vec![Obj::mk_nat(1), object(bvar(0))],
        ),
        (
            "mirror:Lean.Expr.proj._override",
            vec![
                Obj::mk_nat(0),
                Obj::mk_nat(0),
                Obj::mk_ctor(0, vec![Obj::mk_nat(0)], &u64::MAX.to_le_bytes()),
            ],
        ),
    ] {
        assert!(
            matches!(
                execute(row, &fields),
                Outcome::Complete(VmExit::Refused { .. })
            ),
            "{row}"
        );
    }
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
fn native_expr_range_substitution_uses_only_the_selected_slice_in_both_orders() {
    let body = Expr::lam(
        Name::anonymous(),
        bvar(0),
        Expr::app(bvar(0), Expr::app(bvar(1), Expr::app(bvar(2), bvar(3)))),
        BinderInfo::InstImplicit,
    );
    let carrier = object(body.clone());
    let replacements = Obj::mk_array(vec![
        object(literal(99)),
        object(bvar(4)),
        object(bvar(8)),
        object(literal(77)),
    ]);
    for (row, first, second) in [
        ("extern:Lean.Expr.instantiateRange", 4, 8),
        ("extern:Lean.Expr.instantiateRevRange", 8, 4),
    ] {
        let result = call(
            row,
            &[
                carrier.clone_ref(),
                Obj::mk_nat(1),
                Obj::mk_nat(3),
                replacements.clone_ref(),
            ],
        );
        assert_eq!(
            expression(&result),
            Expr::lam(
                Name::anonymous(),
                bvar(first),
                Expr::app(
                    bvar(0),
                    Expr::app(bvar(first + 1), Expr::app(bvar(second + 1), bvar(1)))
                ),
                BinderInfo::InstImplicit,
            )
        );
        let unchanged = call(
            row,
            &[
                carrier.clone_ref(),
                Obj::mk_nat(4),
                Obj::mk_nat(4),
                replacements.clone_ref(),
            ],
        );
        assert_eq!(unchanged.identity_token(), carrier.identity_token());
        for (begin, end) in [(3, 2), (0, 5), (5, 5)] {
            assert!(matches!(
                execute(
                    row,
                    &[
                        carrier.clone_ref(),
                        Obj::mk_nat(begin),
                        Obj::mk_nat(end),
                        replacements.clone_ref()
                    ]
                ),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::ArrayIndexOutOfBounds { .. },
                    ..
                })
            ));
        }
        for endpoints in [
            [Obj::mk_mpz(&[0, 1], false), Obj::mk_nat(4)],
            [Obj::mk_nat(0), Obj::mk_mpz(&[0, 1], false)],
            [Obj::mk_mpz(&[1], true), Obj::mk_nat(4)],
        ] {
            assert!(matches!(
                execute(
                    row,
                    &[
                        carrier.clone_ref(),
                        endpoints[0].clone_ref(),
                        endpoints[1].clone_ref(),
                        replacements.clone_ref()
                    ]
                ),
                Outcome::Complete(VmExit::Refused { .. })
            ));
        }
    }
    assert_eq!(expression(&carrier), body);
    assert_eq!(expression(&replacements.array_child(1)), bvar(4));
}

#[test]
fn native_expr_abstract_distinguishes_variable_kinds_and_rightmost_duplicates() {
    let id = Name::from_components(["same", "id"]);
    let free = Expr::fvar(FVarId(id.clone()));
    let meta = Expr::mvar(MVarId(id));
    let other = Expr::fvar(FVarId(Name::from_components(["other"])));
    let input = Expr::app(
        Expr::app(free.clone(), meta.clone()),
        Expr::app(other.clone(), bvar(7)),
    );
    let variables = Obj::mk_array(vec![
        object(free.clone()),
        object(bvar(11)), // Non-variables still occupy a position.
        object(meta.clone()),
        object(free.clone()),
    ]);
    let carrier = object(input.clone());
    let whole = call(
        "extern:Lean.Expr.abstract",
        &[carrier.clone_ref(), variables.clone_ref()],
    );
    assert_eq!(
        expression(&whole),
        Expr::app(
            Expr::app(bvar(0), bvar(1)),
            Expr::app(other.clone(), bvar(7))
        )
    );
    for (count, expected_free, expected_meta) in [
        (0, free.clone(), meta.clone()),
        (1, bvar(0), meta.clone()),
        (2, bvar(1), meta.clone()),
        (3, bvar(2), bvar(0)),
        (4, bvar(0), bvar(1)),
        (1_usize << 32, bvar(0), bvar(1)),
    ] {
        let result = call(
            "extern:Lean.Expr.abstractRange",
            &[
                carrier.clone_ref(),
                Obj::mk_nat(count),
                variables.clone_ref(),
            ],
        );
        assert_eq!(
            expression(&result),
            Expr::app(
                Expr::app(expected_free, expected_meta),
                Expr::app(other.clone(), bvar(7))
            )
        );
        if count == 0 {
            assert_eq!(result.identity_token(), carrier.identity_token());
        }
    }
    assert_eq!(
        expression(&call(
            "extern:Lean.Expr.abstractRange",
            &[
                carrier.clone_ref(),
                Obj::mk_mpz(&[0, 1], false),
                variables.clone_ref()
            ]
        )),
        expression(&whole)
    );
    assert_eq!(expression(&carrier), input);
    assert_eq!(expression(&variables.array_child(0)), free);
}

#[test]
fn native_expr_abstract_tracks_all_binders_and_preserves_unmodified_shared_fields() {
    let free = Expr::fvar(FVarId(Name::from_components(["x"])));
    let meta = Expr::mvar(MVarId(Name::from_components(["m"])));
    let unchanged = Expr::app(literal(3), literal(5));
    let shared = Expr::app(free.clone(), meta.clone());
    let input = Expr::app(
        shared.clone(),
        Expr::lam(
            Name::from_components(["lambda"]),
            shared.clone(),
            Expr::forall_e(
                Name::anonymous(),
                shared.clone(),
                Expr::let_e(
                    Name::from_components(["let"]),
                    shared.clone(),
                    unchanged,
                    Expr::app(shared.clone(), shared),
                    true,
                ),
                BinderInfo::StrictImplicit,
            ),
            BinderInfo::InstImplicit,
        ),
    );
    let carrier = object(input);
    let result = call(
        "extern:Lean.Expr.abstract",
        &[
            carrier.clone_ref(),
            Obj::mk_array(vec![object(free.clone()), object(meta.clone())]),
        ],
    );
    let original_lambda = carrier.try_ctor_child(1).unwrap();
    let lambda = result.try_ctor_child(1).unwrap();
    assert_eq!(
        result.try_ctor_child(0).unwrap().identity_token(),
        lambda.try_ctor_child(1).unwrap().identity_token(),
        "the same subtree at the same binder depth stays shared"
    );
    assert_eq!(
        lambda.try_ctor_child(0).unwrap().identity_token(),
        original_lambda.try_ctor_child(0).unwrap().identity_token(),
        "binder names retain their original objects"
    );
    let forall = lambda.try_ctor_child(2).unwrap();
    let let_expr = forall.try_ctor_child(2).unwrap();
    let original_let = original_lambda
        .try_ctor_child(2)
        .unwrap()
        .try_ctor_child(2)
        .unwrap();
    assert_eq!(
        let_expr.try_ctor_child(2).unwrap().identity_token(),
        original_let.try_ctor_child(2).unwrap().identity_token()
    );
    for (object, depth) in [
        (result.try_ctor_child(0).unwrap(), 0),
        (forall.try_ctor_child(1).unwrap(), 1),
        (let_expr.try_ctor_child(1).unwrap(), 2),
        (
            let_expr
                .try_ctor_child(3)
                .unwrap()
                .try_ctor_child(0)
                .unwrap(),
            3,
        ),
    ] {
        assert_eq!(expression(&object), Expr::app(bvar(depth + 1), bvar(depth)));
    }
    let body = let_expr.try_ctor_child(3).unwrap();
    assert_eq!(
        body.try_ctor_child(0).unwrap().identity_token(),
        body.try_ctor_child(1).unwrap().identity_token()
    );
    assert_eq!(
        expression(&call(
            "extern:Lean.Expr.instantiateRev",
            &[result, Obj::mk_array(vec![object(free), object(meta)])]
        )),
        expression(&carrier),
        "abstraction and reverse instantiation round-trip closed free/meta variables"
    );
}

#[test]
fn native_expr_abstract_rejects_malformed_operands_and_bounds_binder_contexts() {
    let free = Expr::fvar(FVarId(Name::from_components(["x"])));
    let carrier = object(free.clone());
    for (row, args) in [
        (
            "extern:Lean.Expr.abstract",
            vec![carrier.clone_ref(), Obj::mk_nat(0)],
        ),
        (
            "extern:Lean.Expr.abstract",
            vec![carrier.clone_ref(), Obj::mk_array(vec![Obj::mk_nat(0)])],
        ),
        (
            "extern:Lean.Expr.abstractRange",
            vec![
                carrier.clone_ref(),
                Obj::mk_mpz(&[1], true),
                Obj::mk_array(vec![carrier.clone_ref()]),
            ],
        ),
    ] {
        assert!(matches!(
            execute(row, &args),
            Outcome::Complete(VmExit::Refused { .. })
        ));
    }
    let root = object(Expr::app(
        free.clone(),
        Expr::lam(
            Name::anonymous(),
            literal(0),
            free.clone(),
            BinderInfo::Default,
        ),
    ));
    let mut conversion = Conversion::new();
    let checked = conversion.check_expr(&root).unwrap();
    assert!(matches!(
        abstract_variables(
            &checked,
            &[free],
            &mut conversion,
            &mut WorkBudget {
                allowed: 5,
                visited: 0
            }
        ),
        Err(IntrinsicFailure::MirrorResource {
            resource: "expression traversal nodes",
            ..
        })
    ));
    assert!(matches!(
        Intrinsic::Abstract.invoke_bounded(
            "extern:Lean.Expr.abstract",
            &[carrier.clone_ref(), Obj::mk_array(vec![carrier])],
            1
        ),
        Err(IntrinsicFailure::MirrorResource { .. })
    ));
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
fn native_expr_lower_preserves_binder_contexts_metadata_and_shared_carriers() {
    use fln_core::options::{DataValue, KVMap};
    let name = Name::from_components(["retained"]);
    let metadata = KVMap::from_entries(vec![(name.clone(), DataValue::OfNat(9))]);
    let shared = Expr::app(bvar(2), bvar(4));
    let unchanged = Expr::mdata(metadata, Expr::proj(name.clone(), 7, shared.clone()));
    let root = Expr::app(
        shared.clone(),
        Expr::lam(
            name.clone(),
            shared.clone(),
            Expr::forall_e(
                name.clone(),
                shared.clone(),
                Expr::let_e(name.clone(), shared, literal(8), unchanged.clone(), true),
                BinderInfo::StrictImplicit,
            ),
            BinderInfo::InstImplicit,
        ),
    );
    let carrier = object(root.clone());
    let lowered = call(
        "extern:Lean.Expr.lowerLooseBVars",
        &[carrier.clone_ref(), Obj::mk_nat(2), Obj::mk_nat(1)],
    );
    let outer = Expr::app(bvar(1), bvar(3));
    let inner = Expr::app(bvar(2), bvar(3));
    assert_eq!(
        expression(&lowered),
        Expr::app(
            outer.clone(),
            Expr::lam(
                name.clone(),
                outer,
                Expr::forall_e(
                    name.clone(),
                    inner.clone(),
                    Expr::let_e(name, inner, literal(8), unchanged, true),
                    BinderInfo::StrictImplicit,
                ),
                BinderInfo::InstImplicit,
            ),
        )
    );
    let lambda = lowered.try_ctor_child(1).unwrap();
    assert_eq!(
        lowered.try_ctor_child(0).unwrap().identity_token(),
        lambda.try_ctor_child(1).unwrap().identity_token(),
        "equal binder contexts retain shared transformed carriers"
    );
    let original_lambda = carrier.try_ctor_child(1).unwrap();
    assert_eq!(
        lambda.try_ctor_child(0).unwrap().identity_token(),
        original_lambda.try_ctor_child(0).unwrap().identity_token(),
        "lowering retains binder names"
    );
    let original_let = original_lambda
        .try_ctor_child(2)
        .unwrap()
        .try_ctor_child(2)
        .unwrap();
    let lowered_let = lambda.try_ctor_child(2).unwrap().try_ctor_child(2).unwrap();
    assert_eq!(
        lowered_let.try_ctor_child(3).unwrap().identity_token(),
        original_let.try_ctor_child(3).unwrap().identity_token(),
        "a subtree below the local cutoff retains metadata and projection identity"
    );
    assert_eq!(expression(&carrier), root);
}

#[test]
fn native_expr_lower_observes_full_scalar_guard_and_validates_noops() {
    let carrier = object(bvar(2));
    for (cutoff, amount) in [
        (Obj::mk_nat(0), Obj::mk_nat(1)),
        (Obj::mk_nat(2), Obj::mk_nat(0)),
        (Obj::mk_nat(3), Obj::mk_nat(2)),
        (Obj::mk_nat(1), Obj::mk_nat(1_usize << 32)),
        (Obj::mk_mpz(&[0, 1], false), Obj::mk_nat(1)),
        (Obj::mk_nat(3), Obj::mk_mpz(&[0, 1], false)),
    ] {
        let result = call(
            "extern:Lean.Expr.lowerLooseBVars",
            &[carrier.clone_ref(), cutoff, amount],
        );
        assert_eq!(result.identity_token(), carrier.identity_token());
    }
    for (cutoff, amount, expected) in [
        (2, 1, 1),
        (2, 2, 0),
        ((1_usize << 32) + 1, 2, 0),
        ((1_usize << 32) + 2, (1_usize << 32) + 1, 1),
    ] {
        assert_eq!(
            expression(&call(
                "extern:Lean.Expr.lowerLooseBVars",
                &[
                    carrier.clone_ref(),
                    Obj::mk_nat(cutoff),
                    Obj::mk_nat(amount)
                ],
            )),
            bvar(expected)
        );
    }
    for args in [
        vec![Obj::mk_nat(0), Obj::mk_nat(0), Obj::mk_nat(0)],
        vec![carrier.clone_ref(), Obj::mk_mpz(&[1], true), Obj::mk_nat(0)],
        vec![carrier.clone_ref(), Obj::mk_nat(0), Obj::mk_mpz(&[1], true)],
    ] {
        assert!(matches!(
            execute("extern:Lean.Expr.lowerLooseBVars", &args),
            Outcome::Complete(VmExit::Refused { .. })
        ));
    }
    let shared = bvar(2);
    let root = object(Expr::app(
        shared.clone(),
        Expr::lam(Name::anonymous(), literal(0), shared, BinderInfo::Default),
    ));
    let mut conversion = Conversion::new();
    let checked = conversion.check_expr(&root).unwrap();
    assert!(matches!(
        lower_loose_bvars(
            &checked,
            1,
            1,
            &mut conversion,
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
}

#[test]
fn native_expr_alpha_equivalence_ignores_only_binder_names_and_annotations() {
    use fln_core::options::{DataValue, KVMap};
    let x = Name::from_components(["x"]);
    let y = Name::from_components(["y"]);
    let left = Expr::lam(x.clone(), literal(0), bvar(0), BinderInfo::Default);
    let right = Expr::lam(y.clone(), literal(0), bvar(0), BinderInfo::Implicit);
    let metadata = |value| KVMap::from_entries(vec![(x.clone(), DataValue::OfNat(value))]);
    for (left, right, expected) in [
        (left.clone(), right.clone(), true),
        (
            Expr::app(left.clone(), left.clone()),
            Expr::app(right.clone(), right.clone()),
            true,
        ),
        (
            Expr::forall_e(x.clone(), literal(0), bvar(0), BinderInfo::Default),
            Expr::forall_e(y.clone(), literal(0), bvar(0), BinderInfo::InstImplicit),
            true,
        ),
        (
            left.clone(),
            Expr::forall_e(y.clone(), literal(0), bvar(0), BinderInfo::Default),
            false,
        ),
        (
            Expr::let_e(x.clone(), literal(0), literal(1), bvar(0), false),
            Expr::let_e(y.clone(), literal(0), literal(1), bvar(0), false),
            true,
        ),
        (
            Expr::let_e(x.clone(), literal(0), literal(1), bvar(0), false),
            Expr::let_e(y, literal(0), literal(1), bvar(0), true),
            false,
        ),
        (
            Expr::mdata(metadata(1), left.clone()),
            Expr::mdata(metadata(1), right.clone()),
            true,
        ),
        (
            Expr::mdata(metadata(1), left.clone()),
            Expr::mdata(metadata(2), right),
            false,
        ),
        (
            left,
            Expr::lam(x, literal(0), bvar(1), BinderInfo::Default),
            false,
        ),
        (Expr::sort(Level::zero()), Expr::sort(Level::one()), false),
    ] {
        let args = [object(left), object(right)];
        assert_eq!(
            call("extern:Lean.Expr.eqv", &args).unbox(),
            usize::from(expected)
        );
        assert_eq!(call("extern:Lean.Expr.equal", &args).unbox(), 0);
    }
    assert!(matches!(
        execute(
            "extern:Lean.Expr.eqv",
            &[object(literal(0)), Obj::mk_nat(0)]
        ),
        Outcome::Complete(VmExit::Refused { .. })
    ));
    assert!(matches!(
        Intrinsic::Eqv.invoke_bounded(
            "extern:Lean.Expr.eqv",
            &[object(literal(0)), object(literal(0))],
            1
        ),
        Err(IntrinsicFailure::MirrorResource { .. })
    ));
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
