//! Terminal bytecode calls: codec, independent ownership validation, bounded
//! native execution, and continuation preservation on real Marrow objects.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as R, CodecLimits, Function, FunctionId,
    Instruction as I, OwnershipLimits, Pc, Program, Register, ResultOwnership, ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_rt::obj::shadow;
use fln_vm::extern_row::{ArgumentOwnership as CA, Ownership, ResultOwnership as CR};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{self, CompletedExecution, ExecutionLimits, VmExit};
use std::cell::Cell;
use std::sync::Mutex;

static LOCK: Mutex<()> = Mutex::new(());
const fn r(n: u16) -> Register {
    Register::new(n)
}
const fn f(n: u32) -> FunctionId {
    FunctionId::new(n)
}
fn function(id: u32, args: Vec<A>, result: R, registers: u16, code: Vec<I>) -> Function {
    Function {
        id: f(id),
        arity: u16::try_from(args.len()).unwrap(),
        parameter_ownership: args,
        result_ownership: result,
        register_count: registers,
        code,
    }
}
fn intrinsic(dst: u16, row: &str, args: Vec<Register>) -> I {
    let row = EXTERN_ROWS.iter().find(|entry| entry.id == row).unwrap();
    let contract = Ownership::parse(row.ownership).unwrap();
    let ownership = contract
        .argument_ownership(args.len())
        .unwrap()
        .into_iter()
        .map(|a| match a {
            CA::Borrowed => A::Borrowed,
            CA::Owned => A::Owned,
            CA::Unique => A::Unique,
            CA::Scalar => A::Scalar,
        })
        .collect();
    let result = match contract.result_ownership().unwrap() {
        CR::Borrowed => ResultOwnership::Borrowed,
        CR::Owned => ResultOwnership::Owned,
        CR::Scalar => ResultOwnership::Scalar,
        CR::RawObject => ResultOwnership::RawObject,
    };
    I::Intrinsic {
        dst: r(dst),
        row: row.id.to_string(),
        args,
        argument_ownership: ownership,
        result_ownership: result,
    }
}
fn tail(target: u32, args: Vec<Register>, ownership: Vec<A>, result: R) -> I {
    I::TailCall {
        function: f(target),
        args,
        argument_ownership: ownership,
        result_ownership: result,
    }
}
fn apply(closure: u16, args: Vec<Register>, ownership: Vec<A>, result: R) -> I {
    I::TailApply {
        closure: r(closure),
        args,
        argument_ownership: ownership,
        result_ownership: result,
    }
}
fn returned(outcome: Outcome<VmExit>) -> CompletedExecution {
    match outcome {
        Outcome::Complete(VmExit::Returned(value)) => value,
        other => panic!("execution did not return: {other:?}"),
    }
}
fn limits(depth: u64) -> ExecutionLimits {
    ExecutionLimits {
        max_stack_depth: depth,
        ..ExecutionLimits::default()
    }
}
fn checked(functions: Vec<Function>) -> ValidatedProgram {
    flbc::validate(Program::new(f(0), functions)).unwrap()
}
fn owned(program: &ValidatedProgram) -> ValidatedProgram {
    let owned = flbc::insert_ownership(program, OwnershipLimits::default()).unwrap();
    flbc::validate_ownership_candidate(
        program,
        owned.program().clone(),
        owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .unwrap();
    let bytes = flbc::encode_canonical(owned.program(), CodecLimits::default()).unwrap();
    flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap()
}
fn no_leaks() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "tail execution retains no unreachable handles");
    assert!(events.iter().all(|e| !matches!(
        e.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
}

fn countdown(count: u64, dynamic: bool, mutual: bool) -> ValidatedProgram {
    let ownership = vec![A::Borrowed, A::Owned, A::Owned];
    let entry = function(
        0,
        vec![],
        R::Owned,
        4,
        vec![
            I::Nat {
                dst: r(0),
                value: count,
            },
            I::String {
                dst: r(1),
                value: "left".into(),
            },
            I::String {
                dst: r(2),
                value: "right".into(),
            },
            I::String {
                dst: r(3),
                value: "unused, must be released".into(),
            },
            tail(1, vec![r(0), r(1), r(2)], ownership.clone(), R::Owned),
        ],
    );
    let worker = |id, target| {
        let mut code = vec![
            I::JumpIfZero {
                cond: r(0),
                zero: Pc::new(if dynamic { 5 } else { 4 }),
                nonzero: Pc::new(1),
            },
            I::Nat {
                dst: r(3),
                value: 1,
            },
            intrinsic(4, "extern:Nat.sub", vec![r(0), r(3)]),
        ];
        if dynamic {
            code.push(I::Closure {
                dst: r(5),
                function: f(target),
                captures: vec![r(4)],
                capture_ownership: vec![A::Borrowed],
            });
            code.push(apply(
                5,
                vec![r(2), r(1)],
                vec![A::Owned, A::Owned],
                R::Owned,
            ));
        } else {
            code.push(tail(
                target,
                vec![r(4), r(2), r(1)],
                ownership.clone(),
                R::Owned,
            ));
        }
        code.push(I::Return { src: r(1) });
        function(
            id,
            ownership.clone(),
            R::Owned,
            if dynamic { 6 } else { 5 },
            code,
        )
    };
    let mut functions = vec![entry, worker(1, if mutual { 2 } else { 1 })];
    if mutual {
        functions.push(worker(2, 1));
    }
    checked(functions)
}

#[test]
fn deep_direct_and_mutual_tail_calls_reuse_one_frame_and_permute_owned_arguments() {
    let _guard = LOCK.lock().unwrap();
    for mutual in [false, true] {
        let program = countdown(10_001, false, mutual);
        let optimized = owned(&program);
        for program in [&program, &optimized] {
            shadow::enable();
            let result = returned(interpreter::execute(program, limits(1), None));
            assert_eq!(result.value.string_view().3, b"right\0");
            assert_eq!(result.usage.peak_stack_depth, 1);
            drop(result);
            no_leaks();
        }
    }
}

#[test]
fn deep_exact_closure_tail_calls_keep_captures_and_release_old_frames() {
    let _guard = LOCK.lock().unwrap();
    let program = owned(&countdown(10_000, true, true));
    shadow::enable();
    let result = returned(interpreter::execute(&program, limits(1), None));
    assert_eq!(result.value.string_view().3, b"left\0");
    assert_eq!(result.usage.peak_stack_depth, 1);
    drop(result);
    no_leaks();
}

#[test]
fn fir_lowering_emits_tail_calls_that_transfer_owned_arguments_without_leaks() {
    use fln_comp::fir::{
        self, Binding, Block, BlockId, ClosureTypeDecl, ClosureTypeId, IntrinsicDecl, IntrinsicId,
        Operation, Terminator, ValueId, ValueType,
    };

    let _guard = LOCK.lock().unwrap();
    let value = ValueId::new;
    let block = BlockId::new;
    let target = fir::FunctionId::new;
    for dynamic in [false, true] {
        let worker = |id, next| {
            let mut bindings = vec![
                Binding {
                    id: value(3),
                    ty: ValueType::Nat,
                    operation: Operation::Nat(1),
                },
                Binding {
                    id: value(4),
                    ty: ValueType::Nat,
                    operation: Operation::Intrinsic {
                        intrinsic: IntrinsicId::new(0),
                        args: vec![value(0), value(3)],
                    },
                },
                Binding {
                    id: value(5),
                    ty: ValueType::String,
                    operation: Operation::String("retire this frame's local".into()),
                },
            ];
            let result = if dynamic {
                bindings.push(Binding {
                    id: value(6),
                    ty: ValueType::Closure(ClosureTypeId::new(0)),
                    operation: Operation::Closure {
                        closure_type: ClosureTypeId::new(0),
                        function: target(next),
                        captures: vec![value(4)],
                        capture_ownership: vec![A::Borrowed],
                    },
                });
                bindings.push(Binding {
                    id: value(7),
                    ty: ValueType::String,
                    operation: Operation::Apply {
                        closure: value(6),
                        args: vec![value(2), value(1)],
                        argument_ownership: vec![A::Owned, A::Owned],
                        result_ownership: R::Owned,
                    },
                });
                value(7)
            } else {
                bindings.push(Binding {
                    id: value(6),
                    ty: ValueType::String,
                    operation: Operation::Call {
                        function: target(next),
                        args: vec![value(4), value(2), value(1)],
                    },
                });
                value(6)
            };
            fir::Function {
                id: target(id),
                parameters: vec![ValueType::Nat, ValueType::String, ValueType::String],
                parameter_ownership: vec![A::Borrowed, A::Owned, A::Owned],
                result: ValueType::String,
                result_ownership: R::Owned,
                blocks: vec![
                    Block {
                        id: block(0),
                        bindings: Vec::new(),
                        terminator: Terminator::BranchZero {
                            condition: value(0),
                            zero: block(2),
                            nonzero: block(1),
                        },
                    },
                    Block {
                        id: block(1),
                        bindings,
                        terminator: Terminator::Return { value: result },
                    },
                    Block {
                        id: block(2),
                        bindings: Vec::new(),
                        terminator: Terminator::Return { value: value(1) },
                    },
                ],
            }
        };
        let entry = fir::Function {
            id: target(0),
            parameters: Vec::new(),
            parameter_ownership: Vec::new(),
            result: ValueType::String,
            result_ownership: R::Owned,
            blocks: vec![Block {
                id: block(0),
                bindings: vec![
                    Binding {
                        id: value(0),
                        ty: ValueType::Nat,
                        operation: Operation::Nat(1_001),
                    },
                    Binding {
                        id: value(1),
                        ty: ValueType::String,
                        operation: Operation::String("left".into()),
                    },
                    Binding {
                        id: value(2),
                        ty: ValueType::String,
                        operation: Operation::String("right".into()),
                    },
                    Binding {
                        id: value(3),
                        ty: ValueType::String,
                        operation: Operation::Call {
                            function: target(1),
                            args: vec![value(0), value(1), value(2)],
                        },
                    },
                ],
                terminator: Terminator::Return { value: value(3) },
            }],
        };
        let program = fir::Program::new_with_closures(
            target(0),
            Vec::new(),
            Vec::new(),
            vec![ClosureTypeDecl {
                id: ClosureTypeId::new(0),
                parameters: vec![ValueType::String, ValueType::String],
                parameter_ownership: vec![A::Owned, A::Owned],
                result: ValueType::String,
                result_ownership: R::Owned,
            }],
            vec![IntrinsicDecl {
                id: IntrinsicId::new(0),
                row: "extern:Nat.sub".into(),
                arguments: vec![ValueType::Nat, ValueType::Nat],
                argument_ownership: vec![A::Borrowed, A::Borrowed],
                result: ValueType::Nat,
                result_ownership: ResultOwnership::Owned,
                effect: fir::EffectClass::Pure,
            }],
            vec![entry, worker(1, 2), worker(2, 1)],
        );
        let validated = fir::validate(program, fir::ValidationLimits::default()).unwrap();
        let compiled =
            fir::lower_to_flbc_with_ownership(&validated, OwnershipLimits::default()).unwrap();
        let bytes = flbc::encode_canonical(compiled.program(), CodecLimits::default()).unwrap();
        let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
        shadow::enable();
        let result = returned(interpreter::execute(&decoded, limits(1), None));
        assert_eq!(result.value.string_view().3, b"right\0");
        assert_eq!(result.usage.peak_stack_depth, 1);
        drop(result);
        no_leaks();
    }
}

#[test]
fn tail_calls_inherit_an_ordinary_callers_return_destination() {
    let _guard = LOCK.lock().unwrap();
    let program = owned(&checked(vec![
        function(
            0,
            vec![],
            R::OwnedOrScalar,
            3,
            vec![
                I::Call {
                    dst: r(0),
                    function: f(1),
                    args: vec![],
                    argument_ownership: vec![],
                    result_ownership: R::OwnedOrScalar,
                },
                I::Nat {
                    dst: r(1),
                    value: 2,
                },
                intrinsic(2, "extern:Nat.add", vec![r(0), r(1)]),
                I::Return { src: r(2) },
            ],
        ),
        function(
            1,
            vec![],
            R::OwnedOrScalar,
            0,
            vec![tail(2, vec![], vec![], R::OwnedOrScalar)],
        ),
        function(
            2,
            vec![],
            R::OwnedOrScalar,
            1,
            vec![
                I::Nat {
                    dst: r(0),
                    value: 40,
                },
                I::Return { src: r(0) },
            ],
        ),
    ]));
    let result = returned(interpreter::execute(&program, limits(2), None));
    assert_eq!(result.value.unbox(), 42);
    assert_eq!(result.usage.peak_stack_depth, 2);
    assert!(matches!(
        interpreter::execute(&program, limits(1), None),
        Outcome::Inconclusive(_)
    ));
}

#[test]
fn partial_and_overapplied_tail_closures_complete_through_the_original_continuation() {
    let _guard = LOCK.lock().unwrap();
    let partial = owned(&checked(vec![
        function(
            0,
            vec![],
            R::Owned,
            2,
            vec![
                I::Nat {
                    dst: r(0),
                    value: 20,
                },
                I::Closure {
                    dst: r(1),
                    function: f(1),
                    captures: vec![],
                    capture_ownership: vec![],
                },
                apply(1, vec![r(0)], vec![A::Borrowed], R::Owned),
            ],
        ),
        function(
            1,
            vec![A::Borrowed; 2],
            R::OwnedOrScalar,
            3,
            vec![
                intrinsic(2, "extern:Nat.add", vec![r(0), r(1)]),
                I::Return { src: r(2) },
            ],
        ),
    ]));
    shadow::enable();
    let result = returned(interpreter::execute(&partial, limits(1), None));
    assert_eq!(result.value.closure_view(), (3, 2));
    drop(result);
    no_leaks();
    let over = owned(&checked(vec![
        function(
            0,
            vec![],
            R::OwnedOrScalar,
            3,
            vec![
                I::Nat {
                    dst: r(0),
                    value: 20,
                },
                I::Nat {
                    dst: r(1),
                    value: 22,
                },
                I::Closure {
                    dst: r(2),
                    function: f(1),
                    captures: vec![],
                    capture_ownership: vec![],
                },
                apply(2, vec![r(0), r(1)], vec![A::Borrowed; 2], R::OwnedOrScalar),
            ],
        ),
        function(
            1,
            vec![A::Borrowed],
            R::Owned,
            2,
            vec![
                I::Closure {
                    dst: r(1),
                    function: f(2),
                    captures: vec![r(0)],
                    capture_ownership: vec![A::Borrowed],
                },
                I::Return { src: r(1) },
            ],
        ),
        function(
            2,
            vec![A::Borrowed; 2],
            R::OwnedOrScalar,
            3,
            vec![
                intrinsic(2, "extern:Nat.add", vec![r(0), r(1)]),
                I::Return { src: r(2) },
            ],
        ),
    ]));
    shadow::enable();
    let result = returned(interpreter::execute(&over, limits(2), None));
    assert_eq!(result.value.unbox(), 42);
    assert_eq!(result.usage.peak_stack_depth, 2);
    drop(result);
    no_leaks();
    assert!(matches!(
        interpreter::execute(&over, limits(1), None),
        Outcome::Inconclusive(_)
    ));
}

#[test]
fn cancellation_and_execution_fuel_still_stop_deep_tail_loops_without_leaks() {
    let _guard = LOCK.lock().unwrap();
    let program = owned(&countdown(100_000, true, false));
    shadow::enable();
    let short = ExecutionLimits {
        max_steps: 100,
        ..limits(1)
    };
    assert!(matches!(interpreter::execute(&program, short, None),
        Outcome::Inconclusive(ref stop) if matches!(stop.cause,
            InconclusiveCause::ResourceExhausted { ref usage }
            if usage.reason == ResourceReason::ExecutionSteps && usage.observed == 101)));
    no_leaks();
    let polls = Cell::new(0usize);
    let cancel = || {
        let n = polls.get() + 1;
        polls.set(n);
        n == 100
    };
    shadow::enable();
    assert!(matches!(
        interpreter::execute(&program, limits(1), Some(&cancel)),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(polls.get(), 100);
    no_leaks();
}

#[test]
fn malformed_tail_contracts_and_use_after_consume_never_reach_execution() {
    let _guard = LOCK.lock().unwrap();
    for terminal in [
        tail(1, vec![r(0)], vec![A::Borrowed], R::Scalar),
        apply(0, vec![r(0)], vec![A::Borrowed], R::Scalar),
    ] {
        assert!(matches!(
            flbc::validate(Program::new(
                f(0),
                vec![
                    function(
                        0,
                        vec![],
                        R::Owned,
                        1,
                        vec![
                            I::Nat {
                                dst: r(0),
                                value: 0
                            },
                            terminal
                        ]
                    ),
                    function(
                        1,
                        vec![A::Borrowed],
                        R::Scalar,
                        1,
                        vec![I::Return { src: r(0) }]
                    ),
                ]
            )),
            Err(flbc::ValidationError::TailResultOwnershipContract { .. })
        ));
    }
    let bad = function(
        0,
        vec![],
        R::Owned,
        1,
        vec![
            I::String {
                dst: r(0),
                value: "gone".into(),
            },
            I::Drop { src: r(0) },
            tail(1, vec![r(0)], vec![A::Owned], R::Owned),
        ],
    );
    assert!(matches!(
        flbc::validate(Program::new(
            f(0),
            vec![
                bad,
                function(
                    1,
                    vec![A::Owned],
                    R::Owned,
                    1,
                    vec![I::Return { src: r(0) }]
                ),
            ]
        )),
        Err(flbc::ValidationError::ReadBeforeWrite { .. })
    ));
}

#[test]
fn a_tail_called_thunk_body_still_caches_its_result_exactly_once() {
    let _guard = LOCK.lock().unwrap();
    let parameters = vec![A::Borrowed, A::Scalar];
    let program = owned(&checked(vec![
        function(
            0,
            vec![],
            R::Owned,
            8,
            vec![
                I::Nat {
                    dst: r(0),
                    value: 0,
                },
                intrinsic(1, "extern:ST.Prim.mkRef", vec![r(0)]),
                I::Closure {
                    dst: r(2),
                    function: f(1),
                    captures: vec![r(1)],
                    capture_ownership: vec![A::Borrowed],
                },
                intrinsic(3, "extern:Thunk.mk", vec![r(2)]),
                intrinsic(4, "extern:Thunk.get", vec![r(3)]),
                intrinsic(5, "extern:Thunk.get", vec![r(3)]),
                intrinsic(6, "extern:ST.Prim.Ref.get", vec![r(1)]),
                I::Array {
                    dst: r(7),
                    items: vec![r(3), r(4), r(5), r(6)],
                },
                I::Return { src: r(7) },
            ],
        ),
        function(
            1,
            parameters.clone(),
            R::Owned,
            2,
            vec![tail(2, vec![r(0), r(1)], parameters.clone(), R::Owned)],
        ),
        function(
            2,
            parameters,
            R::Owned,
            7,
            vec![
                intrinsic(2, "extern:ST.Prim.Ref.get", vec![r(0)]),
                I::Nat {
                    dst: r(3),
                    value: 1,
                },
                intrinsic(4, "extern:Nat.add", vec![r(2), r(3)]),
                intrinsic(5, "extern:ST.Prim.Ref.set", vec![r(0), r(4)]),
                I::String {
                    dst: r(6),
                    value: "computed".into(),
                },
                I::Return { src: r(6) },
            ],
        ),
    ]));
    shadow::enable();
    let result = returned(interpreter::execute(&program, limits(2), None));
    assert_eq!(result.usage.peak_stack_depth, 2);
    assert_eq!(result.value.array_child(3).unbox(), 1);
    let first = result.value.array_child(1).identity_token();
    assert_eq!(first, result.value.array_child(2).identity_token());
    assert_eq!(
        first,
        result
            .value
            .array_child(0)
            .evaluated_thunk_value()
            .unwrap()
            .identity_token()
    );
    drop(result);
    no_leaks();
}

#[test]
fn managerless_task_completion_survives_a_tail_dispatch() {
    let _guard = LOCK.lock().unwrap();
    let program = owned(&checked(vec![
        function(
            0,
            vec![],
            R::Owned,
            4,
            vec![
                I::Closure {
                    dst: r(0),
                    function: f(1),
                    captures: vec![],
                    capture_ownership: vec![],
                },
                I::Nat {
                    dst: r(1),
                    value: 0,
                },
                intrinsic(2, "extern:Task.spawn", vec![r(0), r(1)]),
                intrinsic(3, "extern:Task.get", vec![r(2)]),
                I::Return { src: r(3) },
            ],
        ),
        function(
            1,
            vec![A::Scalar],
            R::Owned,
            1,
            vec![tail(2, vec![r(0)], vec![A::Scalar], R::Owned)],
        ),
        function(
            2,
            vec![A::Scalar],
            R::Owned,
            2,
            vec![
                I::String {
                    dst: r(1),
                    value: "task completed".into(),
                },
                I::Return { src: r(1) },
            ],
        ),
    ]));
    shadow::enable();
    let result = returned(interpreter::execute(&program, limits(2), None));
    assert_eq!(result.value.string_view().3, b"task completed\0");
    assert_eq!(result.usage.peak_stack_depth, 2);
    drop(result);
    no_leaks();
}

#[test]
fn terminal_frames_do_not_relax_argument_or_runtime_result_contracts() {
    let _guard = LOCK.lock().unwrap();
    let callee = function(
        1,
        vec![A::Owned],
        R::Owned,
        1,
        vec![I::Return { src: r(0) }],
    );
    for instruction in [
        tail(99, vec![r(0)], vec![A::Owned], R::Owned),
        tail(1, vec![], vec![], R::Owned),
        tail(1, vec![r(0)], vec![A::Borrowed], R::Owned),
        apply(0, vec![], vec![], R::Owned),
        apply(0, vec![r(0), r(0)], vec![A::Owned; 2], R::Owned),
        apply(0, vec![r(0)], vec![A::Unique], R::Owned),
    ] {
        let entry = function(
            0,
            vec![],
            R::Owned,
            1,
            vec![
                I::String {
                    dst: r(0),
                    value: "x".into(),
                },
                instruction,
            ],
        );
        assert!(flbc::validate(Program::new(f(0), vec![entry, callee.clone()])).is_err());
    }
    let invalid_scalar = checked(vec![
        function(
            0,
            vec![],
            R::Scalar,
            0,
            vec![tail(1, vec![], vec![], R::Scalar)],
        ),
        function(
            1,
            vec![],
            R::Scalar,
            1,
            vec![
                I::String {
                    dst: r(0),
                    value: "not scalar".into(),
                },
                I::Return { src: r(0) },
            ],
        ),
    ]);
    shadow::enable();
    assert!(matches!(
        interpreter::execute(&invalid_scalar, limits(1), None),
        Outcome::Complete(VmExit::Refused { .. })
    ));
    no_leaks();
}

#[test]
fn tails_round_trip_canonically_and_old_or_truncated_envelopes_are_refused() {
    let _guard = LOCK.lock().unwrap();
    let program = countdown(2, true, true);
    let bytes = flbc::encode_canonical(&program, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap(),
        bytes
    );
    for end in 0..bytes.len() {
        assert!(flbc::decode_canonical(&bytes[..end], CodecLimits::default()).is_err());
    }
    let mut old = bytes.clone();
    old[8..10].copy_from_slice(&9u16.to_le_bytes());
    assert!(matches!(
        flbc::decode_canonical(&old, CodecLimits::default()),
        Err(flbc::CodecError::UnsupportedWireVersion { seen: 9 })
    ));
    let mut old = bytes;
    old[10..12].copy_from_slice(&14u16.to_le_bytes());
    assert!(flbc::decode_canonical(&old, CodecLimits::default()).is_err());
}
