//! The pinned monomorphic String fold drives ordinary Golem callbacks through
//! canonical bytecode, including their ownership, suspension, and stop paths.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, OwnershipLimits, Pc, Program, Register, ResultOwnership as R,
    ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{Authority, InconclusiveCause, Outcome};
use fln_rt::{
    heartbeat,
    obj::{Obj, shadow},
};
use fln_vm::extern_row::{ArgumentOwnership as CA, Ownership, ResultOwnership as CR};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{
    CompletedExecution, ExecutionLimits, HeartbeatLimit, ValueKind, VmExit, VmRefusal, execute,
    execute_with_heartbeat_limit,
};
use std::cell::Cell;
use std::sync::{Mutex, MutexGuard};

const FOLD: &str = "extern:String.Internal.foldl";
static TEST_LOCK: Mutex<()> = Mutex::new(());

fn lock() -> MutexGuard<'static, ()> {
    TEST_LOCK.lock().unwrap_or_else(|error| error.into_inner())
}

const fn r(index: u16) -> Register {
    Register::new(index)
}

const fn f(index: u32) -> FunctionId {
    FunctionId::new(index)
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

fn string(dst: u16, value: &str) -> I {
    I::String {
        dst: r(dst),
        value: value.to_owned(),
    }
}

fn nat(dst: u16, value: u64) -> I {
    I::Nat { dst: r(dst), value }
}

fn closure(dst: u16, function: u32, captures: &[u16], ownership: &[A]) -> I {
    I::Closure {
        dst: r(dst),
        function: f(function),
        captures: captures.iter().copied().map(r).collect(),
        capture_ownership: ownership.to_vec(),
    }
}

fn intrinsic(dst: u16, row: &str, args: &[u16]) -> I {
    let row = EXTERN_ROWS.iter().find(|entry| entry.id == row).unwrap();
    let contract = Ownership::parse(row.ownership).unwrap();
    I::Intrinsic {
        dst: r(dst),
        row: row.id.to_owned(),
        args: args.iter().copied().map(r).collect(),
        argument_ownership: contract
            .argument_ownership(args.len())
            .unwrap()
            .into_iter()
            .map(|ownership| match ownership {
                CA::Borrowed => A::Borrowed,
                CA::Owned => A::Owned,
                CA::Unique => A::Unique,
                CA::Scalar => A::Scalar,
            })
            .collect(),
        result_ownership: match contract.result_ownership().unwrap() {
            CR::Borrowed => R::Borrowed,
            CR::Owned => R::Owned,
            CR::Scalar => R::Scalar,
            CR::RawObject => R::RawObject,
        },
    }
}

fn entry(initial: &str, input: &str) -> Function {
    function(
        0,
        vec![],
        C::Owned,
        4,
        vec![
            closure(0, 1, &[], &[]),
            string(1, initial),
            string(2, input),
            intrinsic(3, FOLD, &[0, 1, 2]),
            I::Return { src: r(3) },
        ],
    )
}

fn push_callback(ownership: Vec<A>) -> Function {
    function(
        1,
        ownership,
        C::Owned,
        3,
        vec![
            intrinsic(2, "extern:String.push", &[0, 1]),
            I::Return { src: r(2) },
        ],
    )
}

fn replay(functions: Vec<Function>) -> ValidatedProgram {
    let program = flbc::validate(Program::new(f(0), functions)).unwrap();
    let bytes = flbc::encode_canonical(&program, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap(),
        bytes
    );
    decoded
}

fn owned(program: &ValidatedProgram) -> ValidatedProgram {
    let candidate = flbc::insert_ownership(program, OwnershipLimits::default()).unwrap();
    flbc::validate_ownership_candidate(
        program,
        candidate.program().clone(),
        candidate.witness().clone(),
        OwnershipLimits::default(),
    )
    .unwrap();
    let bytes = flbc::encode_canonical(candidate.program(), CodecLimits::default()).unwrap();
    flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap()
}

fn returned(outcome: Outcome<VmExit>) -> CompletedExecution {
    match outcome {
        Outcome::Complete(VmExit::Returned(value)) => value,
        other => panic!("expected a native String fold result: {other:?}"),
    }
}

fn text(value: &Obj) -> String {
    let (size, _, length, bytes) = value.try_string_view().expect("a native String");
    assert_eq!(bytes[size - 1], 0);
    let text = std::str::from_utf8(&bytes[..size - 1]).unwrap();
    assert_eq!(length, text.chars().count());
    text.to_owned()
}

fn limits(depth: u64) -> ExecutionLimits {
    ExecutionLimits {
        max_stack_depth: depth,
        ..ExecutionLimits::default()
    }
}

fn clean_shadow() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "fold callbacks and stops retain no unreachable ABI objects"
    );
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
}

fn resource(outcome: Outcome<VmExit>, reason: ResourceReason, allowed: u64, observed: u64) {
    assert_eq!(outcome.authority(), Authority::NonAuthoritative);
    assert!(matches!(
        outcome,
        Outcome::Inconclusive(ref stop)
            if matches!(&stop.cause,
                InconclusiveCause::ResourceExhausted { usage }
                    if usage.reason == reason
                        && usage.allowed == allowed
                        && usage.observed == observed)
                && stop.progress.is_some()
    ));
}

#[test]
fn flat_callbacks_fold_unicode_scalars_in_order_with_native_argument_ownership() {
    let _guard = lock();
    let input = "aé🦀\0e\u{301}";
    shadow::enable();
    for accumulator in [A::Borrowed, A::Owned] {
        for character in [A::Borrowed, A::Owned, A::Scalar] {
            let program = replay(vec![
                entry("prefix:", input),
                push_callback(vec![accumulator, character]),
            ]);
            for program in [&program, &owned(&program)] {
                let result = returned(execute(program, limits(2), None));
                assert_eq!(text(&result.value), format!("prefix:{input}"));
                assert_eq!(result.usage.peak_stack_depth, 2);
            }
        }
    }
    clean_shadow();
}

#[test]
fn curried_callbacks_return_owned_closures_and_complete_each_character_before_the_next() {
    let _guard = lock();
    let program = replay(vec![
        entry("start:", "é\0🦀"),
        function(
            1,
            vec![A::Owned],
            C::Owned,
            2,
            vec![closure(1, 2, &[0], &[A::Owned]), I::Return { src: r(1) }],
        ),
        function(
            2,
            vec![A::Owned, A::Scalar],
            C::Owned,
            3,
            vec![
                intrinsic(2, "extern:String.push", &[0, 1]),
                I::Return { src: r(2) },
            ],
        ),
    ]);
    shadow::enable();
    for program in [&program, &owned(&program)] {
        let result = returned(execute(program, limits(2), None));
        assert_eq!(text(&result.value), "start:é\0🦀");
        assert_eq!(result.usage.peak_stack_depth, 2);
    }
    clean_shadow();
}

#[test]
fn borrowed_fold_inputs_and_owned_callback_captures_survive_repeated_canonical_calls() {
    let _guard = lock();
    let program = replay(vec![
        function(
            0,
            vec![],
            C::Owned,
            8,
            vec![
                string(0, "!"),
                I::Copy {
                    dst: r(7),
                    src: r(0),
                },
                closure(1, 1, &[7], &[A::Owned]),
                string(2, "prefix"),
                string(3, "aé"),
                intrinsic(4, FOLD, &[1, 2, 3]),
                intrinsic(5, FOLD, &[1, 4, 3]),
                I::Array {
                    dst: r(6),
                    items: [0, 2, 3, 4, 5].into_iter().map(r).collect(),
                },
                I::Return { src: r(6) },
            ],
        ),
        function(
            1,
            vec![A::Owned, A::Borrowed, A::Scalar],
            C::Owned,
            5,
            vec![
                intrinsic(3, "extern:String.Internal.append", &[1, 0]),
                intrinsic(4, "extern:String.push", &[3, 2]),
                I::Return { src: r(4) },
            ],
        ),
    ]);
    let program = owned(&program);
    shadow::enable();
    for _ in 0..2 {
        let result = returned(execute(&program, limits(2), None));
        for (index, expected) in ["!", "prefix", "aé", "prefix!a!é", "prefix!a!é!a!é"]
            .into_iter()
            .enumerate()
        {
            assert_eq!(text(&result.value.array_child(index)), expected);
        }
    }
    clean_shadow();
}

#[test]
fn nested_folds_and_tail_callbacks_keep_their_continuations_and_bounded_stack() {
    let _guard = lock();
    let nested = owned(&replay(vec![
        entry("", "ab"),
        function(
            1,
            vec![A::Owned, A::Scalar],
            C::Owned,
            6,
            vec![
                intrinsic(2, "extern:String.push", &[0, 1]),
                closure(3, 2, &[], &[]),
                string(4, "λ"),
                intrinsic(5, FOLD, &[3, 2, 4]),
                I::Return { src: r(5) },
            ],
        ),
        function(
            2,
            vec![A::Owned, A::Scalar],
            C::Owned,
            2,
            vec![I::TailCall {
                function: f(3),
                args: vec![r(0), r(1)],
                argument_ownership: vec![A::Owned, A::Scalar],
                result_ownership: C::Owned,
            }],
        ),
        function(
            3,
            vec![A::Owned, A::Scalar],
            C::Owned,
            3,
            vec![
                intrinsic(2, "extern:String.push", &[0, 1]),
                I::Return { src: r(2) },
            ],
        ),
    ]));
    shadow::enable();
    let result = returned(execute(&nested, limits(3), None));
    assert_eq!(text(&result.value), "aλbλ");
    assert_eq!(result.usage.peak_stack_depth, 3);
    drop(result);
    resource(
        execute(&nested, limits(2), None),
        ResourceReason::RecursionDepth { limit: 2 },
        2,
        3,
    );
    // Each character still executes its callback. The fold continuation is
    // replaced after each return instead of accumulating one frame per byte.
    let long = replay(vec![
        entry("kept", &"é".repeat(10_000)),
        function(
            1,
            vec![A::Owned, A::Scalar],
            C::Owned,
            2,
            vec![I::Return { src: r(0) }],
        ),
    ]);
    let result = returned(execute(&long, limits(2), None));
    assert_eq!(text(&result.value), "kept");
    assert_eq!(result.usage.peak_stack_depth, 2);
    assert_eq!(result.usage.steps, 10_005);
    drop(result);
    clean_shadow();
}

#[test]
fn an_empty_string_returns_the_initial_value_without_entering_a_diverging_callback() {
    let _guard = lock();
    let program = replay(vec![
        entry("same\0é", ""),
        function(
            1,
            vec![A::Borrowed, A::Scalar],
            C::Owned,
            2,
            vec![I::Jump { target: Pc::new(0) }],
        ),
    ]);
    shadow::enable();
    let result = returned(execute(
        &program,
        ExecutionLimits {
            max_steps: 5,
            ..limits(1)
        },
        None,
    ));
    assert_eq!(text(&result.value), "same\0é");
    assert_eq!(result.usage.steps, 5);
    assert_eq!(result.usage.peak_stack_depth, 1);
    drop(result);
    clean_shadow();
}

#[test]
fn malformed_fold_operands_and_callback_contracts_are_typed_refusals() {
    let _guard = lock();
    shadow::enable();
    for argument in 0..3 {
        let mut main = entry("prefix", "x");
        main.code[argument] = nat(argument as u16, 0);
        let program = replay(vec![main, push_callback(vec![A::Owned, A::Scalar])]);
        assert!(matches!(
            execute(&program, limits(2), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch {
                    actual: ValueKind::Scalar,
                    ..
                },
                ..
            })
        ));
    }
    for parameters in [
        vec![A::Owned, A::Scalar, A::Scalar],
        vec![A::Unique, A::Scalar],
    ] {
        let program = replay(vec![
            entry("prefix", "x"),
            function(1, parameters, C::Owned, 3, vec![I::Return { src: r(0) }]),
        ]);
        assert!(matches!(
            execute(&program, limits(2), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::MalformedClosure { .. }
                    | VmRefusal::ApplyOwnershipMismatch { .. },
                ..
            })
        ));
    }
    let wrong_result = replay(vec![
        entry("prefix", "x"),
        function(
            1,
            vec![A::Owned, A::Scalar],
            C::Scalar,
            2,
            vec![I::Return { src: r(1) }],
        ),
    ]);
    assert!(matches!(
        execute(&wrong_result, limits(2), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::ApplyResultOwnershipMismatch { .. },
            ..
        })
    ));
    for callback in [
        function(
            1,
            vec![A::Owned, A::Scalar],
            C::Owned,
            3,
            vec![
                I::Array {
                    dst: r(2),
                    items: vec![r(0)],
                },
                I::Return { src: r(2) },
            ],
        ),
        function(
            1,
            vec![A::Owned],
            C::Owned,
            1,
            vec![I::Return { src: r(0) }],
        ),
    ] {
        let program = replay(vec![entry("prefix", "x"), callback]);
        assert!(matches!(
            execute(&program, limits(2), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch { .. },
                ..
            })
        ));
    }
    let mut main = entry("prefix", "x");
    main.code[3] = intrinsic(3, FOLD, &[0, 1]);
    let wrong_arity = replay(vec![main, push_callback(vec![A::Owned, A::Scalar])]);
    assert!(matches!(
        execute(&wrong_arity, limits(2), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::IntrinsicArity {
                expected: 3,
                actual: 2,
                ..
            },
            ..
        })
    ));
    let mut main = entry("prefix", "x");
    if let I::Intrinsic {
        argument_ownership, ..
    } = &mut main.code[3]
    {
        argument_ownership[0] = A::Owned;
    }
    let wrong_ownership = replay(vec![main, push_callback(vec![A::Owned, A::Scalar])]);
    assert!(matches!(
        execute(&wrong_ownership, limits(2), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::IntrinsicOwnershipMismatch { argument: 0, .. },
            ..
        })
    ));
    clean_shadow();
}

#[test]
fn callback_steps_cancellation_and_stack_limits_stop_without_retaining_a_partial_fold() {
    let _guard = lock();
    let program = replay(vec![
        entry("owned initial", "é🦀"),
        function(
            1,
            vec![A::Owned, A::Scalar],
            C::Owned,
            2,
            vec![I::Jump { target: Pc::new(0) }],
        ),
    ]);
    shadow::enable();
    resource(
        execute(
            &program,
            ExecutionLimits {
                max_steps: 37,
                ..limits(2)
            },
            None,
        ),
        ResourceReason::ExecutionSteps,
        37,
        38,
    );
    resource(
        execute(&program, limits(1), None),
        ResourceReason::RecursionDepth { limit: 1 },
        1,
        2,
    );
    let polls = Cell::new(0);
    let cancel_in_callback = || {
        polls.set(polls.get() + 1);
        polls.get() == 9
    };
    let cancelled = execute(&program, limits(2), Some(&cancel_in_callback));
    assert_eq!(cancelled.authority(), Authority::NonAuthoritative);
    assert!(matches!(
        cancelled,
        Outcome::Inconclusive(stop)
            if matches!(stop.cause, InconclusiveCause::Cancelled { .. })
    ));
    assert_eq!(polls.get(), 9);
    let retry = replay(vec![
        entry("owned initial", "é🦀"),
        push_callback(vec![A::Owned, A::Scalar]),
    ]);
    let result = returned(execute(&retry, limits(2), None));
    assert_eq!(text(&result.value), "owned initialé🦀");
    drop(result);
    clean_shadow();
}

#[test]
fn callback_panics_and_allocation_limits_propagate_through_the_fold_continuation() {
    let _guard = lock();
    let panic = replay(vec![
        entry("prefix", "é"),
        function(
            1,
            vec![A::Owned, A::Scalar],
            C::Owned,
            3,
            vec![string(2, "fold callback panic"), I::Panic { message: r(2) }],
        ),
    ]);
    shadow::enable();
    assert!(matches!(
        execute(&panic, limits(2), None),
        Outcome::Complete(VmExit::Panicked { message, .. }) if message == "fold callback panic"
    ));
    const OUTPUT_LIMIT: u64 = 16 * 1024 * 1024;
    let growth = replay(vec![
        entry("é", "🦀"),
        function(
            1,
            vec![A::Owned, A::Scalar],
            C::Owned,
            4,
            vec![
                nat(2, OUTPUT_LIMIT / 4 + 1),
                intrinsic(3, "extern:String.Internal.pushn", &[0, 1, 2]),
                I::Return { src: r(3) },
            ],
        ),
    ]);
    resource(
        execute(&growth, limits(2), None),
        ResourceReason::Memory {
            limit_bytes: OUTPUT_LIMIT,
        },
        OUTPUT_LIMIT,
        OUTPUT_LIMIT + 6,
    );
    clean_shadow();
}

#[test]
fn callback_checkpoints_use_the_vm_allocation_heartbeat_context() {
    let _guard = lock();
    let program = replay(vec![
        entry("prefix", "x"),
        function(
            1,
            vec![A::Owned, A::Scalar],
            C::Owned,
            4,
            vec![
                nat(2, 1_001),
                intrinsic(3, "extern:IO.setNumHeartbeats", &[2]),
                I::CheckSystem {
                    module_name: "String.fold.callback".to_owned(),
                },
                I::Return { src: r(0) },
            ],
        ),
    ]);
    shadow::enable();
    heartbeat::set_allocation_heartbeats(0);
    resource(
        execute_with_heartbeat_limit(
            &program,
            limits(2),
            HeartbeatLimit::from_option_units(1),
            None,
        ),
        ResourceReason::Heartbeats {
            consumed: 1_001,
            limit: 1_000,
        },
        1_000,
        1_001,
    );
    heartbeat::set_allocation_heartbeats(0);
    let result = returned(execute_with_heartbeat_limit(
        &program,
        limits(2),
        HeartbeatLimit::UNLIMITED,
        None,
    ));
    assert_eq!(text(&result.value), "prefix");
    drop(result);
    heartbeat::set_allocation_heartbeats(0);
    clean_shadow();
}
