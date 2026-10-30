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
const ANY: &str = "extern:String.Internal.any";
const NEXT_WHILE: &str = "extern:String.Internal.nextWhile";
const ALL: &str = "extern:Substring.Raw.Internal.all";
const TAKE_WHILE: &str = "extern:Substring.Raw.Internal.takeWhile";
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

fn predicate_entry(row: &str, input: &str, begin: u64, end: u64) -> Function {
    let mut code = vec![
        string(0, input),
        closure(1, 1, &[], &[]),
        nat(2, begin),
        nat(3, end),
    ];
    let args = match row {
        ANY => vec![0, 1],
        NEXT_WHILE => vec![0, 1, 2],
        ALL | TAKE_WHILE => {
            code.push(I::Ctor {
                dst: r(4),
                tag: 0,
                fields: vec![r(0), r(2), r(3)],
                scalar_bytes: vec![],
            });
            vec![4, 1]
        }
        _ => unreachable!(),
    };
    code.extend([intrinsic(5, row, &args), I::Return { src: r(5) }]);
    function(0, vec![], C::Erased, 6, code)
}

fn character_predicate(character: char, equal: bool, ownership: A) -> Function {
    let mut code = vec![
        nat(1, u64::from(character)),
        intrinsic(2, "extern:Nat.beq", &[0, 1]),
    ];
    if !equal {
        code.extend([nat(3, 0), intrinsic(2, "extern:Nat.beq", &[2, 3])]);
    }
    code.push(I::Return { src: r(2) });
    function(1, vec![ownership], C::Scalar, 4, code)
}

#[test]
fn predicates_visit_unicode_scalars_and_raw_windows_through_owned_canonical_replay() {
    let _guard = lock();
    shadow::enable();
    for ownership in [A::Borrowed, A::Owned, A::Scalar] {
        for (row, input, begin, end, character, equal, expected) in [
            (ANY, "aλ😀\0z", 0, 0, '😀', true, 1),
            (ANY, "aλ😀\0z", 0, 0, '\0', true, 1),
            (ANY, "aλ😀z", 0, 0, 'x', true, 0),
            (NEXT_WHILE, "aλ😀z", 0, 0, 'z', false, 7),
            (NEXT_WHILE, "aλ😀z", 2, 0, 'A', true, 3),
            (ALL, "aλ😀z", 1, 7, 'z', false, 1),
            (ALL, "aλ😀z", 1, 7, '😀', false, 0),
            (TAKE_WHILE, "aλ😀z", 1, 7, '😀', false, 3),
            (TAKE_WHILE, "aλ😀z", 2, 8, 'A', true, 3),
            (TAKE_WHILE, "aλ😀z", 9, 12, 'A', true, 12),
        ] {
            let program = replay(vec![
                predicate_entry(row, input, begin, end),
                character_predicate(character, equal, ownership),
            ]);
            for program in [&program, &owned(&program)] {
                let result = returned(execute(program, limits(2), None));
                if row == TAKE_WHILE {
                    assert_eq!(text(&result.value.try_ctor_child(0).unwrap()), input);
                    assert_eq!(
                        result.value.try_ctor_child(1).unwrap().unbox(),
                        begin as usize
                    );
                    assert_eq!(result.value.try_ctor_child(2).unwrap().unbox(), expected);
                } else {
                    assert_eq!(result.value.unbox(), expected, "{row}, start {begin}");
                }
                assert_eq!(result.usage.peak_stack_depth, 2);
            }
        }
    }
    clean_shadow();
}

#[test]
fn empty_predicate_windows_do_not_enter_diverging_callbacks() {
    let _guard = lock();
    shadow::enable();
    for (row, input, start, stop, expected) in [
        (ANY, "", 0, 0, 0),
        (NEXT_WHILE, "aλ😀z", 99, 0, 99),
        (ALL, "aλ😀z", 1, 1, 1),
        (TAKE_WHILE, "aλ😀z", 7, 1, 7),
    ] {
        let program = replay(vec![
            predicate_entry(row, input, start, stop),
            function(
                1,
                vec![A::Scalar],
                C::Scalar,
                1,
                vec![I::Jump { target: Pc::new(0) }],
            ),
        ]);
        let result = returned(execute(&program, limits(1), None));
        let value = if row == TAKE_WHILE {
            result.value.try_ctor_child(2).unwrap()
        } else {
            result.value
        };
        assert_eq!(value.unbox(), expected);
        assert_eq!(result.usage.peak_stack_depth, 1);
    }
    clean_shadow();
}

#[test]
fn predicates_short_circuit_before_a_poisoned_suffix() {
    let _guard = lock();
    shadow::enable();
    for row in [ANY, NEXT_WHILE, ALL, TAKE_WHILE] {
        let mut callback = character_predicate('λ', row == ANY, A::Scalar);
        let suffix = callback.code.clone();
        callback.register_count = 6;
        callback.code = vec![
            nat(4, u64::from('z')),
            intrinsic(5, "extern:Nat.beq", &[0, 4]),
            I::JumpIfZero {
                cond: r(5),
                zero: Pc::new(5),
                nonzero: Pc::new(3),
            },
            string(4, "a short-circuited suffix executed"),
            I::Panic { message: r(4) },
        ];
        callback.code.extend(suffix);
        let program = owned(&replay(vec![predicate_entry(row, "aλz", 0, 4), callback]));
        let result = returned(execute(&program, limits(2), None));
        let actual = if row == TAKE_WHILE {
            result.value.try_ctor_child(2).unwrap().unbox()
        } else {
            result.value.unbox()
        };
        assert_eq!(actual, if row == ALL { 0 } else { 1 });
    }
    clean_shadow();
}

#[test]
fn predicate_callbacks_keep_captures_nested_folds_and_tail_return_conventions() {
    let _guard = lock();
    let mut main = predicate_entry(ANY, "aλ😀", 0, 0);
    main.register_count = 7;
    main.code.insert(1, string(6, "owned capture"));
    main.code[2] = closure(1, 1, &[6], &[A::Owned]);
    let program = owned(&replay(vec![
        main,
        function(
            1,
            vec![A::Owned, A::Scalar],
            C::Scalar,
            5,
            vec![
                closure(2, 2, &[], &[]),
                string(3, "λ"),
                intrinsic(4, FOLD, &[2, 0, 3]),
                I::TailCall {
                    function: f(3),
                    args: vec![r(1)],
                    argument_ownership: vec![A::Scalar],
                    result_ownership: C::Scalar,
                },
            ],
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
        {
            let mut callback = character_predicate('😀', true, A::Scalar);
            callback.id = f(3);
            callback
        },
    ]));
    shadow::enable();
    let result = returned(execute(&program, limits(3), None));
    assert_eq!(result.value.unbox(), 1);
    assert_eq!(result.usage.peak_stack_depth, 3);
    drop(result);
    resource(
        execute(&program, limits(2), None),
        ResourceReason::RecursionDepth { limit: 2 },
        2,
        3,
    );
    clean_shadow();
}

#[test]
fn malformed_predicates_cannot_return_non_booleans_or_claim_unique_characters() {
    let _guard = lock();
    shadow::enable();
    for callback in [
        function(
            1,
            vec![A::Scalar],
            C::Scalar,
            2,
            vec![nat(1, 2), I::Return { src: r(1) }],
        ),
        function(
            1,
            vec![A::Scalar],
            C::Owned,
            2,
            vec![string(1, "not Bool"), I::Return { src: r(1) }],
        ),
        function(
            1,
            vec![A::Unique],
            C::Scalar,
            2,
            vec![nat(1, 1), I::Return { src: r(1) }],
        ),
        function(
            1,
            vec![A::Scalar, A::Scalar],
            C::Scalar,
            2,
            vec![I::Return { src: r(1) }],
        ),
    ] {
        let program = replay(vec![predicate_entry(ANY, "x", 0, 0), callback]);
        assert!(matches!(
            execute(&program, limits(2), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::InvalidBoolScalar { .. }
                    | VmRefusal::TypeMismatch { .. }
                    | VmRefusal::ApplyOwnershipMismatch { .. }
                    | VmRefusal::MalformedClosure { .. },
                ..
            })
        ));
    }
    let mut main = predicate_entry(ANY, "", 0, 0);
    main.code[1] = nat(1, 0);
    let program = replay(vec![main]);
    assert!(matches!(
        execute(&program, limits(1), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch { .. },
            ..
        })
    ));
    clean_shadow();
}

#[test]
fn predicate_stops_drop_owned_state_and_huge_raw_positions_stay_arbitrary_precision() {
    let _guard = lock();
    shadow::enable();
    for row in [ANY, NEXT_WHILE, ALL, TAKE_WHILE] {
        let program = replay(vec![
            predicate_entry(row, "aλ😀", 0, 7),
            function(
                1,
                vec![A::Scalar],
                C::Scalar,
                1,
                vec![I::Jump { target: Pc::new(0) }],
            ),
        ]);
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
        let cancellation = || {
            polls.set(polls.get() + 1);
            polls.get() == 11
        };
        assert!(
            matches!(execute(&program, limits(2), Some(&cancellation)), Outcome::Inconclusive(stop)
            if matches!(stop.cause, InconclusiveCause::Cancelled { .. }))
        );
        assert_eq!(polls.get(), 11);
    }
    let mut main = predicate_entry(TAKE_WHILE, "aλ😀z", 0, 0);
    main.code[2] = I::NatBig {
        dst: r(2),
        limbs_le: vec![0, 1],
    };
    main.code[3] = I::NatBig {
        dst: r(3),
        limbs_le: vec![3, 1],
    };
    let program = owned(&replay(vec![
        main,
        character_predicate('A', true, A::Scalar),
    ]));
    let result = returned(execute(&program, limits(2), None));
    let stop = result.value.try_ctor_child(2).unwrap();
    assert_eq!(stop.try_mpz_view().unwrap().2, &[3, 1]);
    drop(stop);
    drop(result);
    resource(
        execute(
            &program,
            ExecutionLimits {
                max_nat_magnitude_bytes: 8,
                ..limits(2)
            },
            None,
        ),
        ResourceReason::Memory { limit_bytes: 8 },
        8,
        16,
    );
    clean_shadow();
}

#[test]
fn invalid_substring_all_preserves_the_pin_panic_default_and_capture_stop() {
    const TEST: &str = "invalid_substring_all_preserves_the_pin_panic_default_and_capture_stop";
    const CHILD: &str = "FLN_SUBSTRING_ALL_PANIC_TEST";
    if std::env::var_os(CHILD).is_none() {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", TEST, "--nocapture", "--test-threads=1"])
            .env(CHILD, "1")
            .env("LEAN_BACKTRACE", "0")
            .env_remove("LEAN_ABORT_ON_PANIC")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(output.stderr.is_empty());
        return;
    }
    let _guard = lock();
    const MESSAGE: &[u8] = b"PANIC at Option.get! Init.Data.Option.BasicAux:22:14: value is none\n";
    shadow::enable();
    // As in stdio_bridge, register the process-lifetime native streams in
    // this fresh subprocess so their retains have complete shadow provenance.
    drop(Obj::stdio_stdout().unwrap());
    for (start, stop) in [(2, 8), (7, 1), (0, 99)] {
        let program = replay(vec![
            predicate_entry(ALL, "aλ😀z", start, stop),
            function(
                1,
                vec![A::Scalar],
                C::Scalar,
                1,
                vec![I::Jump { target: Pc::new(0) }],
            ),
        ]);
        let capture = fln_rt::obj::StdoutCapture::begin_isolated(MESSAGE.len(), true).unwrap();
        let result = returned(execute(&program, limits(1), None));
        assert_eq!(result.value.unbox(), 1);
        drop(result);
        let output = capture.finish();
        assert_eq!(output.error, None);
        assert_eq!(output.bytes, MESSAGE);
        let capture = fln_rt::obj::StdoutCapture::begin_isolated(MESSAGE.len() - 1, true).unwrap();
        assert!(matches!(
            execute(&program, limits(1), None),
            Outcome::Inconclusive(_)
        ));
        let output = capture.finish();
        assert!(output.bytes.is_empty());
        assert_eq!(
            output.error,
            Some(fln_rt::obj::StdoutCaptureError::Limit {
                limit: MESSAGE.len() - 1,
                requested: MESSAGE.len(),
            })
        );
    }
    let (events, live) = shadow::disable_and_drain();
    // Three immortal streams, each with its stream record, Handle, and six
    // callbacks. No transient substring, continuation or result may remain.
    assert_eq!(live, 3 * (1 + 1 + 6));
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
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
