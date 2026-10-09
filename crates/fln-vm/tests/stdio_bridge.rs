//! Bounded native stdout dispatch through validated FLBC. The ABI suite
//! captures actual output; these cells write only empty strings and exercise
//! Apply, TailApply, ownership insertion, continuations, and warm caches.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as R, CodecLimits, Function, FunctionId,
    Instruction as I, OwnershipLimits, Program, Register, ResultOwnership, ValidatedProgram,
};
use fln_core::mode::{BuildProfileId, ContentRoot, Mode};
use fln_core::outcome::Outcome;
use fln_rt::obj::{Obj, shadow};
use fln_vm::extern_row::{ArgumentOwnership as CA, Ownership, ResultOwnership as CR};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{
    CompletedExecution, ExecutionCacheContext, ExecutionLimits, InlineCaches, VmExit, VmRefusal,
    execute, execute_cached,
};
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

fn get_stdout(dst: u16) -> I {
    let row = EXTERN_ROWS
        .iter()
        .find(|row| row.id == "extern:IO.getStdout")
        .unwrap();
    assert_eq!(row.symbol, "lean_get_stdout");
    assert_eq!(row.arity, 0);
    assert_eq!(row.effect, "io");
    let ownership = Ownership::parse(row.ownership).unwrap();
    let arguments = ownership
        .argument_ownership(0)
        .unwrap()
        .into_iter()
        .map(|value| match value {
            CA::Borrowed => A::Borrowed,
            CA::Owned => A::Owned,
            CA::Unique => A::Unique,
            CA::Scalar => A::Scalar,
        })
        .collect();
    let result = match ownership.result_ownership().unwrap() {
        CR::Borrowed => ResultOwnership::Borrowed,
        CR::Owned => ResultOwnership::Owned,
        CR::Scalar => ResultOwnership::Scalar,
        CR::RawObject => ResultOwnership::RawObject,
    };
    I::Intrinsic {
        dst: r(dst),
        row: row.id.to_string(),
        args: Vec::new(),
        argument_ownership: arguments,
        result_ownership: result,
    }
}

fn raw_program(functions: Vec<Function>) -> ValidatedProgram {
    flbc::validate(Program::new(f(0), functions)).unwrap()
}

fn owned_program(program: &ValidatedProgram) -> ValidatedProgram {
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
        other => panic!("execution did not return: {other:?}"),
    }
}

fn refused(outcome: Outcome<VmExit>) -> VmRefusal {
    match outcome {
        Outcome::Complete(VmExit::Refused { refusal, .. }) => refusal,
        other => panic!("execution did not refuse: {other:?}"),
    }
}

fn start_shadow_test(test_name: &str) -> bool {
    const CHILD: &str = "FLN_STDIO_SHADOW_PROCESS_CASE";
    if std::env::var(CHILD).as_deref() != Ok(test_name) {
        let output = std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact", test_name, "--nocapture", "--test-threads=1"])
            .env(CHILD, test_name)
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success()
                && stdout.contains("test result: ok. 1 passed; 0 failed; 0 ignored;"),
            "{stdout}\n{}",
            String::from_utf8_lossy(&output.stderr),
        );
        return false;
    }
    // The process-initial streams are immortal. A fresh subprocess lets the
    // allocation shadow observe their construction, so every getter and field
    // retain below has registered provenance without exempting any RC fault.
    shadow::enable();
    drop(Obj::stdio_stdout().unwrap());
    true
}

fn no_leaks() {
    let (events, live) = shadow::disable_and_drain();
    // The three native initial streams each own one Handle and six closures.
    // All 24 objects are intentionally persistent; every temporary must settle.
    assert_eq!(
        live,
        3 * (1 + 1 + 6),
        "only the immortal stdio graph remains"
    );
    let faults = events
        .iter()
        .filter(|event| {
            matches!(
                event.kind,
                shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
            )
        })
        .collect::<Vec<_>>();
    assert!(faults.is_empty(), "ownership faults: {faults:?}");
}

fn assert_success_packet(value: &Obj) {
    assert_eq!(value.header().tag, 0);
    assert_eq!(value.header().other, 6);
    for (field, expected) in [1, 0, 0, 0].into_iter().enumerate() {
        let value = value.try_ctor_child(field).unwrap();
        assert!(value.is_scalar());
        assert_eq!(value.unbox(), expected);
    }
    for field in [4, 5] {
        let value = value.try_ctor_child(field).unwrap();
        let (size, _, length, bytes) = value.try_string_view().unwrap();
        assert_eq!((size, length, bytes), (1, 0, vec![0]));
    }
}

fn callback_prefix(field: u16) -> Vec<I> {
    vec![
        get_stdout(0),
        I::CtorField {
            dst: r(1),
            src: r(0),
            expected_tag: 0,
            expected_fields: 6,
            field,
        },
        I::String {
            dst: r(2),
            value: String::new(),
        },
        I::Nat {
            dst: r(3),
            value: 0,
        },
    ]
}

fn callback_program(
    tail: bool,
    field: u16,
    args: Vec<Register>,
    ownership: Vec<A>,
    result: R,
) -> ValidatedProgram {
    let mut code = callback_prefix(field);
    if tail {
        code.push(I::TailApply {
            closure: r(1),
            args,
            argument_ownership: ownership,
            result_ownership: result,
        });
    } else {
        code.push(I::Apply {
            dst: r(4),
            closure: r(1),
            args,
            argument_ownership: ownership,
            result_ownership: result,
        });
        code.push(I::Return { src: r(4) });
    }
    raw_program(vec![function(0, Vec::new(), result, 5, code)])
}

#[test]
fn stdout_getter_preserves_the_native_stream_and_only_put_str_is_supported() {
    let _lock = LOCK.lock().unwrap_or_else(|error| error.into_inner());
    if !start_shadow_test("stdout_getter_preserves_the_native_stream_and_only_put_str_is_supported")
    {
        return;
    }
    {
        let program = raw_program(vec![function(
            0,
            Vec::new(),
            R::Owned,
            1,
            vec![get_stdout(0), I::Return { src: r(0) }],
        )]);
        let stream = returned(execute(&program, ExecutionLimits::default(), None)).value;
        assert_eq!(stream.header().tag, 0);
        assert_eq!(stream.header().other, 6);
        for field in 0..6 {
            let callback = stream.try_ctor_child(field).unwrap();
            assert!(callback.closure_shell_parts().is_none());
            assert_eq!(callback.is_stdio_put_str_closure(), field == 4);
        }
    }
    no_leaks();
}

#[test]
fn stdout_apply_and_tail_apply_preserve_transport_through_ownership_and_warm_caches() {
    let _lock = LOCK.lock().unwrap_or_else(|error| error.into_inner());
    if !start_shadow_test(
        "stdout_apply_and_tail_apply_preserve_transport_through_ownership_and_warm_caches",
    ) {
        return;
    }
    {
        for tail in [false, true] {
            let raw = callback_program(tail, 4, vec![r(2), r(3)], vec![A::Borrowed; 2], R::Owned);
            let owned = owned_program(&raw);
            for program in [&raw, &owned] {
                let ordinary = returned(execute(program, ExecutionLimits::default(), None));
                assert_success_packet(&ordinary.value);
                assert_eq!(ordinary.usage.peak_stack_depth, 1);
                let mut caches = InlineCaches::try_new(1024).unwrap();
                let context = ExecutionCacheContext::new(
                    ContentRoot::new([39; 32]),
                    BuildProfileId::new(7),
                    Mode::Sound,
                );
                for _ in 0..3 {
                    let cached = returned(execute_cached(
                        program,
                        ExecutionLimits::default(),
                        None,
                        context,
                        &mut caches,
                    ));
                    assert_success_packet(&cached.value);
                    assert_eq!(cached.usage, ordinary.usage);
                }
                assert!(
                    caches.stats().hits > 0,
                    "the getter/projection have warm cache hits"
                );
            }
        }
    }
    no_leaks();
}

#[test]
fn stdout_golem_overapplication_reaches_the_same_checked_native_continuation() {
    let _lock = LOCK.lock().unwrap_or_else(|error| error.into_inner());
    if !start_shadow_test(
        "stdout_golem_overapplication_reaches_the_same_checked_native_continuation",
    ) {
        return;
    }
    {
        for tail in [false, true] {
            let mut code = callback_prefix(4);
            code.push(I::Closure {
                dst: r(4),
                function: f(1),
                captures: Vec::new(),
                capture_ownership: Vec::new(),
            });
            let args = vec![r(1), r(2), r(3)];
            if tail {
                code.push(I::TailApply {
                    closure: r(4),
                    args,
                    argument_ownership: vec![A::Borrowed; 3],
                    result_ownership: R::Owned,
                });
            } else {
                code.push(I::Apply {
                    dst: r(5),
                    closure: r(4),
                    args,
                    argument_ownership: vec![A::Borrowed; 3],
                    result_ownership: R::Owned,
                });
                code.push(I::Return { src: r(5) });
            }
            let raw = raw_program(vec![
                function(0, Vec::new(), R::Owned, 6, code),
                function(
                    1,
                    vec![A::Borrowed],
                    R::Owned,
                    1,
                    vec![I::Return { src: r(0) }],
                ),
            ]);
            let owned = owned_program(&raw);
            for program in [&raw, &owned] {
                let result = returned(execute(program, ExecutionLimits::default(), None));
                assert_success_packet(&result.value);
                assert_eq!(result.usage.peak_stack_depth, 2);
            }
        }
    }
    no_leaks();
}

#[test]
fn stdout_native_dispatch_refuses_partial_overapplied_and_mismatched_ownership_calls() {
    let _lock = LOCK.lock().unwrap_or_else(|error| error.into_inner());
    if !start_shadow_test(
        "stdout_native_dispatch_refuses_partial_overapplied_and_mismatched_ownership_calls",
    ) {
        return;
    }
    {
        for (args, ownership, result) in [
            (vec![r(2)], vec![A::Borrowed], R::Owned),
            (vec![r(2), r(3), r(3)], vec![A::Borrowed; 3], R::Owned),
            (vec![r(2), r(3)], vec![A::Owned, A::Borrowed], R::Owned),
            (vec![r(2), r(3)], vec![A::Borrowed, A::Scalar], R::Owned),
            (vec![r(2), r(3)], vec![A::Borrowed; 2], R::Scalar),
            (vec![r(2), r(3)], vec![A::Borrowed; 2], R::Erased),
        ] {
            for tail in [false, true] {
                let program = callback_program(tail, 4, args.clone(), ownership.clone(), result);
                assert!(matches!(
                    refused(execute(&program, ExecutionLimits::default(), None)),
                    VmRefusal::NativeStdoutContract { .. }
                ));
            }
        }
    }
    no_leaks();
}

#[test]
fn stdout_native_dispatch_refuses_non_string_world_and_unreviewed_methods() {
    let _lock = LOCK.lock().unwrap_or_else(|error| error.into_inner());
    if !start_shadow_test("stdout_native_dispatch_refuses_non_string_world_and_unreviewed_methods")
    {
        return;
    }
    {
        for field in [0, 1, 2, 3, 5] {
            let program = callback_program(
                false,
                field,
                vec![r(2), r(3)],
                vec![A::Borrowed; 2],
                R::Owned,
            );
            assert_eq!(
                refused(execute(&program, ExecutionLimits::default(), None)),
                VmRefusal::UnsupportedNativeClosure
            );
        }
        let wrong_text =
            callback_program(false, 4, vec![r(3), r(3)], vec![A::Borrowed; 2], R::Owned);
        assert!(matches!(
            refused(execute(&wrong_text, ExecutionLimits::default(), None)),
            VmRefusal::TypeMismatch { argument: 0, .. }
        ));
        for world in [
            I::Nat {
                dst: r(3),
                value: 1,
            },
            I::Ctor {
                dst: r(3),
                tag: 0,
                fields: Vec::new(),
                scalar_bytes: Vec::new(),
            },
        ] {
            let mut code = callback_prefix(4);
            code[3] = world;
            code.push(I::Apply {
                dst: r(4),
                closure: r(1),
                args: vec![r(2), r(3)],
                argument_ownership: vec![A::Borrowed; 2],
                result_ownership: R::Owned,
            });
            code.push(I::Return { src: r(4) });
            let program = raw_program(vec![function(0, Vec::new(), R::Owned, 5, code)]);
            assert!(matches!(
                refused(execute(&program, ExecutionLimits::default(), None)),
                VmRefusal::TypeMismatch { argument: 1, .. }
            ));
        }
    }
    no_leaks();
}

#[test]
fn stdout_action_construction_does_not_invoke_the_native_getter_or_callback() {
    let _lock = LOCK.lock().unwrap_or_else(|error| error.into_inner());
    if !start_shadow_test(
        "stdout_action_construction_does_not_invoke_the_native_getter_or_callback",
    ) {
        return;
    }
    {
        let raw = raw_program(vec![
            function(
                0,
                Vec::new(),
                R::Owned,
                1,
                vec![
                    I::Closure {
                        dst: r(0),
                        function: f(1),
                        captures: Vec::new(),
                        capture_ownership: Vec::new(),
                    },
                    I::Return { src: r(0) },
                ],
            ),
            function(
                1,
                vec![A::Borrowed],
                R::Owned,
                4,
                vec![
                    get_stdout(1),
                    I::CtorField {
                        dst: r(2),
                        src: r(1),
                        expected_tag: 0,
                        expected_fields: 6,
                        field: 4,
                    },
                    I::String {
                        dst: r(3),
                        value: "an unexecuted IO action".to_string(),
                    },
                    I::TailApply {
                        closure: r(2),
                        args: vec![r(3), r(0)],
                        argument_ownership: vec![A::Borrowed; 2],
                        result_ownership: R::Owned,
                    },
                ],
            ),
        ]);
        let value = returned(execute(&raw, ExecutionLimits::default(), None));
        assert!(value.value.closure_shell_parts().is_some());
        assert_eq!(value.usage.steps, 2);
        let owned = owned_program(&raw);
        let value = returned(execute(&owned, ExecutionLimits::default(), None));
        assert!(value.value.closure_shell_parts().is_some());
    }
    no_leaks();
}

const WRITE_MARKER: &str = "FLN_STDOUT_EFFECT_PROBE_7AD9";
const PROCESS_CASE: &str = "FLN_STDIO_BRIDGE_PROCESS_CASE";

fn write_probe_program(case: &str) -> ValidatedProgram {
    let mut code = callback_prefix(if case == "unknown_target" { 0 } else { 4 });
    code[2] = I::String {
        dst: r(2),
        value: WRITE_MARKER.to_string(),
    };
    let mut args = vec![r(2), r(3)];
    let mut ownership = vec![A::Borrowed; 2];
    let mut result = R::Owned;
    match case {
        "success" | "unknown_target" => {}
        "partial" => {
            args.pop();
            ownership.pop();
        }
        "third_argument" | "tail_third_argument" => {
            args.push(r(3));
            ownership.push(A::Borrowed);
        }
        "owned_text" => ownership[0] = A::Owned,
        "scalar_world_contract" => ownership[1] = A::Scalar,
        "scalar_result" => result = R::Scalar,
        "wrong_world" => {
            code[3] = I::Nat {
                dst: r(3),
                value: 1,
            }
        }
        "wrong_string" => {
            code[2] = I::Nat {
                dst: r(2),
                value: 0,
            }
        }
        "golem_then_third_argument" => {
            code.push(I::Closure {
                dst: r(4),
                function: f(1),
                captures: Vec::new(),
                capture_ownership: Vec::new(),
            });
            code.push(I::Apply {
                dst: r(5),
                closure: r(4),
                args: vec![r(1), r(2), r(3), r(3)],
                argument_ownership: vec![A::Borrowed; 4],
                result_ownership: R::Owned,
            });
            code.push(I::Return { src: r(5) });
            return raw_program(vec![
                function(0, Vec::new(), R::Owned, 6, code),
                function(
                    1,
                    vec![A::Borrowed],
                    R::Owned,
                    1,
                    vec![I::Return { src: r(0) }],
                ),
            ]);
        }
        _ => panic!("unknown capture case {case}"),
    }
    if case == "tail_third_argument" {
        code.push(I::TailApply {
            closure: r(1),
            args,
            argument_ownership: ownership,
            result_ownership: result,
        });
    } else {
        code.push(I::Apply {
            dst: r(4),
            closure: r(1),
            args,
            argument_ownership: ownership,
            result_ownership: result,
        });
        code.push(I::Return { src: r(4) });
    }
    raw_program(vec![function(0, Vec::new(), result, 5, code)])
}

#[test]
fn stdout_refusals_do_not_write_to_the_captured_process_stream() {
    // Re-enter only this same cell in a subprocess. Its actual C FILE stdout
    // is captured by Command, so nonempty writes cannot hide behind a Rust
    // test-harness print hook. The success case proves the capture sees them.
    if let Ok(case) = std::env::var(PROCESS_CASE) {
        let program = write_probe_program(&case);
        let outcome = execute(&program, ExecutionLimits::default(), None);
        if case == "success" {
            assert_success_packet(&returned(outcome).value);
        } else {
            let refusal = refused(outcome);
            match case.as_str() {
                "unknown_target" => assert_eq!(refusal, VmRefusal::UnsupportedNativeClosure),
                "wrong_world" | "wrong_string" => {
                    assert!(matches!(refusal, VmRefusal::TypeMismatch { .. }))
                }
                _ => assert!(matches!(refusal, VmRefusal::NativeStdoutContract { .. })),
            }
        }
        return;
    }
    let executable = std::env::current_exe().unwrap();
    for case in [
        "success",
        "partial",
        "third_argument",
        "tail_third_argument",
        "owned_text",
        "scalar_world_contract",
        "scalar_result",
        "wrong_world",
        "wrong_string",
        "unknown_target",
        "golem_then_third_argument",
    ] {
        let output = std::process::Command::new(&executable)
            .args([
                "--exact",
                "stdout_refusals_do_not_write_to_the_captured_process_stream",
                "--nocapture",
            ])
            .env(PROCESS_CASE, case)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "capture case {case}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
        let writes = output
            .stdout
            .windows(WRITE_MARKER.len())
            .filter(|bytes| *bytes == WRITE_MARKER.as_bytes())
            .count();
        assert_eq!(
            writes,
            usize::from(case == "success"),
            "unexpected native writes in {case}"
        );
    }
}
