//! Recoverable language panics and trace callbacks through canonical FLBC.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, OwnershipLimits, Program, Register, ResultOwnership as R, ValidatedProgram,
};
use fln_core::outcome::Outcome;
use fln_rt::obj::{Obj, shadow};
use fln_vm::extern_row::{ArgumentOwnership as CA, Ownership, ResultOwnership as CR};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute};
use std::process::{Command, Output};

const PANIC: &str = "extern:panicCore";
const TRACE: &str = "extern:dbgTrace";
const CHILD: &str = "FLN_RUNTIME_DIAGNOSTICS_CASE";

const fn r(n: u16) -> Register {
    Register::new(n)
}
const fn f(n: u32) -> FunctionId {
    FunctionId::new(n)
}
fn nat(dst: u16, value: u64) -> I {
    I::Nat { dst: r(dst), value }
}
fn string(dst: u16, value: &str) -> I {
    I::String {
        dst: r(dst),
        value: value.to_owned(),
    }
}
fn closure(dst: u16, target: u32, captures: &[u16], ownership: &[A]) -> I {
    I::Closure {
        dst: r(dst),
        function: f(target),
        captures: captures.iter().copied().map(r).collect(),
        capture_ownership: ownership.to_vec(),
    }
}
fn fun(id: u32, args: &[A], result: C, code: Vec<I>) -> Function {
    Function {
        id: f(id),
        arity: args.len() as u16,
        parameter_ownership: args.to_vec(),
        result_ownership: result,
        register_count: 16,
        code,
    }
}
fn intrinsic(dst: u16, name: &str, args: &[u16]) -> I {
    let row = EXTERN_ROWS.iter().find(|row| row.id == name).unwrap();
    let ownership = Ownership::parse(row.ownership).unwrap();
    I::Intrinsic {
        dst: r(dst),
        row: row.id.to_owned(),
        args: args.iter().copied().map(r).collect(),
        argument_ownership: if name == PANIC {
            assert_eq!(row.symbol, "lean_panic_fn_borrowed");
            assert_eq!(
                row.ownership,
                "abi((default_val: borrowed_arg, msg: raw_object) -> raw_object)"
            );
            assert_eq!(args.len(), 2);
            vec![A::Borrowed, A::Owned]
        } else {
            ownership
                .argument_ownership(args.len())
                .unwrap()
                .into_iter()
                .map(|a| match a {
                    CA::Borrowed => A::Borrowed,
                    CA::Owned => A::Owned,
                    CA::Unique => A::Unique,
                    CA::Scalar => A::Scalar,
                })
                .collect()
        },
        result_ownership: match ownership.result_ownership().unwrap() {
            CR::Borrowed => R::Borrowed,
            CR::Owned => R::Owned,
            CR::Scalar => R::Scalar,
            CR::RawObject => R::RawObject,
        },
    }
}
fn replay(functions: Vec<Function>, ownership: bool) -> ValidatedProgram {
    let mut program = flbc::validate(Program::new(f(0), functions)).unwrap();
    if ownership {
        let candidate = flbc::insert_ownership(&program, OwnershipLimits::default()).unwrap();
        flbc::validate_ownership_candidate(
            &program,
            candidate.program().clone(),
            candidate.witness().clone(),
            OwnershipLimits::default(),
        )
        .unwrap();
        program = candidate.program().clone();
    }
    let bytes = flbc::encode_canonical(&program, CodecLimits::default()).unwrap();
    let decoded = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&decoded, CodecLimits::default()).unwrap(),
        bytes
    );
    decoded
}
fn returned(program: &ValidatedProgram) -> Obj {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(value)) => value.value,
        other => panic!("expected a native result: {other:?}"),
    }
}
fn text(value: &Obj) -> String {
    let (size, _, _, bytes) = value.try_string_view().unwrap();
    String::from_utf8(bytes[..size - 1].to_vec()).unwrap()
}
fn subprocess(test: &str) -> Option<Output> {
    if std::env::var(CHILD).as_deref() == Ok(test) {
        return None;
    }
    let output = Command::new(std::env::current_exe().unwrap())
        .args(["--exact", test, "--nocapture", "--test-threads=1"])
        .env(CHILD, test)
        .env("RUST_BACKTRACE", "0")
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
    assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed; 0 failed; 0 ignored;"));
    Some(output)
}
fn start_shadow() {
    if !shadow::enabled() {
        shadow::enable();
        drop(Obj::stdio_stdout().unwrap());
    }
}
fn clean_shadow() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 24,
        "only the three immortal stdio streams, handles and six callbacks each may remain"
    );
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
}

#[test]
fn panic_returns_the_borrowed_default_and_preserves_aliases() {
    let name = "panic_returns_the_borrowed_default_and_preserves_aliases";
    if let Some(output) = subprocess(name) {
        assert_eq!(output.stderr, "recover é🦀\nrecover é🦀\n".as_bytes());
        return;
    }
    for ownership in [false, true] {
        let program = replay(
            vec![fun(
                0,
                &[],
                C::Owned,
                vec![
                    string(0, "default payload"),
                    string(1, "recover é🦀"),
                    intrinsic(2, PANIC, &[0, 1]),
                    I::Array {
                        dst: r(3),
                        items: vec![r(0), r(2)],
                    },
                    I::Return { src: r(3) },
                ],
            )],
            ownership,
        );
        start_shadow();
        let result = returned(&program);
        assert_eq!(text(&result.array_child(0)), "default payload");
        assert_eq!(text(&result.array_child(1)), "default payload");
        let first = result.array_child(0);
        let second = result.array_child(1);
        assert_eq!(first.header().rc, second.header().rc);
        drop((first, second));
        drop(result);
    }
    clean_shadow();
}

#[test]
fn trace_continuation_reuses_the_checked_vm_call_stack() {
    let name = "trace_continuation_reuses_the_checked_vm_call_stack";
    if let Some(output) = subprocess(name) {
        assert_eq!(output.stderr, b"trace\ntrace\ntrace\ntrace\ntrace\ntrace\n");
        return;
    }
    for (ownership, unit_ownership) in [
        (false, A::Scalar),
        (true, A::Scalar),
        (false, A::Borrowed),
        (true, A::Borrowed),
        (false, A::Owned),
        (true, A::Owned),
    ] {
        let program = replay(
            vec![
                fun(
                    0,
                    &[],
                    C::Erased,
                    vec![
                        string(0, "trace"),
                        string(1, "captured"),
                        closure(2, 1, &[1], &[A::Owned]),
                        intrinsic(3, TRACE, &[0, 2]),
                        I::Return { src: r(3) },
                    ],
                ),
                fun(
                    1,
                    &[A::Owned, unit_ownership],
                    C::Owned,
                    vec![I::Return { src: r(0) }],
                ),
            ],
            ownership,
        );
        start_shadow();
        let Outcome::Complete(VmExit::Returned(result)) =
            execute(&program, ExecutionLimits::default(), None)
        else {
            panic!("trace did not finish")
        };
        assert_eq!(result.usage.peak_stack_depth, 2);
        assert_eq!(text(&result.value), "captured");
        drop(result);
    }
    clean_shadow();
}

#[test]
fn runtime_diagnostics_use_stderr_and_preserve_continuation_order() {
    let name = "runtime_diagnostics_use_stderr_and_preserve_continuation_order";
    if let Some(output) = subprocess(name) {
        assert_eq!(output.stderr, b"before\nrecover\nafter\n");
        return;
    }
    let program = replay(
        vec![
            fun(
                0,
                &[],
                C::Erased,
                vec![
                    string(0, "before"),
                    closure(1, 1, &[], &[]),
                    intrinsic(2, TRACE, &[0, 1]),
                    I::Return { src: r(2) },
                ],
            ),
            fun(
                1,
                &[A::Scalar],
                C::Erased,
                vec![
                    nat(1, 17),
                    string(2, "recover"),
                    intrinsic(3, PANIC, &[1, 2]),
                    string(4, "after"),
                    closure(5, 2, &[3], &[A::Owned]),
                    intrinsic(6, TRACE, &[4, 5]),
                    I::Return { src: r(6) },
                ],
            ),
            fun(
                2,
                &[A::Owned, A::Scalar],
                C::Erased,
                vec![I::Return { src: r(0) }],
            ),
        ],
        true,
    );
    start_shadow();
    assert_eq!(returned(&program).unbox(), 17);
    clean_shadow();
}

#[test]
fn trace_partial_application_returns_a_real_callable_object() {
    let name = "trace_partial_application_returns_a_real_callable_object";
    if let Some(output) = subprocess(name) {
        assert_eq!(output.stderr, b"partial\n");
        return;
    }
    let program = replay(
        vec![
            fun(
                0,
                &[],
                C::Scalar,
                vec![
                    string(0, "partial"),
                    closure(1, 1, &[], &[]),
                    intrinsic(2, TRACE, &[0, 1]),
                    nat(3, 42),
                    I::Apply {
                        dst: r(4),
                        closure: r(2),
                        args: vec![r(3)],
                        argument_ownership: vec![A::Scalar],
                        result_ownership: C::Scalar,
                    },
                    I::Return { src: r(4) },
                ],
            ),
            fun(
                1,
                &[A::Scalar, A::Scalar],
                C::Scalar,
                vec![I::Return { src: r(1) }],
            ),
        ],
        true,
    );
    start_shadow();
    assert_eq!(returned(&program).unbox(), 42);
    clean_shadow();
}

#[test]
fn diagnostics_reject_bad_values_and_contracts_before_reporting() {
    let name = "diagnostics_reject_bad_values_and_contracts_before_reporting";
    if let Some(output) = subprocess(name) {
        assert!(output.stderr.is_empty());
        return;
    }
    let mut wrong_contract = intrinsic(2, PANIC, &[0, 1]);
    if let I::Intrinsic {
        argument_ownership, ..
    } = &mut wrong_contract
    {
        argument_ownership[0] = A::Owned;
    }
    let mut wrong_result = intrinsic(2, PANIC, &[0, 1]);
    if let I::Intrinsic {
        result_ownership, ..
    } = &mut wrong_result
    {
        *result_ownership = R::Owned;
    }
    let programs = [
        vec![nat(0, 5), nat(1, 9), intrinsic(2, PANIC, &[0, 1])],
        vec![
            string(0, "must not print"),
            nat(1, 0),
            intrinsic(2, TRACE, &[0, 1]),
        ],
        vec![nat(0, 5), string(1, "must not print"), wrong_contract],
        vec![nat(0, 5), string(1, "must not print"), wrong_result],
    ];
    for mut code in programs {
        code.push(I::Return { src: r(2) });
        let program = replay(vec![fun(0, &[], C::Erased, code)], false);
        start_shadow();
        let result = execute(&program, ExecutionLimits::default(), None);
        assert!(
            matches!(result, Outcome::Complete(VmExit::Refused { .. })),
            "{result:?}"
        );
        drop(result);
    }
    for parameters in [vec![A::Unique], vec![A::Unique, A::Scalar]] {
        let program = replay(
            vec![
                fun(
                    0,
                    &[],
                    C::Erased,
                    vec![
                        string(0, "unsupported Unit uniqueness"),
                        closure(1, 1, &[], &[]),
                        intrinsic(2, TRACE, &[0, 1]),
                        I::Return { src: r(2) },
                    ],
                ),
                fun(1, &parameters, C::Owned, vec![I::Return { src: r(0) }]),
            ],
            false,
        );
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::ApplyOwnershipMismatch {
                    expected: A::Unique,
                    actual: A::Scalar,
                    ..
                },
                ..
            })
        ));
    }
    clean_shadow();
}

#[test]
fn every_trace_step_cutoff_and_cancellation_release_pending_calls() {
    let name = "every_trace_step_cutoff_and_cancellation_release_pending_calls";
    if let Some(output) = subprocess(name) {
        let lines = String::from_utf8(output.stderr).unwrap();
        assert!(lines.lines().all(|line| line == "budgeted"));
        return;
    }
    let program = replay(
        vec![
            fun(
                0,
                &[],
                C::Erased,
                vec![
                    string(0, "budgeted"),
                    closure(1, 1, &[], &[]),
                    intrinsic(2, TRACE, &[0, 1]),
                    I::Return { src: r(2) },
                ],
            ),
            fun(
                1,
                &[A::Scalar],
                C::Owned,
                vec![string(1, "owned payload"), I::Return { src: r(1) }],
            ),
        ],
        true,
    );
    start_shadow();
    let Outcome::Complete(VmExit::Returned(completed)) =
        execute(&program, ExecutionLimits::default(), None)
    else {
        panic!("baseline trace")
    };
    let steps = completed.usage.steps;
    drop(completed);
    for max_steps in 0..steps {
        start_shadow();
        let result = execute(
            &program,
            ExecutionLimits {
                max_steps,
                ..Default::default()
            },
            None,
        );
        assert!(
            matches!(result, Outcome::Inconclusive(_)),
            "cutoff {max_steps}: {result:?}"
        );
        drop(result);
    }
    start_shadow();
    let result = execute(
        &program,
        ExecutionLimits {
            max_stack_depth: 1,
            ..Default::default()
        },
        None,
    );
    assert!(matches!(result, Outcome::Inconclusive(_)));
    drop(result);
    start_shadow();
    let canceled = || true;
    let result = execute(&program, ExecutionLimits::default(), Some(&canceled));
    assert!(matches!(result, Outcome::Inconclusive(_)));
    drop(result);
    clean_shadow();
}
