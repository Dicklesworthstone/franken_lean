//! Completed Task callbacks preserve their declared ownership across frames,
//! partial applications, ownership insertion and canonical FLBC replay.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership as A, CallableResultOwnership as C, CodecLimits, Function, FunctionId,
    Instruction as I, OwnershipLimits, Pc, Program, Register, ResultOwnership as R,
    ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_rt::obj::{Obj, shadow};
use fln_vm::extern_row::{ArgumentOwnership as CA, Ownership, ResultOwnership as CR};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{ExecutionLimits, VmExit, VmRefusal, execute, nat_decimal};
use std::sync::Mutex;

static TEST_LOCK: Mutex<()> = Mutex::new(());

const fn r(index: u16) -> Register {
    Register::new(index)
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

fn call(dst: u16, name: &str, args: &[u16]) -> I {
    let row = EXTERN_ROWS.iter().find(|row| row.id == name).unwrap();
    let ownership = Ownership::parse(row.ownership).unwrap();
    I::Intrinsic {
        dst: r(dst),
        row: name.to_owned(),
        args: args.iter().copied().map(r).collect(),
        argument_ownership: ownership
            .argument_ownership(args.len())
            .unwrap()
            .into_iter()
            .map(|argument| match argument {
                CA::Borrowed => A::Borrowed,
                CA::Owned => A::Owned,
                CA::Unique => A::Unique,
                CA::Scalar => A::Scalar,
            })
            .collect(),
        result_ownership: match ownership.result_ownership().unwrap() {
            CR::Borrowed => R::Borrowed,
            CR::Owned => R::Owned,
            CR::Scalar => R::Scalar,
            CR::RawObject => R::RawObject,
        },
    }
}

fn replay(program: Program, owned: bool) -> ValidatedProgram {
    let mut program = flbc::validate(program).unwrap();
    if owned {
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
    let replay = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, CodecLimits::default()).unwrap(),
        bytes
    );
    replay
}

fn composition(mode: A, bind: bool, heap: bool, partial: bool) -> Program {
    assert!(!bind || !partial);
    let mut code = vec![
        if heap {
            string(0, "retained")
        } else {
            nat(0, 7)
        },
        call(1, "extern:Task.pure", &[0]),
        I::Copy {
            dst: r(10),
            src: r(1),
        },
        string(2, "captured prefix"),
        I::Closure {
            dst: r(3),
            function: FunctionId::new(1),
            captures: vec![r(2)],
            capture_ownership: vec![A::Owned],
        },
        nat(4, 0),
        nat(5, 1),
        if bind {
            call(6, "extern:Task.bind", &[1, 3, 4, 5])
        } else {
            call(6, "extern:Task.map", &[3, 1, 4, 5])
        },
        call(7, "extern:Task.get", &[6]),
    ];
    if partial {
        // map supplied only the payload to a multi-argument callback. get
        // returns the resulting partial closure; it must remain callable
        // after both the source Task and the mapped Task are released.
        code.push(I::Drop { src: r(10) });
        code.push(nat(4, 0));
        code.push(I::Apply {
            dst: r(11),
            closure: r(7),
            args: vec![r(4)],
            argument_ownership: vec![A::Borrowed],
            result_ownership: C::Erased,
        });
        code.push(I::Drop { src: r(7) });
        code.push(if heap {
            string(8, "retained")
        } else {
            nat(8, 7)
        });
    } else {
        code.push(call(8, "extern:Task.get", &[10]));
    }
    let mapped = if partial { 11 } else { 7 };
    code.push(if heap {
        call(9, "extern:String.append", &[mapped, 8])
    } else {
        call(9, "extern:Nat.add", &[mapped, 8])
    });
    if partial {
        // An explicit Drop selects validation of an existing ownership
        // schedule. Release its remaining borrowed handles as well.
        code.extend([
            I::Drop { src: r(4) },
            I::Drop { src: r(5) },
            I::Drop { src: r(8) },
        ]);
        if !heap {
            code.push(I::Drop { src: r(mapped) });
        }
    }
    code.push(I::Return { src: r(9) });
    let mut parameters = vec![A::Owned, mode];
    if partial {
        parameters.push(A::Borrowed);
    }
    let callback = if bind {
        vec![call(3, "extern:Task.pure", &[1]), I::Return { src: r(3) }]
    } else {
        vec![I::Return { src: r(1) }]
    };
    Program::new(
        FunctionId::new(0),
        vec![
            Function {
                id: FunctionId::new(0),
                arity: 0,
                parameter_ownership: vec![],
                result_ownership: C::Erased,
                register_count: 12,
                code,
            },
            Function {
                id: FunctionId::new(1),
                arity: u16::try_from(parameters.len()).unwrap(),
                parameter_ownership: parameters,
                result_ownership: C::Erased,
                register_count: 4,
                code: callback,
            },
        ],
    )
}

fn returned(program: &ValidatedProgram) -> Obj {
    match execute(program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Returned(result)) => result.value,
        other => panic!("expected completed Task result: {other:?}"),
    }
}

fn check_result(value: &Obj, heap: bool) {
    if heap {
        let (size, _, _, bytes) = value.try_string_view().unwrap();
        assert_eq!(&bytes[..size - 1], b"retainedretained");
    } else {
        assert_eq!(nat_decimal(value).as_deref(), Some("14"));
    }
}

fn clean_shadow() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "Task callbacks and stops release retained payloads"
    );
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
}

#[test]
fn completed_task_map_and_bind_honor_borrowed_and_owned_callback_parameters() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for owned in [false, true] {
        for bind in [false, true] {
            for heap in [false, true] {
                for mode in [A::Borrowed, A::Owned, A::Scalar] {
                    if heap && mode == A::Scalar {
                        continue;
                    }
                    let program = replay(composition(mode, bind, heap, false), owned);
                    check_result(&returned(&program), heap);
                }
            }
        }
    }
    clean_shadow();
}

#[test]
fn task_map_can_return_a_shared_partial_closure_with_a_retained_heap_payload() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for owned in [false, true] {
        for mode in [A::Borrowed, A::Owned] {
            let program = replay(composition(mode, false, true, true), owned);
            check_result(&returned(&program), true);
        }
    }
    clean_shadow();
}

#[test]
fn task_callbacks_cannot_claim_unique_payloads_or_relabel_heap_values_as_scalars() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    for bind in [false, true] {
        for (mode, heap) in [(A::Unique, false), (A::Unique, true), (A::Scalar, true)] {
            let program = replay(composition(mode, bind, heap, false), false);
            let outcome = execute(&program, ExecutionLimits::default(), None);
            let payload_ownership = if heap { A::Owned } else { A::Scalar };
            assert!(matches!(
                outcome,
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::ApplyOwnershipMismatch {
                        function,
                        argument: 0,
                        expected,
                        actual,
                    },
                    ..
                }) if function == FunctionId::new(1)
                    && expected == mode
                    && actual == payload_ownership
            ));
        }
    }
    clean_shadow();
}

#[test]
fn a_diverging_task_callback_keeps_the_vm_budget_and_releases_the_payload() {
    let _guard = TEST_LOCK.lock().unwrap();
    shadow::enable();
    let mut program = composition(A::Borrowed, false, true, false);
    program.functions[1].code = vec![I::Jump { target: Pc::new(0) }];
    let program = replay(program, false);
    let outcome = execute(
        &program,
        ExecutionLimits {
            max_steps: 100,
            ..ExecutionLimits::default()
        },
        None,
    );
    let Outcome::Inconclusive(inconclusive) = outcome else {
        panic!("diverging Task callback did not exhaust its budget");
    };
    let InconclusiveCause::ResourceExhausted { usage } = &inconclusive.cause else {
        panic!("Task callback refused before execution: {inconclusive:?}");
    };
    assert_eq!(usage.reason, ResourceReason::ExecutionSteps);
    clean_shadow();
}
