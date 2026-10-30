//! The pin's Void.mk consumes its input and returns the inert scalar zero.
//! Exercise real ABI ownership, including canonical FLBC and external drops.
#![forbid(unsafe_code)]

use fln_comp::flbc::{
    self, ArgumentOwnership, CallableResultOwnership, CodecLimits, Function, FunctionId,
    Instruction, OwnershipLimits, Program, Register, ResultOwnership, ValidatedProgram,
};
use fln_core::outcome::Outcome;
use fln_rt::obj::{EXTERNAL_FINALIZED, Obj, shadow};
use fln_vm::extern_row::Ownership;
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{
    CompletedExecution, ExecutionLimits, VmExit, VmRefusal, execute_function,
};
use std::sync::Mutex;
use std::sync::atomic::Ordering;

static LOCK: Mutex<()> = Mutex::new(());

fn program(
    arity: u16,
    argument_ownership: Vec<ArgumentOwnership>,
    result_ownership: ResultOwnership,
) -> ValidatedProgram {
    let entry = Function {
        id: FunctionId::new(0),
        arity: 0,
        parameter_ownership: vec![],
        result_ownership: CallableResultOwnership::Scalar,
        register_count: 1,
        code: vec![
            Instruction::Nat {
                dst: Register::new(0),
                value: 0,
            },
            Instruction::Return {
                src: Register::new(0),
            },
        ],
    };
    let native = Function {
        id: FunctionId::new(1),
        arity,
        parameter_ownership: vec![ArgumentOwnership::Owned; usize::from(arity)],
        result_ownership: CallableResultOwnership::Scalar,
        register_count: arity + 1,
        code: vec![
            Instruction::Intrinsic {
                dst: Register::new(arity),
                row: "extern:Void.mk".to_owned(),
                args: (0..arity).map(Register::new).collect(),
                argument_ownership,
                result_ownership,
            },
            Instruction::Return {
                src: Register::new(arity),
            },
        ],
    };
    flbc::validate(Program::new(FunctionId::new(0), vec![entry, native])).unwrap()
}

fn native_program() -> ValidatedProgram {
    let row = EXTERN_ROWS
        .iter()
        .find(|row| row.id == "extern:Void.mk")
        .unwrap();
    let contract = Ownership::parse(row.ownership).unwrap();
    assert_eq!(
        contract.argument_ownership(1).unwrap(),
        vec![fln_vm::extern_row::ArgumentOwnership::Owned]
    );
    assert_eq!(
        contract.result_ownership().unwrap(),
        fln_vm::extern_row::ResultOwnership::Owned
    );
    program(1, vec![ArgumentOwnership::Owned], ResultOwnership::Owned)
}

fn canonical_owned(program: &ValidatedProgram) -> ValidatedProgram {
    let owned = flbc::insert_ownership(program, OwnershipLimits::default()).unwrap();
    flbc::validate_ownership_candidate(
        program,
        owned.program().clone(),
        owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .unwrap();
    let bytes = flbc::encode_canonical(owned.program(), CodecLimits::default()).unwrap();
    let replay = flbc::decode_canonical(&bytes, CodecLimits::default()).unwrap();
    assert_eq!(
        flbc::encode_canonical(&replay, CodecLimits::default()).unwrap(),
        bytes
    );
    replay
}

fn returned(program: &ValidatedProgram, value: Obj) -> CompletedExecution {
    let outcome = execute_function(
        program,
        FunctionId::new(1),
        vec![value],
        ExecutionLimits::default(),
        None,
    );
    let Outcome::Complete(VmExit::Returned(result)) = outcome else {
        panic!("{outcome:?}");
    };
    assert!(result.value.is_scalar());
    assert_eq!(result.value.unbox(), 0);
    result
}

fn no_leaks() {
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "Void.mk retains no discarded ABI handles");
    assert!(events.iter().all(|event| !matches!(
        event.kind,
        shadow::EventKind::DoubleRelease | shadow::EventKind::ForeignPointer
    )));
}

#[test]
fn void_mk_accepts_arbitrary_abi_values_and_returns_exact_zero_after_replay() {
    let _guard = LOCK.lock().unwrap();
    let original = native_program();
    let replay = canonical_owned(&original);
    let inputs: [fn() -> Obj; 9] = [
        || Obj::mk_nat(0),
        || Obj::mk_nat(37),
        || Obj::mk_mpz(&[u64::MAX, 1], false),
        || Obj::mk_string("discarded string"),
        || Obj::mk_array(vec![Obj::mk_string("array child")]),
        || Obj::mk_ctor(3, vec![Obj::mk_string("constructor child")], &[7, 8]),
        || Obj::mk_ref(Obj::mk_string("cell occupant")),
        || Obj::mk_closure(2, vec![Obj::mk_string("closure capture")]),
        || Obj::mk_task_pure(Obj::mk_string("finished task value")),
    ];
    for program in [&original, &replay] {
        for make_input in inputs {
            shadow::enable();
            drop(returned(program, make_input()));
            no_leaks();
        }
    }
}

#[test]
fn void_mk_releases_unique_inputs_before_return_and_preserves_retained_aliases() {
    let _guard = LOCK.lock().unwrap();
    let original = native_program();
    let replay = canonical_owned(&original);
    for program in [&original, &replay] {
        shadow::enable();
        let before = EXTERNAL_FINALIZED.load(Ordering::SeqCst);
        let result = returned(program, Obj::mk_external_counting());
        assert_eq!(EXTERNAL_FINALIZED.load(Ordering::SeqCst), before + 1);
        drop(result);
        assert_eq!(EXTERNAL_FINALIZED.load(Ordering::SeqCst), before + 1);
        no_leaks();

        shadow::enable();
        let before = EXTERNAL_FINALIZED.load(Ordering::SeqCst);
        let input = Obj::mk_array(vec![
            Obj::mk_external_counting(),
            Obj::mk_string("retained alias"),
        ]);
        let alias = input.clone_ref();
        drop(returned(program, input));
        assert_eq!(EXTERNAL_FINALIZED.load(Ordering::SeqCst), before);
        assert_eq!(alias.array_child(1).string_view().3, b"retained alias\0");
        drop(alias);
        assert_eq!(EXTERNAL_FINALIZED.load(Ordering::SeqCst), before + 1);
        no_leaks();
    }
}

#[test]
fn void_mk_refuses_wrong_arity_and_forged_ownership_contracts() {
    let _guard = LOCK.lock().unwrap();
    for (arity, arguments, result) in [
        (0, vec![], ResultOwnership::Owned),
        (2, vec![ArgumentOwnership::Owned; 2], ResultOwnership::Owned),
        (1, vec![ArgumentOwnership::Borrowed], ResultOwnership::Owned),
        (1, vec![ArgumentOwnership::Owned], ResultOwnership::Scalar),
    ] {
        let program = program(arity, arguments, result);
        shadow::enable();
        let outcome = execute_function(
            &program,
            FunctionId::new(1),
            (0..arity)
                .map(|_| Obj::mk_string("refused input"))
                .collect(),
            ExecutionLimits::default(),
            None,
        );
        assert!(matches!(
            outcome,
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::IntrinsicOwnershipContract { .. }
                    | VmRefusal::IntrinsicOwnershipMismatch { .. }
                    | VmRefusal::IntrinsicResultOwnershipMismatch { .. },
                ..
            })
        ));
        drop(outcome);
        no_leaks();
    }
}
