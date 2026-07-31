//! G0-3 prototype execution contract: validated FLBC runs over real Marrow
//! objects, and every non-authoritative stop tears the owned register graph
//! down without publishing a value.

#![forbid(unsafe_code)]

use fln_comp::flbc::{
    ArgumentOwnership, CallableResultOwnership, CodecLimits, FLBC_SCHEMA_VERSION, Function,
    FunctionId, Instruction, OwnershipError, OwnershipLimits, OwnershipWitness,
    OwnershipWitnessCount, Pc, Program, Register, ResultOwnership, ValidatedProgram,
    ValidationError, decode_canonical, encode_canonical, insert_ownership, validate,
    validate_ownership_candidate,
};
use fln_comp::{fir, ingress};
use fln_core::diag::ResourceReason;
use fln_core::expr::{BinderInfo, Expr, Literal};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Authority, InconclusiveCause, Outcome};
use fln_rt::abi;
use fln_rt::obj::{Obj, shadow};
use fln_vm::extern_row::{
    ArgumentOwnership as ContractArgumentOwnership, Ownership as ExternOwnership,
    ResultOwnership as ContractResultOwnership,
};
use fln_vm::extern_table_generated::EXTERN_ROWS;
use fln_vm::interpreter::{
    CompletedExecution, ExecutionLimits, ValueKind, VmExit, VmRefusal, execute, value_kind,
};
use std::cell::Cell;
use std::sync::{Mutex, MutexGuard};

static TEST_LOCK: Mutex<()> = Mutex::new(());

fn lock() -> MutexGuard<'static, ()> {
    TEST_LOCK.lock().unwrap_or_else(|error| error.into_inner())
}

const fn r(raw: u16) -> Register {
    Register::new(raw)
}

const fn pc(raw: u32) -> Pc {
    Pc::new(raw)
}

const fn fid(raw: u32) -> FunctionId {
    FunctionId::new(raw)
}

const fn callable_result_ownership(ty: fir::ValueType) -> CallableResultOwnership {
    match ty {
        fir::ValueType::Unit | fir::ValueType::Bool | fir::ValueType::Nat => {
            CallableResultOwnership::Scalar
        }
        fir::ValueType::String
        | fir::ValueType::Constructor
        | fir::ValueType::Array
        | fir::ValueType::Ref
        | fir::ValueType::Thunk
        | fir::ValueType::Task
        | fir::ValueType::Closure(_)
        | fir::ValueType::Abi => CallableResultOwnership::Owned,
    }
}

fn function(id: u32, arity: u16, register_count: u16, code: Vec<Instruction>) -> Function {
    function_with_ownership(
        id,
        vec![ArgumentOwnership::Borrowed; usize::from(arity)],
        register_count,
        code,
    )
}

fn function_with_ownership(
    id: u32,
    parameter_ownership: Vec<ArgumentOwnership>,
    register_count: u16,
    code: Vec<Instruction>,
) -> Function {
    let result_ownership = fixture_result_ownership(&parameter_ownership, &code);
    function_with_callable_result(
        id,
        parameter_ownership,
        result_ownership,
        register_count,
        code,
    )
}

fn function_with_callable_result(
    id: u32,
    parameter_ownership: Vec<ArgumentOwnership>,
    result_ownership: CallableResultOwnership,
    register_count: u16,
    code: Vec<Instruction>,
) -> Function {
    Function {
        id: fid(id),
        arity: u16::try_from(parameter_ownership.len()).expect("test call arity fits u16"),
        parameter_ownership,
        result_ownership,
        register_count,
        code,
    }
}

fn fixture_result_ownership(
    parameter_ownership: &[ArgumentOwnership],
    code: &[Instruction],
) -> CallableResultOwnership {
    let mut inferred = None;
    for (index, instruction) in code.iter().enumerate() {
        let Instruction::Return { src } = instruction else {
            continue;
        };
        let current = fixture_register_result(parameter_ownership, code, index, *src, 0);
        inferred.get_or_insert(current);
    }
    inferred.unwrap_or(CallableResultOwnership::Owned)
}

fn fixture_register_result(
    parameter_ownership: &[ArgumentOwnership],
    code: &[Instruction],
    before: usize,
    register: Register,
    depth: usize,
) -> CallableResultOwnership {
    assert!(depth <= code.len(), "fixture register provenance is cyclic");
    for (index, instruction) in code[..before].iter().enumerate().rev() {
        match instruction {
            Instruction::Nat { dst, .. } if *dst == register => {
                return CallableResultOwnership::Scalar;
            }
            Instruction::String { dst, .. }
            | Instruction::Ctor { dst, .. }
            | Instruction::Array { dst, .. }
            | Instruction::Closure { dst, .. }
                if *dst == register =>
            {
                return CallableResultOwnership::Owned;
            }
            Instruction::Copy { dst, src } | Instruction::Move { dst, src } if *dst == register => {
                return fixture_register_result(
                    parameter_ownership,
                    code,
                    index,
                    *src,
                    depth.saturating_add(1),
                );
            }
            Instruction::Intrinsic { dst, row, .. } if *dst == register => {
                return match row.as_str() {
                    "extern:Nat.add"
                    | "extern:Array.size"
                    | "extern:ST.Prim.Ref.ptrEq"
                    | "extern:ST.Prim.Ref.set" => CallableResultOwnership::Scalar,
                    _ => CallableResultOwnership::Owned,
                };
            }
            Instruction::Call {
                dst,
                result_ownership,
                ..
            }
            | Instruction::Apply {
                dst,
                result_ownership,
                ..
            } if *dst == register => return *result_ownership,
            Instruction::CtorField { dst, .. } if *dst == register => {
                return CallableResultOwnership::Owned;
            }
            _ => {}
        }
    }
    parameter_ownership
        .get(usize::from(register.get()))
        .copied()
        .filter(|ownership| *ownership == ArgumentOwnership::Scalar)
        .map_or(CallableResultOwnership::Owned, |_| {
            CallableResultOwnership::Scalar
        })
}

fn contract_argument_ownership(row: &str, argument_count: usize) -> Vec<ArgumentOwnership> {
    let Some(generated) = EXTERN_ROWS.iter().find(|generated| generated.id == row) else {
        return vec![ArgumentOwnership::Borrowed; argument_count];
    };
    ExternOwnership::parse(generated.ownership)
        .expect("generated ownership grammar")
        .argument_ownership(argument_count)
        .expect("generated executable argument ownership")
        .into_iter()
        .map(|disposition| match disposition {
            ContractArgumentOwnership::Borrowed => ArgumentOwnership::Borrowed,
            ContractArgumentOwnership::Owned => ArgumentOwnership::Owned,
            ContractArgumentOwnership::Unique => ArgumentOwnership::Unique,
            ContractArgumentOwnership::Scalar => ArgumentOwnership::Scalar,
        })
        .collect()
}

fn contract_result_ownership(row: &str) -> ResultOwnership {
    let Some(generated) = EXTERN_ROWS.iter().find(|generated| generated.id == row) else {
        return ResultOwnership::Owned;
    };
    match ExternOwnership::parse(generated.ownership)
        .expect("generated ownership grammar")
        .result_ownership()
        .expect("generated executable result ownership")
    {
        ContractResultOwnership::Owned => ResultOwnership::Owned,
        ContractResultOwnership::Borrowed => ResultOwnership::Borrowed,
        ContractResultOwnership::Scalar => ResultOwnership::Scalar,
        ContractResultOwnership::RawObject => ResultOwnership::RawObject,
    }
}

fn intrinsic(dst: Register, row: &str, args: Vec<Register>) -> Instruction {
    let argument_ownership = contract_argument_ownership(row, args.len());
    Instruction::Intrinsic {
        dst,
        row: row.to_string(),
        args,
        argument_ownership,
        result_ownership: contract_result_ownership(row),
    }
}

fn validated(functions: Vec<Function>) -> ValidatedProgram {
    validate(Program::new(fid(0), functions)).expect("fixture program is valid")
}

fn delayed_thunk_program(register_count: u16, body: Vec<Instruction>) -> ValidatedProgram {
    validated(vec![
        function(
            0,
            0,
            3,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                intrinsic(r(1), "extern:Thunk.mk", vec![r(0)]),
                intrinsic(r(2), "extern:Thunk.get", vec![r(1)]),
                Instruction::Return { src: r(2) },
            ],
        ),
        function_with_ownership(1, vec![ArgumentOwnership::Scalar], register_count, body),
    ])
}

fn managerless_spawn_program(
    arity: u16,
    register_count: u16,
    body: Vec<Instruction>,
) -> ValidatedProgram {
    let parameter_ownership = (0..arity)
        .map(|index| {
            if index == 0 {
                ArgumentOwnership::Scalar
            } else {
                ArgumentOwnership::Borrowed
            }
        })
        .collect();
    validated(vec![
        function(
            0,
            0,
            4,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 0,
                },
                intrinsic(r(2), "extern:Task.spawn", vec![r(0), r(1)]),
                intrinsic(r(3), "extern:Task.get", vec![r(2)]),
                Instruction::Return { src: r(3) },
            ],
        ),
        function_with_ownership(1, parameter_ownership, register_count, body),
    ])
}

fn returned(outcome: Outcome<VmExit>) -> CompletedExecution {
    match outcome {
        Outcome::Complete(VmExit::Returned(completed)) => completed,
        other => panic!("expected a returned value, got {other:?}"),
    }
}

fn string_contents(value: &Obj) -> String {
    assert_eq!(value_kind(value), ValueKind::String);
    let (size, _, _, bytes) = value.string_view();
    assert!(size > 0);
    assert_eq!(bytes[size - 1], 0);
    std::str::from_utf8(&bytes[..size - 1])
        .expect("Marrow string is UTF-8")
        .to_string()
}

#[test]
fn canonical_flbc_artifact_decodes_validates_and_executes_without_a_shadow_value_domain() {
    let _guard = lock();
    let program = validated(vec![function(
        0,
        0,
        3,
        vec![
            Instruction::Nat {
                dst: r(0),
                value: 20,
            },
            Instruction::Nat {
                dst: r(1),
                value: 22,
            },
            intrinsic(r(2), "extern:Nat.add", vec![r(0), r(1)]),
            Instruction::Return { src: r(2) },
        ],
    )]);
    let bytes = encode_canonical(&program, CodecLimits::default()).expect("encode validated FLBC");
    let decoded =
        decode_canonical(&bytes, CodecLimits::default()).expect("decode and validate FLBC");
    let completed = returned(execute(&decoded, ExecutionLimits::default(), None));
    assert_eq!(completed.value.unbox(), 42);

    let mut trailing = bytes;
    trailing.push(0);
    assert!(
        decode_canonical(&trailing, CodecLimits::default()).is_err(),
        "a noncanonical artifact never reaches execute"
    );
}

#[test]
fn validated_fir_lowers_to_canonical_flbc_and_executes_on_marrow_values() {
    let _guard = lock();
    let source = fir::Program::new(
        fir::FunctionId::new(0),
        Vec::new(),
        Vec::new(),
        vec![
            fir::IntrinsicDecl {
                id: fir::IntrinsicId::new(0),
                row: "extern:Nat.add".to_string(),
                arguments: vec![fir::ValueType::Nat, fir::ValueType::Nat],
                argument_ownership: contract_argument_ownership("extern:Nat.add", 2),
                result_ownership: contract_result_ownership("extern:Nat.add"),
                result: fir::ValueType::Nat,
                effect: fir::EffectClass::Pure,
            },
            fir::IntrinsicDecl {
                id: fir::IntrinsicId::new(1),
                row: "extern:String.append".to_string(),
                arguments: vec![fir::ValueType::String, fir::ValueType::String],
                argument_ownership: contract_argument_ownership("extern:String.append", 2),
                result_ownership: contract_result_ownership("extern:String.append"),
                result: fir::ValueType::String,
                effect: fir::EffectClass::Pure,
            },
        ],
        vec![
            fir::Function {
                id: fir::FunctionId::new(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: fir::ValueType::Array,
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![fir::Block {
                    id: fir::BlockId::new(0),
                    bindings: vec![
                        fir::Binding {
                            id: fir::ValueId::new(0),
                            ty: fir::ValueType::Nat,
                            operation: fir::Operation::Nat(20),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(1),
                            ty: fir::ValueType::Nat,
                            operation: fir::Operation::Nat(22),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(2),
                            ty: fir::ValueType::Nat,
                            operation: fir::Operation::Intrinsic {
                                intrinsic: fir::IntrinsicId::new(0),
                                args: vec![fir::ValueId::new(0), fir::ValueId::new(1)],
                            },
                        },
                        fir::Binding {
                            id: fir::ValueId::new(3),
                            ty: fir::ValueType::String,
                            operation: fir::Operation::String("answer=".to_string()),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(4),
                            ty: fir::ValueType::String,
                            operation: fir::Operation::String("42".to_string()),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(5),
                            ty: fir::ValueType::String,
                            operation: fir::Operation::Call {
                                function: fir::FunctionId::new(1),
                                args: vec![fir::ValueId::new(3), fir::ValueId::new(4)],
                            },
                        },
                        fir::Binding {
                            id: fir::ValueId::new(6),
                            ty: fir::ValueType::Array,
                            operation: fir::Operation::Array {
                                items: vec![fir::ValueId::new(2), fir::ValueId::new(5)],
                            },
                        },
                    ],
                    terminator: fir::Terminator::Return {
                        value: fir::ValueId::new(6),
                    },
                }],
            },
            fir::Function {
                id: fir::FunctionId::new(1),
                parameters: vec![fir::ValueType::String, fir::ValueType::String],
                parameter_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                result: fir::ValueType::String,
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![fir::Block {
                    id: fir::BlockId::new(0),
                    bindings: vec![fir::Binding {
                        id: fir::ValueId::new(2),
                        ty: fir::ValueType::String,
                        operation: fir::Operation::Intrinsic {
                            intrinsic: fir::IntrinsicId::new(1),
                            args: vec![fir::ValueId::new(0), fir::ValueId::new(1)],
                        },
                    }],
                    terminator: fir::Terminator::Return {
                        value: fir::ValueId::new(2),
                    },
                }],
            },
        ],
    );
    let validated_fir = fir::validate(source, fir::ValidationLimits::default())
        .expect("validate target-neutral FIR");
    let canonical_fir = validated_fir.canonical_text();
    assert!(
        canonical_fir.contains(
            "function f1 params=[string,string] ownership=[owned,borrowed] result=string"
        )
    );
    assert!(
        canonical_fir.contains("result_ownership=owned effect=pure\n"),
        "FIR canonical identity binds the generated result class"
    );
    let lowered = fir::lower_to_flbc(&validated_fir).expect("mandatory FIR lowering");
    assert_eq!(
        lowered.functions()[1].parameter_ownership,
        [ArgumentOwnership::Owned, ArgumentOwnership::Borrowed]
    );
    assert!(matches!(
        &lowered.functions()[0].code[5],
        Instruction::Call {
            function,
            argument_ownership,
            ..
        } if *function == fid(1)
            && argument_ownership
                == &[ArgumentOwnership::Owned, ArgumentOwnership::Borrowed]
    ));
    assert!(matches!(
        &lowered.functions()[0].code[2],
        Instruction::Intrinsic {
            result_ownership: ResultOwnership::Owned,
            ..
        }
    ));
    let owned = insert_ownership(&lowered, OwnershipLimits::default())
        .expect("direct-call and intrinsic transfers receive one checked ownership graph");
    assert_eq!(owned.witness().functions()[0].consumed_call_args, 1);
    assert_eq!(owned.witness().functions()[1].consumed_extern_args, 1);
    let bytes =
        encode_canonical(owned.program(), CodecLimits::default()).expect("canonical FLBC artifact");
    let decoded =
        decode_canonical(&bytes, CodecLimits::default()).expect("independent FLBC validation");
    let decoded = validate_ownership_candidate(
        &lowered,
        decoded,
        owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .expect("decoded ownership graph rebinds to the FIR-lowered source");

    shadow::enable();
    let completed = returned(execute(decoded.program(), ExecutionLimits::default(), None));
    assert_eq!(completed.value.array_view(), (2, 2));
    assert_eq!(completed.value.array_child(0).unbox(), 42);
    assert_eq!(
        string_contents(&completed.value.array_child(1)),
        "answer=42"
    );
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "FIR-lowered execution releases every ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "FIR lowering introduces no shadow value domain or ownership defect"
    );
}

#[test]
fn owned_direct_call_reuses_its_consumed_destination_and_tears_down_on_stack_stop() {
    let _guard = lock();
    let source = validated(vec![
        function(
            0,
            0,
            1,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "transferred-directly".to_string(),
                },
                Instruction::Call {
                    dst: r(0),
                    function: fid(1),
                    args: vec![r(0)],
                    argument_ownership: vec![ArgumentOwnership::Owned],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(0) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Owned],
            1,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    let owned = insert_ownership(&source, OwnershipLimits::default())
        .expect("consumption makes the call destination a fresh value epoch");
    assert_eq!(owned.witness().functions()[0].consumed_call_args, 1);
    assert_eq!(owned.witness().functions()[1].consumed_call_args, 0);
    assert!(
        !owned.program().functions()[0]
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Drop { src } if *src == r(0))),
        "neither the transferred input nor its same-register result is dropped early"
    );
    let bytes = encode_canonical(owned.program(), CodecLimits::default())
        .expect("owned direct call encodes canonically");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("owned direct call decodes with both ownership vectors");
    let rebound = validate_ownership_candidate(
        &source,
        decoded,
        owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .expect("owned direct call rebinds to its source and consume count");

    shadow::enable();
    let stopped = execute(
        rebound.program(),
        ExecutionLimits {
            max_steps: 10,
            max_stack_depth: 1,
        },
        None,
    );
    assert!(matches!(
        stopped,
        Outcome::Inconclusive(ref inconclusive)
            if matches!(
                inconclusive.cause,
                InconclusiveCause::ResourceExhausted { .. }
            )
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "a stack stop after transfer releases the detached argument exactly once"
    );
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event.kind, shadow::EventKind::Alloc))
            .count(),
        1
    );
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event.kind, shadow::EventKind::Release))
            .count(),
        1
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));

    shadow::enable();
    let completed = returned(execute(rebound.program(), ExecutionLimits::default(), None));
    assert_eq!(string_contents(&completed.value), "transferred-directly");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "the successful transfer drains its returned object"
    );
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event.kind, shadow::EventKind::Alloc))
            .count(),
        1
    );
    assert_eq!(
        events
            .iter()
            .filter(|event| matches!(event.kind, shadow::EventKind::Release))
            .count(),
        1
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));
}

#[test]
fn owned_closure_captures_cross_fir_and_same_destination_runtime_stops() {
    let _guard = lock();
    let fir_source = fir::Program::new_with_closures(
        fir::FunctionId::new(0),
        Vec::new(),
        Vec::new(),
        vec![fir::ClosureTypeDecl {
            id: fir::ClosureTypeId::new(0),
            parameters: vec![fir::ValueType::String],
            parameter_ownership: vec![ArgumentOwnership::Borrowed],
            result: fir::ValueType::String,
            result_ownership: CallableResultOwnership::Owned,
        }],
        Vec::new(),
        vec![
            fir::Function {
                id: fir::FunctionId::new(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: fir::ValueType::String,
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![fir::Block {
                    id: fir::BlockId::new(0),
                    bindings: vec![
                        fir::Binding {
                            id: fir::ValueId::new(0),
                            ty: fir::ValueType::String,
                            operation: fir::Operation::String("owned closure capture".to_string()),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(1),
                            ty: fir::ValueType::String,
                            operation: fir::Operation::String(
                                "borrowed closure capture".to_string(),
                            ),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(2),
                            ty: fir::ValueType::Closure(fir::ClosureTypeId::new(0)),
                            operation: fir::Operation::Closure {
                                closure_type: fir::ClosureTypeId::new(0),
                                function: fir::FunctionId::new(1),
                                captures: vec![fir::ValueId::new(0), fir::ValueId::new(1)],
                                capture_ownership: vec![
                                    ArgumentOwnership::Owned,
                                    ArgumentOwnership::Borrowed,
                                ],
                            },
                        },
                        fir::Binding {
                            id: fir::ValueId::new(3),
                            ty: fir::ValueType::String,
                            operation: fir::Operation::String("application argument".to_string()),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(4),
                            ty: fir::ValueType::String,
                            operation: fir::Operation::Apply {
                                closure: fir::ValueId::new(2),
                                args: vec![fir::ValueId::new(3)],
                                argument_ownership: vec![ArgumentOwnership::Borrowed],
                                result_ownership: CallableResultOwnership::Owned,
                            },
                        },
                    ],
                    terminator: fir::Terminator::Return {
                        value: fir::ValueId::new(4),
                    },
                }],
            },
            fir::Function {
                id: fir::FunctionId::new(1),
                parameters: vec![
                    fir::ValueType::String,
                    fir::ValueType::String,
                    fir::ValueType::String,
                ],
                parameter_ownership: vec![
                    ArgumentOwnership::Owned,
                    ArgumentOwnership::Borrowed,
                    ArgumentOwnership::Borrowed,
                ],
                result: fir::ValueType::String,
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![fir::Block {
                    id: fir::BlockId::new(0),
                    bindings: vec![fir::Binding {
                        id: fir::ValueId::new(3),
                        ty: fir::ValueType::String,
                        operation: fir::Operation::Alias(fir::ValueId::new(0)),
                    }],
                    terminator: fir::Terminator::Return {
                        value: fir::ValueId::new(3),
                    },
                }],
            },
        ],
    );
    let fir_validated = fir::validate(fir_source, fir::ValidationLimits::default())
        .expect("mixed closure capture ownership is valid FIR");
    assert!(
        fir_validated
            .canonical_text()
            .contains("closure s0 f1 captures=[v0,v1] ownership=[owned,borrowed]")
    );
    let lowered =
        fir::lower_to_flbc(&fir_validated).expect("mixed FIR capture ownership lowers to FLBC");
    assert!(lowered.functions()[0].code.iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::Closure {
                function,
                capture_ownership,
                ..
            } if *function == fid(1)
                && capture_ownership
                    == &[ArgumentOwnership::Owned, ArgumentOwnership::Borrowed]
        )
    }));
    let owned = insert_ownership(&lowered, OwnershipLimits::default())
        .expect("FIR-lowered closure consumes exactly its owned capture");
    assert_eq!(owned.witness().functions()[0].consumed_closure_captures, 1);
    let bytes = encode_canonical(owned.program(), CodecLimits::default())
        .expect("mixed closure ownership encodes canonically");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("mixed closure ownership decodes independently");
    let rebound = validate_ownership_candidate(
        &lowered,
        decoded,
        owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .expect("decoded closure ownership rebinds to the FIR-lowered source");

    shadow::enable();
    let completed = returned(execute(rebound.program(), ExecutionLimits::default(), None));
    assert_eq!(string_contents(&completed.value), "owned closure capture");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "the FIR closure path releases every Marrow object");
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));

    let same_destination_source = validated(vec![
        function(
            0,
            0,
            4,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "same destination capture".to_string(),
                },
                Instruction::String {
                    dst: r(1),
                    value: "borrowed sibling".to_string(),
                },
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: vec![r(0), r(1)],
                    capture_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                },
                Instruction::String {
                    dst: r(2),
                    value: "open argument".to_string(),
                },
                Instruction::Apply {
                    dst: r(3),
                    closure: r(0),
                    args: vec![r(2)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(3) },
            ],
        ),
        function_with_ownership(
            1,
            vec![
                ArgumentOwnership::Owned,
                ArgumentOwnership::Borrowed,
                ArgumentOwnership::Borrowed,
            ],
            3,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    let same_destination_owned =
        insert_ownership(&same_destination_source, OwnershipLimits::default())
            .expect("the consuming capture makes its destination a fresh value epoch");
    assert_eq!(
        same_destination_owned.witness().functions()[0].consumed_closure_captures,
        1
    );
    let same_destination_code = &same_destination_owned.program().functions()[0].code;
    let closure_position = same_destination_code
        .iter()
        .position(
            |instruction| matches!(instruction, Instruction::Closure { dst, .. } if *dst == r(0)),
        )
        .expect("the owned closure survives insertion");
    let shell_drop_positions = same_destination_code
        .iter()
        .enumerate()
        .filter_map(|(position, instruction)| {
            matches!(instruction, Instruction::Drop { src } if *src == r(0)).then_some(position)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        shell_drop_positions.len(),
        1,
        "only the replacement closure shell receives a synthesized drop"
    );
    assert!(
        shell_drop_positions[0] > closure_position,
        "the consumed capture epoch is not confused with its same-register closure shell"
    );
    let bytes = encode_canonical(same_destination_owned.program(), CodecLimits::default())
        .expect("same-destination closure encodes canonically");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("same-destination closure decodes with its capture contract");
    let rebound = validate_ownership_candidate(
        &same_destination_source,
        decoded,
        same_destination_owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .expect("same-destination closure ownership rebinds independently");

    shadow::enable();
    let stopped = execute(
        rebound.program(),
        ExecutionLimits {
            max_steps: 20,
            max_stack_depth: 1,
        },
        None,
    );
    assert!(matches!(
        stopped,
        Outcome::Inconclusive(ref inconclusive)
            if matches!(
                inconclusive.cause,
                InconclusiveCause::ResourceExhausted { ref usage }
                    if usage.reason == ResourceReason::RecursionDepth { limit: 1 }
            )
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "a stack stop releases the closure shell and both capture ownership paths"
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));

    shadow::enable();
    let completed = returned(execute(rebound.program(), ExecutionLimits::default(), None));
    assert_eq!(
        string_contents(&completed.value),
        "same destination capture"
    );
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "successful same-destination execution drains the reusable closure graph"
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));
}

#[test]
fn owned_apply_arguments_cross_fir_partial_exact_overapplication_and_refuse_drift() {
    let _guard = lock();
    let string = fir::ValueType::String;
    let s0 = fir::ClosureTypeId::new(0);
    let s1 = fir::ClosureTypeId::new(1);
    let s2 = fir::ClosureTypeId::new(2);
    let fir_source = fir::Program::new_with_closures(
        fir::FunctionId::new(0),
        Vec::new(),
        Vec::new(),
        vec![
            fir::ClosureTypeDecl {
                id: s0,
                parameters: vec![string],
                parameter_ownership: vec![ArgumentOwnership::Borrowed],
                result: string,
                result_ownership: CallableResultOwnership::Owned,
            },
            fir::ClosureTypeDecl {
                id: s1,
                parameters: vec![string],
                parameter_ownership: vec![ArgumentOwnership::Owned],
                result: fir::ValueType::Closure(s0),
                result_ownership: CallableResultOwnership::Owned,
            },
            fir::ClosureTypeDecl {
                id: s2,
                parameters: vec![string, string],
                parameter_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                result: string,
                result_ownership: CallableResultOwnership::Owned,
            },
        ],
        Vec::new(),
        vec![
            fir::Function {
                id: fir::FunctionId::new(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: fir::ValueType::Array,
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![fir::Block {
                    id: fir::BlockId::new(0),
                    bindings: vec![
                        fir::Binding {
                            id: fir::ValueId::new(0),
                            ty: string,
                            operation: fir::Operation::String("partial-owned".to_string()),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(1),
                            ty: string,
                            operation: fir::Operation::String("partial-borrowed".to_string()),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(2),
                            ty: fir::ValueType::Closure(s2),
                            operation: fir::Operation::Closure {
                                closure_type: s2,
                                function: fir::FunctionId::new(1),
                                captures: Vec::new(),
                                capture_ownership: Vec::new(),
                            },
                        },
                        fir::Binding {
                            id: fir::ValueId::new(3),
                            ty: fir::ValueType::Closure(s0),
                            operation: fir::Operation::Apply {
                                closure: fir::ValueId::new(2),
                                args: vec![fir::ValueId::new(0)],
                                argument_ownership: vec![ArgumentOwnership::Owned],
                                result_ownership: CallableResultOwnership::Owned,
                            },
                        },
                        fir::Binding {
                            id: fir::ValueId::new(4),
                            ty: string,
                            operation: fir::Operation::Apply {
                                closure: fir::ValueId::new(3),
                                args: vec![fir::ValueId::new(1)],
                                argument_ownership: vec![ArgumentOwnership::Borrowed],
                                result_ownership: CallableResultOwnership::Owned,
                            },
                        },
                        fir::Binding {
                            id: fir::ValueId::new(5),
                            ty: string,
                            operation: fir::Operation::String("over-owned".to_string()),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(6),
                            ty: string,
                            operation: fir::Operation::String("over-borrowed".to_string()),
                        },
                        fir::Binding {
                            id: fir::ValueId::new(7),
                            ty: fir::ValueType::Closure(s1),
                            operation: fir::Operation::Closure {
                                closure_type: s1,
                                function: fir::FunctionId::new(2),
                                captures: Vec::new(),
                                capture_ownership: Vec::new(),
                            },
                        },
                        fir::Binding {
                            id: fir::ValueId::new(8),
                            ty: string,
                            operation: fir::Operation::Apply {
                                closure: fir::ValueId::new(7),
                                args: vec![fir::ValueId::new(5), fir::ValueId::new(6)],
                                argument_ownership: vec![
                                    ArgumentOwnership::Owned,
                                    ArgumentOwnership::Borrowed,
                                ],
                                result_ownership: CallableResultOwnership::Owned,
                            },
                        },
                        fir::Binding {
                            id: fir::ValueId::new(9),
                            ty: fir::ValueType::Array,
                            operation: fir::Operation::Array {
                                items: vec![fir::ValueId::new(4), fir::ValueId::new(8)],
                            },
                        },
                    ],
                    terminator: fir::Terminator::Return {
                        value: fir::ValueId::new(9),
                    },
                }],
            },
            fir::Function {
                id: fir::FunctionId::new(1),
                parameters: vec![string, string],
                parameter_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                result: string,
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![fir::Block {
                    id: fir::BlockId::new(0),
                    bindings: vec![fir::Binding {
                        id: fir::ValueId::new(2),
                        ty: string,
                        operation: fir::Operation::Alias(fir::ValueId::new(0)),
                    }],
                    terminator: fir::Terminator::Return {
                        value: fir::ValueId::new(2),
                    },
                }],
            },
            fir::Function {
                id: fir::FunctionId::new(2),
                parameters: vec![string],
                parameter_ownership: vec![ArgumentOwnership::Owned],
                result: fir::ValueType::Closure(s0),
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![fir::Block {
                    id: fir::BlockId::new(0),
                    bindings: vec![fir::Binding {
                        id: fir::ValueId::new(1),
                        ty: fir::ValueType::Closure(s0),
                        operation: fir::Operation::Closure {
                            closure_type: s0,
                            function: fir::FunctionId::new(3),
                            captures: vec![fir::ValueId::new(0)],
                            capture_ownership: vec![ArgumentOwnership::Owned],
                        },
                    }],
                    terminator: fir::Terminator::Return {
                        value: fir::ValueId::new(1),
                    },
                }],
            },
            fir::Function {
                id: fir::FunctionId::new(3),
                parameters: vec![string, string],
                parameter_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                result: string,
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![fir::Block {
                    id: fir::BlockId::new(0),
                    bindings: vec![fir::Binding {
                        id: fir::ValueId::new(2),
                        ty: string,
                        operation: fir::Operation::Alias(fir::ValueId::new(0)),
                    }],
                    terminator: fir::Terminator::Return {
                        value: fir::ValueId::new(2),
                    },
                }],
            },
        ],
    );
    let fir_validated = fir::validate(fir_source, fir::ValidationLimits::default())
        .expect("partial, exact, and over Apply ownership is valid FIR");
    let fir_text = fir_validated.canonical_text();
    assert!(fir_text.contains(
        "closure_type s2 params=[string,string] ownership=[owned,borrowed] result=string"
    ));
    assert!(fir_text.contains("apply v2 args=[v0] ownership=[owned]"));
    assert!(fir_text.contains("apply v7 args=[v5,v6] ownership=[owned,borrowed]"));

    let lowered = fir::lower_to_flbc(&fir_validated)
        .expect("owned partial, exact, and over Apply lowers to FLBC");
    let owned = insert_ownership(&lowered, OwnershipLimits::default())
        .expect("Apply argument transfer is accepted by the independent ownership pass");
    assert_eq!(owned.witness().functions()[0].consumed_apply_args, 2);
    assert_eq!(owned.witness().functions()[2].consumed_closure_captures, 1);
    let bytes = encode_canonical(owned.program(), CodecLimits::default())
        .expect("owned Apply artifact encodes canonically");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("owned Apply artifact decodes independently");
    let rebound = validate_ownership_candidate(
        &lowered,
        decoded,
        owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .expect("owned Apply artifact rebinds to FIR and its consume witness");

    shadow::enable();
    let stopped = execute(
        rebound.program(),
        ExecutionLimits {
            max_steps: 100,
            max_stack_depth: 1,
        },
        None,
    );
    assert!(matches!(
        stopped,
        Outcome::Inconclusive(ref inconclusive)
            if matches!(
                inconclusive.cause,
                InconclusiveCause::ResourceExhausted { ref usage }
                    if usage.reason == ResourceReason::RecursionDepth { limit: 1 }
            )
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "a stack stop after an owned partial Apply releases every retained payload"
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));

    shadow::enable();
    let completed = returned(execute(rebound.program(), ExecutionLimits::default(), None));
    assert_eq!(completed.value.array_view(), (2, 2));
    assert_eq!(
        string_contents(&completed.value.array_child(0)),
        "partial-owned"
    );
    assert_eq!(
        string_contents(&completed.value.array_child(1)),
        "over-owned"
    );
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "successful partial, exact, and over Apply drains every Marrow object"
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));

    let same_destination_source = validated(vec![
        function(
            0,
            0,
            2,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "same Apply destination".to_string(),
                },
                Instruction::Closure {
                    dst: r(1),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Apply {
                    dst: r(0),
                    closure: r(1),
                    args: vec![r(0)],
                    argument_ownership: vec![ArgumentOwnership::Owned],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(0) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Owned],
            1,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    let same_destination_owned =
        insert_ownership(&same_destination_source, OwnershipLimits::default())
            .expect("a consumed Apply argument opens its destination epoch");
    assert_eq!(
        same_destination_owned.witness().functions()[0].consumed_apply_args,
        1
    );
    let bytes = encode_canonical(same_destination_owned.program(), CodecLimits::default())
        .expect("same-destination Apply encodes canonically");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("same-destination Apply decodes canonically");
    let same_destination = validate_ownership_candidate(
        &same_destination_source,
        decoded,
        same_destination_owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .expect("same-destination Apply rebinds independently");
    shadow::enable();
    let completed = returned(execute(
        same_destination.program(),
        ExecutionLimits::default(),
        None,
    ));
    assert_eq!(string_contents(&completed.value), "same Apply destination");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "same-destination Apply drains its exact token");
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));

    let unique_partial = validated(vec![
        function(
            0,
            0,
            3,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "unique partial".to_string(),
                },
                Instruction::Closure {
                    dst: r(1),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Apply {
                    dst: r(2),
                    closure: r(1),
                    args: vec![r(0)],
                    argument_ownership: vec![ArgumentOwnership::Unique],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(2) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Unique, ArgumentOwnership::Borrowed],
            2,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    shadow::enable();
    let refused = execute(&unique_partial, ExecutionLimits::default(), None);
    assert!(matches!(
        refused,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::ApplyUniquePartial {
                function,
                argument: 0,
            },
            ..
        }) if function == fid(1)
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "Unique under-application refuses before transfer and drains the entry frame"
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));

    let direct_contract_drift = validated(vec![
        function(
            0,
            0,
            3,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "contract drift".to_string(),
                },
                Instruction::Closure {
                    dst: r(1),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Apply {
                    dst: r(2),
                    closure: r(1),
                    args: vec![r(0)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(2) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Owned],
            1,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    shadow::enable();
    let refused = execute(&direct_contract_drift, ExecutionLimits::default(), None);
    assert!(matches!(
        refused,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::ApplyOwnershipMismatch {
                function,
                argument: 0,
                expected: ArgumentOwnership::Owned,
                actual: ArgumentOwnership::Borrowed,
            },
            ..
        }) if function == fid(1)
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "a dynamic Apply contract mismatch refuses before argument transfer"
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));

    let returned_contract_drift = validated(vec![
        function(
            0,
            0,
            4,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "first transfer".to_string(),
                },
                Instruction::String {
                    dst: r(1),
                    value: "remainder drift".to_string(),
                },
                Instruction::Closure {
                    dst: r(2),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Apply {
                    dst: r(3),
                    closure: r(2),
                    args: vec![r(0), r(1)],
                    argument_ownership: vec![ArgumentOwnership::Owned, ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(3) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Owned],
            2,
            vec![
                Instruction::Closure {
                    dst: r(1),
                    function: fid(2),
                    captures: vec![r(0)],
                    capture_ownership: vec![ArgumentOwnership::Owned],
                },
                Instruction::Return { src: r(1) },
            ],
        ),
        function_with_ownership(
            2,
            vec![ArgumentOwnership::Owned, ArgumentOwnership::Owned],
            2,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    shadow::enable();
    let refused = execute(&returned_contract_drift, ExecutionLimits::default(), None);
    assert!(matches!(
        refused,
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::ApplyOwnershipMismatch {
                function,
                argument: 0,
                expected: ArgumentOwnership::Owned,
                actual: ArgumentOwnership::Borrowed,
            },
            ..
        }) if function == fid(2)
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "over-application validates the returned closure segment and drains transferred state"
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));
}

#[test]
fn core_expr_ingress_reaches_canonical_flbc_and_golem_without_host_evaluation() {
    let _guard = lock();
    let source = Expr::let_e(
        Name::anonymous(),
        Expr::sort(Level::zero()),
        Expr::lit(Literal::Str("core-to-golem".to_string())),
        Expr::mdata(KVMap::new(), Expr::bvar(0).expect("small de Bruijn index")),
        false,
    );
    let source_hash = source.hash();
    let ingress = ingress::lower_closed_expr(&source, ingress::IngressLimits::default())
        .expect("closed core expression enters validated FIR");
    assert_eq!(ingress.source_expr_hash(), source_hash);
    assert_eq!(
        ingress.work(),
        ingress::IngressWork {
            visited_nodes: 4,
            source_bindings: 1,
            capture_analysis_nodes: 0,
            captured_values: 0,
            elided_capture_slots: 0,
            intrinsic_calls: 0,
            constructor_calls: 0,
            projection_calls: 0,
            function_calls: 0,
            lambda_conversions: 0,
            recursive_self_closures: 0,
            mutual_group_closures: 0,
            closure_applications: 0,
            generated_constructors: 0,
            generated_projections: 0,
            generated_closure_types: 0,
            generated_functions: 1,
            function_parameters: 0,
            generated_values: 1,
            literal_bytes: 13,
            maximum_context_depth: 1,
        }
    );
    assert!(
        ingress
            .fir()
            .canonical_text()
            .contains("v0:string = string 13:636f72652d746f2d676f6c656d")
    );

    let lowered =
        fir::lower_to_flbc(ingress.fir()).expect("validated ingress must lower through FIR");
    let bytes =
        encode_canonical(&lowered, CodecLimits::default()).expect("canonical FLBC artifact");
    let decoded =
        decode_canonical(&bytes, CodecLimits::default()).expect("independent FLBC validation");
    assert_eq!(
        encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
        bytes
    );

    shadow::enable();
    let completed = returned(execute(&decoded, ExecutionLimits::default(), None));
    assert_eq!(string_contents(&completed.value), "core-to-golem");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "core Expr execution releases every Marrow object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "core Expr ingress introduces no shadow ownership defect"
    );
}

#[test]
fn core_linear_ownership_drops_dead_heap_values_at_their_final_use() {
    let _guard = lock();
    let source = Expr::let_e(
        Name::anonymous(),
        Expr::sort(Level::zero()),
        Expr::lit(Literal::Str("dead-before-next-allocation".to_string())),
        Expr::lit(Literal::Str("ownership-result".to_string())),
        false,
    );
    let ingress = ingress::lower_closed_expr(&source, ingress::IngressLimits::default())
        .expect("closed heap values enter validated FIR");
    let raw = fir::lower_to_flbc(ingress.fir()).expect("ordinary mandatory FIR lowering");
    let owned = fir::lower_to_flbc_with_ownership(ingress.fir(), OwnershipLimits::default())
        .expect("bounded ownership insertion and independent validation");
    assert_eq!(
        owned.witness().canonical_text(),
        concat!(
            "flbc-ownership/14\n",
            "function f0 mode=inserted-linear result=owned source=3 emitted=4 drops=1 moves=0 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
        )
    );
    assert_eq!(
        owned.program().functions()[0].code,
        vec![
            Instruction::String {
                dst: r(0),
                value: "dead-before-next-allocation".to_string(),
            },
            Instruction::Drop { src: r(0) },
            Instruction::String {
                dst: r(1),
                value: "ownership-result".to_string(),
            },
            Instruction::Return { src: r(1) },
        ]
    );

    let bytes = encode_canonical(owned.program(), CodecLimits::default())
        .expect("ownership candidate encodes canonically");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("ownership candidate passes independent FLBC decode");
    let decoded = validate_ownership_candidate(
        &raw,
        decoded,
        owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .expect("decoded candidate rebinds to the source and witness");
    assert_eq!(
        encode_canonical(decoded.program(), CodecLimits::default())
            .expect("decoded ownership candidate re-encodes"),
        bytes
    );

    shadow::enable();
    let completed = returned(execute(decoded.program(), ExecutionLimits::default(), None));
    assert_eq!(
        string_contents(&completed.value),
        "ownership-result",
        "eager release does not change the returned ABI value"
    );
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "ownership-inserted execution drains Marrow");
    let lifetime_events: Vec<_> = events
        .iter()
        .filter(|event| {
            matches!(
                event.kind,
                shadow::EventKind::Alloc | shadow::EventKind::Release
            )
        })
        .map(|event| (event.kind, event.tag))
        .collect();
    assert_eq!(
        lifetime_events,
        vec![
            (shadow::EventKind::Alloc, Some(0)),
            (shadow::EventKind::Release, Some(0)),
            (shadow::EventKind::Alloc, Some(1)),
            (shadow::EventKind::Release, Some(1)),
        ],
        "the dead first String is released before the returned String allocates"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "eager drops preserve the single Marrow ownership domain"
    );
}

#[test]
fn straight_line_register_reuse_releases_each_value_epoch_without_leaking() {
    let _guard = lock();
    let source = validated(vec![function(
        0,
        0,
        3,
        vec![
            Instruction::String {
                dst: r(0),
                value: "initial".to_string(),
            },
            Instruction::Copy {
                dst: r(0),
                src: r(0),
            },
            Instruction::Copy {
                dst: r(1),
                src: r(0),
            },
            Instruction::String {
                dst: r(0),
                value: "first".to_string(),
            },
            Instruction::String {
                dst: r(0),
                value: "second".to_string(),
            },
            Instruction::Copy {
                dst: r(2),
                src: r(0),
            },
            Instruction::Return { src: r(2) },
        ],
    )]);
    let owned = insert_ownership(&source, OwnershipLimits::default())
        .expect("straight-line register reuse receives exact value epochs");
    assert_eq!(
        owned.witness().canonical_text(),
        concat!(
            "flbc-ownership/14\n",
            "function f0 mode=inserted-linear-reuse result=owned source=7 emitted=9 drops=2 moves=3 redefs=3 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
        )
    );
    assert_eq!(
        owned.program().functions()[0].code,
        vec![
            Instruction::String {
                dst: r(0),
                value: "initial".to_string(),
            },
            Instruction::Move {
                dst: r(0),
                src: r(0),
            },
            Instruction::Move {
                dst: r(1),
                src: r(0),
            },
            Instruction::Drop { src: r(1) },
            Instruction::String {
                dst: r(0),
                value: "first".to_string(),
            },
            Instruction::Drop { src: r(0) },
            Instruction::String {
                dst: r(0),
                value: "second".to_string(),
            },
            Instruction::Move {
                dst: r(2),
                src: r(0),
            },
            Instruction::Return { src: r(2) },
        ]
    );

    let bytes = encode_canonical(owned.program(), CodecLimits::default())
        .expect("register-reuse candidate encodes canonically");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("register-reuse candidate remains ordinary valid FLBC");
    let rebound = validate_ownership_candidate(
        &source,
        decoded,
        owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .expect("decoded register-reuse candidate rebinds to every source epoch");

    let raw = returned(execute(&source, ExecutionLimits::default(), None));
    assert_eq!(string_contents(&raw.value), "second");
    drop(raw);

    shadow::enable();
    let completed = returned(execute(rebound.program(), ExecutionLimits::default(), None));
    assert_eq!(string_contents(&completed.value), "second");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "register reuse drains every Marrow value epoch");
    let lifetime_events: Vec<_> = events
        .iter()
        .filter(|event| {
            matches!(
                event.kind,
                shadow::EventKind::Alloc | shadow::EventKind::Release
            )
        })
        .map(|event| (event.kind, event.tag))
        .collect();
    assert_eq!(
        lifetime_events,
        vec![
            (shadow::EventKind::Alloc, Some(0)),
            (shadow::EventKind::Release, Some(0)),
            (shadow::EventKind::Alloc, Some(1)),
            (shadow::EventKind::Release, Some(1)),
            (shadow::EventKind::Alloc, Some(2)),
            (shadow::EventKind::Release, Some(2)),
        ],
        "each overwritten allocation is released before the next value epoch"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "self-transfer and register reuse stay inside one Marrow ownership domain"
    );
}

#[test]
fn acyclic_cfg_register_reuse_executes_both_value_epochs_without_leaking() {
    let _guard = lock();
    for (condition, expected_result) in [(0, "zero"), (1, "nonzero")] {
        let source = validated(vec![function(
            0,
            0,
            4,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "initial".to_string(),
                },
                Instruction::Nat {
                    dst: r(1),
                    value: condition,
                },
                Instruction::JumpIfZero {
                    cond: r(1),
                    zero: pc(3),
                    nonzero: pc(5),
                },
                Instruction::String {
                    dst: r(0),
                    value: "zero".to_string(),
                },
                Instruction::Jump { target: pc(6) },
                Instruction::String {
                    dst: r(0),
                    value: "nonzero".to_string(),
                },
                Instruction::Copy {
                    dst: r(2),
                    src: r(0),
                },
                Instruction::Return { src: r(2) },
            ],
        )]);
        let owned = insert_ownership(&source, OwnershipLimits::default())
            .expect("acyclic register reuse receives path-specific ownership");
        assert_eq!(
            owned.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-acyclic-cfg-reuse result=owned source=8 emitted=14 drops=3 moves=1 redefs=2 edges=3 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );

        let bytes = encode_canonical(owned.program(), CodecLimits::default())
            .expect("acyclic reuse candidate encodes canonically");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("acyclic reuse candidate decodes");
        let rebound = validate_ownership_candidate(
            &source,
            decoded,
            owned.witness().clone(),
            OwnershipLimits::default(),
        )
        .expect("decoded candidate rebinds to every path-local value");

        let raw = returned(execute(&source, ExecutionLimits::default(), None));
        assert_eq!(string_contents(&raw.value), expected_result);
        drop(raw);

        shadow::enable();
        let completed = returned(execute(rebound.program(), ExecutionLimits::default(), None));
        assert_eq!(string_contents(&completed.value), expected_result);
        drop(completed);
        let (events, live) = shadow::disable_and_drain();
        assert_eq!(live, 0, "each acyclic reuse path drains Marrow");
        let lifetime_events: Vec<_> = events
            .iter()
            .filter(|event| {
                matches!(
                    event.kind,
                    shadow::EventKind::Alloc | shadow::EventKind::Release
                )
            })
            .map(|event| (event.kind, event.tag))
            .collect();
        assert_eq!(
            lifetime_events,
            vec![
                (shadow::EventKind::Alloc, Some(0)),
                (shadow::EventKind::Release, Some(0)),
                (shadow::EventKind::Alloc, Some(1)),
                (shadow::EventKind::Release, Some(1)),
            ],
            "the dead entry epoch is released before the selected branch epoch"
        );
        assert!(
            events.iter().all(|event| {
                event.kind != shadow::EventKind::DoubleRelease
                    && event.kind != shadow::EventKind::ForeignPointer
            }),
            "branch-local register reuse stays inside one Marrow ownership domain"
        );
    }
}

#[test]
fn cyclic_cfg_register_reuse_executes_zero_one_and_bounded_many_iterations() {
    fn source(initial_condition: u64, next_condition: u64) -> ValidatedProgram {
        validated(vec![function(
            0,
            0,
            2,
            vec![
                Instruction::String {
                    dst: r(1),
                    value: "initial".to_string(),
                },
                Instruction::Nat {
                    dst: r(0),
                    value: initial_condition,
                },
                Instruction::JumpIfZero {
                    cond: r(0),
                    zero: pc(6),
                    nonzero: pc(3),
                },
                Instruction::String {
                    dst: r(1),
                    value: "iteration".to_string(),
                },
                Instruction::Nat {
                    dst: r(0),
                    value: next_condition,
                },
                Instruction::Jump { target: pc(2) },
                Instruction::Return { src: r(1) },
            ],
        )])
    }

    fn lower_and_rebind(source: &ValidatedProgram) -> fln_comp::flbc::OwnershipProgram {
        let owned = insert_ownership(source, OwnershipLimits::default())
            .expect("cyclic register reuse receives fixed-point ownership");
        assert_eq!(
            owned.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-cyclic-cfg-reuse result=owned source=7 emitted=13 drops=3 moves=0 redefs=2 edges=3 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        let bytes = encode_canonical(owned.program(), CodecLimits::default())
            .expect("cyclic reuse candidate encodes canonically");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("cyclic reuse candidate decodes");
        let rebound = validate_ownership_candidate(
            source,
            decoded,
            owned.witness().clone(),
            OwnershipLimits::default(),
        )
        .expect("independent fixed point rebinds the runtime candidate");
        assert_eq!(
            encode_canonical(rebound.program(), CodecLimits::default())
                .expect("rebound cyclic reuse candidate re-encodes"),
            bytes
        );
        rebound
    }

    fn lifetimes(events: &[shadow::ShadowEvent]) -> Vec<(shadow::EventKind, Option<u64>)> {
        events
            .iter()
            .filter(|event| {
                matches!(
                    event.kind,
                    shadow::EventKind::Alloc | shadow::EventKind::Release
                )
            })
            .map(|event| (event.kind, event.tag))
            .collect()
    }

    fn assert_clean(events: &[shadow::ShadowEvent]) {
        assert!(events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }));
    }

    let _guard = lock();

    let zero_trip = lower_and_rebind(&source(0, 0));
    shadow::enable();
    let completed = returned(execute(
        zero_trip.program(),
        ExecutionLimits::default(),
        None,
    ));
    assert_eq!(string_contents(&completed.value), "initial");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "zero-trip cyclic reuse drains Marrow");
    assert_eq!(
        lifetimes(&events),
        vec![
            (shadow::EventKind::Alloc, Some(0)),
            (shadow::EventKind::Release, Some(0)),
        ]
    );
    assert_clean(&events);

    let one_trip = lower_and_rebind(&source(1, 0));
    shadow::enable();
    let completed = returned(execute(
        one_trip.program(),
        ExecutionLimits::default(),
        None,
    ));
    assert_eq!(string_contents(&completed.value), "iteration");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "one-trip cyclic reuse drains both value epochs");
    assert_eq!(
        lifetimes(&events),
        vec![
            (shadow::EventKind::Alloc, Some(0)),
            (shadow::EventKind::Release, Some(0)),
            (shadow::EventKind::Alloc, Some(1)),
            (shadow::EventKind::Release, Some(1)),
        ],
        "the prior loop-carried value retires before its replacement allocates"
    );
    assert_clean(&events);

    let looping = lower_and_rebind(&source(1, 1));
    shadow::enable();
    let stopped = execute(
        looping.program(),
        ExecutionLimits {
            max_steps: 15,
            max_stack_depth: 8,
        },
        None,
    );
    assert_eq!(stopped.authority(), Authority::NonAuthoritative);
    match stopped {
        Outcome::Inconclusive(inconclusive) => match inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                assert!(usage.is_genuine_exhaustion());
                assert_eq!(usage.allowed, 15);
                assert_eq!(usage.observed, 16);
                assert_eq!(
                    usage.reason,
                    ResourceReason::Heartbeats {
                        consumed: 16,
                        limit: 15,
                    }
                );
            }
            other => panic!("expected cyclic reuse step exhaustion, got {other:?}"),
        },
        other => panic!("expected cyclic reuse Inconclusive, got {other:?}"),
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "bounded repeated replacement tears down the current value epoch"
    );
    assert_eq!(
        lifetimes(&events),
        vec![
            (shadow::EventKind::Alloc, Some(0)),
            (shadow::EventKind::Release, Some(0)),
            (shadow::EventKind::Alloc, Some(1)),
            (shadow::EventKind::Release, Some(1)),
            (shadow::EventKind::Alloc, Some(2)),
            (shadow::EventKind::Release, Some(2)),
        ]
    );
    assert_clean(&events);
}

#[test]
fn preowned_flbc_is_checked_before_golem_and_preserves_transfer_events() {
    let _guard = lock();
    let source = validated(vec![function(
        0,
        0,
        4,
        vec![
            Instruction::String {
                dst: r(0),
                value: "moved".to_string(),
            },
            Instruction::Move {
                dst: r(1),
                src: r(0),
            },
            Instruction::String {
                dst: r(2),
                value: "dropped-first".to_string(),
            },
            Instruction::Drop { src: r(2) },
            Instruction::Drop { src: r(1) },
            Instruction::String {
                dst: r(3),
                value: "returned".to_string(),
            },
            Instruction::Return { src: r(3) },
        ],
    )]);
    let owned = insert_ownership(&source, OwnershipLimits::default())
        .expect("balanced pre-owned FLBC passes the independent state walk");
    assert_eq!(owned.program().functions(), source.functions());
    assert_eq!(
        owned.witness().canonical_text(),
        concat!(
            "flbc-ownership/14\n",
            "function f0 mode=validated-existing-ownership result=owned source=7 emitted=7 drops=0 moves=0 existing_drops=2 existing_moves=1 redefs=0 edges=0 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
        )
    );
    let bytes = encode_canonical(owned.program(), CodecLimits::default())
        .expect("pre-owned FLBC encodes canonically");
    let decoded = decode_canonical(&bytes, CodecLimits::default()).expect("pre-owned FLBC decodes");
    let rebound = validate_ownership_candidate(
        &source,
        decoded,
        owned.witness().clone(),
        OwnershipLimits::default(),
    )
    .expect("decoded pre-owned FLBC repeats the state walk and count binding");

    shadow::enable();
    let completed = returned(execute(rebound.program(), ExecutionLimits::default(), None));
    assert_eq!(string_contents(&completed.value), "returned");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "validated pre-owned execution drains Marrow");
    let lifetime_events: Vec<_> = events
        .iter()
        .filter(|event| {
            matches!(
                event.kind,
                shadow::EventKind::Alloc | shadow::EventKind::Release
            )
        })
        .map(|event| (event.kind, event.tag))
        .collect();
    assert_eq!(
        lifetime_events,
        vec![
            (shadow::EventKind::Alloc, Some(0)),
            (shadow::EventKind::Alloc, Some(1)),
            (shadow::EventKind::Release, Some(1)),
            (shadow::EventKind::Release, Some(0)),
            (shadow::EventKind::Alloc, Some(2)),
            (shadow::EventKind::Release, Some(2)),
        ],
        "Move transfers without a retain-release pair and explicit Drops keep source order"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "validated pre-owned execution stays inside one Marrow ownership domain"
    );

    let invalid = validated(vec![function(
        0,
        0,
        2,
        vec![
            Instruction::String {
                dst: r(0),
                value: "source".to_string(),
            },
            Instruction::String {
                dst: r(1),
                value: "live-destination".to_string(),
            },
            Instruction::Move {
                dst: r(1),
                src: r(0),
            },
            Instruction::Return { src: r(1) },
        ],
    )]);
    shadow::enable();
    assert!(matches!(
        insert_ownership(&invalid, OwnershipLimits::default()),
        Err(OwnershipError::OwnershipOverwrite {
            source_position: 2,
            register,
            ..
        }) if register == r(1)
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0);
    assert!(
        events.is_empty(),
        "invalid pre-owned input refuses before any Marrow object exists"
    );
}

#[test]
fn fir_acyclic_cfg_ownership_executes_both_edges_with_balanced_marrow() {
    fn source(condition: u64) -> fir::ValidatedProgram {
        let program = fir::Program::new(
            fir::FunctionId::new(0),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![fir::Function {
                id: fir::FunctionId::new(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: fir::ValueType::String,
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![
                    fir::Block {
                        id: fir::BlockId::new(0),
                        bindings: vec![
                            fir::Binding {
                                id: fir::ValueId::new(0),
                                ty: fir::ValueType::String,
                                operation: fir::Operation::String("branch-owned".to_string()),
                            },
                            fir::Binding {
                                id: fir::ValueId::new(1),
                                ty: fir::ValueType::String,
                                operation: fir::Operation::String("shared-return".to_string()),
                            },
                            fir::Binding {
                                id: fir::ValueId::new(2),
                                ty: fir::ValueType::Nat,
                                operation: fir::Operation::Nat(condition),
                            },
                        ],
                        terminator: fir::Terminator::BranchZero {
                            condition: fir::ValueId::new(2),
                            zero: fir::BlockId::new(1),
                            nonzero: fir::BlockId::new(2),
                        },
                    },
                    fir::Block {
                        id: fir::BlockId::new(1),
                        bindings: vec![
                            fir::Binding {
                                id: fir::ValueId::new(3),
                                ty: fir::ValueType::String,
                                operation: fir::Operation::Alias(fir::ValueId::new(0)),
                            },
                            fir::Binding {
                                id: fir::ValueId::new(4),
                                ty: fir::ValueType::String,
                                operation: fir::Operation::String("left-only".to_string()),
                            },
                        ],
                        terminator: fir::Terminator::Jump {
                            target: fir::BlockId::new(3),
                        },
                    },
                    fir::Block {
                        id: fir::BlockId::new(2),
                        bindings: Vec::new(),
                        terminator: fir::Terminator::Jump {
                            target: fir::BlockId::new(3),
                        },
                    },
                    fir::Block {
                        id: fir::BlockId::new(3),
                        bindings: Vec::new(),
                        terminator: fir::Terminator::Return {
                            value: fir::ValueId::new(1),
                        },
                    },
                ],
            }],
        );
        fir::validate(program, fir::ValidationLimits::default())
            .expect("acyclic branch and join are valid FIR")
    }

    let _guard = lock();
    for (condition, expected_lifetimes) in [
        (
            0,
            vec![
                (shadow::EventKind::Alloc, Some(0)),
                (shadow::EventKind::Alloc, Some(1)),
                (shadow::EventKind::Release, Some(0)),
                (shadow::EventKind::Alloc, Some(2)),
                (shadow::EventKind::Release, Some(2)),
                (shadow::EventKind::Release, Some(1)),
            ],
        ),
        (
            1,
            vec![
                (shadow::EventKind::Alloc, Some(0)),
                (shadow::EventKind::Alloc, Some(1)),
                (shadow::EventKind::Release, Some(0)),
                (shadow::EventKind::Release, Some(1)),
            ],
        ),
    ] {
        let source = source(condition);
        let raw = fir::lower_to_flbc(&source).expect("validated branch FIR lowers");
        let owned = fir::lower_to_flbc_with_ownership(&source, OwnershipLimits::default())
            .expect("acyclic CFG ownership insertion validates");
        assert_eq!(
            owned.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-acyclic-cfg result=owned source=9 emitted=18 drops=5 moves=1 redefs=0 edges=4 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        assert_eq!(
            &owned.program().functions()[0].code[4..=5],
            &[
                Instruction::Move {
                    dst: r(3),
                    src: r(0),
                },
                Instruction::Drop { src: r(3) },
            ],
            "the final alias transfers ownership without a retain and redundant source drop"
        );

        let bytes = encode_canonical(owned.program(), CodecLimits::default())
            .expect("ownership CFG encodes canonically");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("ownership CFG decodes as ordinary valid FLBC");
        let decoded = validate_ownership_candidate(
            &raw,
            decoded,
            owned.witness().clone(),
            OwnershipLimits::default(),
        )
        .expect("decoded CFG rebinds to source, edge layout, and witness");

        shadow::enable();
        let completed = returned(execute(decoded.program(), ExecutionLimits::default(), None));
        assert_eq!(string_contents(&completed.value), "shared-return");
        drop(completed);
        let (events, live) = shadow::disable_and_drain();
        assert_eq!(live, 0, "each branch drains every Marrow object");
        let lifetimes: Vec<_> = events
            .iter()
            .filter(|event| {
                matches!(
                    event.kind,
                    shadow::EventKind::Alloc | shadow::EventKind::Release
                )
            })
            .map(|event| (event.kind, event.tag))
            .collect();
        assert_eq!(
            lifetimes, expected_lifetimes,
            "each edge executes only its canonical path-specific releases"
        );
        assert!(
            events.iter().all(|event| {
                event.kind != shadow::EventKind::DoubleRelease
                    && event.kind != shadow::EventKind::ForeignPointer
            }),
            "CFG ownership keeps one Marrow ownership domain"
        );
    }
}

#[test]
fn fir_cyclic_cfg_ownership_returns_or_stops_bounded_without_leaking() {
    fn source(condition: u64) -> fir::ValidatedProgram {
        let program = fir::Program::new(
            fir::FunctionId::new(0),
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![fir::Function {
                id: fir::FunctionId::new(0),
                parameters: Vec::new(),
                parameter_ownership: Vec::new(),
                result: fir::ValueType::String,
                result_ownership: CallableResultOwnership::Owned,
                blocks: vec![
                    fir::Block {
                        id: fir::BlockId::new(0),
                        bindings: vec![
                            fir::Binding {
                                id: fir::ValueId::new(0),
                                ty: fir::ValueType::String,
                                operation: fir::Operation::String("loop-return".to_string()),
                            },
                            fir::Binding {
                                id: fir::ValueId::new(1),
                                ty: fir::ValueType::Nat,
                                operation: fir::Operation::Nat(condition),
                            },
                        ],
                        terminator: fir::Terminator::Jump {
                            target: fir::BlockId::new(1),
                        },
                    },
                    fir::Block {
                        id: fir::BlockId::new(1),
                        bindings: Vec::new(),
                        terminator: fir::Terminator::BranchZero {
                            condition: fir::ValueId::new(1),
                            zero: fir::BlockId::new(3),
                            nonzero: fir::BlockId::new(2),
                        },
                    },
                    fir::Block {
                        id: fir::BlockId::new(2),
                        bindings: vec![
                            fir::Binding {
                                id: fir::ValueId::new(2),
                                ty: fir::ValueType::String,
                                operation: fir::Operation::String("iteration-dead".to_string()),
                            },
                            fir::Binding {
                                id: fir::ValueId::new(3),
                                ty: fir::ValueType::String,
                                operation: fir::Operation::Alias(fir::ValueId::new(0)),
                            },
                        ],
                        terminator: fir::Terminator::Jump {
                            target: fir::BlockId::new(1),
                        },
                    },
                    fir::Block {
                        id: fir::BlockId::new(3),
                        bindings: Vec::new(),
                        terminator: fir::Terminator::Return {
                            value: fir::ValueId::new(0),
                        },
                    },
                ],
            }],
        );
        fir::validate(program, fir::ValidationLimits::default())
            .expect("loop header, body, and exit are valid FIR")
    }

    fn lower_and_rebind(
        source: &fir::ValidatedProgram,
    ) -> (ValidatedProgram, fln_comp::flbc::OwnershipProgram) {
        let raw = fir::lower_to_flbc(source).expect("validated cyclic FIR lowers");
        let owned = fir::lower_to_flbc_with_ownership(source, OwnershipLimits::default())
            .expect("cyclic CFG ownership insertion validates");
        assert_eq!(
            owned.witness().canonical_text(),
            concat!(
                "flbc-ownership/14\n",
                "function f0 mode=inserted-cyclic-cfg result=owned source=8 emitted=15 drops=3 moves=0 redefs=0 edges=4 extern_consumes=0 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=0 owned_callable_results=0 scalar_callable_results=0\n",
            )
        );
        let bytes = encode_canonical(owned.program(), CodecLimits::default())
            .expect("cyclic ownership CFG encodes canonically");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("cyclic ownership CFG decodes as ordinary valid FLBC");
        let rebound = validate_ownership_candidate(
            &raw,
            decoded,
            owned.witness().clone(),
            OwnershipLimits::default(),
        )
        .expect("decoded cycle rebinds to source, fixed point, layout, and witness");
        assert_eq!(
            encode_canonical(rebound.program(), CodecLimits::default())
                .expect("rebound cycle re-encodes"),
            bytes
        );
        (raw, rebound)
    }

    let _guard = lock();
    let returning_source = source(0);
    let (returning_raw, returning_owned) = lower_and_rebind(&returning_source);
    assert_eq!(
        returning_raw.functions()[0].code,
        vec![
            Instruction::String {
                dst: r(0),
                value: "loop-return".to_string(),
            },
            Instruction::Nat {
                dst: r(1),
                value: 0,
            },
            Instruction::Jump { target: pc(3) },
            Instruction::JumpIfZero {
                cond: r(1),
                zero: pc(7),
                nonzero: pc(4),
            },
            Instruction::String {
                dst: r(2),
                value: "iteration-dead".to_string(),
            },
            Instruction::Copy {
                dst: r(3),
                src: r(0),
            },
            Instruction::Jump { target: pc(3) },
            Instruction::Return { src: r(0) },
        ]
    );
    assert_eq!(
        returning_owned.program().functions()[0].code,
        vec![
            Instruction::String {
                dst: r(0),
                value: "loop-return".to_string(),
            },
            Instruction::Nat {
                dst: r(1),
                value: 0,
            },
            Instruction::Jump { target: pc(10) },
            Instruction::JumpIfZero {
                cond: r(1),
                zero: pc(11),
                nonzero: pc(13),
            },
            Instruction::String {
                dst: r(2),
                value: "iteration-dead".to_string(),
            },
            Instruction::Drop { src: r(2) },
            Instruction::Copy {
                dst: r(3),
                src: r(0),
            },
            Instruction::Drop { src: r(3) },
            Instruction::Jump { target: pc(14) },
            Instruction::Return { src: r(0) },
            Instruction::Jump { target: pc(3) },
            Instruction::Drop { src: r(1) },
            Instruction::Jump { target: pc(9) },
            Instruction::Jump { target: pc(4) },
            Instruction::Jump { target: pc(3) },
        ]
    );

    shadow::enable();
    let completed = returned(execute(
        returning_owned.program(),
        ExecutionLimits::default(),
        None,
    ));
    assert_eq!(string_contents(&completed.value), "loop-return");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "the loop exit drains its returned Marrow object");
    let lifetimes: Vec<_> = events
        .iter()
        .filter(|event| {
            matches!(
                event.kind,
                shadow::EventKind::Alloc | shadow::EventKind::Release
            )
        })
        .map(|event| (event.kind, event.tag))
        .collect();
    assert_eq!(
        lifetimes,
        vec![
            (shadow::EventKind::Alloc, Some(0)),
            (shadow::EventKind::Release, Some(0)),
        ]
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));

    let looping_source = source(1);
    let (_, looping_owned) = lower_and_rebind(&looping_source);
    shadow::enable();
    let stopped = execute(
        looping_owned.program(),
        ExecutionLimits {
            max_steps: 14,
            max_stack_depth: 8,
        },
        None,
    );
    assert_eq!(stopped.authority(), Authority::NonAuthoritative);
    match stopped {
        Outcome::Inconclusive(inconclusive) => match inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                assert!(usage.is_genuine_exhaustion());
                assert_eq!(usage.allowed, 14);
                assert_eq!(usage.observed, 15);
                assert_eq!(
                    usage.reason,
                    ResourceReason::Heartbeats {
                        consumed: 15,
                        limit: 14,
                    }
                );
            }
            other => panic!("expected loop step exhaustion, got {other:?}"),
        },
        other => panic!("expected cyclic Inconclusive, got {other:?}"),
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "bounded nontermination tears down the loop's live register graph"
    );
    let lifetimes: Vec<_> = events
        .iter()
        .filter(|event| {
            matches!(
                event.kind,
                shadow::EventKind::Alloc | shadow::EventKind::Release
            )
        })
        .map(|event| (event.kind, event.tag))
        .collect();
    assert_eq!(
        lifetimes,
        vec![
            (shadow::EventKind::Alloc, Some(0)),
            (shadow::EventKind::Alloc, Some(1)),
            (shadow::EventKind::Release, Some(1)),
            (shadow::EventKind::Release, Some(0)),
        ],
        "each completed loop iteration releases its dead heap value before retry"
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));
}

#[test]
fn generated_contract_intrinsics_compile_from_core_expr_and_execute_on_marrow_values() {
    fn binding(
        row: &str,
        arguments: Vec<fir::ValueType>,
        result: fir::ValueType,
    ) -> ingress::IntrinsicBinding {
        let generated = EXTERN_ROWS
            .iter()
            .find(|candidate| candidate.id == row)
            .expect("implemented row remains in the generated extern contract");
        assert_eq!(generated.effect, "pure");
        assert_eq!(usize::try_from(generated.arity).ok(), Some(arguments.len()));
        ingress::IntrinsicBinding {
            name: Name::from_components(generated.name.split('.')),
            universe_arity: usize::try_from(generated.levels).expect("u32 fits usize"),
            row: generated.id.to_string(),
            argument_ownership: contract_argument_ownership(generated.id, arguments.len()),
            result_ownership: contract_result_ownership(generated.id),
            arguments,
            result,
            effect: fir::EffectClass::Pure,
        }
    }

    fn call(name: &[&str], arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(name.iter().copied()), Vec::new()),
            Expr::app,
        )
    }

    fn compile(source: &Expr, catalog: &[ingress::IntrinsicBinding]) -> ValidatedProgram {
        let ingress = ingress::lower_closed_expr_with_intrinsics(
            source,
            catalog,
            ingress::IngressLimits::default(),
        )
        .expect("typed direct intrinsic application enters FIR");
        let lowered =
            fir::lower_to_flbc(ingress.fir()).expect("validated ingress lowers through FIR");
        let bytes = encode_canonical(&lowered, CodecLimits::default())
            .expect("canonical direct-application FLBC");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("independent direct-application FLBC validation");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
            bytes
        );
        decoded
    }

    let _guard = lock();
    let catalog = [
        binding(
            "extern:String.append",
            vec![fir::ValueType::String, fir::ValueType::String],
            fir::ValueType::String,
        ),
        binding(
            "extern:Nat.add",
            vec![fir::ValueType::Nat, fir::ValueType::Nat],
            fir::ValueType::Nat,
        ),
    ];
    let nat_source = call(
        &["Nat", "add"],
        [
            Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(20))),
            Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(22))),
        ],
    );
    let string_source = call(
        &["String", "append"],
        [
            Expr::lit(Literal::Str("core-".to_string())),
            Expr::lit(Literal::Str("golem".to_string())),
        ],
    );

    let nat_program = compile(&nat_source, &catalog);
    let string_program = compile(&string_source, &catalog);
    shadow::enable();
    let nat = returned(execute(&nat_program, ExecutionLimits::default(), None));
    assert_eq!(nat.value.unbox(), 42);
    drop(nat);
    let string = returned(execute(&string_program, ExecutionLimits::default(), None));
    assert_eq!(string_contents(&string.value), "core-golem");
    drop(string);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "direct intrinsic execution releases every object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "contract-bound direct calls preserve Marrow ownership"
    );
}

#[test]
fn typed_first_order_core_functions_execute_through_canonical_flbc_calls() {
    fn call(name: &[&str], arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(name.iter().copied()), Vec::new()),
            Expr::app,
        )
    }

    let generated = EXTERN_ROWS
        .iter()
        .find(|candidate| candidate.id == "extern:Nat.add")
        .expect("Nat.add remains in the generated extern contract");
    assert_eq!(generated.name, "Nat.add");
    assert_eq!(generated.effect, "pure");
    assert_eq!(generated.arity, 2);
    let add = ingress::IntrinsicBinding {
        name: Name::from_components(generated.name.split('.')),
        universe_arity: usize::try_from(generated.levels).expect("u32 fits usize"),
        row: generated.id.to_string(),
        argument_ownership: contract_argument_ownership(generated.id, 2),
        result_ownership: contract_result_ownership(generated.id),
        arguments: vec![fir::ValueType::Nat, fir::ValueType::Nat],
        result: fir::ValueType::Nat,
        effect: fir::EffectClass::Pure,
    };
    let inc = ingress::FunctionBinding {
        name: Name::from_components(["User", "inc"]),
        universe_arity: 0,
        parameters: vec![fir::ValueType::Nat],
        parameter_ownership: vec![ArgumentOwnership::Borrowed],
        result: fir::ValueType::Nat,
        result_ownership: CallableResultOwnership::Scalar,
        body: call(
            &["Nat", "add"],
            [
                Expr::bvar(0).expect("small de Bruijn index"),
                Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(1))),
            ],
        ),
    };
    let twice = ingress::FunctionBinding {
        name: Name::from_components(["User", "twice"]),
        universe_arity: 0,
        parameters: vec![fir::ValueType::Nat],
        parameter_ownership: vec![ArgumentOwnership::Borrowed],
        result: fir::ValueType::Nat,
        result_ownership: CallableResultOwnership::Scalar,
        body: call(
            &["User", "inc"],
            [call(
                &["User", "inc"],
                [Expr::bvar(0).expect("small de Bruijn index")],
            )],
        ),
    };
    let source = call(
        &["User", "twice"],
        [Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(
            40,
        )))],
    );
    let ingress = ingress::lower_closed_expr_with_catalogs(
        &source,
        &[add],
        &[],
        &[twice, inc],
        ingress::IngressLimits::default(),
    )
    .expect("typed first-order bodies enter validated FIR");
    assert_eq!(ingress.work().function_calls, 3);
    assert_eq!(ingress.work().intrinsic_calls, 1);
    assert_eq!(ingress.work().generated_functions, 3);
    assert!(
        ingress
            .fir()
            .canonical_text()
            .contains("v1:nat = call f2 [v0]")
    );

    let lowered =
        fir::lower_to_flbc(ingress.fir()).expect("first-order FIR lowers through validation");
    let bytes =
        encode_canonical(&lowered, CodecLimits::default()).expect("canonical first-order FLBC");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("independent first-order FLBC validation");
    assert_eq!(
        encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
        bytes
    );

    let _guard = lock();
    shadow::enable();
    let completed = returned(execute(&decoded, ExecutionLimits::default(), None));
    assert_eq!(completed.value.unbox(), 42);
    assert_eq!(completed.usage.peak_stack_depth, 3);
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "first-order execution releases every ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "Core-to-FIR direct calls preserve Marrow ownership"
    );
}

#[test]
fn typed_local_core_closures_execute_nat_and_string_captures_with_balanced_ownership() {
    fn call(name: &[&str], arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(name.iter().copied()), Vec::new()),
            Expr::app,
        )
    }

    fn intrinsic(
        row: &str,
        arguments: Vec<fir::ValueType>,
        result: fir::ValueType,
    ) -> ingress::IntrinsicBinding {
        let generated = EXTERN_ROWS
            .iter()
            .find(|candidate| candidate.id == row)
            .expect("closure intrinsic remains in the generated contract");
        assert_eq!(generated.effect, "pure");
        assert_eq!(usize::try_from(generated.arity).ok(), Some(arguments.len()));
        ingress::IntrinsicBinding {
            name: Name::from_components(generated.name.split('.')),
            universe_arity: usize::try_from(generated.levels).expect("u32 fits usize"),
            row: generated.id.to_string(),
            argument_ownership: contract_argument_ownership(generated.id, arguments.len()),
            result_ownership: contract_result_ownership(generated.id),
            arguments,
            result,
            effect: fir::EffectClass::Pure,
        }
    }

    fn lambda(name: &str, body: Expr) -> Expr {
        Expr::lam(
            Name::from_components([name]),
            Expr::sort(Level::zero()),
            body,
            BinderInfo::Default,
        )
    }

    fn compile(
        source: &Expr,
        intrinsic: ingress::IntrinsicBinding,
        lambda: &Expr,
        parameter: fir::ValueType,
        result: fir::ValueType,
    ) -> ValidatedProgram {
        let annotation = ingress::LambdaBinding {
            lambda: lambda.clone(),
            parameters: vec![parameter],
            parameter_ownership: vec![ArgumentOwnership::Borrowed],
            result,
            result_ownership: callable_result_ownership(result),
            recursion: ingress::LambdaRecursion::NonRecursive,
        };
        let ingress = ingress::lower_closed_expr_with_lambdas(
            source,
            &[intrinsic],
            &[],
            &[],
            &[annotation],
            ingress::IngressLimits::default(),
        )
        .expect("typed local closure enters validated FIR");
        assert_eq!(ingress.work().source_bindings, 2);
        assert_eq!(ingress.work().capture_analysis_nodes, 5);
        assert_eq!(ingress.work().captured_values, 1);
        assert_eq!(ingress.work().elided_capture_slots, 1);
        assert_eq!(ingress.work().lambda_conversions, 1);
        assert_eq!(ingress.work().closure_applications, 1);
        assert_eq!(ingress.work().generated_closure_types, 1);
        assert_eq!(ingress.work().generated_functions, 2);
        let lowered =
            fir::lower_to_flbc(ingress.fir()).expect("typed closure FIR lowers through validation");
        let capture_widths = lowered
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter_map(|instruction| match instruction {
                Instruction::Closure { captures, .. } => Some(captures.len()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(capture_widths, [1]);
        let bytes =
            encode_canonical(&lowered, CodecLimits::default()).expect("canonical closure FLBC");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("independent closure FLBC validation");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
            bytes
        );
        decoded
    }

    let add = intrinsic(
        "extern:Nat.add",
        vec![fir::ValueType::Nat, fir::ValueType::Nat],
        fir::ValueType::Nat,
    );
    let nat_lambda = lambda(
        "incrementFromBase",
        call(
            &["Nat", "add"],
            [
                Expr::bvar(2).expect("captured base beyond unused neighbor"),
                Expr::bvar(0).expect("lambda increment"),
            ],
        ),
    );
    let nat_source = Expr::let_e(
        Name::from_components(["base"]),
        Expr::sort(Level::zero()),
        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(40))),
        Expr::let_e(
            Name::from_components(["unused"]),
            Expr::sort(Level::zero()),
            Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(99))),
            Expr::app(
                nat_lambda.clone(),
                Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(2))),
            ),
            false,
        ),
        false,
    );
    let nat_program = compile(
        &nat_source,
        add,
        &nat_lambda,
        fir::ValueType::Nat,
        fir::ValueType::Nat,
    );

    let append = intrinsic(
        "extern:String.append",
        vec![fir::ValueType::String, fir::ValueType::String],
        fir::ValueType::String,
    );
    let string_lambda = lambda(
        "appendSuffix",
        call(
            &["String", "append"],
            [
                Expr::bvar(0).expect("lambda prefix"),
                Expr::bvar(2).expect("captured suffix beyond unused neighbor"),
            ],
        ),
    );
    let string_source = Expr::let_e(
        Name::from_components(["suffix"]),
        Expr::sort(Level::zero()),
        Expr::lit(Literal::Str("-golem".to_string())),
        Expr::let_e(
            Name::from_components(["unused"]),
            Expr::sort(Level::zero()),
            Expr::lit(Literal::Str("not-captured".to_string())),
            Expr::app(
                string_lambda.clone(),
                Expr::lit(Literal::Str("core".to_string())),
            ),
            false,
        ),
        false,
    );
    let string_program = compile(
        &string_source,
        append,
        &string_lambda,
        fir::ValueType::String,
        fir::ValueType::String,
    );

    let _guard = lock();
    shadow::enable();
    let nat = returned(execute(&nat_program, ExecutionLimits::default(), None));
    assert_eq!(nat.value.unbox(), 42);
    assert_eq!(nat.usage.peak_stack_depth, 2);
    drop(nat);
    let string = returned(execute(&string_program, ExecutionLimits::default(), None));
    assert_eq!(string_contents(&string.value), "core-golem");
    assert_eq!(string.usage.peak_stack_depth, 2);
    drop(string);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "local closure execution releases every ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "Core-to-FIR closure conversion preserves Marrow ownership"
    );
}

#[test]
fn typed_higher_order_core_closures_pass_and_return_abi_closures() {
    fn nat(value: u64) -> Expr {
        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)))
    }

    fn call(name: &[&str], arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(name.iter().copied()), Vec::new()),
            Expr::app,
        )
    }

    fn lambda(name: &str, body: Expr) -> Expr {
        Expr::lam(
            Name::from_components([name]),
            Expr::sort(Level::zero()),
            body,
            BinderInfo::Default,
        )
    }

    fn annotation(
        lambda: &Expr,
        parameter: fir::ValueType,
        result: fir::ValueType,
    ) -> ingress::LambdaBinding {
        ingress::LambdaBinding {
            lambda: lambda.clone(),
            parameters: vec![parameter],
            parameter_ownership: vec![ArgumentOwnership::Borrowed],
            result,
            result_ownership: callable_result_ownership(result),
            recursion: ingress::LambdaRecursion::NonRecursive,
        }
    }

    fn compile(
        source: &Expr,
        intrinsics: &[ingress::IntrinsicBinding],
        lambdas: &[ingress::LambdaBinding],
        expected_capture_widths: &[usize],
    ) -> ValidatedProgram {
        let ingressed = ingress::lower_closed_expr_with_lambdas(
            source,
            intrinsics,
            &[],
            &[],
            lambdas,
            ingress::IngressLimits::default(),
        )
        .expect("typed higher-order closure enters validated FIR");
        assert_eq!(ingressed.work().lambda_conversions, 2);
        assert_eq!(ingressed.work().closure_applications, 2);
        assert_eq!(ingressed.work().generated_closure_types, 2);
        assert_eq!(ingressed.work().generated_functions, 3);
        let lowered =
            fir::lower_to_flbc(ingressed.fir()).expect("higher-order FIR independently validates");
        let capture_widths = lowered
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter_map(|instruction| match instruction {
                Instruction::Closure { captures, .. } => Some(captures.len()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(capture_widths, expected_capture_widths);
        let bytes = encode_canonical(&lowered, CodecLimits::default())
            .expect("canonical higher-order FLBC");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("independent higher-order FLBC validation");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
            bytes
        );
        decoded
    }

    let nat_to_nat = fir::ValueType::Closure(fir::ClosureTypeId::new(0));
    let identity = lambda("identity", Expr::bvar(0).expect("identity parameter"));
    let apply = lambda(
        "apply",
        Expr::app(Expr::bvar(0).expect("closure parameter"), nat(41)),
    );
    let pass_program = compile(
        &Expr::app(apply.clone(), identity.clone()),
        &[],
        &[
            annotation(&apply, nat_to_nat, fir::ValueType::Nat),
            annotation(&identity, fir::ValueType::Nat, fir::ValueType::Nat),
        ],
        &[0, 0],
    );

    let generated_add = EXTERN_ROWS
        .iter()
        .find(|candidate| candidate.id == "extern:Nat.add")
        .expect("Nat.add remains in the generated contract");
    let add = ingress::IntrinsicBinding {
        name: Name::from_components(generated_add.name.split('.')),
        universe_arity: usize::try_from(generated_add.levels).expect("u32 fits usize"),
        row: generated_add.id.to_string(),
        argument_ownership: contract_argument_ownership(generated_add.id, 2),
        result_ownership: contract_result_ownership(generated_add.id),
        arguments: vec![fir::ValueType::Nat, fir::ValueType::Nat],
        result: fir::ValueType::Nat,
        effect: fir::EffectClass::Pure,
    };
    let inner = lambda(
        "delta",
        call(
            &["Nat", "add"],
            [
                Expr::bvar(1).expect("captured base"),
                Expr::bvar(0).expect("delta parameter"),
            ],
        ),
    );
    let outer = lambda("base", Expr::mdata(KVMap::new(), inner.clone()));
    let return_source = Expr::let_e(
        Name::from_components(["returnedClosure"]),
        Expr::sort(Level::zero()),
        Expr::app(outer.clone(), nat(40)),
        Expr::app(Expr::bvar(0).expect("returned closure binding"), nat(2)),
        false,
    );
    let return_program = compile(
        &return_source,
        &[add],
        &[
            annotation(&outer, fir::ValueType::Nat, nat_to_nat),
            annotation(&inner, fir::ValueType::Nat, fir::ValueType::Nat),
        ],
        &[0, 1],
    );

    let _guard = lock();
    shadow::enable();
    let passed = returned(execute(&pass_program, ExecutionLimits::default(), None));
    assert_eq!(passed.value.unbox(), 41);
    drop(passed);
    let returned_closure = returned(execute(&return_program, ExecutionLimits::default(), None));
    assert_eq!(returned_closure.value.unbox(), 42);
    drop(returned_closure);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "higher-order execution releases every ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "closure-valued parameters and results preserve Marrow ownership"
    );
}

#[test]
fn core_abi_boxing_boundaries_execute_without_a_shadow_value_domain() {
    fn nat(value: u64) -> Expr {
        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)))
    }

    fn string(value: &str) -> Expr {
        Expr::lit(Literal::Str(value.to_string()))
    }

    fn call(name: &[&str], arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(name.iter().copied()), Vec::new()),
            Expr::app,
        )
    }

    fn function_binding(
        name: &[&str],
        parameters: Vec<fir::ValueType>,
        result: fir::ValueType,
        body: Expr,
    ) -> ingress::FunctionBinding {
        let parameter_ownership = vec![ArgumentOwnership::Borrowed; parameters.len()];
        ingress::FunctionBinding {
            name: Name::from_components(name.iter().copied()),
            universe_arity: 0,
            parameters,
            parameter_ownership,
            result,
            result_ownership: callable_result_ownership(result),
            body,
        }
    }

    fn canonical_flbc(ingressed: &ingress::IngressedProgram) -> ValidatedProgram {
        let lowered =
            fir::lower_to_flbc(ingressed.fir()).expect("ABI-boundary FIR independently validates");
        let bytes = encode_canonical(&lowered, CodecLimits::default())
            .expect("canonical ABI-boundary FLBC");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("independent ABI-boundary FLBC validation");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
            bytes
        );
        decoded
    }

    let generated_add = EXTERN_ROWS
        .iter()
        .find(|candidate| candidate.id == "extern:Nat.add")
        .expect("Nat.add remains in the generated contract");
    let add = ingress::IntrinsicBinding {
        name: Name::from_components(generated_add.name.split('.')),
        universe_arity: usize::try_from(generated_add.levels).expect("u32 fits usize"),
        row: generated_add.id.to_string(),
        argument_ownership: contract_argument_ownership(generated_add.id, 2),
        result_ownership: contract_result_ownership(generated_add.id),
        arguments: vec![fir::ValueType::Nat, fir::ValueType::Nat],
        result: fir::ValueType::Nat,
        effect: fir::EffectClass::Pure,
    };
    let mut scalar_identity = function_binding(
        &["User", "abiIdentity"],
        vec![fir::ValueType::Abi],
        fir::ValueType::Abi,
        Expr::bvar(0).expect("ABI identity parameter"),
    );
    scalar_identity.result_ownership = CallableResultOwnership::Scalar;
    let recover_nat = function_binding(
        &["User", "recoverNat"],
        vec![fir::ValueType::Abi],
        fir::ValueType::Nat,
        Expr::bvar(0).expect("ABI Nat parameter"),
    );
    let mut boxed_result = function_binding(
        &["User", "boxedResult"],
        Vec::new(),
        fir::ValueType::Abi,
        nat(1),
    );
    boxed_result.result_ownership = CallableResultOwnership::Scalar;
    let holder = ingress::ConstructorBinding {
        name: Name::from_components(["User", "Holder", "mk"]),
        projection_structure: Some(Name::from_components(["User", "Holder"])),
        universe_arity: 0,
        tag: 3,
        fields: vec![fir::ValueType::Abi],
        static_scalar_bytes: Vec::new(),
    };
    let projected = Expr::proj(
        holder
            .projection_structure
            .clone()
            .expect("holder projection structure"),
        0,
        call(&["User", "Holder", "mk"], [nat(21)]),
    );
    let numeric_source = call(
        &["Nat", "add"],
        [
            call(
                &["User", "recoverNat"],
                [call(&["User", "abiIdentity"], [nat(20)])],
            ),
            call(
                &["Nat", "add"],
                [projected, call(&["User", "boxedResult"], [])],
            ),
        ],
    );
    let numeric = ingress::lower_closed_expr_with_catalogs(
        &numeric_source,
        std::slice::from_ref(&add),
        std::slice::from_ref(&holder),
        &[recover_nat, scalar_identity.clone(), boxed_result],
        ingress::IngressLimits::default(),
    )
    .expect("numeric ABI-boundary Core enters validated FIR");
    assert_eq!(numeric.fir().schema_version(), fir::FIR_SCHEMA_VERSION);
    assert_eq!(
        numeric.fir().canonical_text().matches(" = box v").count(),
        3
    );
    assert_eq!(
        numeric
            .fir()
            .canonical_text()
            .matches(" = unbox nat v")
            .count(),
        3
    );
    assert_eq!(
        numeric
            .fir()
            .canonical_text()
            .matches("result=abi result_ownership=scalar")
            .count(),
        2,
        "ABI callables select the scalar result class explicitly"
    );
    let numeric_program = canonical_flbc(&numeric);
    assert_eq!(
        numeric_program
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter(|instruction| matches!(instruction, Instruction::Copy { .. }))
            .count(),
        6
    );

    let recover_string = function_binding(
        &["User", "recoverString"],
        vec![fir::ValueType::Abi],
        fir::ValueType::String,
        Expr::bvar(0).expect("ABI String parameter"),
    );
    let mut owned_identity = scalar_identity;
    owned_identity.result_ownership = CallableResultOwnership::Owned;
    let string_source = call(
        &["User", "recoverString"],
        [call(&["User", "abiIdentity"], [string("boxed-string")])],
    );
    let string_ingress = ingress::lower_closed_expr_with_catalogs(
        &string_source,
        &[],
        &[],
        &[owned_identity, recover_string],
        ingress::IngressLimits::default(),
    )
    .expect("heap ABI-boundary Core enters validated FIR");
    assert_eq!(
        string_ingress
            .fir()
            .canonical_text()
            .matches("result=abi result_ownership=owned")
            .count(),
        1,
        "the same ABI shape can independently select the owned result class"
    );
    let string_program = canonical_flbc(&string_ingress);
    assert_eq!(
        string_program
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter(|instruction| matches!(instruction, Instruction::Copy { .. }))
            .count(),
        2
    );

    let lambda = Expr::lam(
        Name::from_components(["abiArgument"]),
        Expr::sort(Level::zero()),
        Expr::bvar(0).expect("ABI lambda parameter"),
        BinderInfo::Default,
    );
    let lambda_ingress = ingress::lower_closed_expr_with_lambdas(
        &Expr::app(lambda.clone(), nat(42)),
        &[],
        &[],
        &[],
        &[ingress::LambdaBinding {
            lambda,
            parameters: vec![fir::ValueType::Abi],
            parameter_ownership: vec![ArgumentOwnership::Borrowed],
            result: fir::ValueType::Nat,
            result_ownership: CallableResultOwnership::Scalar,
            recursion: ingress::LambdaRecursion::NonRecursive,
        }],
        ingress::IngressLimits::default(),
    )
    .expect("closure ABI-boundary Core enters validated FIR");
    let lambda_program = canonical_flbc(&lambda_ingress);
    assert_eq!(
        lambda_program
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter(|instruction| matches!(instruction, Instruction::Copy { .. }))
            .count(),
        2
    );

    let _guard = lock();
    shadow::enable();
    let numeric_result = returned(execute(&numeric_program, ExecutionLimits::default(), None));
    assert_eq!(numeric_result.value.unbox(), 42);
    drop(numeric_result);
    let string_result = returned(execute(&string_program, ExecutionLimits::default(), None));
    assert_eq!(string_contents(&string_result.value), "boxed-string");
    drop(string_result);
    let lambda_result = returned(execute(&lambda_program, ExecutionLimits::default(), None));
    assert_eq!(lambda_result.value.unbox(), 42);
    drop(lambda_result);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "scalar, heap, and closure ABI boundaries release every Marrow object"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "boxing and unboxing preserve the single Marrow ownership domain"
    );
}

#[test]
fn typed_core_partial_and_overapplication_execute_on_golem_and_marrow() {
    fn nat(value: u64) -> Expr {
        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)))
    }

    fn call(name: &[&str], arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(name.iter().copied()), Vec::new()),
            Expr::app,
        )
    }

    fn lambda(name: &str, body: Expr) -> Expr {
        Expr::lam(
            Name::from_components([name]),
            Expr::sort(Level::zero()),
            body,
            BinderInfo::Default,
        )
    }

    fn annotation(
        lambda: &Expr,
        parameters: Vec<fir::ValueType>,
        result: fir::ValueType,
    ) -> ingress::LambdaBinding {
        ingress::LambdaBinding {
            lambda: lambda.clone(),
            parameter_ownership: vec![ArgumentOwnership::Borrowed; parameters.len()],
            parameters,
            result,
            result_ownership: callable_result_ownership(result),
            recursion: ingress::LambdaRecursion::NonRecursive,
        }
    }

    fn compile(
        source: &Expr,
        intrinsic: &ingress::IntrinsicBinding,
        lambdas: &[ingress::LambdaBinding],
        expected_closure_types: usize,
        expected_apply_widths: &[usize],
        expected_capture_widths: &[usize],
    ) -> ValidatedProgram {
        let ingressed = ingress::lower_closed_expr_with_lambdas(
            source,
            std::slice::from_ref(intrinsic),
            &[],
            &[],
            lambdas,
            ingress::IngressLimits::default(),
        )
        .expect("typed application chain enters validated FIR");
        assert_eq!(ingressed.fir().schema_version(), fir::FIR_SCHEMA_VERSION);
        assert_eq!(
            ingressed.work().generated_closure_types,
            expected_closure_types
        );
        let lowered = fir::lower_to_flbc(ingressed.fir()).expect("application-chain FIR validates");
        let apply_widths = lowered
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter_map(|instruction| match instruction {
                Instruction::Apply { args, .. } => Some(args.len()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(apply_widths, expected_apply_widths);
        let capture_widths = lowered
            .functions()
            .iter()
            .flat_map(|function| &function.code)
            .filter_map(|instruction| match instruction {
                Instruction::Closure { captures, .. } => Some(captures.len()),
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(capture_widths, expected_capture_widths);
        let bytes = encode_canonical(&lowered, CodecLimits::default())
            .expect("canonical application-chain FLBC");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("independent application-chain FLBC validation");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
            bytes
        );
        decoded
    }

    let generated_add = EXTERN_ROWS
        .iter()
        .find(|candidate| candidate.id == "extern:Nat.add")
        .expect("Nat.add remains in the generated contract");
    let add = ingress::IntrinsicBinding {
        name: Name::from_components(generated_add.name.split('.')),
        universe_arity: usize::try_from(generated_add.levels).expect("u32 fits usize"),
        row: generated_add.id.to_string(),
        argument_ownership: contract_argument_ownership(generated_add.id, 2),
        result_ownership: contract_result_ownership(generated_add.id),
        arguments: vec![fir::ValueType::Nat, fir::ValueType::Nat],
        result: fir::ValueType::Nat,
        effect: fir::EffectClass::Pure,
    };

    let add_pair = lambda(
        "left",
        lambda(
            "right",
            call(
                &["Nat", "add"],
                [
                    Expr::bvar(1).expect("left parameter"),
                    Expr::bvar(0).expect("right parameter"),
                ],
            ),
        ),
    );
    let partial_source = Expr::let_e(
        Name::from_components(["partial"]),
        Expr::sort(Level::zero()),
        Expr::app(add_pair.clone(), nat(20)),
        Expr::app(Expr::bvar(0).expect("partial closure"), nat(22)),
        false,
    );
    let partial_program = compile(
        &partial_source,
        &add,
        &[annotation(
            &add_pair,
            vec![fir::ValueType::Nat, fir::ValueType::Nat],
            fir::ValueType::Nat,
        )],
        2,
        &[1, 1],
        &[0],
    );

    let inner = lambda(
        "rhs",
        call(
            &["Nat", "add"],
            [
                Expr::bvar(1).expect("captured lhs"),
                Expr::bvar(0).expect("rhs parameter"),
            ],
        ),
    );
    let outer = lambda("lhs", Expr::mdata(KVMap::new(), inner.clone()));
    let nat_to_nat = fir::ValueType::Closure(fir::ClosureTypeId::new(0));
    let over_program = compile(
        &Expr::app(Expr::app(outer.clone(), nat(20)), nat(22)),
        &add,
        &[
            annotation(&outer, vec![fir::ValueType::Nat], nat_to_nat),
            annotation(&inner, vec![fir::ValueType::Nat], fir::ValueType::Nat),
        ],
        2,
        &[2],
        &[0, 1],
    );

    let _guard = lock();
    shadow::enable();
    let partial = returned(execute(&partial_program, ExecutionLimits::default(), None));
    assert_eq!(partial.value.unbox(), 42);
    drop(partial);
    let over = returned(execute(&over_program, ExecutionLimits::default(), None));
    assert_eq!(over.value.unbox(), 42);
    drop(over);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "typed application chains release every ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "partial and closure-result overapplication preserve Marrow ownership"
    );
}

#[test]
fn self_recursive_core_closures_return_acyclic_environments_and_stop_typed() {
    fn nat(value: u64) -> Expr {
        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)))
    }

    fn lambda(name: &str, body: Expr) -> Expr {
        Expr::lam(
            Name::from_components([name]),
            Expr::sort(Level::zero()),
            body,
            BinderInfo::Default,
        )
    }

    fn recursive_binding(
        lambda: &Expr,
        parameters: Vec<fir::ValueType>,
        result: fir::ValueType,
    ) -> ingress::LambdaBinding {
        ingress::LambdaBinding {
            lambda: lambda.clone(),
            parameter_ownership: vec![ArgumentOwnership::Borrowed; parameters.len()],
            parameters,
            result,
            result_ownership: callable_result_ownership(result),
            recursion: ingress::LambdaRecursion::SelfBinder,
        }
    }

    fn compile(source: &Expr, binding: ingress::LambdaBinding) -> ValidatedProgram {
        let ingressed = ingress::lower_closed_expr_with_lambdas(
            source,
            &[],
            &[],
            &[],
            &[binding],
            ingress::IngressLimits::default(),
        )
        .expect("self-recursive Core expression enters validated FIR");
        assert_eq!(ingressed.work().recursive_self_closures, 1);
        let lowered =
            fir::lower_to_flbc(ingressed.fir()).expect("self-recursive FIR validates as FLBC");
        let bytes = encode_canonical(&lowered, CodecLimits::default())
            .expect("canonical self-recursive FLBC");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("independent self-recursive FLBC validation");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
            bytes
        );
        decoded
    }

    let self_type = fir::ValueType::Closure(fir::ClosureTypeId::new(0));
    let returning_self = lambda(
        "self",
        lambda(
            "argument",
            Expr::let_e(
                Name::from_components(["observedCapture"]),
                Expr::sort(Level::zero()),
                Expr::bvar(2).expect("captured string outside self and argument"),
                Expr::let_e(
                    Name::from_components(["selfAlias"]),
                    Expr::sort(Level::zero()),
                    Expr::bvar(2).expect("self under the local capture observation"),
                    Expr::bvar(0).expect("aliased recursive self"),
                    false,
                ),
                false,
            ),
        ),
    );
    let captured_chain = Expr::let_e(
        Name::from_components(["captured"]),
        Expr::sort(Level::zero()),
        Expr::lit(Literal::Str("cycle-free".to_string())),
        Expr::app(Expr::app(returning_self.clone(), nat(0)), nat(1)),
        false,
    );
    let returned_program = compile(
        &captured_chain,
        recursive_binding(&returning_self, vec![fir::ValueType::Nat], self_type),
    );

    let partially_applying_self = lambda(
        "self",
        lambda(
            "left",
            lambda(
                "right",
                Expr::app(
                    Expr::bvar(2).expect("recursive self closure"),
                    Expr::bvar(1).expect("first recursive argument"),
                ),
            ),
        ),
    );
    let partial_program = compile(
        &Expr::app(Expr::app(partially_applying_self.clone(), nat(7)), nat(8)),
        recursive_binding(
            &partially_applying_self,
            vec![fir::ValueType::Nat, fir::ValueType::Nat],
            fir::ValueType::Closure(fir::ClosureTypeId::new(0)),
        ),
    );

    let looping = lambda(
        "self",
        lambda(
            "argument",
            Expr::app(
                Expr::bvar(1).expect("recursive self closure"),
                Expr::bvar(0).expect("recursive argument"),
            ),
        ),
    );
    let looping_program = compile(
        &Expr::app(looping.clone(), nat(0)),
        recursive_binding(&looping, vec![fir::ValueType::Nat], fir::ValueType::Nat),
    );

    let _guard = lock();
    shadow::enable();
    let completed = returned(execute(&returned_program, ExecutionLimits::default(), None));
    assert_eq!(value_kind(&completed.value), ValueKind::Closure);
    let (arity, fixed) = completed
        .value
        .closure_shell_parts()
        .expect("returned recursive closure remains a Golem shell");
    assert_eq!(arity, 3, "one capture plus one argument and target word");
    assert_eq!(fixed.len(), 2);
    assert_eq!(fixed[0].unbox(), 1, "the target word names function 1");
    assert_eq!(string_contents(&fixed[1]), "cycle-free");
    drop(fixed);
    drop(completed);

    let partial = returned(execute(&partial_program, ExecutionLimits::default(), None));
    let (arity, fixed) = partial
        .value
        .closure_shell_parts()
        .expect("recursive underapplication returns an ordinary Golem shell");
    assert_eq!(arity, 3);
    assert_eq!(fixed.len(), 2);
    assert_eq!(fixed[0].unbox(), 1, "the target word names function 1");
    assert_eq!(
        fixed[1].unbox(),
        7,
        "the recursive self closure retains the first argument"
    );
    drop(fixed);
    drop(partial);

    let stopped = execute(
        &looping_program,
        ExecutionLimits {
            max_steps: 100,
            max_stack_depth: 3,
        },
        None,
    );
    match stopped {
        Outcome::Inconclusive(inconclusive) => match inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                assert!(usage.is_genuine_exhaustion());
                assert_eq!(usage.allowed, 3);
                assert_eq!(usage.observed, 4);
                assert_eq!(usage.reason, ResourceReason::RecursionDepth { limit: 3 });
            }
            other => panic!("expected recursive depth exhaustion, got {other:?}"),
        },
        other => panic!("expected recursive Inconclusive, got {other:?}"),
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "returned and exhausted recursive closures release every ABI object"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "acyclic recursive environments preserve Marrow ownership"
    );
}

#[test]
fn mutual_recursive_core_closures_return_peers_and_stop_typed_without_cycles() {
    fn nat(value: u64) -> Expr {
        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(value)))
    }

    fn string(value: &str) -> Expr {
        Expr::lit(Literal::Str(value.to_string()))
    }

    fn lambda(name: &str, body: Expr) -> Expr {
        Expr::lam(
            Name::from_components([name]),
            Expr::sort(Level::zero()),
            body,
            BinderInfo::Default,
        )
    }

    fn member_binding(
        lambda: &Expr,
        parameters: Vec<fir::ValueType>,
        result: fir::ValueType,
        member: u16,
    ) -> ingress::LambdaBinding {
        ingress::LambdaBinding {
            lambda: lambda.clone(),
            parameter_ownership: vec![ArgumentOwnership::Borrowed; parameters.len()],
            parameters,
            result,
            result_ownership: callable_result_ownership(result),
            recursion: ingress::LambdaRecursion::MutualMember {
                group: 31,
                member,
                members: 2,
            },
        }
    }

    fn compile(source: &Expr, bindings: &[ingress::LambdaBinding]) -> ValidatedProgram {
        let ingressed = ingress::lower_closed_expr_with_lambdas(
            source,
            &[],
            &[],
            &[],
            bindings,
            ingress::IngressLimits::default(),
        )
        .expect("mutual recursive Core expression enters validated FIR");
        assert_eq!(ingressed.work().recursive_self_closures, 0);
        assert_eq!(ingressed.work().mutual_group_closures, 4);
        let lowered =
            fir::lower_to_flbc(ingressed.fir()).expect("mutual recursive FIR validates as FLBC");
        let bytes = encode_canonical(&lowered, CodecLimits::default())
            .expect("canonical mutual recursive FLBC");
        let decoded = decode_canonical(&bytes, CodecLimits::default())
            .expect("independent mutual recursive FLBC validation");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
            bytes
        );
        decoded
    }

    let first = lambda(
        "first",
        lambda(
            "second",
            lambda(
                "argument",
                Expr::let_e(
                    Name::from_components(["peerAlias"]),
                    Expr::sort(Level::zero()),
                    Expr::bvar(1).expect("second mutual member"),
                    Expr::bvar(0).expect("aliased second member"),
                    false,
                ),
            ),
        ),
    );
    let second = lambda(
        "first",
        lambda(
            "second",
            lambda(
                "text",
                Expr::bvar(3).expect("captured string outside the mutual group"),
            ),
        ),
    );
    let peer_bindings = [
        member_binding(
            &first,
            vec![fir::ValueType::Nat],
            fir::ValueType::Closure(fir::ClosureTypeId::new(1)),
            0,
        ),
        member_binding(
            &second,
            vec![fir::ValueType::String],
            fir::ValueType::String,
            1,
        ),
    ];
    let returned_peer_source = Expr::let_e(
        Name::from_components(["captured"]),
        Expr::sort(Level::zero()),
        string("mutual-capture"),
        Expr::app(first.clone(), nat(0)),
        false,
    );
    let returned_peer_program = compile(&returned_peer_source, &peer_bindings);
    let completed_peer_source = Expr::let_e(
        Name::from_components(["captured"]),
        Expr::sort(Level::zero()),
        string("mutual-capture"),
        Expr::app(Expr::app(first.clone(), nat(0)), string("ignored-argument")),
        false,
    );
    let completed_peer_program = compile(&completed_peer_source, &peer_bindings);

    let looping_first = lambda(
        "first",
        lambda(
            "second",
            lambda(
                "argument",
                Expr::app(
                    Expr::bvar(1).expect("second mutual member"),
                    Expr::bvar(0).expect("recursive argument"),
                ),
            ),
        ),
    );
    let looping_second = lambda(
        "first",
        lambda(
            "second",
            lambda(
                "argument",
                Expr::app(
                    Expr::bvar(2).expect("first mutual member"),
                    Expr::bvar(0).expect("recursive argument"),
                ),
            ),
        ),
    );
    let looping_bindings = [
        member_binding(
            &looping_first,
            vec![fir::ValueType::Nat],
            fir::ValueType::Nat,
            0,
        ),
        member_binding(
            &looping_second,
            vec![fir::ValueType::Nat],
            fir::ValueType::Nat,
            1,
        ),
    ];
    let looping_program = compile(&Expr::app(looping_first.clone(), nat(0)), &looping_bindings);

    let _guard = lock();
    shadow::enable();
    let returned_peer = returned(execute(
        &returned_peer_program,
        ExecutionLimits::default(),
        None,
    ));
    assert_eq!(value_kind(&returned_peer.value), ValueKind::Closure);
    let (arity, fixed) = returned_peer
        .value
        .closure_shell_parts()
        .expect("returned mutual peer remains a Golem shell");
    assert_eq!(arity, 3, "one capture plus one argument and target word");
    assert_eq!(fixed.len(), 2);
    assert_eq!(fixed[0].unbox(), 2, "the target word names peer function 2");
    assert_eq!(string_contents(&fixed[1]), "mutual-capture");
    drop(fixed);
    drop(returned_peer);

    let completed_peer = returned(execute(
        &completed_peer_program,
        ExecutionLimits::default(),
        None,
    ));
    assert_eq!(string_contents(&completed_peer.value), "mutual-capture");
    drop(completed_peer);

    let stopped = execute(
        &looping_program,
        ExecutionLimits {
            max_steps: 100,
            max_stack_depth: 3,
        },
        None,
    );
    match stopped {
        Outcome::Inconclusive(inconclusive) => match inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                assert!(usage.is_genuine_exhaustion());
                assert_eq!(usage.allowed, 3);
                assert_eq!(usage.observed, 4);
                assert_eq!(usage.reason, ResourceReason::RecursionDepth { limit: 3 });
            }
            other => panic!("expected mutual recursion depth exhaustion, got {other:?}"),
        },
        other => panic!("expected mutual recursion Inconclusive, got {other:?}"),
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "returned, completed and exhausted mutual groups release every ABI object"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "acyclic mutual closure groups preserve Marrow ownership"
    );
}

#[test]
fn effectful_core_closures_drive_thunks_and_managerless_tasks() {
    fn generated(id: &str) -> &'static fln_vm::extern_table_generated::GeneratedExternRow {
        EXTERN_ROWS
            .iter()
            .find(|candidate| candidate.id == id)
            .unwrap_or_else(|| panic!("{id} remains in the generated extern contract"))
    }

    fn effect(token: &str) -> fir::EffectClass {
        match token {
            "pure" => fir::EffectClass::Pure,
            "state" => fir::EffectClass::State,
            "io" => fir::EffectClass::Io,
            "task" => fir::EffectClass::Task,
            other => panic!("unsupported bounded FIR effect class {other}"),
        }
    }

    fn binding(
        id: &str,
        arguments: Vec<fir::ValueType>,
        result: fir::ValueType,
    ) -> ingress::IntrinsicBinding {
        let row = generated(id);
        let term_arity = row
            .arity
            .checked_sub(row.levels)
            .and_then(|arity| usize::try_from(arity).ok())
            .expect("generated term arity fits usize");
        assert_eq!(
            arguments.len(),
            term_arity,
            "{id} binding covers every explicit term argument"
        );
        ingress::IntrinsicBinding {
            name: Name::from_components(row.name.split('.')),
            universe_arity: usize::try_from(row.levels).expect("u32 fits usize"),
            row: row.id.to_string(),
            argument_ownership: contract_argument_ownership(row.id, arguments.len()),
            result_ownership: contract_result_ownership(row.id),
            arguments,
            result,
            effect: effect(row.effect),
        }
    }

    fn call(id: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
        let row = generated(id);
        let levels = (0..row.levels).map(|_| Level::zero()).collect();
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(row.name.split('.')), levels),
            Expr::app,
        )
    }

    fn lambda(name: &str, value: &str) -> Expr {
        Expr::lam(
            Name::from_components([name]),
            Expr::sort(Level::zero()),
            Expr::lit(Literal::Str(value.to_string())),
            BinderInfo::Default,
        )
    }

    let delayed = lambda("thunkUnit", "delayed-");
    let spawned = lambda("taskUnit", "task");
    let closure_type = fir::ValueType::Closure(fir::ClosureTypeId::new(0));
    let catalog = vec![
        binding("extern:Thunk.mk", vec![closure_type], fir::ValueType::Thunk),
        binding(
            "extern:Thunk.get",
            vec![fir::ValueType::Thunk],
            fir::ValueType::String,
        ),
        binding(
            "extern:Task.spawn",
            vec![closure_type, fir::ValueType::Nat],
            fir::ValueType::Task,
        ),
        binding(
            "extern:Task.get",
            vec![fir::ValueType::Task],
            fir::ValueType::String,
        ),
        binding(
            "extern:String.append",
            vec![fir::ValueType::String, fir::ValueType::String],
            fir::ValueType::String,
        ),
    ];
    assert_eq!(
        catalog
            .iter()
            .find(|binding| binding.row == "extern:Task.spawn")
            .map(|binding| binding.effect),
        Some(fir::EffectClass::Task)
    );

    let source = Expr::let_e(
        Name::from_components(["delayed"]),
        Expr::sort(Level::zero()),
        call("extern:Thunk.mk", [delayed.clone()]),
        Expr::let_e(
            Name::from_components(["delayedValue"]),
            Expr::sort(Level::zero()),
            call(
                "extern:Thunk.get",
                [Expr::bvar(0).expect("delayed thunk binding")],
            ),
            Expr::let_e(
                Name::from_components(["spawned"]),
                Expr::sort(Level::zero()),
                call(
                    "extern:Task.spawn",
                    [
                        spawned.clone(),
                        Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(0))),
                    ],
                ),
                Expr::let_e(
                    Name::from_components(["taskValue"]),
                    Expr::sort(Level::zero()),
                    call(
                        "extern:Task.get",
                        [Expr::bvar(0).expect("spawned task binding")],
                    ),
                    call(
                        "extern:String.append",
                        [
                            Expr::bvar(2).expect("forced thunk result"),
                            Expr::bvar(0).expect("joined task result"),
                        ],
                    ),
                    false,
                ),
                false,
            ),
            false,
        ),
        false,
    );
    let lambdas = vec![
        ingress::LambdaBinding {
            lambda: delayed,
            parameters: vec![fir::ValueType::Unit],
            parameter_ownership: vec![ArgumentOwnership::Scalar],
            result: fir::ValueType::String,
            result_ownership: CallableResultOwnership::Owned,
            recursion: ingress::LambdaRecursion::NonRecursive,
        },
        ingress::LambdaBinding {
            lambda: spawned,
            parameters: vec![fir::ValueType::Unit],
            parameter_ownership: vec![ArgumentOwnership::Scalar],
            result: fir::ValueType::String,
            result_ownership: CallableResultOwnership::Owned,
            recursion: ingress::LambdaRecursion::NonRecursive,
        },
    ];
    let compile = |intrinsics: &[ingress::IntrinsicBinding]| {
        let ingressed = ingress::lower_closed_expr_with_lambdas(
            &source,
            intrinsics,
            &[],
            &[],
            &lambdas,
            ingress::IngressLimits::default(),
        )
        .expect("effectful closures enter validated FIR");
        assert_eq!(ingressed.work().intrinsic_calls, 5);
        assert_eq!(ingressed.work().lambda_conversions, 2);
        assert_eq!(ingressed.work().generated_closure_types, 1);
        assert_eq!(
            ingressed.fir().closure_types()[0]
                .parameter_ownership
                .as_slice(),
            &[ArgumentOwnership::Scalar],
            "the explicit hidden-Unit contract survives Core ingress"
        );
        assert!(ingressed.fir().canonical_text().contains("effect=task"));
        let lowered =
            fir::lower_to_flbc(ingressed.fir()).expect("effectful FIR lowers to checked FLBC");
        let bytes =
            encode_canonical(&lowered, CodecLimits::default()).expect("canonical effectful FLBC");
        let decoded =
            decode_canonical(&bytes, CodecLimits::default()).expect("independent FLBC validation");
        assert_eq!(
            encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
            bytes
        );
        (
            ingressed.source_expr_hash(),
            ingressed.work(),
            ingressed.fir().canonical_text(),
            bytes,
            decoded,
        )
    };
    let canonical = compile(&catalog);
    let mut reversed = catalog;
    reversed.reverse();
    let reordered = compile(&reversed);
    assert_eq!(
        (&canonical.0, canonical.1, &canonical.2, &canonical.3),
        (&reordered.0, reordered.1, &reordered.2, &reordered.3),
        "intrinsic catalog input order cannot change effectful FIR or FLBC identity"
    );

    let _guard = lock();
    shadow::enable();
    let completed = returned(execute(&canonical.4, ExecutionLimits::default(), None));
    assert_eq!(string_contents(&completed.value), "delayed-task");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "effectful closure execution drains every ABI object"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "Thunk and Task continuations preserve Marrow ownership"
    );
}

#[test]
fn typed_core_constructors_execute_through_canonical_flbc_and_marrow() {
    fn call(name: &[&str], arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(name.iter().copied()), Vec::new()),
            Expr::app,
        )
    }

    let constructor = ingress::ConstructorBinding {
        name: Name::from_components(["User", "Pair", "mk"]),
        projection_structure: None,
        universe_arity: 0,
        tag: 11,
        fields: vec![fir::ValueType::Nat, fir::ValueType::String],
        static_scalar_bytes: vec![0x5A],
    };
    let source = call(
        &["User", "Pair", "mk"],
        [
            Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(42))),
            Expr::lit(Literal::Str("answer".to_string())),
        ],
    );
    let ingress = ingress::lower_closed_expr_with_catalogs(
        &source,
        &[],
        &[constructor],
        &[],
        ingress::IngressLimits::default(),
    )
    .expect("typed constructor enters validated FIR");
    assert_eq!(ingress.work().constructor_calls, 1);
    assert_eq!(ingress.work().generated_constructors, 1);
    assert_eq!(ingress.work().generated_values, 3);
    assert!(
        ingress
            .fir()
            .canonical_text()
            .contains("v2:ctor = ctor c0 fields=[v0,v1]")
    );

    let lowered =
        fir::lower_to_flbc(ingress.fir()).expect("constructor FIR lowers through validation");
    let bytes =
        encode_canonical(&lowered, CodecLimits::default()).expect("canonical constructor FLBC");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("independent constructor FLBC validation");
    assert_eq!(
        encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
        bytes
    );

    let _guard = lock();
    shadow::enable();
    let completed = returned(execute(&decoded, ExecutionLimits::default(), None));
    assert_eq!(value_kind(&completed.value), ValueKind::Ctor(11));
    assert_eq!(completed.value.ctor_child(0).unbox(), 42);
    assert_eq!(string_contents(&completed.value.ctor_child(1)), "answer");
    assert_eq!(completed.usage.peak_stack_depth, 1);
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "constructor execution releases every ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "Core-to-FIR constructors preserve Marrow ownership"
    );
}

#[test]
fn typed_core_projections_execute_nat_and_string_fields_with_balanced_ownership() {
    fn call(name: &[&str], arguments: impl IntoIterator<Item = Expr>) -> Expr {
        arguments.into_iter().fold(
            Expr::const_(Name::from_components(name.iter().copied()), Vec::new()),
            Expr::app,
        )
    }

    let pair_structure = Name::from_components(["User", "Pair"]);
    let pair = ingress::ConstructorBinding {
        name: Name::from_components(["User", "Pair", "mk"]),
        projection_structure: Some(pair_structure.clone()),
        universe_arity: 0,
        tag: 11,
        fields: vec![fir::ValueType::Nat, fir::ValueType::String],
        static_scalar_bytes: vec![0x5A],
    };
    let observed = ingress::ConstructorBinding {
        name: Name::from_components(["User", "Observed", "mk"]),
        projection_structure: None,
        universe_arity: 0,
        tag: 12,
        fields: vec![fir::ValueType::Nat, fir::ValueType::String],
        static_scalar_bytes: Vec::new(),
    };
    let pair_value = call(
        &["User", "Pair", "mk"],
        [
            Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(42))),
            Expr::lit(Literal::Str("answer".to_string())),
        ],
    );
    let source = Expr::let_e(
        Name::from_components(["pair"]),
        Expr::sort(Level::zero()),
        pair_value,
        call(
            &["User", "Observed", "mk"],
            [
                Expr::proj(
                    pair_structure.clone(),
                    0,
                    Expr::bvar(0).expect("small de Bruijn index"),
                ),
                Expr::proj(
                    pair_structure,
                    1,
                    Expr::bvar(0).expect("small de Bruijn index"),
                ),
            ],
        ),
        false,
    );
    let ingress = ingress::lower_closed_expr_with_catalogs(
        &source,
        &[],
        &[pair, observed],
        &[],
        ingress::IngressLimits::default(),
    )
    .expect("typed projections enter validated FIR");
    assert_eq!(ingress.work().constructor_calls, 2);
    assert_eq!(ingress.work().projection_calls, 2);
    assert_eq!(ingress.work().generated_projections, 2);
    assert!(
        ingress
            .fir()
            .canonical_text()
            .contains("projection p1 constructor=c1 field=1")
    );

    let lowered =
        fir::lower_to_flbc(ingress.fir()).expect("projection FIR lowers through validation");
    let bytes =
        encode_canonical(&lowered, CodecLimits::default()).expect("canonical projection FLBC");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("independent projection FLBC validation");
    assert_eq!(
        encode_canonical(&decoded, CodecLimits::default()).expect("canonical re-encoding"),
        bytes
    );

    let _guard = lock();
    shadow::enable();
    let completed = returned(execute(&decoded, ExecutionLimits::default(), None));
    assert_eq!(value_kind(&completed.value), ValueKind::Ctor(12));
    assert_eq!(completed.value.ctor_child(0).unbox(), 42);
    assert_eq!(string_contents(&completed.value.ctor_child(1)), "answer");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "projection execution releases every ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "checked projections preserve Marrow ownership"
    );
}

#[test]
fn abi_values_cross_direct_calls_and_intrinsics_without_a_shadow_value_domain() {
    let _guard = lock();
    let program = validated(vec![
        function(
            0,
            0,
            8,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 20,
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 22,
                },
                intrinsic(r(2), "extern:Nat.add", vec![r(0), r(1)]),
                Instruction::String {
                    dst: r(3),
                    value: "answer=".to_string(),
                },
                Instruction::String {
                    dst: r(4),
                    value: "42".to_string(),
                },
                Instruction::Call {
                    dst: r(5),
                    function: fid(1),
                    args: vec![r(3), r(4)],
                    argument_ownership: vec![
                        ArgumentOwnership::Borrowed,
                        ArgumentOwnership::Borrowed,
                    ],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Array {
                    dst: r(6),
                    items: vec![r(2), r(5)],
                },
                intrinsic(r(7), "extern:Array.size", vec![r(6)]),
                Instruction::Return { src: r(6) },
            ],
        ),
        function(
            1,
            2,
            3,
            vec![
                intrinsic(r(2), "extern:String.append", vec![r(0), r(1)]),
                Instruction::Return { src: r(2) },
            ],
        ),
    ]);

    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(completed.usage.steps, 11);
    assert_eq!(completed.usage.peak_stack_depth, 2);
    assert_eq!(value_kind(&completed.value), ValueKind::Array);
    assert_eq!(completed.value.obj_tag(), usize::from(abi::TAG_ARRAY));
    assert_eq!(completed.value.array_view(), (2, 2));

    let nat = completed.value.array_child(0);
    assert!(nat.is_scalar());
    assert_eq!(nat.unbox(), 42);
    let text = completed.value.array_child(1);
    assert_eq!(string_contents(&text), "answer=42");
}

#[test]
fn closures_capture_abi_values_and_exact_application_uses_the_same_objects() {
    let _guard = lock();
    let program = validated(vec![
        function(
            0,
            0,
            4,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 40,
                },
                Instruction::Closure {
                    dst: r(1),
                    function: fid(1),
                    captures: vec![r(0)],
                    capture_ownership: vec![ArgumentOwnership::Borrowed],
                },
                Instruction::Nat {
                    dst: r(2),
                    value: 2,
                },
                Instruction::Apply {
                    dst: r(3),
                    closure: r(1),
                    args: vec![r(2)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Scalar,
                },
                Instruction::Return { src: r(3) },
            ],
        ),
        function(
            1,
            2,
            3,
            vec![
                intrinsic(r(2), "extern:Nat.add", vec![r(0), r(1)]),
                Instruction::Return { src: r(2) },
            ],
        ),
    ]);

    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(completed.value.unbox(), 42);
    assert_eq!(completed.usage.steps, 7);
    assert_eq!(completed.usage.peak_stack_depth, 2);
}

#[test]
fn under_application_returns_a_real_marrow_closure_shell() {
    let _guard = lock();
    let program = validated(vec![
        function(
            0,
            0,
            4,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 10,
                },
                Instruction::Closure {
                    dst: r(1),
                    function: fid(1),
                    captures: vec![r(0)],
                    capture_ownership: vec![ArgumentOwnership::Borrowed],
                },
                Instruction::Nat {
                    dst: r(2),
                    value: 20,
                },
                Instruction::Apply {
                    dst: r(3),
                    closure: r(1),
                    args: vec![r(2)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(3) },
            ],
        ),
        function(1, 3, 3, vec![Instruction::Return { src: r(0) }]),
    ]);

    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(value_kind(&completed.value), ValueKind::Closure);
    assert_eq!(completed.value.obj_tag(), usize::from(abi::TAG_CLOSURE));
    assert_eq!(
        completed.value.closure_view(),
        (4, 3),
        "the target word and two fixed ABI values leave one argument open"
    );
    let (arity, fixed) = completed
        .value
        .closure_shell_parts()
        .expect("FLBC under-application retains the shell representation");
    assert_eq!(arity, 4);
    assert_eq!(fixed.len(), 3);
    assert_eq!(fixed[0].unbox(), 1, "the private word names function 1");
    assert_eq!(fixed[1].unbox(), 10);
    assert_eq!(fixed[2].unbox(), 20);
}

#[test]
fn repeated_and_over_application_preserve_argument_order() {
    let _guard = lock();
    let repeated = validated(vec![
        function(
            0,
            0,
            6,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 10,
                },
                Instruction::Closure {
                    dst: r(1),
                    function: fid(1),
                    captures: vec![r(0)],
                    capture_ownership: vec![ArgumentOwnership::Borrowed],
                },
                Instruction::Nat {
                    dst: r(2),
                    value: 20,
                },
                Instruction::Apply {
                    dst: r(3),
                    closure: r(1),
                    args: vec![r(2)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Nat {
                    dst: r(4),
                    value: 12,
                },
                Instruction::Apply {
                    dst: r(5),
                    closure: r(3),
                    args: vec![r(4)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Scalar,
                },
                Instruction::Return { src: r(5) },
            ],
        ),
        function(
            1,
            3,
            5,
            vec![
                intrinsic(r(3), "extern:Nat.add", vec![r(0), r(1)]),
                intrinsic(r(4), "extern:Nat.add", vec![r(3), r(2)]),
                Instruction::Return { src: r(4) },
            ],
        ),
    ]);
    let completed = returned(execute(&repeated, ExecutionLimits::default(), None));
    assert_eq!(completed.value.unbox(), 42);
    assert_eq!(completed.usage.steps, 10);

    let over_applied = validated(vec![
        function(
            0,
            0,
            4,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 20,
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 22,
                },
                Instruction::Closure {
                    dst: r(2),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Apply {
                    dst: r(3),
                    closure: r(2),
                    args: vec![r(0), r(1)],
                    argument_ownership: vec![
                        ArgumentOwnership::Borrowed,
                        ArgumentOwnership::Borrowed,
                    ],
                    result_ownership: CallableResultOwnership::Scalar,
                },
                Instruction::Return { src: r(3) },
            ],
        ),
        function(
            1,
            1,
            2,
            vec![
                Instruction::Closure {
                    dst: r(1),
                    function: fid(2),
                    captures: vec![r(0)],
                    capture_ownership: vec![ArgumentOwnership::Borrowed],
                },
                Instruction::Return { src: r(1) },
            ],
        ),
        function(
            2,
            2,
            3,
            vec![
                intrinsic(r(2), "extern:Nat.add", vec![r(0), r(1)]),
                Instruction::Return { src: r(2) },
            ],
        ),
    ]);
    let completed = returned(execute(&over_applied, ExecutionLimits::default(), None));
    assert_eq!(completed.value.unbox(), 42);
    assert_eq!(completed.usage.steps, 9);
    assert_eq!(
        completed.usage.peak_stack_depth, 2,
        "the returned closure replaces, rather than nests above, the first callee"
    );
}

#[test]
fn validator_refuses_malformed_closure_forms_before_execution() {
    let _guard = lock();
    let missing = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            1,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(9),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Return { src: r(0) },
            ],
        )],
    );
    assert!(matches!(
        validate(missing),
        Err(ValidationError::MissingClosureTarget { target, .. }) if target == fid(9)
    ));

    let saturated = Program::new(
        fid(0),
        vec![
            function(
                0,
                0,
                2,
                vec![
                    Instruction::Nat {
                        dst: r(0),
                        value: 1,
                    },
                    Instruction::Closure {
                        dst: r(1),
                        function: fid(1),
                        captures: vec![r(0)],
                        capture_ownership: vec![ArgumentOwnership::Borrowed],
                    },
                    Instruction::Return { src: r(1) },
                ],
            ),
            function(1, 1, 1, vec![Instruction::Return { src: r(0) }]),
        ],
    );
    assert!(matches!(
        validate(saturated),
        Err(ValidationError::ClosureCaptureArity {
            target_arity: 1,
            captures: 1,
            ..
        })
    ));

    let empty_apply = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            2,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 1,
                },
                Instruction::Apply {
                    dst: r(1),
                    closure: r(0),
                    args: Vec::new(),
                    argument_ownership: Vec::new(),
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(1) },
            ],
        )],
    );
    assert!(matches!(
        validate(empty_apply),
        Err(ValidationError::EmptyApply { .. })
    ));

    let overflow = Program::new(
        fid(0),
        vec![
            function(
                0,
                0,
                1,
                vec![
                    Instruction::Closure {
                        dst: r(0),
                        function: fid(1),
                        captures: Vec::new(),
                        capture_ownership: Vec::new(),
                    },
                    Instruction::Return { src: r(0) },
                ],
            ),
            function(
                1,
                u16::MAX,
                u16::MAX,
                vec![Instruction::Return { src: r(0) }],
            ),
        ],
    );
    assert!(matches!(
        validate(overflow),
        Err(ValidationError::ClosureArityOverflow {
            target_arity: u16::MAX,
            ..
        })
    ));
}

#[test]
fn callable_result_contracts_refuse_wrong_returns_and_dynamic_apply_classes() {
    let _guard = lock();
    let owned_returning_scalar = validated(vec![function_with_callable_result(
        0,
        Vec::new(),
        CallableResultOwnership::Owned,
        1,
        vec![
            Instruction::Nat {
                dst: r(0),
                value: 7,
            },
            Instruction::Return { src: r(0) },
        ],
    )]);
    let scalar_returning_heap = validated(vec![function_with_callable_result(
        0,
        Vec::new(),
        CallableResultOwnership::Scalar,
        1,
        vec![
            Instruction::String {
                dst: r(0),
                value: "heap".to_string(),
            },
            Instruction::Return { src: r(0) },
        ],
    )]);
    let exact_mismatch = validated(vec![
        function(
            0,
            0,
            3,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 7,
                },
                Instruction::Apply {
                    dst: r(2),
                    closure: r(0),
                    args: vec![r(1)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Owned,
                },
                Instruction::Return { src: r(2) },
            ],
        ),
        function_with_callable_result(
            1,
            vec![ArgumentOwnership::Borrowed],
            CallableResultOwnership::Scalar,
            1,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    let partial_mismatch = validated(vec![
        function(
            0,
            0,
            3,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 7,
                },
                Instruction::Apply {
                    dst: r(2),
                    closure: r(0),
                    args: vec![r(1)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Scalar,
                },
                Instruction::Return { src: r(2) },
            ],
        ),
        function_with_callable_result(
            1,
            vec![ArgumentOwnership::Borrowed, ArgumentOwnership::Borrowed],
            CallableResultOwnership::Scalar,
            2,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    let overapplication_mismatch = validated(vec![
        function(
            0,
            0,
            4,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 7,
                },
                Instruction::Nat {
                    dst: r(2),
                    value: 8,
                },
                Instruction::Apply {
                    dst: r(3),
                    closure: r(0),
                    args: vec![r(1), r(2)],
                    argument_ownership: vec![
                        ArgumentOwnership::Borrowed,
                        ArgumentOwnership::Borrowed,
                    ],
                    result_ownership: CallableResultOwnership::Scalar,
                },
                Instruction::Return { src: r(3) },
            ],
        ),
        function_with_callable_result(
            1,
            vec![ArgumentOwnership::Borrowed],
            CallableResultOwnership::Scalar,
            1,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);

    shadow::enable();
    assert!(matches!(
        execute(
            &owned_returning_scalar,
            ExecutionLimits::default(),
            None
        ),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::CallableResultKind {
                function,
                expected: CallableResultOwnership::Owned,
                actual: ValueKind::Scalar,
            },
            ..
        }) if function == fid(0)
    ));
    assert!(matches!(
        execute(&scalar_returning_heap, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::CallableResultKind {
                function,
                expected: CallableResultOwnership::Scalar,
                actual: ValueKind::String,
            },
            ..
        }) if function == fid(0)
    ));
    assert!(matches!(
        execute(&exact_mismatch, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::ApplyResultOwnershipMismatch {
                function,
                expected: CallableResultOwnership::Scalar,
                actual: CallableResultOwnership::Owned,
            },
            ..
        }) if function == fid(1)
    ));
    for program in [&partial_mismatch, &overapplication_mismatch] {
        assert!(matches!(
            execute(program, ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::ApplyResultOwnershipMismatch {
                    function,
                    expected: CallableResultOwnership::Owned,
                    actual: CallableResultOwnership::Scalar,
                },
                ..
            }) if function == fid(1)
        ));
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "callable result refusals release every Marrow object"
    );
    assert!(events.iter().all(|event| {
        event.kind != shadow::EventKind::DoubleRelease
            && event.kind != shadow::EventKind::ForeignPointer
    }));
}

#[test]
fn closure_stops_and_dynamic_refusals_are_typed_and_rc_clean() {
    let _guard = lock();
    let stack_limited = validated(vec![
        function(
            0,
            0,
            2,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 1,
                },
                Instruction::Apply {
                    dst: r(1),
                    closure: r(0),
                    args: vec![r(1)],
                    argument_ownership: vec![ArgumentOwnership::Borrowed],
                    result_ownership: CallableResultOwnership::Scalar,
                },
                Instruction::Return { src: r(1) },
            ],
        ),
        function_with_callable_result(
            1,
            vec![ArgumentOwnership::Borrowed],
            CallableResultOwnership::Scalar,
            1,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    let stopped = execute(
        &stack_limited,
        ExecutionLimits {
            max_steps: 20,
            max_stack_depth: 1,
        },
        None,
    );
    assert!(matches!(
        stopped,
        Outcome::Inconclusive(ref inconclusive)
            if matches!(
                inconclusive.cause,
                InconclusiveCause::ResourceExhausted { ref usage }
                    if usage.reason == ResourceReason::RecursionDepth { limit: 1 }
            )
    ));

    let polls = Cell::new(0usize);
    let cancel_before_apply = || {
        let next = polls.get() + 1;
        polls.set(next);
        next == 4
    };
    let cancelled = execute(
        &stack_limited,
        ExecutionLimits::default(),
        Some(&cancel_before_apply),
    );
    assert!(matches!(
        cancelled,
        Outcome::Inconclusive(ref inconclusive)
            if matches!(inconclusive.cause, InconclusiveCause::Cancelled { .. })
    ));

    let wrong_type = validated(vec![function(
        0,
        0,
        2,
        vec![
            Instruction::String {
                dst: r(0),
                value: "not a closure".to_string(),
            },
            Instruction::Nat {
                dst: r(1),
                value: 1,
            },
            Instruction::Apply {
                dst: r(1),
                closure: r(0),
                args: vec![r(1)],
                argument_ownership: vec![ArgumentOwnership::Borrowed],
                result_ownership: CallableResultOwnership::Scalar,
            },
            Instruction::Return { src: r(1) },
        ],
    )]);

    shadow::enable();
    {
        let refused = execute(&wrong_type, ExecutionLimits::default(), None);
        assert!(matches!(
            refused,
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch {
                    operation: "apply",
                    argument: 0,
                    expected: "Golem closure",
                    actual: ValueKind::String,
                },
                ..
            })
        ));
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "dynamic refusal retained no closure input");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "closure refusal kept the Marrow ownership graph balanced"
    );
}

#[test]
fn st_ref_intrinsics_preserve_aliasing_replacement_and_identity() {
    let _guard = lock();
    let program = validated(vec![function(
        0,
        0,
        14,
        vec![
            Instruction::String {
                dst: r(0),
                value: "old".to_string(),
            },
            intrinsic(r(1), "extern:ST.Prim.mkRef", vec![r(0)]),
            Instruction::Copy {
                dst: r(2),
                src: r(1),
            },
            intrinsic(r(3), "extern:ST.Prim.Ref.ptrEq", vec![r(1), r(2)]),
            Instruction::String {
                dst: r(4),
                value: "new".to_string(),
            },
            intrinsic(r(5), "extern:ST.Prim.Ref.swap", vec![r(1), r(4)]),
            intrinsic(r(6), "extern:ST.Prim.Ref.get", vec![r(2)]),
            Instruction::String {
                dst: r(7),
                value: "final".to_string(),
            },
            intrinsic(r(8), "extern:ST.Prim.Ref.set", vec![r(2), r(7)]),
            intrinsic(r(9), "extern:ST.Prim.Ref.get", vec![r(1)]),
            Instruction::String {
                dst: r(10),
                value: "final".to_string(),
            },
            intrinsic(r(11), "extern:ST.Prim.mkRef", vec![r(10)]),
            intrinsic(r(12), "extern:ST.Prim.Ref.ptrEq", vec![r(1), r(11)]),
            Instruction::Array {
                dst: r(13),
                items: vec![r(3), r(5), r(6), r(8), r(9), r(12)],
            },
            Instruction::Return { src: r(13) },
        ],
    )]);

    shadow::enable();
    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(completed.value.array_view(), (6, 6));
    assert_eq!(
        completed.value.array_child(0).unbox(),
        1,
        "a copied handle aliases the same cell"
    );
    assert_eq!(string_contents(&completed.value.array_child(1)), "old");
    assert_eq!(
        string_contents(&completed.value.array_child(2)),
        "new",
        "the alias observes the swapped value"
    );
    assert_eq!(
        completed.value.array_child(3).unbox(),
        0,
        "Ref.set returns Unit"
    );
    assert_eq!(
        string_contents(&completed.value.array_child(4)),
        "final",
        "the original handle observes a set through its alias"
    );
    assert_eq!(
        completed.value.array_child(5).unbox(),
        0,
        "equal contents in separately allocated cells have distinct identity"
    );
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "the effect program releases every ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "cell replacement preserves exact ownership"
    );
}

#[test]
fn st_ref_take_transfers_the_exact_value_and_accepts_a_refill() {
    let _guard = lock();
    let program = validated(vec![function(
        0,
        0,
        8,
        vec![
            Instruction::String {
                dst: r(0),
                value: "taken".to_string(),
            },
            Instruction::Copy {
                dst: r(1),
                src: r(0),
            },
            intrinsic(r(2), "extern:ST.Prim.mkRef", vec![r(0)]),
            intrinsic(r(3), "extern:ST.Prim.Ref.take", vec![r(2)]),
            Instruction::String {
                dst: r(4),
                value: "refilled".to_string(),
            },
            intrinsic(r(5), "extern:ST.Prim.Ref.set", vec![r(2), r(4)]),
            intrinsic(r(6), "extern:ST.Prim.Ref.get", vec![r(2)]),
            Instruction::Array {
                dst: r(7),
                items: vec![r(1), r(3), r(5), r(6)],
            },
            Instruction::Return { src: r(7) },
        ],
    )]);

    shadow::enable();
    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(completed.value.array_view(), (4, 4));
    let retained_alias = completed.value.array_child(0);
    let taken = completed.value.array_child(1);
    assert_eq!(string_contents(&retained_alias), "taken");
    assert_eq!(string_contents(&taken), "taken");
    assert_eq!(
        retained_alias.identity_token(),
        taken.identity_token(),
        "Golem returns the exact value formerly owned by the cell"
    );
    assert_eq!(
        completed.value.array_child(2).unbox(),
        0,
        "the refill returns Unit"
    );
    assert_eq!(string_contents(&completed.value.array_child(3)), "refilled");
    drop(retained_alias);
    drop(taken);
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "the take/refill program releases every ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "take/refill preserves exact ownership in the interpreter"
    );
}

#[test]
fn evaluated_thunks_and_finished_tasks_round_trip_abi_values() {
    let _guard = lock();
    let program = validated(vec![function(
        0,
        0,
        8,
        vec![
            Instruction::String {
                dst: r(0),
                value: "payload".to_string(),
            },
            intrinsic(r(1), "extern:Thunk.pure", vec![r(0)]),
            intrinsic(r(2), "extern:Thunk.get", vec![r(1)]),
            Instruction::Copy {
                dst: r(6),
                src: r(2),
            },
            intrinsic(r(3), "extern:Task.pure", vec![r(2)]),
            Instruction::Copy {
                dst: r(7),
                src: r(3),
            },
            intrinsic(r(4), "extern:Task.get", vec![r(3)]),
            Instruction::Array {
                dst: r(5),
                items: vec![r(1), r(6), r(7), r(4)],
            },
            Instruction::Return { src: r(5) },
        ],
    )]);

    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(completed.value.array_view(), (4, 4));
    assert_eq!(
        value_kind(&completed.value.array_child(0)),
        ValueKind::Thunk
    );
    assert_eq!(string_contents(&completed.value.array_child(1)), "payload");
    assert_eq!(value_kind(&completed.value.array_child(2)), ValueKind::Task);
    assert_eq!(string_contents(&completed.value.array_child(3)), "payload");
}

#[test]
fn delayed_thunk_forces_once_and_caches_the_same_abi_value() {
    let _guard = lock();
    let program = validated(vec![
        function(
            0,
            0,
            8,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 0,
                },
                intrinsic(r(1), "extern:ST.Prim.mkRef", vec![r(0)]),
                Instruction::Closure {
                    dst: r(2),
                    function: fid(1),
                    captures: vec![r(1)],
                    capture_ownership: vec![ArgumentOwnership::Borrowed],
                },
                intrinsic(r(3), "extern:Thunk.mk", vec![r(2)]),
                intrinsic(r(4), "extern:Thunk.get", vec![r(3)]),
                intrinsic(r(5), "extern:Thunk.get", vec![r(3)]),
                intrinsic(r(6), "extern:ST.Prim.Ref.get", vec![r(1)]),
                Instruction::Array {
                    dst: r(7),
                    items: vec![r(3), r(4), r(5), r(6)],
                },
                Instruction::Return { src: r(7) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Borrowed, ArgumentOwnership::Scalar],
            7,
            vec![
                intrinsic(r(2), "extern:ST.Prim.Ref.get", vec![r(0)]),
                Instruction::Nat {
                    dst: r(3),
                    value: 1,
                },
                intrinsic(r(4), "extern:Nat.add", vec![r(2), r(3)]),
                intrinsic(r(5), "extern:ST.Prim.Ref.set", vec![r(0), r(4)]),
                Instruction::String {
                    dst: r(6),
                    value: "forced".to_string(),
                },
                Instruction::Return { src: r(6) },
            ],
        ),
    ]);

    shadow::enable();
    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(completed.value.array_view(), (4, 4));
    assert_eq!(completed.usage.peak_stack_depth, 2);
    {
        let thunk = completed.value.array_child(0);
        let first = completed.value.array_child(1);
        let cached = completed.value.array_child(2);
        assert_eq!(value_kind(&thunk), ValueKind::Thunk);
        assert_eq!(string_contents(&first), "forced");
        assert_eq!(string_contents(&cached), "forced");
        assert_eq!(
            first.identity_token(),
            cached.identity_token(),
            "the second force retains the cached object instead of re-running"
        );
        let stored = thunk
            .evaluated_thunk_value()
            .expect("successful force completes the ABI thunk");
        assert_eq!(stored.identity_token(), first.identity_token());
        assert_eq!(
            completed.value.array_child(3).unbox(),
            1,
            "the captured cell proves the delayed closure ran exactly once"
        );
    }
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "forced thunk execution leaves no live ABI object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "forcing and cached reads preserve exact ownership"
    );
}

#[test]
fn delayed_thunk_caches_an_under_applied_closure_without_entering_it() {
    let _guard = lock();
    let program = validated(vec![
        function(
            0,
            0,
            5,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                intrinsic(r(1), "extern:Thunk.mk", vec![r(0)]),
                intrinsic(r(2), "extern:Thunk.get", vec![r(1)]),
                intrinsic(r(3), "extern:Thunk.get", vec![r(1)]),
                Instruction::Array {
                    dst: r(4),
                    items: vec![r(2), r(3)],
                },
                Instruction::Return { src: r(4) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Scalar, ArgumentOwnership::Borrowed],
            2,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);

    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(
        completed.usage.peak_stack_depth, 1,
        "under-application completes without entering the target"
    );
    let first = completed.value.array_child(0);
    let cached = completed.value.array_child(1);
    assert_eq!(value_kind(&first), ValueKind::Closure);
    assert_eq!(first.closure_view(), (3, 2));
    assert_eq!(first.identity_token(), cached.identity_token());
    let (_, fixed) = first
        .closure_shell_parts()
        .expect("the cached partial application stays a Golem shell");
    assert_eq!(fixed[0].unbox(), 1);
    assert_eq!(fixed[1].unbox(), 0, "Thunk.get supplies Unit");
}

#[test]
fn delayed_thunk_stops_and_panics_do_not_publish_or_leak() {
    let _guard = lock();
    let simple = delayed_thunk_program(
        2,
        vec![
            Instruction::String {
                dst: r(1),
                value: "recovered".to_string(),
            },
            Instruction::Return { src: r(1) },
        ],
    );

    shadow::enable();
    let stack_limited = execute(
        &simple,
        ExecutionLimits {
            max_steps: 20,
            max_stack_depth: 1,
        },
        None,
    );
    assert!(matches!(
        stack_limited,
        Outcome::Inconclusive(ref inconclusive)
            if matches!(
                inconclusive.cause,
                InconclusiveCause::ResourceExhausted { ref usage }
                    if usage.reason == ResourceReason::RecursionDepth { limit: 1 }
            )
    ));

    let polls = Cell::new(0usize);
    let cancel_in_callee = || {
        let next = polls.get() + 1;
        polls.set(next);
        next == 4
    };
    assert!(matches!(
        execute(
            &simple,
            ExecutionLimits::default(),
            Some(&cancel_in_callee)
        ),
        Outcome::Inconclusive(ref inconclusive)
            if matches!(inconclusive.cause, InconclusiveCause::Cancelled { .. })
    ));

    let panicking = delayed_thunk_program(
        2,
        vec![
            Instruction::String {
                dst: r(1),
                value: "boom".to_string(),
            },
            Instruction::Panic { message: r(1) },
        ],
    );
    assert!(matches!(
        execute(&panicking, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Panicked { message, .. }) if message == "boom"
    ));

    let recovered = returned(execute(&simple, ExecutionLimits::default(), None));
    assert_eq!(string_contents(&recovered.value), "recovered");
    drop(recovered);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "every aborted thunk state is reclaimed");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "stop, panic, and recovery keep the thunk ownership graph balanced"
    );
}

#[test]
fn managerless_task_spawn_map_and_bind_share_the_closure_continuation_stack() {
    let _guard = lock();
    let program = validated(vec![
        function(
            0,
            0,
            19,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 0,
                },
                Instruction::Closure {
                    dst: r(1),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(11),
                    value: 0,
                },
                intrinsic(r(2), "extern:Task.spawn", vec![r(1), r(11)]),
                Instruction::Copy {
                    dst: r(12),
                    src: r(2),
                },
                Instruction::Copy {
                    dst: r(13),
                    src: r(2),
                },
                Instruction::Closure {
                    dst: r(3),
                    function: fid(2),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(14),
                    value: 0,
                },
                intrinsic(r(4), "extern:Task.map", vec![r(3), r(2), r(14), r(0)]),
                Instruction::Copy {
                    dst: r(15),
                    src: r(4),
                },
                Instruction::Copy {
                    dst: r(16),
                    src: r(4),
                },
                Instruction::Closure {
                    dst: r(5),
                    function: fid(3),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(17),
                    value: 0,
                },
                intrinsic(r(6), "extern:Task.bind", vec![r(4), r(5), r(17), r(0)]),
                Instruction::Copy {
                    dst: r(18),
                    src: r(6),
                },
                intrinsic(r(7), "extern:Task.get", vec![r(13)]),
                intrinsic(r(8), "extern:Task.get", vec![r(16)]),
                intrinsic(r(9), "extern:Task.get", vec![r(18)]),
                Instruction::Array {
                    dst: r(10),
                    items: vec![r(12), r(15), r(6), r(7), r(8), r(9)],
                },
                Instruction::Return { src: r(10) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Scalar],
            2,
            vec![
                Instruction::String {
                    dst: r(1),
                    value: "seed".to_string(),
                },
                Instruction::Return { src: r(1) },
            ],
        ),
        function_with_ownership(
            2,
            vec![ArgumentOwnership::Owned],
            3,
            vec![
                Instruction::String {
                    dst: r(1),
                    value: "-mapped".to_string(),
                },
                intrinsic(r(2), "extern:String.append", vec![r(0), r(1)]),
                Instruction::Return { src: r(2) },
            ],
        ),
        function_with_ownership(
            3,
            vec![ArgumentOwnership::Owned],
            4,
            vec![
                Instruction::String {
                    dst: r(1),
                    value: "-bound".to_string(),
                },
                intrinsic(r(2), "extern:String.append", vec![r(0), r(1)]),
                intrinsic(r(3), "extern:Task.pure", vec![r(2)]),
                Instruction::Return { src: r(3) },
            ],
        ),
    ]);

    shadow::enable();
    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(completed.value.array_view(), (6, 6));
    assert_eq!(completed.usage.peak_stack_depth, 2);
    assert_eq!(value_kind(&completed.value.array_child(0)), ValueKind::Task);
    assert_eq!(value_kind(&completed.value.array_child(1)), ValueKind::Task);
    assert_eq!(value_kind(&completed.value.array_child(2)), ValueKind::Task);
    assert_eq!(string_contents(&completed.value.array_child(3)), "seed");
    assert_eq!(
        string_contents(&completed.value.array_child(4)),
        "seed-mapped"
    );
    assert_eq!(
        string_contents(&completed.value.array_child(5)),
        "seed-mapped-bound"
    );
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "managerless task composition releases every object"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "spawn, map, and bind preserve exact ABI ownership"
    );
}

#[test]
fn managerless_task_bind_returns_the_continuation_task_without_rewrapping() {
    let _guard = lock();
    let program = validated(vec![
        function(
            0,
            0,
            8,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "source".to_string(),
                },
                intrinsic(r(1), "extern:Task.pure", vec![r(0)]),
                Instruction::String {
                    dst: r(2),
                    value: "result".to_string(),
                },
                intrinsic(r(3), "extern:Task.pure", vec![r(2)]),
                Instruction::Closure {
                    dst: r(4),
                    function: fid(1),
                    captures: vec![r(3)],
                    capture_ownership: vec![ArgumentOwnership::Borrowed],
                },
                Instruction::Nat {
                    dst: r(5),
                    value: 0,
                },
                intrinsic(r(6), "extern:Task.bind", vec![r(1), r(4), r(5), r(5)]),
                Instruction::Array {
                    dst: r(7),
                    items: vec![r(3), r(6)],
                },
                Instruction::Return { src: r(7) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Borrowed, ArgumentOwnership::Owned],
            2,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);

    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    let expected = completed.value.array_child(0);
    let bound = completed.value.array_child(1);
    assert_eq!(
        expected.identity_token(),
        bound.identity_token(),
        "managerless bind returns the continuation task itself"
    );
    let payload = bound
        .finished_task_value()
        .expect("the continuation returned a finished task");
    assert_eq!(string_contents(&payload), "result");
}

#[test]
fn managerless_task_spawn_wraps_an_under_applied_closure_without_entering_it() {
    let _guard = lock();
    let program = managerless_spawn_program(2, 2, vec![Instruction::Return { src: r(0) }]);

    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(
        completed.usage.peak_stack_depth, 1,
        "under-application does not enter the target"
    );
    assert_eq!(value_kind(&completed.value), ValueKind::Closure);
    assert_eq!(completed.value.closure_view(), (3, 2));
    let (_, fixed) = completed
        .value
        .closure_shell_parts()
        .expect("the task payload remains a Golem closure shell");
    assert_eq!(fixed[0].unbox(), 1);
    assert_eq!(fixed[1].unbox(), 0, "Task.spawn supplies Unit");
}

#[test]
fn internal_thunk_and_task_application_bind_argument_ownership_before_entry() {
    let _guard = lock();
    let thunk = validated(vec![
        function(
            0,
            0,
            3,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                intrinsic(r(1), "extern:Thunk.mk", vec![r(0)]),
                intrinsic(r(2), "extern:Thunk.get", vec![r(1)]),
                Instruction::Return { src: r(2) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Borrowed],
            2,
            vec![
                Instruction::String {
                    dst: r(1),
                    value: "unreachable".to_string(),
                },
                Instruction::Return { src: r(1) },
            ],
        ),
    ]);
    let spawn = validated(vec![
        function(
            0,
            0,
            3,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 0,
                },
                intrinsic(r(2), "extern:Task.spawn", vec![r(0), r(1)]),
                Instruction::Return { src: r(2) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Owned],
            2,
            vec![
                Instruction::String {
                    dst: r(1),
                    value: "unreachable".to_string(),
                },
                Instruction::Return { src: r(1) },
            ],
        ),
    ]);
    let map = validated(vec![
        function(
            0,
            0,
            6,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "payload".to_string(),
                },
                intrinsic(r(1), "extern:Task.pure", vec![r(0)]),
                Instruction::Closure {
                    dst: r(2),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(3),
                    value: 0,
                },
                Instruction::Nat {
                    dst: r(4),
                    value: 0,
                },
                intrinsic(r(5), "extern:Task.map", vec![r(2), r(1), r(3), r(4)]),
                Instruction::Return { src: r(5) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Borrowed],
            1,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    let bind = validated(vec![
        function(
            0,
            0,
            6,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "payload".to_string(),
                },
                intrinsic(r(1), "extern:Task.pure", vec![r(0)]),
                Instruction::Closure {
                    dst: r(2),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(3),
                    value: 0,
                },
                Instruction::Nat {
                    dst: r(4),
                    value: 0,
                },
                intrinsic(r(5), "extern:Task.bind", vec![r(1), r(2), r(3), r(4)]),
                Instruction::Return { src: r(5) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Unique],
            3,
            vec![
                Instruction::String {
                    dst: r(1),
                    value: "unreachable".to_string(),
                },
                intrinsic(r(2), "extern:Task.pure", vec![r(1)]),
                Instruction::Return { src: r(2) },
            ],
        ),
    ]);
    let cases = [
        (
            "Thunk.get",
            thunk,
            ArgumentOwnership::Borrowed,
            ArgumentOwnership::Scalar,
        ),
        (
            "Task.spawn",
            spawn,
            ArgumentOwnership::Owned,
            ArgumentOwnership::Scalar,
        ),
        (
            "Task.map",
            map,
            ArgumentOwnership::Borrowed,
            ArgumentOwnership::Owned,
        ),
        (
            "Task.bind",
            bind,
            ArgumentOwnership::Unique,
            ArgumentOwnership::Owned,
        ),
    ];

    shadow::enable();
    for (row, program, expected, actual) in cases {
        assert!(
            matches!(
                execute(&program, ExecutionLimits::default(), None),
                Outcome::Complete(VmExit::Refused {
                    refusal: VmRefusal::ApplyOwnershipMismatch {
                        function,
                        argument: 0,
                        expected: observed_expected,
                        actual: observed_actual,
                    },
                    usage,
                }) if function == fid(1)
                    && observed_expected == expected
                    && observed_actual == actual
                    && usage.peak_stack_depth == 1
            ),
            "{row} must reject its internal argument contract before target entry"
        );
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "internal ownership refusals release every transferred value"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "internal ownership refusals preserve exact ABI ownership"
    );
}

#[test]
fn managerless_task_rows_refuse_bad_kinds_scalars_and_bind_results_without_leaks() {
    let _guard = lock();
    let wrong_closure = validated(vec![function(
        0,
        0,
        3,
        vec![
            Instruction::String {
                dst: r(0),
                value: "not a closure".to_string(),
            },
            Instruction::Nat {
                dst: r(1),
                value: 0,
            },
            intrinsic(r(2), "extern:Task.spawn", vec![r(0), r(1)]),
            Instruction::Return { src: r(2) },
        ],
    )]);
    let wrong_priority = validated(vec![
        function(
            0,
            0,
            3,
            vec![
                Instruction::Closure {
                    dst: r(0),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::String {
                    dst: r(1),
                    value: "not a priority".to_string(),
                },
                intrinsic(r(2), "extern:Task.spawn", vec![r(0), r(1)]),
                Instruction::Return { src: r(2) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Scalar],
            1,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    let invalid_sync = validated(vec![
        function(
            0,
            0,
            6,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "payload".to_string(),
                },
                intrinsic(r(1), "extern:Task.pure", vec![r(0)]),
                Instruction::Closure {
                    dst: r(2),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(3),
                    value: 0,
                },
                Instruction::Nat {
                    dst: r(4),
                    value: 2,
                },
                intrinsic(r(5), "extern:Task.map", vec![r(2), r(1), r(3), r(4)]),
                Instruction::Return { src: r(5) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Owned],
            1,
            vec![Instruction::Return { src: r(0) }],
        ),
    ]);
    let bind_non_task = validated(vec![
        function(
            0,
            0,
            5,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "source".to_string(),
                },
                intrinsic(r(1), "extern:Task.pure", vec![r(0)]),
                Instruction::Closure {
                    dst: r(2),
                    function: fid(1),
                    captures: Vec::new(),
                    capture_ownership: Vec::new(),
                },
                Instruction::Nat {
                    dst: r(3),
                    value: 0,
                },
                intrinsic(r(4), "extern:Task.bind", vec![r(1), r(2), r(3), r(3)]),
                Instruction::Return { src: r(4) },
            ],
        ),
        function_with_ownership(
            1,
            vec![ArgumentOwnership::Owned],
            2,
            vec![
                Instruction::String {
                    dst: r(1),
                    value: "not a Task".to_string(),
                },
                Instruction::Return { src: r(1) },
            ],
        ),
    ]);

    shadow::enable();
    assert!(matches!(
        execute(&wrong_closure, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch {
                operation: "Task.spawn",
                argument: 0,
                expected: "Golem closure",
                actual: ValueKind::String,
            },
            ..
        })
    ));
    assert!(matches!(
        execute(&wrong_priority, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch {
                operation: "Task.spawn",
                argument: 1,
                expected: "Nat scalar",
                actual: ValueKind::String,
            },
            ..
        })
    ));
    assert!(matches!(
        execute(&invalid_sync, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::InvalidBoolScalar {
                operation: "Task.map",
                argument: 3,
                value: 2,
            },
            ..
        })
    ));
    assert!(matches!(
        execute(&bind_non_task, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch {
                operation: "Task.bind result",
                argument: 0,
                expected: "finished Task",
                actual: ValueKind::String,
            },
            ..
        })
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "every managerless task refusal releases its inputs"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "task refusal paths preserve exact ABI ownership"
    );
}

#[test]
fn managerless_task_stops_and_panics_do_not_publish_or_leak() {
    let _guard = lock();
    let simple = managerless_spawn_program(
        1,
        2,
        vec![
            Instruction::String {
                dst: r(1),
                value: "recovered".to_string(),
            },
            Instruction::Return { src: r(1) },
        ],
    );

    shadow::enable();
    let step_limited = execute(
        &simple,
        ExecutionLimits {
            max_steps: 3,
            max_stack_depth: 8,
        },
        None,
    );
    assert!(matches!(
        step_limited,
        Outcome::Inconclusive(ref inconclusive)
            if matches!(
                inconclusive.cause,
                InconclusiveCause::ResourceExhausted { ref usage }
                    if usage.reason
                        == ResourceReason::Heartbeats {
                            consumed: 4,
                            limit: 3,
                        }
            )
    ));

    let stack_limited = execute(
        &simple,
        ExecutionLimits {
            max_steps: 20,
            max_stack_depth: 1,
        },
        None,
    );
    assert!(matches!(
        stack_limited,
        Outcome::Inconclusive(ref inconclusive)
            if matches!(
                inconclusive.cause,
                InconclusiveCause::ResourceExhausted { ref usage }
                    if usage.reason == ResourceReason::RecursionDepth { limit: 1 }
            )
    ));

    let polls = Cell::new(0usize);
    let cancel_in_callee = || {
        let next = polls.get() + 1;
        polls.set(next);
        next == 4
    };
    assert!(matches!(
        execute(
            &simple,
            ExecutionLimits::default(),
            Some(&cancel_in_callee)
        ),
        Outcome::Inconclusive(ref inconclusive)
            if matches!(inconclusive.cause, InconclusiveCause::Cancelled { .. })
    ));

    let panicking = managerless_spawn_program(
        1,
        2,
        vec![
            Instruction::String {
                dst: r(1),
                value: "boom".to_string(),
            },
            Instruction::Panic { message: r(1) },
        ],
    );
    assert!(matches!(
        execute(&panicking, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Panicked { message, .. }) if message == "boom"
    ));

    let recovered = returned(execute(&simple, ExecutionLimits::default(), None));
    assert_eq!(string_contents(&recovered.value), "recovered");
    drop(recovered);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "every stopped task continuation is reclaimed");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "task stop, panic, and recovery keep the ownership graph balanced"
    );
}

#[test]
fn pure_effect_intrinsics_refuse_wrong_abi_kinds_without_leaks() {
    let _guard = lock();
    let cases = [
        ("extern:ST.Prim.Ref.get", "ST.Prim.Ref.get", "ST.Ref"),
        ("extern:ST.Prim.Ref.take", "ST.Prim.Ref.take", "ST.Ref"),
        ("extern:Thunk.mk", "Thunk.mk", "Golem closure"),
        ("extern:Thunk.get", "Thunk.get", "Thunk"),
        ("extern:Task.get", "Task.get", "finished Task"),
    ];

    shadow::enable();
    for (row, operation, expected) in cases {
        let program = validated(vec![function(
            0,
            0,
            2,
            vec![
                Instruction::String {
                    dst: r(0),
                    value: "wrong kind".to_string(),
                },
                intrinsic(r(1), row, vec![r(0)]),
                Instruction::Return { src: r(1) },
            ],
        )]);
        assert!(matches!(
            execute(&program, ExecutionLimits::default(), None),
            Outcome::Complete(VmExit::Refused {
                refusal: VmRefusal::TypeMismatch {
                    operation: actual_operation,
                    argument: 0,
                    expected: actual_expected,
                    actual: ValueKind::String,
                },
                ..
            }) if actual_operation == operation && actual_expected == expected
        ));
    }
    let wrong_arity = validated(vec![function(
        0,
        0,
        1,
        vec![
            Instruction::Intrinsic {
                dst: r(0),
                row: "extern:ST.Prim.Ref.take".to_string(),
                args: Vec::new(),
                argument_ownership: Vec::new(),
                result_ownership: contract_result_ownership("extern:ST.Prim.Ref.take"),
            },
            Instruction::Return { src: r(0) },
        ],
    )]);
    assert!(matches!(
        execute(&wrong_arity, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::IntrinsicArity {
                ref row,
                expected: 1,
                actual: 0,
            },
            ..
        }) if row == "extern:ST.Prim.Ref.take"
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "typed effect refusals retain no operand");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "typed effect refusals preserve the owned object graph"
    );
}

#[test]
fn control_flow_copy_move_drop_and_constructor_ownership_are_executable() {
    let _guard = lock();
    let program = validated(vec![function(
        0,
        0,
        5,
        vec![
            Instruction::Nat {
                dst: r(0),
                value: 0,
            },
            Instruction::JumpIfZero {
                cond: r(0),
                zero: pc(2),
                nonzero: pc(4),
            },
            Instruction::Nat {
                dst: r(1),
                value: 7,
            },
            Instruction::Jump { target: pc(5) },
            Instruction::Nat {
                dst: r(1),
                value: 9,
            },
            Instruction::Copy {
                dst: r(2),
                src: r(1),
            },
            Instruction::Ctor {
                dst: r(3),
                tag: 3,
                fields: vec![r(2)],
                scalar_bytes: Vec::new(),
            },
            Instruction::Move {
                dst: r(4),
                src: r(3),
            },
            Instruction::Drop { src: r(2) },
            Instruction::Return { src: r(4) },
        ],
    )]);

    let completed = returned(execute(&program, ExecutionLimits::default(), None));
    assert_eq!(value_kind(&completed.value), ValueKind::Ctor(3));
    assert_eq!(completed.value.ctor_child(0).unbox(), 7);
}

#[test]
fn constructor_projection_refuses_scalar_wrong_tag_and_wrong_shape_before_reading() {
    let scalar = validated(vec![function(
        0,
        0,
        2,
        vec![
            Instruction::Nat {
                dst: r(0),
                value: 7,
            },
            Instruction::CtorField {
                dst: r(1),
                src: r(0),
                expected_tag: 1,
                expected_fields: 1,
                field: 0,
            },
            Instruction::Return { src: r(1) },
        ],
    )]);
    let wrong_tag = validated(vec![function(
        0,
        0,
        3,
        vec![
            Instruction::Nat {
                dst: r(0),
                value: 7,
            },
            Instruction::Ctor {
                dst: r(1),
                tag: 2,
                fields: vec![r(0)],
                scalar_bytes: Vec::new(),
            },
            Instruction::CtorField {
                dst: r(2),
                src: r(1),
                expected_tag: 1,
                expected_fields: 1,
                field: 0,
            },
            Instruction::Return { src: r(2) },
        ],
    )]);
    let wrong_shape = validated(vec![function(
        0,
        0,
        4,
        vec![
            Instruction::Nat {
                dst: r(0),
                value: 7,
            },
            Instruction::Nat {
                dst: r(1),
                value: 8,
            },
            Instruction::Ctor {
                dst: r(2),
                tag: 1,
                fields: vec![r(0), r(1)],
                scalar_bytes: Vec::new(),
            },
            Instruction::CtorField {
                dst: r(3),
                src: r(2),
                expected_tag: 1,
                expected_fields: 1,
                field: 0,
            },
            Instruction::Return { src: r(3) },
        ],
    )]);
    let cases = [
        (
            scalar,
            VmRefusal::ConstructorProjectionTag {
                expected: 1,
                actual: ValueKind::Scalar,
            },
        ),
        (
            wrong_tag,
            VmRefusal::ConstructorProjectionTag {
                expected: 1,
                actual: ValueKind::Ctor(2),
            },
        ),
        (
            wrong_shape,
            VmRefusal::ConstructorProjectionShape {
                expected_fields: 1,
                actual_fields: 2,
            },
        ),
    ];

    let _guard = lock();
    for (program, expected) in cases {
        shadow::enable();
        let refusal = match execute(&program, ExecutionLimits::default(), None) {
            Outcome::Complete(VmExit::Refused { refusal, .. }) => Some(refusal),
            _ => None,
        };
        assert_eq!(refusal, Some(expected));
        let (events, live) = shadow::disable_and_drain();
        assert_eq!(live, 0, "projection refusal releases every ABI object");
        assert!(
            events.iter().all(|event| {
                event.kind != shadow::EventKind::DoubleRelease
                    && event.kind != shadow::EventKind::ForeignPointer
            }),
            "projection refusal preserves Marrow ownership"
        );
    }
}

#[test]
fn generated_array_ownership_transfers_exactly_and_refuses_drift_before_execution() {
    let _guard = lock();
    let source = validated(vec![function(
        0,
        0,
        5,
        vec![
            Instruction::String {
                dst: r(0),
                value: "first".to_string(),
            },
            Instruction::Array {
                dst: r(1),
                items: vec![r(0)],
            },
            Instruction::String {
                dst: r(2),
                value: "second".to_string(),
            },
            intrinsic(r(3), "extern:Array.push", vec![r(1), r(2)]),
            intrinsic(r(4), "extern:Array.size", vec![r(3)]),
            Instruction::Return { src: r(3) },
        ],
    )]);
    let limits = OwnershipLimits::default();
    let owned = insert_ownership(&source, limits)
        .expect("generated owned arguments transfer into the call");
    assert_eq!(
        owned.witness().canonical_text(),
        concat!(
            "flbc-ownership/14\n",
            "function f0 mode=inserted-linear result=owned source=6 emitted=8 drops=2 moves=0 redefs=0 edges=0 extern_consumes=2 call_consumes=0 closure_consumes=0 apply_consumes=0 borrowed_results=0 raw_results=2 owned_callable_results=0 scalar_callable_results=0\n",
        )
    );
    assert!(
        !owned.program().functions()[0]
            .code
            .iter()
            .any(|instruction| {
                matches!(
                    instruction,
                    Instruction::Drop { src } if *src == r(1) || *src == r(2)
                )
            }),
        "the ownership pass never drops either transferred Array.push argument"
    );

    let bytes = encode_canonical(owned.program(), CodecLimits::default())
        .expect("ownership-bound Array.push artifact");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("independent codec retains argument ownership");
    let rebound = validate_ownership_candidate(&source, decoded, owned.witness().clone(), limits)
        .expect("decoded ownership candidate remains bound to its source");

    shadow::enable();
    let completed = returned(execute(rebound.program(), ExecutionLimits::default(), None));
    assert_eq!(completed.value.array_view(), (2, 2));
    assert_eq!(string_contents(&completed.value.array_child(0)), "first");
    assert_eq!(string_contents(&completed.value.array_child(1)), "second");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "owned intrinsic execution drains every Marrow object"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "owned argument transfer stays inside one Marrow ownership domain"
    );

    let drift = validated(vec![function(
        0,
        0,
        4,
        vec![
            Instruction::String {
                dst: r(0),
                value: "first".to_string(),
            },
            Instruction::Array {
                dst: r(1),
                items: vec![r(0)],
            },
            Instruction::String {
                dst: r(2),
                value: "second".to_string(),
            },
            Instruction::Intrinsic {
                dst: r(3),
                row: "extern:Array.push".to_string(),
                args: vec![r(1), r(2)],
                argument_ownership: vec![ArgumentOwnership::Borrowed, ArgumentOwnership::Owned],
                result_ownership: contract_result_ownership("extern:Array.push"),
            },
            Instruction::Return { src: r(3) },
        ],
    )]);

    shadow::enable();
    assert!(matches!(
        execute(&drift, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::IntrinsicOwnershipMismatch {
                ref row,
                argument: 0,
                expected: ArgumentOwnership::Owned,
                actual: ArgumentOwnership::Borrowed,
            },
            ..
        }) if row == "extern:Array.push"
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "ownership mismatch is refused before any operand escapes its frame"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "ownership mismatch tears down the untouched Marrow graph exactly once"
    );
}

#[test]
fn generated_intrinsic_results_promote_borrowed_bind_raw_and_refuse_drift() {
    let _guard = lock();
    let source = validated(vec![function(
        0,
        0,
        5,
        vec![
            Instruction::String {
                dst: r(0),
                value: "borrowed-child".to_string(),
            },
            Instruction::Array {
                dst: r(1),
                items: vec![r(0)],
            },
            Instruction::Nat {
                dst: r(2),
                value: 0,
            },
            intrinsic(r(3), "extern:Array.ugetBorrowed", vec![r(1), r(2)]),
            intrinsic(r(4), "extern:Array.size", vec![r(1)]),
            Instruction::Return { src: r(3) },
        ],
    )]);
    let limits = OwnershipLimits::default();
    let owned = insert_ownership(&source, limits)
        .expect("borrowed result and raw scalar share one checked ownership graph");
    let witness = &owned.witness().functions()[0];
    assert_eq!(witness.borrowed_intrinsic_results, 1);
    assert_eq!(witness.raw_intrinsic_results, 1);
    assert!(
        owned.witness().canonical_text().contains(
            "borrowed_results=1 raw_results=1 owned_callable_results=0 scalar_callable_results=0\n"
        ),
        "the canonical witness binds both generated result classes"
    );

    let mut borrowed_rows = owned.witness().functions().to_vec();
    borrowed_rows[0].borrowed_intrinsic_results = 0;
    let forged_borrowed = OwnershipWitness::new(owned.witness().schema_version(), borrowed_rows);
    assert!(matches!(
        validate_ownership_candidate(&source, owned.program().clone(), forged_borrowed, limits,),
        Err(OwnershipError::WitnessCount {
            count: OwnershipWitnessCount::BorrowedIntrinsicResults,
            expected: 1,
            actual: 0,
            ..
        })
    ));
    let mut raw_rows = owned.witness().functions().to_vec();
    raw_rows[0].raw_intrinsic_results = 0;
    let forged_raw = OwnershipWitness::new(owned.witness().schema_version(), raw_rows);
    assert!(matches!(
        validate_ownership_candidate(&source, owned.program().clone(), forged_raw, limits),
        Err(OwnershipError::WitnessCount {
            count: OwnershipWitnessCount::RawIntrinsicResults,
            expected: 1,
            actual: 0,
            ..
        })
    ));

    let bytes = encode_canonical(owned.program(), CodecLimits::default())
        .expect("result-ownership-bound artifact");
    let decoded = decode_canonical(&bytes, CodecLimits::default())
        .expect("independent codec retains result ownership");
    let rebound = validate_ownership_candidate(&source, decoded, owned.witness().clone(), limits)
        .expect("decoded result ownership rebinds to its FIR-independent source");

    shadow::enable();
    let completed = returned(execute(rebound.program(), ExecutionLimits::default(), None));
    assert_eq!(string_contents(&completed.value), "borrowed-child");
    drop(completed);
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "one borrowed-result promotion survives source teardown and releases exactly once"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "the source Array remains reusable through Array.size before its child escapes"
    );

    let drift = validated(vec![function(
        0,
        0,
        4,
        vec![
            Instruction::String {
                dst: r(0),
                value: "first".to_string(),
            },
            Instruction::Array {
                dst: r(1),
                items: vec![r(0)],
            },
            Instruction::String {
                dst: r(2),
                value: "second".to_string(),
            },
            Instruction::Intrinsic {
                dst: r(3),
                row: "extern:Array.push".to_string(),
                args: vec![r(1), r(2)],
                argument_ownership: contract_argument_ownership("extern:Array.push", 2),
                result_ownership: ResultOwnership::Owned,
            },
            Instruction::Return { src: r(3) },
        ],
    )]);
    shadow::enable();
    assert!(matches!(
        execute(&drift, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::IntrinsicResultOwnershipMismatch {
                ref row,
                expected: ResultOwnership::RawObject,
                actual: ResultOwnership::Owned,
            },
            ..
        }) if row == "extern:Array.push"
    ));
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(
        live, 0,
        "result mismatch is refused before either owned argument transfers"
    );
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "result drift tears down the untouched frame without Marrow faults"
    );
}

#[test]
fn validator_refuses_version_bounds_flow_and_fallthrough_before_execution() {
    let _guard = lock();

    let mut wrong_version = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            1,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 1,
                },
                Instruction::Return { src: r(0) },
            ],
        )],
    );
    wrong_version.schema_version = FLBC_SCHEMA_VERSION + 1;
    assert_eq!(
        validate(wrong_version),
        Err(ValidationError::UnsupportedVersion {
            seen: FLBC_SCHEMA_VERSION + 1
        })
    );

    let out_of_bounds = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            1,
            vec![
                Instruction::Nat {
                    dst: r(1),
                    value: 1,
                },
                Instruction::Return { src: r(0) },
            ],
        )],
    );
    assert!(matches!(
        validate(out_of_bounds),
        Err(ValidationError::RegisterOutOfBounds {
            register,
            register_count: 1,
            ..
        }) if register == r(1)
    ));

    let read_before_write = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            2,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 0,
                },
                Instruction::JumpIfZero {
                    cond: r(0),
                    zero: pc(2),
                    nonzero: pc(3),
                },
                Instruction::Nat {
                    dst: r(1),
                    value: 1,
                },
                Instruction::Return { src: r(1) },
            ],
        )],
    );
    assert!(matches!(
        validate(read_before_write),
        Err(ValidationError::ReadBeforeWrite {
            pc: at,
            register,
            ..
        }) if at == pc(3) && register == r(1)
    ));

    let fallthrough = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            1,
            vec![Instruction::Nat {
                dst: r(0),
                value: 1,
            }],
        )],
    );
    assert!(matches!(
        validate(fallthrough),
        Err(ValidationError::Fallthrough { pc: at, .. }) if at == pc(0)
    ));
}

#[test]
fn validator_refuses_unreachable_bytes_and_wrong_direct_call_arity() {
    let _guard = lock();
    let unreachable = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            1,
            vec![
                Instruction::Jump { target: pc(2) },
                Instruction::Return { src: r(0) },
                Instruction::Nat {
                    dst: r(0),
                    value: 3,
                },
                Instruction::Return { src: r(0) },
            ],
        )],
    );
    assert!(matches!(
        validate(unreachable),
        Err(ValidationError::UnreachableInstruction { pc: at, .. }) if at == pc(1)
    ));

    let wrong_arity = Program::new(
        fid(0),
        vec![
            function(
                0,
                0,
                1,
                vec![
                    Instruction::Call {
                        dst: r(0),
                        function: fid(1),
                        args: Vec::new(),
                        argument_ownership: Vec::new(),
                        result_ownership: CallableResultOwnership::Owned,
                    },
                    Instruction::Return { src: r(0) },
                ],
            ),
            function(1, 1, 1, vec![Instruction::Return { src: r(0) }]),
        ],
    );
    assert!(matches!(
        validate(wrong_arity),
        Err(ValidationError::CallArity {
            target,
            expected: 1,
            actual: 0,
            ..
        }) if target == fid(1)
    ));
}

#[test]
fn validator_binds_constructor_boundaries_to_the_generated_abi_contract() {
    let _guard = lock();
    let largest_valid = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            2,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 1,
                },
                Instruction::Ctor {
                    dst: r(1),
                    tag: abi::TAG_MAX_CTOR_TAG,
                    fields: vec![r(0); abi::MAX_CTOR_FIELDS - 1],
                    scalar_bytes: vec![0; abi::MAX_CTOR_SCALARS_SIZE - 1],
                },
                Instruction::Return { src: r(1) },
            ],
        )],
    );
    assert!(
        validate(largest_valid).is_ok(),
        "the strict contract maxima admit their predecessor"
    );

    let too_many_fields = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            2,
            vec![
                Instruction::Nat {
                    dst: r(0),
                    value: 1,
                },
                Instruction::Ctor {
                    dst: r(1),
                    tag: 0,
                    fields: vec![r(0); abi::MAX_CTOR_FIELDS],
                    scalar_bytes: Vec::new(),
                },
                Instruction::Return { src: r(1) },
            ],
        )],
    );
    assert!(matches!(
        validate(too_many_fields),
        Err(ValidationError::TooManyCtorFields { count, .. })
            if count == abi::MAX_CTOR_FIELDS
    ));

    let too_many_scalars = Program::new(
        fid(0),
        vec![function(
            0,
            0,
            1,
            vec![
                Instruction::Ctor {
                    dst: r(0),
                    tag: 0,
                    fields: Vec::new(),
                    scalar_bytes: vec![0; abi::MAX_CTOR_SCALARS_SIZE],
                },
                Instruction::Return { src: r(0) },
            ],
        )],
    );
    assert!(matches!(
        validate(too_many_scalars),
        Err(ValidationError::TooManyCtorScalarBytes { count, .. })
            if count == abi::MAX_CTOR_SCALARS_SIZE
    ));
}

#[test]
fn step_stack_and_cancellation_stops_are_non_authoritative() {
    let _guard = lock();
    let loop_program = validated(vec![function(
        0,
        0,
        0,
        vec![Instruction::Jump { target: pc(0) }],
    )]);
    let exhausted = execute(
        &loop_program,
        ExecutionLimits {
            max_steps: 3,
            max_stack_depth: 4,
        },
        None,
    );
    assert_eq!(exhausted.authority(), Authority::NonAuthoritative);
    match exhausted {
        Outcome::Inconclusive(inconclusive) => match inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                assert!(usage.is_genuine_exhaustion());
                assert_eq!(usage.allowed, 3);
                assert_eq!(usage.observed, 4);
                assert_eq!(
                    usage.reason,
                    ResourceReason::Heartbeats {
                        consumed: 4,
                        limit: 3
                    }
                );
            }
            other => panic!("expected step exhaustion, got {other:?}"),
        },
        other => panic!("expected Inconclusive, got {other:?}"),
    }

    let cancelled = || true;
    let stopped = execute(&loop_program, ExecutionLimits::default(), Some(&cancelled));
    assert!(matches!(
        stopped,
        Outcome::Inconclusive(ref inconclusive)
            if matches!(inconclusive.cause, InconclusiveCause::Cancelled { .. })
    ));

    let recursive = validated(vec![function(
        0,
        0,
        1,
        vec![
            Instruction::Call {
                dst: r(0),
                function: fid(0),
                args: Vec::new(),
                argument_ownership: Vec::new(),
                result_ownership: CallableResultOwnership::Scalar,
            },
            Instruction::Return { src: r(0) },
        ],
    )]);
    let stack_stop = execute(
        &recursive,
        ExecutionLimits {
            max_steps: 100,
            max_stack_depth: 2,
        },
        None,
    );
    match stack_stop {
        Outcome::Inconclusive(inconclusive) => match inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => {
                assert!(usage.is_genuine_exhaustion());
                assert_eq!(usage.allowed, 2);
                assert_eq!(usage.observed, 3);
                assert_eq!(usage.reason, ResourceReason::RecursionDepth { limit: 2 });
            }
            other => panic!("expected stack exhaustion, got {other:?}"),
        },
        other => panic!("expected Inconclusive, got {other:?}"),
    }
}

#[test]
fn user_panic_and_dynamic_intrinsic_refusals_remain_completed_answers() {
    let _guard = lock();
    let panic_program = validated(vec![function(
        0,
        0,
        1,
        vec![
            Instruction::String {
                dst: r(0),
                value: "boom".to_string(),
            },
            Instruction::Panic { message: r(0) },
        ],
    )]);
    match execute(&panic_program, ExecutionLimits::default(), None) {
        Outcome::Complete(VmExit::Panicked { message, usage }) => {
            assert_eq!(message, "boom");
            assert_eq!(usage.steps, 2);
        }
        other => panic!("expected user panic, got {other:?}"),
    }

    let wrong_type = validated(vec![function(
        0,
        0,
        3,
        vec![
            Instruction::String {
                dst: r(0),
                value: "not a Nat".to_string(),
            },
            Instruction::Nat {
                dst: r(1),
                value: 1,
            },
            intrinsic(r(2), "extern:Nat.add", vec![r(0), r(1)]),
            Instruction::Return { src: r(2) },
        ],
    )]);
    assert!(matches!(
        execute(&wrong_type, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::TypeMismatch {
                operation: "Nat.add",
                argument: 0,
                expected: "Nat scalar",
                actual: ValueKind::String,
            },
            ..
        })
    ));

    let unknown_row = validated(vec![function(
        0,
        0,
        2,
        vec![
            Instruction::Nat {
                dst: r(0),
                value: 1,
            },
            intrinsic(r(1), "extern:Prototype.notInCensus", vec![r(0)]),
            Instruction::Return { src: r(1) },
        ],
    )]);
    assert!(matches!(
        execute(&unknown_row, ExecutionLimits::default(), None),
        Outcome::Complete(VmExit::Refused {
            refusal: VmRefusal::UnknownIntrinsic { row },
            ..
        }) if row == "extern:Prototype.notInCensus"
    ));
}

#[test]
fn a_budget_stop_releases_every_live_register_and_the_next_run_recovers() {
    let _guard = lock();
    let holds_heap_value = validated(vec![function(
        0,
        0,
        1,
        vec![
            Instruction::String {
                dst: r(0),
                value: "owned until stop".to_string(),
            },
            Instruction::Jump { target: pc(1) },
        ],
    )]);

    shadow::enable();
    {
        let stopped = execute(
            &holds_heap_value,
            ExecutionLimits {
                max_steps: 2,
                max_stack_depth: 4,
            },
            None,
        );
        assert!(matches!(stopped, Outcome::Inconclusive(_)));
    }
    let (events, live) = shadow::disable_and_drain();
    assert_eq!(live, 0, "the stopped frame retained no Marrow object");
    assert!(
        events.iter().all(|event| {
            event.kind != shadow::EventKind::DoubleRelease
                && event.kind != shadow::EventKind::ForeignPointer
        }),
        "the stop path has balanced ownership"
    );

    let recovery = validated(vec![function(
        0,
        0,
        1,
        vec![
            Instruction::Nat {
                dst: r(0),
                value: 9,
            },
            Instruction::Return { src: r(0) },
        ],
    )]);
    let completed = returned(execute(&recovery, ExecutionLimits::default(), None));
    assert_eq!(completed.value.unbox(), 9);
}
