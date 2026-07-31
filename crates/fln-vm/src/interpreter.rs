//! Deterministic FLBC register interpreter for the G0-3 prototype.
//!
//! The register file contains only [`Obj`] handles from Marrow's safe surface:
//! there is no host-value shadow representation and no conversion at calls.
//! Execution accepts only [`ValidatedProgram`]. Cooperative cancellation and
//! step/stack exhaustion use the shared FL-INV-07 [`Outcome`] algebra, whose
//! non-authoritative arms cannot carry a partially published object.
//!
//! Interpreter closures are real Marrow closure objects. Their first fixed
//! slot is a tagged function-table word followed by captured ABI values. The
//! raw function field remains the explicit shell sentinel, so applying a
//! native/plugin closure is a typed unsupported result until the G0 trampoline
//! exists; this slice does not misreport that boundary as zero-conversion
//! plugin interoperability.
//!
//! The pure effect nucleus uses the same identity: `ST.Ref` cells, evaluated
//! thunks, and finished tasks are Marrow objects all the way through their
//! intrinsic rows. A delayed thunk claims its closure once and completes only
//! through the ordinary return continuation. The manager-absent `Task.spawn`,
//! `Task.map`, and `Task.bind` fallbacks use that same continuation machinery
//! and produce only finished tasks. Scheduled tasks, concurrent thunk forcing,
//! ambient IO, and capability effects remain outside this slice.

use crate::extern_row::{
    ArgumentOwnership as ContractArgumentOwnership, Ownership as ExternOwnership,
    ResultOwnership as ContractResultOwnership,
};
use crate::extern_table_generated::EXTERN_ROWS;
use fln_comp::flbc::{
    ArgumentOwnership, CallableResultOwnership, FunctionId, Instruction, Register, ResultOwnership,
    ValidatedProgram,
};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome, ResourceUsage};
use fln_rt::abi;
use fln_rt::obj::Obj;
use std::fmt;

/// Caller-supplied execution limits. A value of zero permits no work in that
/// dimension; the first attempted unit reports `observed = 1`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionLimits {
    pub max_steps: u64,
    pub max_stack_depth: u64,
}

impl Default for ExecutionLimits {
    fn default() -> Self {
        Self {
            max_steps: 1_000_000,
            max_stack_depth: 1_000,
        }
    }
}

/// Logical resource use of a terminal, authoritative execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExecutionUsage {
    pub steps: u64,
    pub peak_stack_depth: u64,
}

/// A successful return. `value` is the owned Marrow ABI object that occupied
/// the entry function's return register.
pub struct CompletedExecution {
    pub value: Obj,
    pub usage: ExecutionUsage,
}

impl fmt::Debug for CompletedExecution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CompletedExecution")
            .field("value_kind", &value_kind(&self.value))
            .field("usage", &self.usage)
            .finish()
    }
}

/// A fully determined execution result. Refusal and user panic are completed
/// domain answers; only cancellation/resource/internal failure live outside
/// this enum in [`Outcome`].
#[derive(Debug)]
pub enum VmExit {
    Returned(CompletedExecution),
    Panicked {
        message: String,
        usage: ExecutionUsage,
    },
    Refused {
        refusal: VmRefusal,
        usage: ExecutionUsage,
    },
}

/// Runtime object category, derived directly from the ABI header/tagged word.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueKind {
    Scalar,
    Ctor(u8),
    Promise,
    Closure,
    Array,
    StructArray,
    ScalarArray,
    String,
    Mpz,
    Thunk,
    Task,
    Ref,
    External,
    Reserved,
}

/// A completed refusal: the bytecode was structurally valid, but a dynamic
/// value or requested host row did not satisfy the operation contract.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VmRefusal {
    UnknownIntrinsic {
        row: String,
    },
    UnsupportedIntrinsic {
        row: String,
    },
    IntrinsicArity {
        row: String,
        expected: usize,
        actual: usize,
    },
    IntrinsicOwnershipContract {
        row: String,
        reason: String,
    },
    IntrinsicOwnershipMismatch {
        row: String,
        argument: usize,
        expected: ArgumentOwnership,
        actual: ArgumentOwnership,
    },
    IntrinsicResultOwnershipMismatch {
        row: String,
        expected: ResultOwnership,
        actual: ResultOwnership,
    },
    IntrinsicResultImplementationMismatch {
        row: String,
        expected: ResultOwnership,
        actual: ResultOwnership,
    },
    IntrinsicResultKind {
        row: String,
        expected: &'static str,
        actual: ValueKind,
    },
    CallResultOwnershipMismatch {
        function: FunctionId,
        expected: CallableResultOwnership,
        actual: CallableResultOwnership,
    },
    ApplyResultOwnershipMismatch {
        function: FunctionId,
        expected: CallableResultOwnership,
        actual: CallableResultOwnership,
    },
    CallableResultKind {
        function: FunctionId,
        expected: CallableResultOwnership,
        actual: ValueKind,
    },
    ApplyOwnershipMismatch {
        function: FunctionId,
        argument: usize,
        expected: ArgumentOwnership,
        actual: ArgumentOwnership,
    },
    ApplyUniquePartial {
        function: FunctionId,
        argument: usize,
    },
    TypeMismatch {
        operation: &'static str,
        argument: usize,
        expected: &'static str,
        actual: ValueKind,
    },
    NatOverflow {
        operation: &'static str,
    },
    ArrayIndexOutOfBounds {
        index: usize,
        size: usize,
    },
    ConstructorProjectionTag {
        expected: u8,
        actual: ValueKind,
    },
    ConstructorProjectionShape {
        expected_fields: usize,
        actual_fields: usize,
    },
    InvalidStringObject,
    UnsupportedNativeClosure,
    MalformedClosure {
        reason: &'static str,
    },
    InvalidBoolScalar {
        operation: &'static str,
        argument: usize,
        value: usize,
    },
    ThunkForceInFlight,
    UnsupportedTaskState,
}

impl fmt::Display for VmRefusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownIntrinsic { row } => write!(f, "unknown intrinsic row {row:?}"),
            Self::UnsupportedIntrinsic { row } => {
                write!(f, "intrinsic row {row:?} has no prototype implementation")
            }
            Self::IntrinsicArity {
                row,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} received {actual} values, expected {expected}"
            ),
            Self::IntrinsicOwnershipContract { row, reason } => write!(
                f,
                "intrinsic row {row:?} has a non-executable ownership contract: {reason}"
            ),
            Self::IntrinsicOwnershipMismatch {
                row,
                argument,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} argument {argument} ownership is {}, generated contract requires {}",
                actual.token(),
                expected.token()
            ),
            Self::IntrinsicResultOwnershipMismatch {
                row,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} result ownership is {}, generated contract requires {}",
                actual.token(),
                expected.token()
            ),
            Self::IntrinsicResultImplementationMismatch {
                row,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} implementation produced a {} result, executable bytecode requires {}",
                actual.token(),
                expected.token()
            ),
            Self::IntrinsicResultKind {
                row,
                expected,
                actual,
            } => write!(
                f,
                "intrinsic row {row:?} result expected {expected}, got {actual:?}"
            ),
            Self::CallResultOwnershipMismatch {
                function,
                expected,
                actual,
            } => write!(
                f,
                "Call result ownership is {}, function {} requires {}",
                actual.token(),
                function.get(),
                expected.token()
            ),
            Self::ApplyResultOwnershipMismatch {
                function,
                expected,
                actual,
            } => write!(
                f,
                "Apply result ownership is {}, dynamic function {} requires {}",
                actual.token(),
                function.get(),
                expected.token()
            ),
            Self::CallableResultKind {
                function,
                expected,
                actual,
            } => write!(
                f,
                "function {} returned {actual:?}, contract requires {}",
                function.get(),
                expected.token()
            ),
            Self::ApplyOwnershipMismatch {
                function,
                argument,
                expected,
                actual,
            } => write!(
                f,
                "Apply argument {argument} ownership is {}, dynamic function {} requires {}",
                actual.token(),
                function.get(),
                expected.token()
            ),
            Self::ApplyUniquePartial { function, argument } => write!(
                f,
                "Apply argument {argument} for function {} is unique but under-application would retain it in a reusable closure",
                function.get()
            ),
            Self::TypeMismatch {
                operation,
                argument,
                expected,
                actual,
            } => write!(
                f,
                "{operation} argument {argument} expected {expected}, got {actual:?}"
            ),
            Self::NatOverflow { operation } => {
                write!(
                    f,
                    "{operation} result exceeds the prototype Nat scalar range"
                )
            }
            Self::ArrayIndexOutOfBounds { index, size } => {
                write!(f, "array index {index} is outside size {size}")
            }
            Self::ConstructorProjectionTag { expected, actual } => write!(
                f,
                "constructor projection expected tag {expected}, got {actual:?}"
            ),
            Self::ConstructorProjectionShape {
                expected_fields,
                actual_fields,
            } => write!(
                f,
                "constructor projection expected {expected_fields} object fields, got {actual_fields}"
            ),
            Self::InvalidStringObject => write!(f, "Marrow String object is not canonical UTF-8"),
            Self::UnsupportedNativeClosure => {
                write!(
                    f,
                    "native closure application requires the plugin trampoline"
                )
            }
            Self::MalformedClosure { reason } => {
                write!(f, "Golem closure shell is malformed: {reason}")
            }
            Self::InvalidBoolScalar {
                operation,
                argument,
                value,
            } => write!(
                f,
                "{operation} argument {argument} expected Bool scalar 0 or 1, got {value}"
            ),
            Self::ThunkForceInFlight => {
                write!(f, "thunk force is already in flight")
            }
            Self::UnsupportedTaskState => {
                write!(f, "scheduled or waiting task access is not implemented")
            }
        }
    }
}

impl std::error::Error for VmRefusal {}

/// Cooperative cancellation source. It is sampled before every instruction;
/// a true observation stops without executing or publishing that instruction.
pub trait CancellationProbe {
    fn is_cancelled(&self) -> bool;
}

impl<F> CancellationProbe for F
where
    F: Fn() -> bool,
{
    fn is_cancelled(&self) -> bool {
        self()
    }
}

struct Frame {
    function: FunctionId,
    pc: usize,
    registers: Vec<Option<Obj>>,
    return_to: Option<ReturnTo>,
}

enum ReturnTo {
    Store(Register),
    Apply {
        destination: Register,
        args: Vec<Obj>,
        argument_ownership: Vec<ArgumentOwnership>,
        result_ownership: CallableResultOwnership,
    },
    CompleteThunk {
        destination: Register,
        thunk: Obj,
        result_ownership: ResultOwnership,
    },
    CompleteManagerlessTask {
        destination: Register,
        completion: ManagerlessTaskCompletion,
        row: &'static str,
        result_ownership: ResultOwnership,
    },
}

enum PreparedApply {
    Partial {
        function: FunctionId,
        captures: Vec<Obj>,
    },
    Call {
        function: FunctionId,
        args: Vec<Obj>,
        remainder: Vec<Obj>,
        remainder_ownership: Vec<ArgumentOwnership>,
    },
}

struct ApplyPlan {
    function: FunctionId,
    captures: Vec<Obj>,
    required: usize,
}

enum ManagerlessTaskCompletion {
    WrapPure,
    RequireFinishedTask,
}

struct ManagerlessTaskApplication {
    row: &'static str,
    closure: Obj,
    argument: Obj,
    argument_ownership: ArgumentOwnership,
    completion: ManagerlessTaskCompletion,
}

struct IntrinsicResult {
    ownership: ResultOwnership,
    value: Obj,
}

impl IntrinsicResult {
    fn owned(value: Obj) -> Self {
        Self {
            ownership: ResultOwnership::Owned,
            value,
        }
    }

    fn borrowed_promoted(value: Obj) -> Self {
        Self {
            ownership: ResultOwnership::Borrowed,
            value,
        }
    }

    fn raw_object(value: Obj) -> Self {
        Self {
            ownership: ResultOwnership::RawObject,
            value,
        }
    }

    const fn ownership(&self) -> ResultOwnership {
        self.ownership
    }

    fn into_object(self) -> Obj {
        self.value
    }
}

enum Stop {
    Inconclusive(Inconclusive),
    InternalFault(InternalFault),
}

/// Execute a validated program. Non-authoritative paths contain no object
/// result, so a caller cannot accidentally cache a half-run register.
pub fn execute(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> Outcome<VmExit> {
    match run(program, limits, cancellation) {
        Ok(exit) => Outcome::Complete(exit),
        Err(Stop::Inconclusive(inconclusive)) => Outcome::Inconclusive(inconclusive),
        Err(Stop::InternalFault(fault)) => Outcome::InternalFault(fault),
    }
}

fn run(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    cancellation: Option<&dyn CancellationProbe>,
) -> Result<VmExit, Stop> {
    if limits.max_stack_depth < 1 {
        return Err(stack_exhausted(limits.max_stack_depth, 1, "entry frame"));
    }
    let entry = program.function(program.entry()).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-TARGET",
            "validated entry function disappeared",
        ))
    })?;
    let mut stack = vec![Frame {
        function: entry.id,
        pc: 0,
        registers: empty_registers(entry.register_count),
        return_to: None,
    }];
    let mut steps = 0u64;
    let mut peak_stack_depth = 1u64;

    loop {
        let frame = stack.last().ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-FRAME-STACK",
                "execution stack became empty without an entry return",
            ))
        })?;
        let function = program.function(frame.function).ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-VALIDATED-TARGET",
                format!(
                    "validated function {} disappeared during execution",
                    frame.function.get()
                ),
            ))
        })?;
        let instruction = function.code.get(frame.pc).cloned().ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-VALIDATED-PC",
                format!(
                    "function {} reached invalid pc {}",
                    frame.function.get(),
                    frame.pc
                ),
            ))
        })?;
        let location = format!("function {} pc {}", frame.function.get(), frame.pc);

        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Err(Stop::Inconclusive(
                Inconclusive::cancelled(location.clone()).with_progress(location),
            ));
        }
        let observed_steps = steps.checked_add(1).ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-RESOURCE-ACCOUNTING",
                "step counter overflowed",
            ))
        })?;
        if observed_steps > limits.max_steps {
            return Err(step_exhausted(limits.max_steps, observed_steps, &location));
        }
        steps = observed_steps;

        match instruction {
            Instruction::Nat { dst, value } => {
                let value = usize::try_from(value).map_err(|_| {
                    Stop::InternalFault(InternalFault::new(
                        "FLBC-VALIDATED-NAT",
                        "validated Nat constant does not fit the certified target",
                    ))
                })?;
                set_register(current_frame_mut(&mut stack)?, dst, Obj::mk_nat(value))?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::String { dst, value } => {
                set_register(current_frame_mut(&mut stack)?, dst, Obj::mk_string(&value))?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Copy { dst, src } => {
                let value = clone_register(current_frame(&stack)?, src)?;
                set_register(current_frame_mut(&mut stack)?, dst, value)?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Move { dst, src } => {
                if dst != src {
                    let value = take_register(current_frame_mut(&mut stack)?, src)?;
                    set_register(current_frame_mut(&mut stack)?, dst, value)?;
                }
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Drop { src } => {
                drop(take_register(current_frame_mut(&mut stack)?, src)?);
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Ctor {
                dst,
                tag,
                fields,
                scalar_bytes,
            } => {
                let values = clone_registers(current_frame(&stack)?, fields.iter().copied())?;
                set_register(
                    current_frame_mut(&mut stack)?,
                    dst,
                    Obj::mk_ctor(tag, values, &scalar_bytes),
                )?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::CtorField {
                dst,
                src,
                expected_tag,
                expected_fields,
                field,
            } => {
                let projected = {
                    let value = register(current_frame(&stack)?, src)?;
                    let actual = value_kind(value);
                    if actual != ValueKind::Ctor(expected_tag) {
                        return Ok(VmExit::Refused {
                            refusal: VmRefusal::ConstructorProjectionTag {
                                expected: expected_tag,
                                actual,
                            },
                            usage: usage(steps, peak_stack_depth),
                        });
                    }
                    let actual_fields = usize::from(value.header().other);
                    let expected_fields = usize::from(expected_fields);
                    if actual_fields != expected_fields {
                        return Ok(VmExit::Refused {
                            refusal: VmRefusal::ConstructorProjectionShape {
                                expected_fields,
                                actual_fields,
                            },
                            usage: usage(steps, peak_stack_depth),
                        });
                    }
                    value.ctor_child(usize::from(field))
                };
                set_register(current_frame_mut(&mut stack)?, dst, projected)?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Array { dst, items } => {
                let values = clone_registers(current_frame(&stack)?, items.iter().copied())?;
                set_register(current_frame_mut(&mut stack)?, dst, Obj::mk_array(values))?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Intrinsic {
                dst,
                row,
                args,
                argument_ownership,
                result_ownership,
            } => {
                let expected_arguments = match generated_argument_ownership(&row, args.len()) {
                    Ok(expected) => expected,
                    Err(refusal) => {
                        return Ok(VmExit::Refused {
                            refusal,
                            usage: usage(steps, peak_stack_depth),
                        });
                    }
                };
                if let Some((argument, (expected, actual))) = expected_arguments
                    .iter()
                    .copied()
                    .zip(argument_ownership.iter().copied())
                    .enumerate()
                    .find(|(_, (expected, actual))| expected != actual)
                {
                    return Ok(VmExit::Refused {
                        refusal: VmRefusal::IntrinsicOwnershipMismatch {
                            row,
                            argument,
                            expected,
                            actual,
                        },
                        usage: usage(steps, peak_stack_depth),
                    });
                }
                let expected_result = match generated_result_ownership(&row) {
                    Ok(expected) => expected,
                    Err(refusal) => {
                        return Ok(VmExit::Refused {
                            refusal,
                            usage: usage(steps, peak_stack_depth),
                        });
                    }
                };
                if expected_result != result_ownership {
                    return Ok(VmExit::Refused {
                        refusal: VmRefusal::IntrinsicResultOwnershipMismatch {
                            row,
                            expected: expected_result,
                            actual: result_ownership,
                        },
                        usage: usage(steps, peak_stack_depth),
                    });
                }
                let values = transfer_intrinsic_arguments(
                    current_frame_mut(&mut stack)?,
                    &args,
                    &argument_ownership,
                )?;
                if row == "extern:Thunk.get" {
                    let thunk = match delayed_thunk_operand(values) {
                        Ok(thunk) => thunk,
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    };
                    if let Some(value) = thunk.evaluated_thunk_value() {
                        let value = match finish_intrinsic_result(
                            &row,
                            result_ownership,
                            IntrinsicResult::owned(value),
                        ) {
                            Ok(value) => value,
                            Err(refusal) => {
                                return Ok(VmExit::Refused {
                                    refusal,
                                    usage: usage(steps, peak_stack_depth),
                                });
                            }
                        };
                        set_register(current_frame_mut(&mut stack)?, dst, value)?;
                        advance(current_frame_mut(&mut stack)?)?;
                    } else {
                        let closure = match thunk.claim_thunk_closure() {
                            Some(closure) => closure,
                            None => {
                                return Ok(VmExit::Refused {
                                    refusal: VmRefusal::ThunkForceInFlight,
                                    usage: usage(steps, peak_stack_depth),
                                });
                            }
                        };
                        match prepare_internal_apply(
                            program,
                            &closure,
                            Obj::mk_nat(0),
                            ArgumentOwnership::Scalar,
                        ) {
                            Ok(PreparedApply::Partial { function, captures }) => {
                                let value = make_golem_closure(program, function, captures)?;
                                let value = match finish_intrinsic_result(
                                    &row,
                                    result_ownership,
                                    IntrinsicResult::owned(value),
                                ) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                                cache_thunk_value(&thunk, &value)?;
                                set_register(current_frame_mut(&mut stack)?, dst, value)?;
                                advance(current_frame_mut(&mut stack)?)?;
                            }
                            Ok(PreparedApply::Call {
                                function,
                                args,
                                remainder,
                                remainder_ownership: _,
                            }) => {
                                if !remainder.is_empty() {
                                    return Err(Stop::InternalFault(InternalFault::new(
                                        "FLBC-THUNK-APPLY",
                                        "one Unit argument over-applied a validated closure",
                                    )));
                                }
                                advance(current_frame_mut(&mut stack)?)?;
                                let next_depth = push_call(
                                    program,
                                    &mut stack,
                                    function,
                                    args,
                                    ReturnTo::CompleteThunk {
                                        destination: dst,
                                        thunk,
                                        result_ownership,
                                    },
                                    limits.max_stack_depth,
                                    &location,
                                )?;
                                peak_stack_depth = peak_stack_depth.max(next_depth);
                            }
                            Err(refusal) => {
                                return Ok(VmExit::Refused {
                                    refusal,
                                    usage: usage(steps, peak_stack_depth),
                                });
                            }
                        }
                    }
                } else if is_managerless_task_row(&row) {
                    let application = match managerless_task_application(&row, values) {
                        Ok(application) => application,
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    };
                    match prepare_internal_apply(
                        program,
                        &application.closure,
                        application.argument,
                        application.argument_ownership,
                    ) {
                        Ok(PreparedApply::Partial { function, captures }) => {
                            let value = make_golem_closure(program, function, captures)?;
                            let value =
                                match complete_managerless_task(application.completion, value) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                            let value = match finish_intrinsic_result(
                                application.row,
                                result_ownership,
                                IntrinsicResult::owned(value),
                            ) {
                                Ok(value) => value,
                                Err(refusal) => {
                                    return Ok(VmExit::Refused {
                                        refusal,
                                        usage: usage(steps, peak_stack_depth),
                                    });
                                }
                            };
                            set_register(current_frame_mut(&mut stack)?, dst, value)?;
                            advance(current_frame_mut(&mut stack)?)?;
                        }
                        Ok(PreparedApply::Call {
                            function,
                            args,
                            remainder,
                            remainder_ownership: _,
                        }) => {
                            if !remainder.is_empty() {
                                return Err(Stop::InternalFault(InternalFault::new(
                                    "FLBC-TASK-APPLY",
                                    "one managerless task argument over-applied a validated closure",
                                )));
                            }
                            advance(current_frame_mut(&mut stack)?)?;
                            let next_depth = push_call(
                                program,
                                &mut stack,
                                function,
                                args,
                                ReturnTo::CompleteManagerlessTask {
                                    destination: dst,
                                    completion: application.completion,
                                    row: application.row,
                                    result_ownership,
                                },
                                limits.max_stack_depth,
                                &location,
                            )?;
                            peak_stack_depth = peak_stack_depth.max(next_depth);
                        }
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    }
                } else {
                    match invoke_intrinsic(&row, &values) {
                        Ok(result) => {
                            let value =
                                match finish_intrinsic_result(&row, result_ownership, result) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                            set_register(current_frame_mut(&mut stack)?, dst, value)?;
                            advance(current_frame_mut(&mut stack)?)?;
                        }
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    }
                }
            }
            Instruction::Call {
                dst,
                function,
                args,
                argument_ownership,
                result_ownership,
            } => {
                let callee = program.function(function).ok_or_else(|| {
                    Stop::InternalFault(InternalFault::new(
                        "FLBC-VALIDATED-TARGET",
                        format!("validated call target {} disappeared", function.get()),
                    ))
                })?;
                if callee.parameter_ownership != argument_ownership {
                    return Err(Stop::InternalFault(InternalFault::new(
                        "FLBC-CALL-OWNERSHIP",
                        format!(
                            "validated call to function {} disagrees with its parameter ownership",
                            function.get()
                        ),
                    )));
                }
                if callee.result_ownership != result_ownership {
                    return Ok(VmExit::Refused {
                        refusal: VmRefusal::CallResultOwnershipMismatch {
                            function,
                            expected: callee.result_ownership,
                            actual: result_ownership,
                        },
                        usage: usage(steps, peak_stack_depth),
                    });
                }
                let values = transfer_call_arguments(
                    current_frame_mut(&mut stack)?,
                    &args,
                    &argument_ownership,
                )?;
                advance(current_frame_mut(&mut stack)?)?;
                let next_depth = push_call(
                    program,
                    &mut stack,
                    function,
                    values,
                    ReturnTo::Store(dst),
                    limits.max_stack_depth,
                    &location,
                )?;
                peak_stack_depth = peak_stack_depth.max(next_depth);
            }
            Instruction::Closure {
                dst,
                function,
                captures,
                capture_ownership,
            } => {
                let callee = program.function(function).ok_or_else(|| {
                    Stop::InternalFault(InternalFault::new(
                        "FLBC-VALIDATED-TARGET",
                        format!("validated closure target {} disappeared", function.get()),
                    ))
                })?;
                let Some(expected) = callee.parameter_ownership.get(..captures.len()) else {
                    return Err(Stop::InternalFault(InternalFault::new(
                        "FLBC-CLOSURE-OWNERSHIP",
                        "validated closure capture count exceeds the target parameter contract",
                    )));
                };
                if expected != capture_ownership {
                    return Err(Stop::InternalFault(InternalFault::new(
                        "FLBC-CLOSURE-OWNERSHIP",
                        format!(
                            "validated closure for function {} disagrees with its capture ownership",
                            function.get()
                        ),
                    )));
                }
                if capture_ownership.contains(&ArgumentOwnership::Unique) {
                    return Err(Stop::InternalFault(InternalFault::new(
                        "FLBC-CLOSURE-OWNERSHIP",
                        "validated reusable closure carries a unique capture",
                    )));
                }
                let captures = transfer_closure_captures(
                    current_frame_mut(&mut stack)?,
                    &captures,
                    &capture_ownership,
                )?;
                let closure = make_golem_closure(program, function, captures)?;
                set_register(current_frame_mut(&mut stack)?, dst, closure)?;
                advance(current_frame_mut(&mut stack)?)?;
            }
            Instruction::Apply {
                dst,
                closure,
                args,
                argument_ownership,
                result_ownership,
            } => {
                let closure = clone_register(current_frame(&stack)?, closure)?;
                let plan = match plan_apply(
                    program,
                    &closure,
                    args.len(),
                    Some(&argument_ownership),
                    Some(result_ownership),
                ) {
                    Ok(plan) => plan,
                    Err(refusal) => {
                        return Ok(VmExit::Refused {
                            refusal,
                            usage: usage(steps, peak_stack_depth),
                        });
                    }
                };
                let args = transfer_apply_arguments(
                    current_frame_mut(&mut stack)?,
                    &args,
                    &argument_ownership,
                )?;
                match finish_apply(plan, args, Some(argument_ownership)) {
                    PreparedApply::Partial { function, captures } => {
                        let value = make_golem_closure(program, function, captures)?;
                        set_register(current_frame_mut(&mut stack)?, dst, value)?;
                        advance(current_frame_mut(&mut stack)?)?;
                    }
                    PreparedApply::Call {
                        function,
                        args,
                        remainder,
                        remainder_ownership,
                    } => {
                        let return_to = if remainder.is_empty() {
                            ReturnTo::Store(dst)
                        } else {
                            ReturnTo::Apply {
                                destination: dst,
                                args: remainder,
                                argument_ownership: remainder_ownership,
                                result_ownership,
                            }
                        };
                        advance(current_frame_mut(&mut stack)?)?;
                        let next_depth = push_call(
                            program,
                            &mut stack,
                            function,
                            args,
                            return_to,
                            limits.max_stack_depth,
                            &location,
                        )?;
                        peak_stack_depth = peak_stack_depth.max(next_depth);
                    }
                }
            }
            Instruction::Jump { target } => {
                current_frame_mut(&mut stack)?.pc =
                    usize::try_from(target.get()).map_err(|_| {
                        Stop::InternalFault(InternalFault::new(
                            "FLBC-VALIDATED-PC",
                            "validated jump target does not fit usize",
                        ))
                    })?;
            }
            Instruction::JumpIfZero {
                cond,
                zero,
                nonzero,
            } => {
                let frame = current_frame(&stack)?;
                let condition = register(frame, cond)?;
                if !condition.is_scalar() {
                    return Ok(VmExit::Refused {
                        refusal: type_mismatch("jump_if_zero", 0, "Nat scalar", condition),
                        usage: usage(steps, peak_stack_depth),
                    });
                }
                let target = if condition.unbox() == 0 {
                    zero
                } else {
                    nonzero
                };
                current_frame_mut(&mut stack)?.pc =
                    usize::try_from(target.get()).map_err(|_| {
                        Stop::InternalFault(InternalFault::new(
                            "FLBC-VALIDATED-PC",
                            "validated branch target does not fit usize",
                        ))
                    })?;
            }
            Instruction::Return { src } => {
                let value = take_register(current_frame_mut(&mut stack)?, src)?;
                let value =
                    match finish_callable_result(function.id, function.result_ownership, value) {
                        Ok(value) => value,
                        Err(refusal) => {
                            return Ok(VmExit::Refused {
                                refusal,
                                usage: usage(steps, peak_stack_depth),
                            });
                        }
                    };
                let finished = stack.pop().ok_or_else(|| {
                    Stop::InternalFault(InternalFault::new(
                        "FLBC-FRAME-STACK",
                        "return observed an empty execution stack",
                    ))
                })?;
                match finished.return_to {
                    None => {
                        if !stack.is_empty() {
                            return Err(Stop::InternalFault(InternalFault::new(
                                "FLBC-FRAME-RETURN",
                                "non-entry frame has no return action",
                            )));
                        }
                        return Ok(VmExit::Returned(CompletedExecution {
                            value,
                            usage: usage(steps, peak_stack_depth),
                        }));
                    }
                    Some(return_to) => {
                        if stack.is_empty() {
                            return Err(Stop::InternalFault(InternalFault::new(
                                "FLBC-FRAME-RETURN",
                                "entry frame unexpectedly has a return action",
                            )));
                        }
                        match return_to {
                            ReturnTo::Store(destination) => {
                                set_register(current_frame_mut(&mut stack)?, destination, value)?;
                            }
                            ReturnTo::Apply {
                                destination,
                                args,
                                argument_ownership,
                                result_ownership,
                            } => {
                                match prepare_owned_apply(
                                    program,
                                    &value,
                                    args,
                                    argument_ownership,
                                    result_ownership,
                                ) {
                                    Ok(PreparedApply::Partial { function, captures }) => {
                                        let closure =
                                            make_golem_closure(program, function, captures)?;
                                        set_register(
                                            current_frame_mut(&mut stack)?,
                                            destination,
                                            closure,
                                        )?;
                                    }
                                    Ok(PreparedApply::Call {
                                        function,
                                        args,
                                        remainder,
                                        remainder_ownership,
                                    }) => {
                                        let return_to = if remainder.is_empty() {
                                            ReturnTo::Store(destination)
                                        } else {
                                            ReturnTo::Apply {
                                                destination,
                                                args: remainder,
                                                argument_ownership: remainder_ownership,
                                                result_ownership,
                                            }
                                        };
                                        let next_depth = push_call(
                                            program,
                                            &mut stack,
                                            function,
                                            args,
                                            return_to,
                                            limits.max_stack_depth,
                                            &location,
                                        )?;
                                        peak_stack_depth = peak_stack_depth.max(next_depth);
                                    }
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                }
                            }
                            ReturnTo::CompleteThunk {
                                destination,
                                thunk,
                                result_ownership,
                            } => {
                                let value = match finish_intrinsic_result(
                                    "extern:Thunk.get",
                                    result_ownership,
                                    IntrinsicResult::owned(value),
                                ) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                                cache_thunk_value(&thunk, &value)?;
                                set_register(current_frame_mut(&mut stack)?, destination, value)?;
                            }
                            ReturnTo::CompleteManagerlessTask {
                                destination,
                                completion,
                                row,
                                result_ownership,
                            } => {
                                let value = match complete_managerless_task(completion, value) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                                let value = match finish_intrinsic_result(
                                    row,
                                    result_ownership,
                                    IntrinsicResult::owned(value),
                                ) {
                                    Ok(value) => value,
                                    Err(refusal) => {
                                        return Ok(VmExit::Refused {
                                            refusal,
                                            usage: usage(steps, peak_stack_depth),
                                        });
                                    }
                                };
                                set_register(current_frame_mut(&mut stack)?, destination, value)?;
                            }
                        }
                    }
                }
            }
            Instruction::Panic { message } => {
                let message = string_value(register(current_frame(&stack)?, message)?, "panic", 0);
                return match message {
                    Ok(message) => Ok(VmExit::Panicked {
                        message,
                        usage: usage(steps, peak_stack_depth),
                    }),
                    Err(refusal) => Ok(VmExit::Refused {
                        refusal,
                        usage: usage(steps, peak_stack_depth),
                    }),
                };
            }
        }
    }
}

fn make_golem_closure(
    program: &ValidatedProgram,
    function: FunctionId,
    captures: Vec<Obj>,
) -> Result<Obj, Stop> {
    let callee = program.function(function).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-TARGET",
            format!(
                "validated closure target {} disappeared during execution",
                function.get()
            ),
        ))
    })?;
    if captures.len() >= usize::from(callee.arity) {
        return Err(Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-CLOSURE",
            format!(
                "closure target {} has {} captures for arity {}",
                function.get(),
                captures.len(),
                callee.arity
            ),
        )));
    }
    let encoded_arity = callee.arity.checked_add(1).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-CLOSURE",
            "validated closure arity cannot encode the target word",
        ))
    })?;
    let target_word = usize::try_from(function.get()).map_err(|_| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-CLOSURE-TARGET",
            "function id does not fit the target word",
        ))
    })?;
    if target_word > usize::MAX >> 1 {
        return Err(Stop::InternalFault(InternalFault::new(
            "FLBC-CLOSURE-TARGET",
            "function id does not fit a Marrow Nat scalar",
        )));
    }
    let mut fixed = Vec::with_capacity(captures.len() + 1);
    fixed.push(Obj::mk_nat(target_word));
    fixed.extend(captures);
    Ok(Obj::mk_closure(encoded_arity, fixed))
}

fn prepare_internal_apply(
    program: &ValidatedProgram,
    closure: &Obj,
    argument: Obj,
    argument_ownership: ArgumentOwnership,
) -> Result<PreparedApply, VmRefusal> {
    let ownership = [argument_ownership];
    let plan = plan_apply(program, closure, 1, Some(&ownership), None)?;
    Ok(finish_apply(plan, vec![argument], Some(ownership.into())))
}

fn prepare_owned_apply(
    program: &ValidatedProgram,
    closure: &Obj,
    args: Vec<Obj>,
    argument_ownership: Vec<ArgumentOwnership>,
    result_ownership: CallableResultOwnership,
) -> Result<PreparedApply, VmRefusal> {
    let plan = plan_apply(
        program,
        closure,
        args.len(),
        Some(&argument_ownership),
        Some(result_ownership),
    )?;
    Ok(finish_apply(plan, args, Some(argument_ownership)))
}

fn plan_apply(
    program: &ValidatedProgram,
    closure: &Obj,
    argument_count: usize,
    argument_ownership: Option<&[ArgumentOwnership]>,
    result_ownership: Option<CallableResultOwnership>,
) -> Result<ApplyPlan, VmRefusal> {
    if value_kind(closure) != ValueKind::Closure {
        return Err(type_mismatch("apply", 0, "Golem closure", closure));
    }
    let Some((encoded_arity, fixed)) = closure.closure_shell_parts() else {
        return Err(VmRefusal::UnsupportedNativeClosure);
    };
    let mut fixed = fixed.into_iter();
    let target_word = fixed.next().ok_or(VmRefusal::MalformedClosure {
        reason: "missing target word",
    })?;
    if !target_word.is_scalar() {
        return Err(VmRefusal::MalformedClosure {
            reason: "target word is not a Nat scalar",
        });
    }
    let raw_function =
        u32::try_from(target_word.unbox()).map_err(|_| VmRefusal::MalformedClosure {
            reason: "target word is outside the FunctionId range",
        })?;
    let function = FunctionId::new(raw_function);
    let callee = program
        .function(function)
        .ok_or(VmRefusal::MalformedClosure {
            reason: "target function is absent",
        })?;
    if callee.arity.checked_add(1) != Some(encoded_arity) {
        return Err(VmRefusal::MalformedClosure {
            reason: "encoded arity does not match the target function",
        });
    }

    let captures: Vec<Obj> = fixed.collect();
    if captures.len() >= usize::from(callee.arity) {
        return Err(VmRefusal::MalformedClosure {
            reason: "fixed arguments exhaust the target arity",
        });
    }
    let required = usize::from(callee.arity) - captures.len();
    let expected_result_ownership = if argument_count < required {
        CallableResultOwnership::Owned
    } else {
        callee.result_ownership
    };
    if let Some(actual) = result_ownership
        && argument_count <= required
        && actual != expected_result_ownership
    {
        return Err(VmRefusal::ApplyResultOwnershipMismatch {
            function,
            expected: expected_result_ownership,
            actual,
        });
    }
    if argument_count > required && callee.result_ownership != CallableResultOwnership::Owned {
        return Err(VmRefusal::ApplyResultOwnershipMismatch {
            function,
            expected: CallableResultOwnership::Owned,
            actual: callee.result_ownership,
        });
    }
    if let Some(actual) = argument_ownership {
        let segment = argument_count.min(required);
        let expected =
            &callee.parameter_ownership[captures.len()..captures.len().saturating_add(segment)];
        if let Some((argument, (expected, actual))) = expected
            .iter()
            .copied()
            .zip(actual.iter().copied())
            .enumerate()
            .find(|(_, (expected, actual))| expected != actual)
        {
            return Err(VmRefusal::ApplyOwnershipMismatch {
                function,
                argument,
                expected,
                actual,
            });
        }
        if argument_count < required
            && let Some(argument) = actual
                .iter()
                .position(|disposition| *disposition == ArgumentOwnership::Unique)
        {
            return Err(VmRefusal::ApplyUniquePartial { function, argument });
        }
    }
    Ok(ApplyPlan {
        function,
        captures,
        required,
    })
}

fn finish_apply(
    plan: ApplyPlan,
    args: Vec<Obj>,
    argument_ownership: Option<Vec<ArgumentOwnership>>,
) -> PreparedApply {
    let ApplyPlan {
        function,
        mut captures,
        required,
    } = plan;
    if args.len() < required {
        captures.extend(args);
        return PreparedApply::Partial { function, captures };
    }

    let mut args = args.into_iter();
    captures.extend(args.by_ref().take(required));
    let remainder_ownership = argument_ownership
        .map(|ownership| ownership.into_iter().skip(required).collect())
        .unwrap_or_default();
    PreparedApply::Call {
        function,
        args: captures,
        remainder: args.collect(),
        remainder_ownership,
    }
}

fn push_call(
    program: &ValidatedProgram,
    stack: &mut Vec<Frame>,
    function: FunctionId,
    args: Vec<Obj>,
    return_to: ReturnTo,
    max_stack_depth: u64,
    location: &str,
) -> Result<u64, Stop> {
    let next_len = stack.len().checked_add(1).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-RESOURCE-ACCOUNTING",
            "stack length overflowed",
        ))
    })?;
    let next_depth = u64::try_from(next_len).map_err(|_| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-RESOURCE-ACCOUNTING",
            "stack depth does not fit the resource counter",
        ))
    })?;
    if next_depth > max_stack_depth {
        return Err(stack_exhausted(max_stack_depth, next_depth, location));
    }
    let callee = program.function(function).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-TARGET",
            format!("validated call target {} disappeared", function.get()),
        ))
    })?;
    if args.len() != usize::from(callee.arity) {
        return Err(Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-ARITY",
            format!(
                "function {} received {} arguments after validation, expected {}",
                function.get(),
                args.len(),
                callee.arity
            ),
        )));
    }
    let mut registers = empty_registers(callee.register_count);
    for (slot, value) in registers.iter_mut().zip(args) {
        *slot = Some(value);
    }
    stack.push(Frame {
        function,
        pc: 0,
        registers,
        return_to: Some(return_to),
    });
    Ok(next_depth)
}

fn current_frame(stack: &[Frame]) -> Result<&Frame, Stop> {
    stack.last().ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-FRAME-STACK",
            "execution attempted to read an empty frame stack",
        ))
    })
}

fn current_frame_mut(stack: &mut [Frame]) -> Result<&mut Frame, Stop> {
    stack.last_mut().ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-FRAME-STACK",
            "execution attempted to mutate an empty frame stack",
        ))
    })
}

fn empty_registers(count: u16) -> Vec<Option<Obj>> {
    std::iter::repeat_with(|| None)
        .take(usize::from(count))
        .collect()
}

fn usage(steps: u64, peak_stack_depth: u64) -> ExecutionUsage {
    ExecutionUsage {
        steps,
        peak_stack_depth,
    }
}

fn step_exhausted(allowed: u64, observed: u64, location: &str) -> Stop {
    Stop::Inconclusive(
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::Heartbeats {
                consumed: observed,
                limit: allowed,
            },
            allowed,
            observed,
        })
        .with_progress(location),
    )
}

fn stack_exhausted(allowed: u64, observed: u64, location: &str) -> Stop {
    Stop::Inconclusive(
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::RecursionDepth { limit: allowed },
            allowed,
            observed,
        })
        .with_progress(location),
    )
}

fn advance(frame: &mut Frame) -> Result<(), Stop> {
    frame.pc = frame.pc.checked_add(1).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-PC",
            "program counter overflowed",
        ))
    })?;
    Ok(())
}

fn register(frame: &Frame, register: Register) -> Result<&Obj, Stop> {
    frame
        .registers
        .get(register.index())
        .and_then(Option::as_ref)
        .ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-VALIDATED-REGISTER",
                format!(
                    "function {} pc {} read missing register {}",
                    frame.function.get(),
                    frame.pc,
                    register.get()
                ),
            ))
        })
}

fn clone_register(frame: &Frame, register_id: Register) -> Result<Obj, Stop> {
    register(frame, register_id).map(Obj::clone_ref)
}

fn clone_registers(
    frame: &Frame,
    registers: impl IntoIterator<Item = Register>,
) -> Result<Vec<Obj>, Stop> {
    registers
        .into_iter()
        .map(|register_id| clone_register(frame, register_id))
        .collect()
}

fn generated_argument_ownership(
    row: &str,
    argument_count: usize,
) -> Result<Vec<ArgumentOwnership>, VmRefusal> {
    let generated = EXTERN_ROWS
        .iter()
        .find(|generated| generated.id == row)
        .ok_or_else(|| VmRefusal::UnknownIntrinsic {
            row: row.to_string(),
        })?;
    let parsed = ExternOwnership::parse(generated.ownership)
        .and_then(|ownership| ownership.argument_ownership(argument_count))
        .map_err(|error| VmRefusal::IntrinsicOwnershipContract {
            row: row.to_string(),
            reason: error.message().to_string(),
        })?;
    let mut ownership = Vec::new();
    ownership.try_reserve_exact(parsed.len()).map_err(|_| {
        VmRefusal::IntrinsicOwnershipContract {
            row: row.to_string(),
            reason: format!(
                "could not reserve {} executable ownership dispositions",
                parsed.len()
            ),
        }
    })?;
    ownership.extend(parsed.into_iter().map(|disposition| match disposition {
        ContractArgumentOwnership::Borrowed => ArgumentOwnership::Borrowed,
        ContractArgumentOwnership::Owned => ArgumentOwnership::Owned,
        ContractArgumentOwnership::Unique => ArgumentOwnership::Unique,
        ContractArgumentOwnership::Scalar => ArgumentOwnership::Scalar,
    }));
    Ok(ownership)
}

fn generated_result_ownership(row: &str) -> Result<ResultOwnership, VmRefusal> {
    let generated = EXTERN_ROWS
        .iter()
        .find(|generated| generated.id == row)
        .ok_or_else(|| VmRefusal::UnknownIntrinsic {
            row: row.to_string(),
        })?;
    let ownership = ExternOwnership::parse(generated.ownership)
        .and_then(|ownership| ownership.result_ownership())
        .map_err(|error| VmRefusal::IntrinsicOwnershipContract {
            row: row.to_string(),
            reason: error.message().to_string(),
        })?;
    Ok(match ownership {
        ContractResultOwnership::Owned => ResultOwnership::Owned,
        ContractResultOwnership::Borrowed => ResultOwnership::Borrowed,
        ContractResultOwnership::Scalar => ResultOwnership::Scalar,
        ContractResultOwnership::RawObject => ResultOwnership::RawObject,
    })
}

fn finish_intrinsic_result(
    row: &str,
    expected: ResultOwnership,
    result: IntrinsicResult,
) -> Result<Obj, VmRefusal> {
    let actual = result.ownership();
    if actual != expected {
        return Err(VmRefusal::IntrinsicResultImplementationMismatch {
            row: row.to_string(),
            expected,
            actual,
        });
    }
    let value = result.into_object();
    if expected == ResultOwnership::Scalar && !value.is_scalar() {
        return Err(VmRefusal::IntrinsicResultKind {
            row: row.to_string(),
            expected: "tagged scalar",
            actual: value_kind(&value),
        });
    }
    Ok(value)
}

fn finish_callable_result(
    function: FunctionId,
    expected: CallableResultOwnership,
    value: Obj,
) -> Result<Obj, VmRefusal> {
    let matches = match expected {
        CallableResultOwnership::Owned => !value.is_scalar(),
        CallableResultOwnership::Scalar => value.is_scalar(),
    };
    if !matches {
        return Err(VmRefusal::CallableResultKind {
            function,
            expected,
            actual: value_kind(&value),
        });
    }
    Ok(value)
}

fn transfer_intrinsic_arguments(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<Vec<Obj>, Stop> {
    transfer_arguments(
        frame,
        registers,
        ownership,
        "FLBC-INTRINSIC-ARGUMENTS",
        "intrinsic",
    )
}

fn transfer_call_arguments(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<Vec<Obj>, Stop> {
    transfer_arguments(
        frame,
        registers,
        ownership,
        "FLBC-CALL-ARGUMENTS",
        "direct-call",
    )
}

fn transfer_closure_captures(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<Vec<Obj>, Stop> {
    transfer_arguments(
        frame,
        registers,
        ownership,
        "FLBC-CLOSURE-CAPTURES",
        "closure capture",
    )
}

fn transfer_apply_arguments(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
) -> Result<Vec<Obj>, Stop> {
    transfer_arguments(frame, registers, ownership, "FLBC-APPLY-ARGUMENTS", "Apply")
}

fn transfer_arguments(
    frame: &mut Frame,
    registers: &[Register],
    ownership: &[ArgumentOwnership],
    fault_code: &'static str,
    boundary: &'static str,
) -> Result<Vec<Obj>, Stop> {
    let mut borrowed = Vec::new();
    borrowed.try_reserve_exact(registers.len()).map_err(|_| {
        Stop::InternalFault(InternalFault::new(
            fault_code,
            format!(
                "could not reserve {} borrowed {boundary} argument slots",
                registers.len()
            ),
        ))
    })?;
    borrowed.resize_with(registers.len(), || None::<Obj>);
    for (index, (register_id, disposition)) in registers
        .iter()
        .copied()
        .zip(ownership.iter().copied())
        .enumerate()
    {
        if !disposition.consumes() {
            borrowed[index] = Some(clone_register(frame, register_id)?);
        }
    }
    for (register_id, disposition) in registers.iter().copied().zip(ownership.iter().copied()) {
        if disposition.consumes() {
            register(frame, register_id)?;
        }
    }

    let mut values = Vec::new();
    values.try_reserve_exact(registers.len()).map_err(|_| {
        Stop::InternalFault(InternalFault::new(
            fault_code,
            format!(
                "could not reserve {} transferred {boundary} arguments",
                registers.len()
            ),
        ))
    })?;
    for (index, (register_id, disposition)) in registers
        .iter()
        .copied()
        .zip(ownership.iter().copied())
        .enumerate()
    {
        if disposition.consumes() {
            values.push(take_register(frame, register_id)?);
        } else {
            values.push(borrowed[index].take().ok_or_else(|| {
                Stop::InternalFault(InternalFault::new(
                    fault_code,
                    format!("borrowed {boundary} argument {index} was not prepared"),
                ))
            })?);
        }
    }
    Ok(values)
}

fn take_register(frame: &mut Frame, register: Register) -> Result<Obj, Stop> {
    frame
        .registers
        .get_mut(register.index())
        .and_then(Option::take)
        .ok_or_else(|| {
            Stop::InternalFault(InternalFault::new(
                "FLBC-VALIDATED-REGISTER",
                format!(
                    "function {} pc {} moved missing register {}",
                    frame.function.get(),
                    frame.pc,
                    register.get()
                ),
            ))
        })
}

fn set_register(frame: &mut Frame, register: Register, value: Obj) -> Result<(), Stop> {
    let slot = frame.registers.get_mut(register.index()).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-VALIDATED-REGISTER",
            format!(
                "function {} pc {} wrote missing register {}",
                frame.function.get(),
                frame.pc,
                register.get()
            ),
        ))
    })?;
    *slot = Some(value);
    Ok(())
}

fn invoke_intrinsic(row: &str, args: &[Obj]) -> Result<IntrinsicResult, VmRefusal> {
    ensure_intrinsic_row(row)?;
    match row {
        "extern:Nat.add" => {
            expect_arity(row, args, 2)?;
            let lhs = nat_value(&args[0], "Nat.add", 0)?;
            let rhs = nat_value(&args[1], "Nat.add", 1)?;
            let sum = lhs.checked_add(rhs).ok_or(VmRefusal::NatOverflow {
                operation: "Nat.add",
            })?;
            if sum > usize::MAX >> 1 {
                return Err(VmRefusal::NatOverflow {
                    operation: "Nat.add",
                });
            }
            Ok(IntrinsicResult::owned(Obj::mk_nat(sum)))
        }
        "extern:String.append" => {
            expect_arity(row, args, 2)?;
            let mut lhs = string_value(&args[0], "String.append", 0)?;
            lhs.push_str(&string_value(&args[1], "String.append", 1)?);
            Ok(IntrinsicResult::owned(Obj::mk_string(&lhs)))
        }
        "extern:Array.size" => {
            expect_arity(row, args, 1)?;
            let (size, _) = array_value(&args[0], "Array.size", 0)?;
            if size > usize::MAX >> 1 {
                return Err(VmRefusal::NatOverflow {
                    operation: "Array.size",
                });
            }
            Ok(IntrinsicResult::raw_object(Obj::mk_nat(size)))
        }
        "extern:Array.getInternal" => {
            expect_arity(row, args, 2)?;
            let (size, _) = array_value(&args[0], "Array.getInternal", 0)?;
            let index = nat_value(&args[1], "Array.getInternal", 1)?;
            if index >= size {
                return Err(VmRefusal::ArrayIndexOutOfBounds { index, size });
            }
            Ok(IntrinsicResult::owned(args[0].array_child(index)))
        }
        "extern:Array.ugetBorrowed" => {
            expect_arity(row, args, 2)?;
            let (size, _) = array_value(&args[0], "Array.ugetBorrowed", 0)?;
            let index = nat_value(&args[1], "Array.ugetBorrowed", 1)?;
            if index >= size {
                return Err(VmRefusal::ArrayIndexOutOfBounds { index, size });
            }
            Ok(IntrinsicResult::borrowed_promoted(
                args[0].array_child(index),
            ))
        }
        "extern:Array.push" => {
            expect_arity(row, args, 2)?;
            let (size, _) = array_value(&args[0], "Array.push", 0)?;
            let mut items = Vec::with_capacity(size.saturating_add(1));
            for index in 0..size {
                items.push(args[0].array_child(index));
            }
            items.push(args[1].clone_ref());
            Ok(IntrinsicResult::raw_object(Obj::mk_array(items)))
        }
        "extern:ST.Prim.mkRef" => {
            expect_arity(row, args, 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_ref(args[0].clone_ref())))
        }
        "extern:ST.Prim.Ref.get" => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.get", 0, "ST.Ref", ValueKind::Ref)?;
            Ok(IntrinsicResult::owned(args[0].ref_get()))
        }
        "extern:ST.Prim.Ref.take" => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.take", 0, "ST.Ref", ValueKind::Ref)?;
            Ok(IntrinsicResult::owned(args[0].ref_take()))
        }
        "extern:ST.Prim.Ref.set" => {
            expect_arity(row, args, 2)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.set", 0, "ST.Ref", ValueKind::Ref)?;
            args[0].ref_set(args[1].clone_ref());
            Ok(IntrinsicResult::owned(Obj::mk_nat(0)))
        }
        "extern:ST.Prim.Ref.swap" => {
            expect_arity(row, args, 2)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.swap", 0, "ST.Ref", ValueKind::Ref)?;
            Ok(IntrinsicResult::owned(
                args[0].ref_swap(args[1].clone_ref()),
            ))
        }
        "extern:ST.Prim.Ref.ptrEq" => {
            expect_arity(row, args, 2)?;
            expect_value_kind(&args[0], "ST.Prim.Ref.ptrEq", 0, "ST.Ref", ValueKind::Ref)?;
            expect_value_kind(&args[1], "ST.Prim.Ref.ptrEq", 1, "ST.Ref", ValueKind::Ref)?;
            Ok(IntrinsicResult::owned(Obj::mk_nat(
                if args[0].ref_ptr_eq(&args[1]) { 1 } else { 0 },
            )))
        }
        "extern:Thunk.pure" => {
            expect_arity(row, args, 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_thunk_value(
                args[0].clone_ref(),
            )))
        }
        "extern:Thunk.mk" => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "Thunk.mk", 0, "Golem closure", ValueKind::Closure)?;
            if args[0].closure_shell_parts().is_none() {
                return Err(VmRefusal::UnsupportedNativeClosure);
            }
            Ok(IntrinsicResult::owned(Obj::mk_thunk_closure(
                args[0].clone_ref(),
            )))
        }
        "extern:Task.pure" => {
            expect_arity(row, args, 1)?;
            Ok(IntrinsicResult::owned(Obj::mk_task_pure(
                args[0].clone_ref(),
            )))
        }
        "extern:Task.get" => {
            expect_arity(row, args, 1)?;
            expect_value_kind(&args[0], "Task.get", 0, "finished Task", ValueKind::Task)?;
            args[0]
                .finished_task_value()
                .map(IntrinsicResult::owned)
                .ok_or(VmRefusal::UnsupportedTaskState)
        }
        _ => Err(VmRefusal::UnsupportedIntrinsic {
            row: row.to_string(),
        }),
    }
}

fn ensure_intrinsic_row(row: &str) -> Result<(), VmRefusal> {
    if !EXTERN_ROWS.iter().any(|generated| generated.id == row) {
        return Err(VmRefusal::UnknownIntrinsic {
            row: row.to_string(),
        });
    }
    Ok(())
}

fn delayed_thunk_operand(args: Vec<Obj>) -> Result<Obj, VmRefusal> {
    const ROW: &str = "extern:Thunk.get";
    ensure_intrinsic_row(ROW)?;
    expect_arity(ROW, &args, 1)?;
    let thunk = args
        .into_iter()
        .next()
        .ok_or_else(|| VmRefusal::IntrinsicArity {
            row: ROW.to_string(),
            expected: 1,
            actual: 0,
        })?;
    expect_value_kind(&thunk, "Thunk.get", 0, "Thunk", ValueKind::Thunk)?;
    Ok(thunk)
}

fn cache_thunk_value(thunk: &Obj, value: &Obj) -> Result<(), Stop> {
    if thunk.complete_claimed_thunk(value.clone_ref()) {
        return Ok(());
    }
    Err(Stop::InternalFault(InternalFault::new(
        "FLBC-THUNK-COMPLETION",
        "claimed thunk rejected its single completion",
    )))
}

fn is_managerless_task_row(row: &str) -> bool {
    matches!(
        row,
        "extern:Task.spawn" | "extern:Task.map" | "extern:Task.bind"
    )
}

fn managerless_task_application(
    row: &str,
    args: Vec<Obj>,
) -> Result<ManagerlessTaskApplication, VmRefusal> {
    ensure_intrinsic_row(row)?;
    match row {
        "extern:Task.spawn" => {
            let [closure, priority] = exact_owned_args(row, args)?;
            expect_golem_task_closure(&closure, "Task.spawn", 0)?;
            nat_value(&priority, "Task.spawn", 1)?;
            Ok(ManagerlessTaskApplication {
                row: "extern:Task.spawn",
                closure,
                argument: Obj::mk_nat(0),
                argument_ownership: ArgumentOwnership::Scalar,
                completion: ManagerlessTaskCompletion::WrapPure,
            })
        }
        "extern:Task.map" => {
            let [closure, task, priority, sync] = exact_owned_args(row, args)?;
            expect_golem_task_closure(&closure, "Task.map", 0)?;
            expect_value_kind(&task, "Task.map", 1, "finished Task", ValueKind::Task)?;
            nat_value(&priority, "Task.map", 2)?;
            bool_value(&sync, "Task.map", 3)?;
            let argument = task
                .finished_task_value()
                .ok_or(VmRefusal::UnsupportedTaskState)?;
            Ok(ManagerlessTaskApplication {
                row: "extern:Task.map",
                closure,
                argument,
                argument_ownership: ArgumentOwnership::Owned,
                completion: ManagerlessTaskCompletion::WrapPure,
            })
        }
        "extern:Task.bind" => {
            let [task, closure, priority, sync] = exact_owned_args(row, args)?;
            expect_value_kind(&task, "Task.bind", 0, "finished Task", ValueKind::Task)?;
            expect_golem_task_closure(&closure, "Task.bind", 1)?;
            nat_value(&priority, "Task.bind", 2)?;
            bool_value(&sync, "Task.bind", 3)?;
            let argument = task
                .finished_task_value()
                .ok_or(VmRefusal::UnsupportedTaskState)?;
            Ok(ManagerlessTaskApplication {
                row: "extern:Task.bind",
                closure,
                argument,
                argument_ownership: ArgumentOwnership::Owned,
                completion: ManagerlessTaskCompletion::RequireFinishedTask,
            })
        }
        _ => Err(VmRefusal::UnsupportedIntrinsic {
            row: row.to_string(),
        }),
    }
}

fn exact_owned_args<const N: usize>(row: &str, args: Vec<Obj>) -> Result<[Obj; N], VmRefusal> {
    args.try_into()
        .map_err(|args: Vec<Obj>| VmRefusal::IntrinsicArity {
            row: row.to_string(),
            expected: N,
            actual: args.len(),
        })
}

fn expect_golem_task_closure(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<(), VmRefusal> {
    expect_value_kind(
        value,
        operation,
        argument,
        "Golem closure",
        ValueKind::Closure,
    )?;
    if value.closure_shell_parts().is_none() {
        return Err(VmRefusal::UnsupportedNativeClosure);
    }
    Ok(())
}

fn complete_managerless_task(
    completion: ManagerlessTaskCompletion,
    value: Obj,
) -> Result<Obj, VmRefusal> {
    match completion {
        ManagerlessTaskCompletion::WrapPure => Ok(Obj::mk_task_pure(value)),
        ManagerlessTaskCompletion::RequireFinishedTask => {
            expect_value_kind(
                &value,
                "Task.bind result",
                0,
                "finished Task",
                ValueKind::Task,
            )?;
            if value.finished_task_value().is_none() {
                return Err(VmRefusal::UnsupportedTaskState);
            }
            Ok(value)
        }
    }
}

fn expect_arity(row: &str, args: &[Obj], expected: usize) -> Result<(), VmRefusal> {
    if args.len() != expected {
        return Err(VmRefusal::IntrinsicArity {
            row: row.to_string(),
            expected,
            actual: args.len(),
        });
    }
    Ok(())
}

fn expect_value_kind(
    value: &Obj,
    operation: &'static str,
    argument: usize,
    expected: &'static str,
    expected_kind: ValueKind,
) -> Result<(), VmRefusal> {
    let actual = value_kind(value);
    if actual != expected_kind {
        return Err(VmRefusal::TypeMismatch {
            operation,
            argument,
            expected,
            actual,
        });
    }
    Ok(())
}

fn nat_value(value: &Obj, operation: &'static str, argument: usize) -> Result<usize, VmRefusal> {
    if !value.is_scalar() {
        return Err(type_mismatch(operation, argument, "Nat scalar", value));
    }
    Ok(value.unbox())
}

fn bool_value(value: &Obj, operation: &'static str, argument: usize) -> Result<bool, VmRefusal> {
    let value = nat_value(value, operation, argument)?;
    match value {
        0 => Ok(false),
        1 => Ok(true),
        value => Err(VmRefusal::InvalidBoolScalar {
            operation,
            argument,
            value,
        }),
    }
}

fn array_value(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<(usize, usize), VmRefusal> {
    if value_kind(value) != ValueKind::Array {
        return Err(type_mismatch(operation, argument, "Array", value));
    }
    Ok(value.array_view())
}

fn string_value(
    value: &Obj,
    operation: &'static str,
    argument: usize,
) -> Result<String, VmRefusal> {
    if value_kind(value) != ValueKind::String {
        return Err(type_mismatch(operation, argument, "String", value));
    }
    let (size, _, _, bytes) = value.string_view();
    if size == 0 || size > bytes.len() || bytes[size - 1] != 0 {
        return Err(VmRefusal::InvalidStringObject);
    }
    std::str::from_utf8(&bytes[..size - 1])
        .map(str::to_string)
        .map_err(|_| VmRefusal::InvalidStringObject)
}

fn type_mismatch(
    operation: &'static str,
    argument: usize,
    expected: &'static str,
    value: &Obj,
) -> VmRefusal {
    VmRefusal::TypeMismatch {
        operation,
        argument,
        expected,
        actual: value_kind(value),
    }
}

/// Derive the runtime category without exposing an address or host shadow.
pub fn value_kind(value: &Obj) -> ValueKind {
    if value.is_scalar() {
        return ValueKind::Scalar;
    }
    let tag = value.obj_tag();
    if tag <= usize::from(abi::TAG_MAX_CTOR_TAG) {
        return ValueKind::Ctor(u8::try_from(tag).unwrap_or(abi::TAG_RESERVED));
    }
    match tag {
        tag if tag == usize::from(abi::TAG_PROMISE) => ValueKind::Promise,
        tag if tag == usize::from(abi::TAG_CLOSURE) => ValueKind::Closure,
        tag if tag == usize::from(abi::TAG_ARRAY) => ValueKind::Array,
        tag if tag == usize::from(abi::TAG_STRUCT_ARRAY) => ValueKind::StructArray,
        tag if tag == usize::from(abi::TAG_SCALAR_ARRAY) => ValueKind::ScalarArray,
        tag if tag == usize::from(abi::TAG_STRING) => ValueKind::String,
        tag if tag == usize::from(abi::TAG_MPZ) => ValueKind::Mpz,
        tag if tag == usize::from(abi::TAG_THUNK) => ValueKind::Thunk,
        tag if tag == usize::from(abi::TAG_TASK) => ValueKind::Task,
        tag if tag == usize::from(abi::TAG_REF) => ValueKind::Ref,
        tag if tag == usize::from(abi::TAG_EXTERNAL) => ValueKind::External,
        _ => ValueKind::Reserved,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn intrinsic_result_adapter_refuses_class_and_scalar_kind_drift() {
        let scalar_kind = finish_intrinsic_result(
            "extern:Float.abs",
            ResultOwnership::Scalar,
            IntrinsicResult {
                ownership: ResultOwnership::Scalar,
                value: Obj::mk_string("not-a-scalar"),
            },
        );
        assert!(matches!(
            scalar_kind,
            Err(VmRefusal::IntrinsicResultKind {
                ref row,
                expected: "tagged scalar",
                actual: ValueKind::String,
            }) if row == "extern:Float.abs"
        ));

        let class = finish_intrinsic_result(
            "extern:Array.ugetBorrowed",
            ResultOwnership::Borrowed,
            IntrinsicResult::owned(Obj::mk_nat(0)),
        );
        assert!(matches!(
            class,
            Err(VmRefusal::IntrinsicResultImplementationMismatch {
                ref row,
                expected: ResultOwnership::Borrowed,
                actual: ResultOwnership::Owned,
            }) if row == "extern:Array.ugetBorrowed"
        ));
    }
}
