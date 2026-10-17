//! The pinned monomorphic String fold uses ordinary VM call frames. Each
//! Unicode scalar schedules a checked callback; no callback executes on the
//! host stack, and every stop drops the pending fold and its owned handles.

use super::{
    ApplyPlan, ArgumentOwnership, CallableResultOwnership, FunctionId, Obj, PreparedApply,
    ValidatedProgram, VmRefusal, exact_owned_args, finish_apply, plan_apply, string_bytes,
    string_value,
};

pub(super) const ROW: &str = "extern:String.Internal.foldl";
const OPERATION: &str = "String.Internal.foldl";

pub(super) struct State {
    callback: Obj,
    // Decode the borrowed input once. The offset advances only by the width
    // of a decoded scalar, so a continuation never starts inside UTF-8.
    input: String,
    offset: usize,
    // A curried callback first consumes the accumulator, then its returned
    // closure consumes this scalar. Flat callbacks leave the slot empty.
    pending_character: Option<Obj>,
}

pub(super) enum Step {
    Complete(Obj),
    Call {
        function: FunctionId,
        args: Vec<Obj>,
        state: State,
    },
}

pub(super) fn start(program: &ValidatedProgram, args: Vec<Obj>) -> Result<Step, VmRefusal> {
    let [callback, initial, source] = exact_owned_args::<3>(ROW, args)?;
    string_bytes(&initial, OPERATION, 1)?;
    let input = string_value(&source, OPERATION, 2)?;
    // Even an empty fold requires the row's callable shape, but never runs
    // its body or creates a callback frame.
    if input.is_empty() {
        callback_plan(program, &callback, &[false, true])?;
        return Ok(Step::Complete(initial));
    }
    next(
        program,
        State {
            callback,
            input,
            offset: 0,
            pending_character: None,
        },
        initial,
    )
}

pub(super) fn resume(
    program: &ValidatedProgram,
    mut state: State,
    value: Obj,
) -> Result<Step, VmRefusal> {
    if let Some(character) = state.pending_character.take() {
        let (function, args, remainder) = prepare(program, &value, vec![character])?;
        state.pending_character = remainder;
        return Ok(Step::Call {
            function,
            args,
            state,
        });
    }
    // Callable ownership alone does not establish the String result type:
    // an owned array or closure is still a malformed fold callback result.
    string_bytes(&value, OPERATION, 0)?;
    next(program, state, value)
}

fn next(program: &ValidatedProgram, mut state: State, accumulator: Obj) -> Result<Step, VmRefusal> {
    let suffix = state
        .input
        .get(state.offset..)
        .ok_or(VmRefusal::InvalidStringObject)?;
    let Some(character) = suffix.chars().next() else {
        return Ok(Step::Complete(accumulator));
    };
    state.offset += character.len_utf8();
    let (function, args, remainder) = prepare(
        program,
        &state.callback,
        vec![accumulator, Obj::mk_nat(character as usize)],
    )?;
    state.pending_character = remainder;
    Ok(Step::Call {
        function,
        args,
        state,
    })
}

fn callback_plan(
    program: &ValidatedProgram,
    callback: &Obj,
    scalar_arguments: &[bool],
) -> Result<ApplyPlan, VmRefusal> {
    let plan = plan_apply(
        program,
        callback,
        scalar_arguments.len(),
        None,
        Some(CallableResultOwnership::Owned),
    )?;
    if plan.required > scalar_arguments.len() {
        return Err(VmRefusal::MalformedClosure {
            reason: "String.Internal.foldl callback requires too many arguments",
        });
    }
    let function = program
        .function(plan.function)
        .ok_or(VmRefusal::MalformedClosure {
            reason: "target function is absent",
        })?;
    let parameters =
        &function.parameter_ownership[plan.captures.len()..plan.captures.len() + plan.required];
    for (argument, (expected, scalar)) in parameters
        .iter()
        .copied()
        .zip(scalar_arguments.iter().copied())
        .enumerate()
    {
        // The fold owns references acquired from its borrowed arguments and
        // from preceding callback results. It can give a reference away or
        // lend it, but cannot promise uniqueness. Character words may use
        // any of the ordinary scalar/owned/borrowed calling dispositions.
        let actual = match expected {
            ArgumentOwnership::Unique => Some(ArgumentOwnership::Borrowed),
            ArgumentOwnership::Scalar if !scalar => Some(ArgumentOwnership::Owned),
            ArgumentOwnership::Borrowed | ArgumentOwnership::Owned | ArgumentOwnership::Scalar => {
                None
            }
        };
        if let Some(actual) = actual {
            return Err(VmRefusal::ApplyOwnershipMismatch {
                function: plan.function,
                argument,
                expected,
                actual,
            });
        }
    }
    Ok(plan)
}

fn prepare(
    program: &ValidatedProgram,
    callback: &Obj,
    args: Vec<Obj>,
) -> Result<(FunctionId, Vec<Obj>, Option<Obj>), VmRefusal> {
    let scalar_arguments: Vec<_> = args.iter().map(Obj::is_scalar).collect();
    let plan = callback_plan(program, callback, &scalar_arguments)?;
    match finish_apply(plan, args, None) {
        PreparedApply::Call {
            function,
            args,
            remainder,
            remainder_ownership: _,
        } => {
            // At most two arguments entered this helper and every checked
            // closure consumes at least one. A remainder is exactly the
            // character waiting for the second half of a curried callback.
            Ok((function, args, remainder.into_iter().next()))
        }
        PreparedApply::Partial { .. } => Err(VmRefusal::MalformedClosure {
            reason: "String.Internal.foldl callback requires too many arguments",
        }),
    }
}
