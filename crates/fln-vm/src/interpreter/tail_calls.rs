//! Terminal calls reuse a frame only after the ordinary argument and result
//! contracts have been checked. Return actions belong to the *caller* and must
//! survive replacement, including thunk caching and managerless Task completion.
use super::*;

pub(super) fn ordinary_call(instruction: Instruction) -> (Instruction, bool) {
    match instruction {
        Instruction::TailCall {
            function,
            args,
            argument_ownership,
            result_ownership,
        } => (
            Instruction::Call {
                // Never read or written: an exact tail call has no destination.
                dst: Register::new(0),
                function,
                args,
                argument_ownership,
                result_ownership,
            },
            true,
        ),
        Instruction::TailApply {
            closure,
            args,
            argument_ownership,
            result_ownership,
        } => (
            Instruction::Apply {
                // Non-exact applications reuse the already validated closure
                // slot after all original operands have been transferred.
                dst: closure,
                closure,
                args,
                argument_ownership,
                result_ownership,
            },
            true,
        ),
        instruction => (instruction, false),
    }
}

pub(super) fn replace_frame(
    program: &ValidatedProgram,
    stack: &mut [Frame],
    function: FunctionId,
    args: Vec<Obj>,
) -> Result<(), Stop> {
    let callee = program.function(function).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-TAIL-TARGET",
            "checked tail target disappeared",
        ))
    })?;
    let frame = current_frame_mut(stack)?;
    let caller = program.function(frame.function).ok_or_else(|| {
        Stop::InternalFault(InternalFault::new(
            "FLBC-TAIL-CALLER",
            "checked tail caller disappeared",
        ))
    })?;
    if args.len() != usize::from(callee.arity) || caller.result_ownership != callee.result_ownership
    {
        return Err(Stop::InternalFault(InternalFault::new(
            "FLBC-TAIL-CONTRACT",
            "checked tail call changed arity or the caller's result contract",
        )));
    }
    // The argument vector already owns every incoming handle. Destroy the
    // caller's remaining handles only now; permutations and aliases are safe.
    let mut registers = empty_registers(callee.register_count);
    for (slot, value) in registers.iter_mut().zip(args) {
        *slot = Some(value);
    }
    frame.registers = registers;
    frame.function = function;
    frame.pc = 0;
    frame.pending_tail_return = None;
    // frame.return_to is deliberately unchanged, even for the entry frame.
    Ok(())
}

pub(super) fn prepare_return(frame: &mut Frame, destination: Register) {
    for slot in &mut frame.registers {
        *slot = None;
    }
    frame.pending_tail_return = Some(destination);
}
