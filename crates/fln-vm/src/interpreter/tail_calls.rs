//! Terminal calls reuse a frame only after the ordinary argument and result
//! contracts have been checked. Return actions belong to the *caller* and must
//! survive replacement, including thunk caching and managerless Task completion.
use super::*;

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
    // Keep the backing storage across tail calls, including a smaller frame
    // followed by a larger one. Only a new largest frame needs more capacity.
    for slot in &mut frame.registers {
        *slot = None;
    }
    let register_count = usize::from(callee.register_count);
    if register_count > frame.registers.len() {
        frame
            .registers
            .reserve_exact(register_count - frame.registers.len());
    }
    frame.registers.resize_with(register_count, || None);
    for (slot, value) in frame.registers.iter_mut().zip(args) {
        *slot = Some(value);
    }
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

#[cfg(test)]
mod tests {
    use super::*;
    use fln_comp::flbc::{self, Function, Program};

    #[test]
    fn mutual_tail_frames_reuse_capacity_and_release_old_handles_after_transfer() {
        let r = Register::new;
        let f = FunctionId::new;
        let ownership = vec![ArgumentOwnership::Owned, ArgumentOwnership::Owned];
        let tail = |target| Instruction::TailCall {
            function: f(target),
            args: vec![r(1), r(0)],
            argument_ownership: ownership.clone(),
            result_ownership: CallableResultOwnership::Owned,
        };
        let worker = |id, count, target| Function {
            id: f(id),
            arity: 2,
            parameter_ownership: ownership.clone(),
            result_ownership: CallableResultOwnership::Owned,
            register_count: count,
            code: vec![
                Instruction::String {
                    dst: r(count - 1),
                    value: "discarded local".to_string(),
                },
                tail(target),
            ],
        };
        let program = flbc::validate(Program::new(
            f(0),
            vec![
                Function {
                    id: f(0),
                    arity: 0,
                    parameter_ownership: Vec::new(),
                    result_ownership: CallableResultOwnership::Owned,
                    register_count: 8,
                    code: vec![
                        Instruction::String {
                            dst: r(0),
                            value: "left".to_string(),
                        },
                        Instruction::String {
                            dst: r(1),
                            value: "right".to_string(),
                        },
                        Instruction::String {
                            dst: r(7),
                            value: "discarded local".to_string(),
                        },
                        tail(1),
                    ],
                },
                worker(1, 3, 2),
                worker(2, 8, 3),
                worker(3, 12, 1),
            ],
        ))
        .expect("well-formed owned mutual tail calls");
        let left = Obj::mk_string("left");
        let right = Obj::mk_string("right");
        let mut registers = empty_registers(8);
        registers[0] = Some(left.clone_ref());
        registers[1] = Some(right.clone_ref());
        let mut stack = [Frame {
            function: f(0),
            pc: 3,
            registers,
            return_to: Some(ReturnTo::Store(r(6))),
            pending_tail_return: None,
        }];

        for iteration in 0..90 {
            let frame = &mut stack[0];
            let local = Obj::mk_string("discarded local");
            let last = frame.registers.len() - 1;
            frame.registers[last] = Some(local.clone_ref());
            assert_eq!(local.header().rc, 2);
            frame.pc = if frame.function == f(0) { 3 } else { 1 };
            let Instruction::TailCall { function, args, .. } =
                &program.function(frame.function).unwrap().code[frame.pc]
            else {
                panic!("each worker tail-calls the next worker");
            };
            let required = usize::from(program.function(*function).unwrap().register_count);
            let old_capacity = frame.registers.capacity();
            let old_storage = frame.registers.as_ptr();
            let Ok(incoming) = transfer_call_arguments(frame, args, &ownership) else {
                panic!("both incoming owned handles transfer before frame reuse");
            };
            assert!(replace_frame(&program, &mut stack, *function, incoming).is_ok());

            let frame = &stack[0];
            assert_eq!(frame.registers.len(), required);
            if required <= old_capacity {
                assert_eq!(frame.registers.as_ptr(), old_storage);
                assert_eq!(frame.registers.capacity(), old_capacity);
            }
            assert!(frame.registers[2..].iter().all(Option::is_none));
            assert_eq!(local.header().rc, 1, "old local was released");
            assert_eq!(left.header().rc, 2);
            assert_eq!(right.header().rc, 2);
            let expected = if iteration % 2 == 0 { &right } else { &left };
            assert_eq!(
                frame.registers[0].as_ref().unwrap().identity_token(),
                expected.identity_token(),
                "owned arguments keep their identity across the swap"
            );
            assert_eq!(frame.pc, 0);
            assert!(frame.pending_tail_return.is_none());
            assert!(matches!(
                &frame.return_to,
                Some(ReturnTo::Store(destination)) if *destination == r(6)
            ));
        }
        drop(stack);
        assert_eq!(left.header().rc, 1);
        assert_eq!(right.header().rc, 1);
    }
}
