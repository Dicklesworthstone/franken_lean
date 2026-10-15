//! The language's recoverable panic and strict debugging continuation.
//!
//! `panicCore` is not FLBC's terminating `Panic` instruction: it reports the
//! message and retains its borrowed default. Trace calls use ordinary checked
//! VM frames, never the native closure trampoline or a recursive interpreter.

use super::{
    ArgumentOwnership, IntrinsicApplication, IntrinsicCompletion, IntrinsicFailure,
    IntrinsicResult, Obj, VmRefusal, exact_owned_args, expect_arity, expect_golem_task_closure,
    string_value,
};

/// The census correctly records a raw C pointer for `msg`, not an ownership
/// typedef. Only this exact reviewed export consumes that pointer. Keep every
/// other raw-pointer argument refused by the generic contract interpreter.
pub(super) fn argument_ownership(
    row: &crate::extern_table_generated::GeneratedExternRow,
    arity: usize,
) -> Option<Result<Vec<crate::extern_row::ArgumentOwnership>, crate::extern_row::ContractError>> {
    if row.id == "extern:panicCore"
        && row.symbol == "lean_panic_fn_borrowed"
        && row.ownership == "abi((default_val: borrowed_arg, msg: raw_object) -> raw_object)"
        && arity == 2
    {
        use crate::extern_row::ArgumentOwnership::{Borrowed, Owned};
        Some(Ok(vec![Borrowed, Owned]))
    } else {
        None
    }
}

pub(super) fn panic(row: &str, args: &[Obj]) -> Result<IntrinsicResult, IntrinsicFailure> {
    expect_arity(row, args, 2)?;
    let message = string_value(&args[1], "panicCore", 1)?;
    fln_rt::diagnostics::report_panic(message.as_bytes());
    Ok(IntrinsicResult::raw_object(args[0].clone_ref()))
}

pub(super) fn trace(row: &'static str, args: Vec<Obj>) -> Result<IntrinsicApplication, VmRefusal> {
    let [message, closure] = exact_owned_args(row, args)?;
    let message = string_value(&message, "dbgTrace", 0)?;
    expect_golem_task_closure(&closure, "dbgTrace", 1)?;
    // The caller validates the closure's concrete arity/ownership before
    // reporting, then applies it to the exact erased Unit representation.
    Ok(IntrinsicApplication {
        row,
        closure,
        arguments: vec![Obj::mk_nat(0)],
        argument_ownership: vec![ArgumentOwnership::Scalar],
        completion: IntrinsicCompletion::RawResult,
        trace: Some(message),
    })
}
