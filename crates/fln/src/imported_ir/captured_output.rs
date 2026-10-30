//! Isolated output capability for explicitly selected Reference user/library IR.

use super::{IrCapturedOutput, Outcome};
use fln_comp::flbc::{FunctionId, ValidatedProgram};
use fln_core::diag::ResourceReason;
use fln_core::outcome::{Inconclusive, InternalFault, ResourceUsage};
use fln_rt::obj::{Obj, StdoutCapture, StdoutCaptureError};
use fln_vm::interpreter::{
    CancellationProbe, CommandExecutionContext, ExecutionLimits, VmExit,
    execute_function_with_context, execute_with_context,
};

pub(super) fn execute(
    program: &ValidatedProgram,
    limits: ExecutionLimits,
    cancellation: Option<&dyn CancellationProbe>,
    max_bytes: usize,
) -> (Outcome<VmExit>, IrCapturedOutput) {
    capture(max_bytes, |context| {
        execute_with_context(program, limits, context, cancellation)
    })
}

pub(super) fn execute_function(
    program: &ValidatedProgram,
    function: FunctionId,
    arguments: Vec<Obj>,
    limits: ExecutionLimits,
    cancellation: Option<&dyn CancellationProbe>,
    max_bytes: usize,
) -> (Outcome<VmExit>, IrCapturedOutput) {
    capture(max_bytes, |context| {
        execute_function_with_context(program, function, arguments, limits, context, cancellation)
    })
}

fn capture(
    max_bytes: usize,
    run: impl FnOnce(CommandExecutionContext) -> Outcome<VmExit>,
) -> (Outcome<VmExit>, IrCapturedOutput) {
    let empty = || IrCapturedOutput {
        bytes: Vec::new(),
        max_bytes,
    };
    // An inner evaluation must not hide an already exhausted outer envelope.
    if let Some(error) = StdoutCapture::current_error() {
        return (failure(error), empty());
    }
    let capture = match StdoutCapture::begin_isolated(max_bytes, true) {
        Ok(capture) => capture,
        Err(error) => return (failure(error), empty()),
    };
    let outcome = run(CommandExecutionContext::UNLIMITED.with_captured_reference_output());
    // Native diagnostics can fail their sink without a callback return. Check
    // the complete scope before accepting any VM result, including a refusal.
    let scope_error = StdoutCapture::current_error();
    let captured = capture.finish();
    let outcome = captured.error.or(scope_error).map_or(outcome, failure);
    (
        outcome,
        IrCapturedOutput {
            bytes: captured.bytes,
            max_bytes,
        },
    )
}

fn failure(error: StdoutCaptureError) -> Outcome<VmExit> {
    match error {
        StdoutCaptureError::Limit { limit, requested } => Outcome::Inconclusive(
            Inconclusive::resource(ResourceUsage {
                reason: ResourceReason::Memory {
                    limit_bytes: limit as u64,
                },
                allowed: limit as u64,
                observed: requested as u64,
            })
            .with_progress("imported IR output byte allowance"),
        ),
        StdoutCaptureError::Allocation => Outcome::Inconclusive(
            Inconclusive::dependency_unavailable("host allocation for imported IR output capture"),
        ),
        StdoutCaptureError::InvalidStdout | StdoutCaptureError::InvalidStderr => {
            Outcome::Inconclusive(Inconclusive::dependency_unavailable(
                "imported IR output requires native stdout and stderr streams",
            ))
        }
        StdoutCaptureError::ScopeUnavailable => Outcome::InternalFault(InternalFault::new(
            "IMPORTED-IR-OUTPUT-SCOPE",
            "imported IR output capture lost its installed scope",
        )),
    }
}

#[cfg(test)]
mod tests;
