//! The executable Lean door: checked arguments, one main invocation, and its
//! process status. Main stdout is retained after the completed frontend's
//! output, on the same worker that owns the native stdout capture scope.

use super::{MultiplexerOutput, SourcePresentation, source_check, source_failure};
use fln::source_main::MainOutcome;
use std::ffi::OsString;
use std::path::PathBuf;

const MAX_OUTPUT_BYTES: usize = 16 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ArgumentsError {
    InvalidUtf8 { index: usize },
    Limit { limit: usize },
    Allocation,
}

impl ArgumentsError {
    fn output(&self) -> MultiplexerOutput {
        match self {
            Self::InvalidUtf8 { index } => failure(
                "input",
                &format!("script argument {index} is not valid UTF-8"),
                false,
                1,
            ),
            Self::Limit { limit } => failure(
                "resource",
                &format!("script arguments exceed the {limit}-byte input limit"),
                false,
                3,
            ),
            Self::Allocation => {
                failure("resource", "could not allocate script arguments", false, 3)
            }
        }
    }
}

/// Stop before copying an oversized argv. Empty arguments still cost one
/// byte, so the count is bounded as well as the total UTF-8 payload.
pub(super) fn arguments(
    arguments: impl IntoIterator<Item = OsString>,
    limit: usize,
) -> Result<Vec<String>, ArgumentsError> {
    let mut result = Vec::new();
    let mut bytes = 0usize;
    for (index, argument) in arguments.into_iter().enumerate() {
        let argument = argument
            .into_string()
            .map_err(|_| ArgumentsError::InvalidUtf8 { index })?;
        bytes = bytes
            .checked_add(argument.len())
            .and_then(|bytes| bytes.checked_add(1))
            .filter(|bytes| *bytes <= limit)
            .ok_or(ArgumentsError::Limit { limit })?;
        result
            .try_reserve(1)
            .map_err(|_| ArgumentsError::Allocation)?;
        result.push(argument);
    }
    Ok(result)
}

pub(super) fn run(
    path: PathBuf,
    arguments: Result<Vec<String>, ArgumentsError>,
    max_bytes: usize,
    import_jobs: std::num::NonZeroUsize,
    vm_limits: fln::VmExecutionLimits,
) -> MultiplexerOutput {
    let arguments = match arguments {
        Ok(arguments) => arguments,
        Err(error) => return error.output(),
    };
    source_check::run_imported_lean_main(&path, arguments, max_bytes, import_jobs, vm_limits)
}

fn failure(class: &'static str, detail: &str, authority: bool, code: u8) -> MultiplexerOutput {
    source_failure(class, detail, authority, SourcePresentation::Lean, code)
}

fn capture_failure(error: fln::StdoutCaptureError) -> MultiplexerOutput {
    let (class, code) = match error {
        fln::StdoutCaptureError::Allocation | fln::StdoutCaptureError::Limit { .. } => {
            ("resource", 3)
        }
        fln::StdoutCaptureError::InvalidStdout => ("capability", 5),
        fln::StdoutCaptureError::ScopeUnavailable => ("internal-fault", 4),
    };
    failure(
        class,
        &format!("main stdout capture: {error:?}"),
        false,
        code,
    )
}

fn invoke(
    commands: &fln::SourceCommandBatchExecution,
    arguments: &[String],
    limits: fln::EngineExecutionLimits,
) -> MultiplexerOutput {
    let main = match commands.execute_main(arguments, &fln::KVMap::new(), limits) {
        Ok(fln::Outcome::Complete(main)) => main,
        Ok(fln::Outcome::Inconclusive(reason)) => {
            return failure(
                "inconclusive",
                &format!("main did not finish: {reason:?}"),
                false,
                3,
            );
        }
        Ok(fln::Outcome::InternalFault(fault)) => {
            return failure(
                "internal-fault",
                &format!("main faulted: {fault:?}"),
                false,
                4,
            );
        }
        Err(error) => {
            let (class, authority, code) = error.disposition();
            return failure(class, &error.to_string(), authority, code);
        }
    };
    match &main.execution.exit {
        fln::VmExit::Panicked { message, usage } => {
            return super::source_terminal(
                "program-panic",
                &format!("main panicked: {message}"),
                usage.steps,
                usage.system_polls,
                usage.peak_stack_depth,
                SourcePresentation::Lean,
            );
        }
        fln::VmExit::Refused { refusal, usage } => {
            return super::source_terminal(
                "vm-refusal",
                &format!("main was refused: {refusal}"),
                usage.steps,
                usage.system_polls,
                usage.peak_stack_depth,
                SourcePresentation::Lean,
            );
        }
        fln::VmExit::Returned(_) => {}
    }
    match main.outcome() {
        Ok(MainOutcome::Returned { exit_code }) => MultiplexerOutput {
            stdout: String::new(),
            stderr: String::new(),
            // The library retains all 32 bits. This CLI's process abstraction
            // uses the low byte, as observed by a Unix parent process.
            exit_code: exit_code.to_le_bytes()[0],
        },
        Ok(MainOutcome::Raised { runtime_type, exit }) => {
            let error = super::source_evaluation::raised(&main.execution, &runtime_type, exit);
            let (class, authority, code) = error.disposition();
            failure(class, &format!("main: {error}"), authority, code)
        }
        Err(error) => {
            let (class, authority, code) = error.disposition();
            failure(class, &error.to_string(), authority, code)
        }
    }
}

/// Enter only after every frontend execution and its output have been checked.
/// The capture accepts whole UTF-8 writes under its escaped-byte allowance;
/// that is also an upper bound on the returned raw text. Main is never retried.
pub(super) fn execute(
    commands: &fln::SourceCommandBatchExecution,
    arguments: &[String],
    limits: fln::EngineExecutionLimits,
    frontend: MultiplexerOutput,
) -> MultiplexerOutput {
    if frontend.exit_code != 0 {
        return frontend;
    }
    let mut prefix = frontend.stdout;
    let Some(remaining) = MAX_OUTPUT_BYTES.checked_sub(prefix.len()) else {
        return failure("resource", "frontend output exceeds 16 MiB", false, 3);
    };
    let guard = match fln::StdoutCapture::begin(remaining) {
        Ok(guard) => guard,
        Err(error) => {
            let mut result = capture_failure(error);
            result.stdout = prefix;
            return result;
        }
    };
    let invoked = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        invoke(commands, arguments, limits)
    }));
    let captured = guard.finish();
    let mut result = match captured.error {
        Some(error) => capture_failure(error),
        None => {
            invoked.unwrap_or_else(|_| failure("internal-fault", "main worker panicked", false, 4))
        }
    };
    let text = match std::str::from_utf8(&captured.bytes) {
        Ok(text) => text,
        Err(_) => {
            let mut result = failure(
                "internal-fault",
                "main stdout violated its UTF-8 contract",
                false,
                4,
            );
            result.stdout = prefix;
            return result;
        }
    };
    if prefix.try_reserve(text.len()).is_err() {
        result = failure("resource", "could not retain main stdout", false, 3);
    } else {
        prefix.push_str(text);
    }
    result.stdout = prefix;
    result
}

#[cfg(test)]
mod tests;
