//! Publish the retained CLI response after native stdout effects. Lean's
//! runtime uses C stdio, while this host uses Rust's independent stdout buffer.

use crate::MultiplexerOutput;
use std::io::Write;
use std::process::ExitCode;

/// Write a completed response and return its process status.
///
/// Native stdout must be flushed first: otherwise a pipe can receive the
/// rendered result before the native writes which produced it. This is a host
/// publication boundary, not a change to individual Lean writes or capture
/// semantics. Any flush/write failure returns status 1; accepted native bytes
/// cannot be rolled back and the evaluated program is never executed again.
pub fn write_output(output: MultiplexerOutput) -> ExitCode {
    if fln::flush_native_stdout().is_err() {
        return ExitCode::from(1);
    }
    let mut stdout = std::io::stdout().lock();
    if stdout
        .write_all(output.stdout.as_bytes())
        .and_then(|()| stdout.flush())
        .is_err()
    {
        return ExitCode::from(1);
    }
    let mut stderr = std::io::stderr().lock();
    if stderr
        .write_all(output.stderr.as_bytes())
        .and_then(|()| stderr.flush())
        .is_err()
    {
        return ExitCode::from(1);
    }
    ExitCode::from(output.exit_code)
}

#[cfg(test)]
mod tests;
