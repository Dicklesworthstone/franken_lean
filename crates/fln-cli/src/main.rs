#![forbid(unsafe_code)]

use std::io::Write;

fn main() -> std::process::ExitCode {
    // A refused allocation unwinds to the frontier's per-module guard instead of
    // aborting the process (fln-frontier-oom-abort-w9dx).
    fln::install_host_allocation_failure_hook();
    fln_cli::install_json_execution_panic_hook();
    let output = fln_cli::run(std::env::args_os().skip(1));
    if std::io::stdout()
        .lock()
        .write_all(output.stdout.as_bytes())
        .is_err()
    {
        return std::process::ExitCode::from(1);
    }
    if std::io::stderr()
        .lock()
        .write_all(output.stderr.as_bytes())
        .is_err()
    {
        return std::process::ExitCode::from(1);
    }
    std::process::ExitCode::from(output.exit_code)
}
