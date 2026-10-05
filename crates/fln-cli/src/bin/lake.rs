#![forbid(unsafe_code)]

mod support;

fn main() -> std::process::ExitCode {
    // A refused allocation unwinds to the frontier's per-module guard instead of
    // aborting the process (fln-frontier-oom-abort-w9dx).
    fln::install_host_allocation_failure_hook();
    let arguments = std::env::args_os().skip(1);
    let output = fln_cli::run_lake(arguments);
    support::write_output(output)
}
