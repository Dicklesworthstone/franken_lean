#![forbid(unsafe_code)]

fn main() -> std::process::ExitCode {
    // A refused allocation unwinds to the frontier's per-module guard instead of
    // aborting the process (fln-frontier-oom-abort-w9dx).
    fln::install_host_allocation_failure_hook();
    fln_cli::install_json_execution_panic_hook();
    let output = fln_cli::run(std::env::args_os().skip(1));
    fln_cli::write_output(output)
}
