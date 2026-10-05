#![forbid(unsafe_code)]

mod support;

fn main() -> std::process::ExitCode {
    // A refused allocation unwinds to the frontier's per-module guard instead of
    // aborting the process (fln-frontier-oom-abort-w9dx).
    fln::install_host_allocation_failure_hook();
    let arguments = std::env::args_os().skip(1).collect::<Vec<_>>();
    let output = if matches!(
        arguments.as_slice(),
        [argument] if argument.to_str() == Some("--server")
    ) {
        support::serve_lsp()
    } else {
        let stdin = std::io::stdin();
        let mut stdin = stdin.lock();
        fln_cli::run_lean_with_input(arguments, &mut stdin)
    };
    support::write_output(output)
}
