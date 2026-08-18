#![forbid(unsafe_code)]

use std::io::Write;

fn main() -> std::process::ExitCode {
    let stdin = std::io::stdin();
    let mut stdin = stdin.lock();
    let output = fln_cli::run_lean_with_input(std::env::args_os().skip(1), &mut stdin);
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
