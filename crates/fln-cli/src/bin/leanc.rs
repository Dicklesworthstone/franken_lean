#![forbid(unsafe_code)]

mod support;

fn main() -> std::process::ExitCode {
    let arguments = std::env::args_os().skip(1);
    let output = fln_cli::run_leanc(arguments);
    support::write_output(output)
}
