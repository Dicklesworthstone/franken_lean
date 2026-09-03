#![forbid(unsafe_code)]

mod support;

fn main() -> std::process::ExitCode {
    let arguments = std::env::args_os().skip(1).collect::<Vec<_>>();
    let output = support::fln_server_command(&arguments)
        .unwrap_or_else(|| fln_cli::run(arguments));
    support::write_output(output)
}
