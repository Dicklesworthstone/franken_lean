#![forbid(unsafe_code)]

mod support;

fn main() -> std::process::ExitCode {
    let arguments = std::env::args_os().skip(1).collect::<Vec<_>>();
    let output = match arguments.as_slice() {
        [argument] if argument.to_str() == Some("serve-lsp") => support::serve_lsp(),
        [first, ..] if first.to_str() == Some("serve-lsp") => fln_cli::MultiplexerOutput {
            stdout: String::new(),
            stderr: "fln: serve-lsp does not accept arguments\n".to_owned(),
            exit_code: 2,
        },
        _ => fln_cli::run(arguments),
    };
    support::write_output(output)
}
