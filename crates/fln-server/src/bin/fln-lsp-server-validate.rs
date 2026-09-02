#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::fs::File;
use std::io::{self, BufReader};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub use fln_server::{json_string, transport};

#[path = "../json.rs"]
mod json;
#[allow(dead_code)]
#[path = "../server_transcript.rs"]
mod server_transcript;
#[allow(dead_code)]
#[path = "../transcript.rs"]
mod transcript;

const USAGE: &str = "Usage: fln-lsp-server-validate [--] INPUT\n\
\n\
Validate one exact Content-Length-framed JSON-RPC server transcript.\n\
Use INPUT=- to read standard input. The bounded profile accepts notifications\n\
and result/error responses; server-initiated requests are refused. Known\n\
Lantern notification payloads are validated against their structural schemas.\n";

#[derive(Debug, Clone, PartialEq, Eq)]
enum Command {
    Help,
    Validate(PathBuf),
}

fn parse_args(arguments: impl IntoIterator<Item = OsString>) -> Result<Command, String> {
    let mut arguments = arguments.into_iter();
    let _program = arguments.next();
    let mut options = true;
    let mut input = None;
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            continue;
        }
        if options && matches!(argument.to_str(), Some("-h" | "--help")) {
            if input.is_some() || arguments.next().is_some() {
                return Err("--help cannot be combined with validation arguments".to_string());
            }
            return Ok(Command::Help);
        }
        if options && argument.to_string_lossy().starts_with('-') && argument != "-" {
            return Err(format!("unknown option: {}", argument.to_string_lossy()));
        }
        if input.replace(PathBuf::from(argument)).is_some() {
            return Err("exactly one server transcript is required".to_string());
        }
    }
    input
        .map(Command::Validate)
        .ok_or_else(|| "missing server transcript".to_string())
}

fn validate_path(path: &Path) -> Result<String, String> {
    let evidence = if path == Path::new("-") {
        let stdin = io::stdin();
        server_transcript::validate_server_transcript_reader(&mut BufReader::new(stdin.lock()))
    } else {
        let metadata = std::fs::metadata(path)
            .map_err(|error| format!("could not inspect {}: {error}", path.display()))?;
        if metadata.len() > transcript::MAX_TRANSCRIPT_BYTES {
            return Err(format!(
                "{} is {} bytes; the transcript ceiling is {}",
                path.display(),
                metadata.len(),
                transcript::MAX_TRANSCRIPT_BYTES
            ));
        }
        let file = File::open(path)
            .map_err(|error| format!("could not open {}: {error}", path.display()))?;
        server_transcript::validate_server_transcript_reader(&mut BufReader::new(file))
    }?;
    Ok(server_transcript::render_server_transcript_validation(
        evidence.stats,
    ))
}

fn main() -> ExitCode {
    let command = match parse_args(std::env::args_os()) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("fln-lsp-server-validate: {error}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match command {
        Command::Help => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Command::Validate(path) => match validate_path(&path) {
            Ok(receipt) => {
                print!("{receipt}");
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("fln-lsp-server-validate: {error}");
                ExitCode::from(1)
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{BufReader, Cursor};

    fn frame(body: &str) -> Vec<u8> {
        let mut framed = Vec::new();
        fln_server::transport::write_message(&mut framed, body.as_bytes()).unwrap();
        framed
    }

    #[test]
    fn parser_honors_stdin_and_end_of_options() {
        assert_eq!(
            parse_args(["fln-lsp-server-validate", "-"].map(OsString::from)),
            Ok(Command::Validate(PathBuf::from("-")))
        );
        assert_eq!(
            parse_args(
                ["fln-lsp-server-validate", "--", "--server.frames"]
                    .map(OsString::from)
            ),
            Ok(Command::Validate(PathBuf::from("--server.frames")))
        );
    }

    #[test]
    fn mixed_server_stream_emits_schema_v3_resource_evidence() {
        let mut bytes = frame(r#"{"jsonrpc":"2.0","id":1,"result":null}"#);
        bytes.extend(frame(
            r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":3,"message":"ok"}}"#,
        ));
        bytes.extend(frame(
            r#"{"jsonrpc":"2.0","id":"x","error":{"code":-32601,"message":"method not found"}}"#,
        ));
        let evidence = server_transcript::validate_server_transcript_reader(
            &mut BufReader::new(Cursor::new(bytes)),
        )
        .unwrap();
        let receipt = server_transcript::render_server_transcript_validation(evidence.stats);
        assert!(receipt.contains("\"schema\":\"fln.lsp-server-transcript/3\""));
        assert!(receipt.contains("\"responses\":2"));
        assert!(receipt.contains("\"notifications\":1"));
        assert!(receipt.contains("\"logMessages\":1"));
        assert!(receipt.contains("\"metadataBytes\":"));
        assert!(receipt.contains("\"metadataByteCeiling\":33554432"));
    }
}
