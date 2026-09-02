#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::fs::File;
use std::io::{self, BufReader};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub use fln_server::{json_string, transport};

#[path = "../json.rs"]
mod json;
#[path = "../transcript.rs"]
pub mod transcript;

const USAGE: &str = "Usage: fln-lsp-validate [--] INPUT\n\
\n\
Validate one exact Content-Length-framed JSON-RPC client transcript.\n\
Use INPUT=- to read standard input.\n";

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
            return Err("exactly one transcript is required".to_string());
        }
    }
    input
        .map(Command::Validate)
        .ok_or_else(|| "missing input transcript".to_string())
}

fn validate_path(path: &Path) -> Result<transcript::TranscriptStats, String> {
    if path == Path::new("-") {
        let stdin = io::stdin();
        return transcript::validate_reader(&mut BufReader::new(stdin.lock()));
    }
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
    transcript::validate_reader(&mut BufReader::new(file))
}

fn main() -> ExitCode {
    let command = match parse_args(std::env::args_os()) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("fln-lsp-validate: {error}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match command {
        Command::Help => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Command::Validate(path) => match validate_path(&path) {
            Ok(stats) => {
                print!("{}", transcript::render_validation(stats));
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("fln-lsp-validate: {error}");
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
    fn validates_requests_and_notifications_without_normalizing_ids() {
        let bodies = [
            r#"{"jsonrpc":"2.0","id":1.25e2,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":null,"method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ];
        let expected_body_bytes = bodies
            .iter()
            .map(|body| u64::try_from(body.len()).unwrap())
            .sum();
        let mut bytes = Vec::new();
        for body in bodies {
            bytes.extend(frame(body));
        }
        let expected_wire_bytes = u64::try_from(bytes.len()).unwrap();
        let stats = transcript::validate_reader(&mut BufReader::new(Cursor::new(bytes))).unwrap();
        assert_eq!(
            stats,
            transcript::TranscriptStats {
                frames: 4,
                requests: 2,
                notifications: 2,
                wire_bytes: expected_wire_bytes,
                body_bytes: expected_body_bytes,
            }
        );
        assert_eq!(
            transcript::render_validation(stats),
            format!(
                "{{\"schema\":\"fln.lsp-transcript-validation/2\",\"frames\":4,\"requests\":2,\"notifications\":2,\"wireBytes\":{expected_wire_bytes},\"bodyBytes\":{expected_body_bytes}}}\n"
            )
        );
    }

    #[test]
    fn names_the_first_invalid_frame_and_reason() {
        for (body, reason) in [
            (r#"{"jsonrpc":"2.0","method":3}"#, "non-string method"),
            (
                r#"{"jsonrpc":"1.0","method":"x"}"#,
                "unsupported JSON-RPC version",
            ),
            (
                r#"{"jsonrpc":"2.0","method":"x","params":3}"#,
                "params must be an object or array",
            ),
            (r#"[]"#, "not a JSON-RPC object"),
            (r#"{"jsonrpc":"2.0","method":"x",}"#, "malformed JSON"),
        ] {
            let error = transcript::validate_bytes(&frame(body)).unwrap_err();
            assert!(error.contains("frame 1"));
            assert!(error.contains(reason), "{error}");
        }
    }

    #[test]
    fn argument_parser_honors_stdin_and_end_of_options() {
        assert_eq!(
            parse_args(["fln-lsp-validate", "-"].map(OsString::from)),
            Ok(Command::Validate(PathBuf::from("-")))
        );
        assert_eq!(
            parse_args(["fln-lsp-validate", "--", "--recording"].map(OsString::from)),
            Ok(Command::Validate(PathBuf::from("--recording")))
        );
    }
}
