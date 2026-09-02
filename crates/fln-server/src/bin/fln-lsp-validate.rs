#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::fs::File;
use std::io::{self, BufRead, BufReader};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub use fln_server::{json_string, transport};

#[path = "../json.rs"]
mod json;
#[path = "../transcript.rs"]
pub mod transcript;

const USAGE: &str = "Usage: fln-lsp-validate [--client-lifecycle] [--] INPUT\n\
\n\
Validate one exact Content-Length-framed JSON-RPC client transcript.\n\
Use INPUT=- to read standard input.\n\
By default only framing and JSON-RPC shape are validated, which preserves\n\
negative replay fixtures. --client-lifecycle additionally requires known\n\
method roles and a complete initialize/initialized/shutdown/exit handshake.\n";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ValidationMode {
    Syntax,
    ClientLifecycle,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Config {
    input: PathBuf,
    mode: ValidationMode,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Command {
    Help,
    Validate(Config),
}

fn parse_args(arguments: impl IntoIterator<Item = OsString>) -> Result<Command, String> {
    let mut arguments = arguments.into_iter();
    let _program = arguments.next();
    let mut options = true;
    let mut lifecycle = false;
    let mut input = None;
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            continue;
        }
        if options && matches!(argument.to_str(), Some("-h" | "--help")) {
            if lifecycle || input.is_some() || arguments.next().is_some() {
                return Err("--help cannot be combined with validation arguments".to_string());
            }
            return Ok(Command::Help);
        }
        if options && argument == "--client-lifecycle" {
            if lifecycle {
                return Err("--client-lifecycle may be supplied at most once".to_string());
            }
            lifecycle = true;
            continue;
        }
        if options && argument.to_string_lossy().starts_with('-') && argument != "-" {
            return Err(format!("unknown option: {}", argument.to_string_lossy()));
        }
        if input.replace(PathBuf::from(argument)).is_some() {
            return Err("exactly one transcript is required".to_string());
        }
    }
    Ok(Command::Validate(Config {
        input: input.ok_or_else(|| "missing input transcript".to_string())?,
        mode: if lifecycle {
            ValidationMode::ClientLifecycle
        } else {
            ValidationMode::Syntax
        },
    }))
}

fn validate_reader(input: &mut dyn BufRead, mode: ValidationMode) -> Result<String, String> {
    match mode {
        ValidationMode::Syntax => {
            transcript::validate_reader(input).map(transcript::render_validation)
        }
        ValidationMode::ClientLifecycle => transcript::validate_client_lifecycle_reader(input)
            .map(transcript::render_client_lifecycle_validation),
    }
}

fn validate_path(config: &Config) -> Result<String, String> {
    if config.input == Path::new("-") {
        let stdin = io::stdin();
        return validate_reader(&mut BufReader::new(stdin.lock()), config.mode);
    }
    let metadata = std::fs::metadata(&config.input)
        .map_err(|error| format!("could not inspect {}: {error}", config.input.display()))?;
    if metadata.len() > transcript::MAX_TRANSCRIPT_BYTES {
        return Err(format!(
            "{} is {} bytes; the transcript ceiling is {}",
            config.input.display(),
            metadata.len(),
            transcript::MAX_TRANSCRIPT_BYTES
        ));
    }
    let file = File::open(&config.input)
        .map_err(|error| format!("could not open {}: {error}", config.input.display()))?;
    validate_reader(&mut BufReader::new(file), config.mode)
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
        Command::Validate(config) => match validate_path(&config) {
            Ok(receipt) => {
                print!("{receipt}");
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

    fn lifecycle() -> Vec<u8> {
        let mut bytes = Vec::new();
        for body in [
            r#"{"jsonrpc":"2.0","id":1.25e2,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":null,"method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ] {
            bytes.extend(frame(body));
        }
        bytes
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
        let receipt = validate_reader(
            &mut BufReader::new(Cursor::new(bytes)),
            ValidationMode::Syntax,
        )
        .unwrap();
        assert_eq!(
            receipt,
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
    fn argument_parser_honors_modes_stdin_and_end_of_options() {
        assert_eq!(
            parse_args(["fln-lsp-validate", "-"].map(OsString::from)),
            Ok(Command::Validate(Config {
                input: PathBuf::from("-"),
                mode: ValidationMode::Syntax,
            }))
        );
        assert_eq!(
            parse_args(
                ["fln-lsp-validate", "--client-lifecycle", "-"]
                    .map(OsString::from)
            ),
            Ok(Command::Validate(Config {
                input: PathBuf::from("-"),
                mode: ValidationMode::ClientLifecycle,
            }))
        );
        assert_eq!(
            parse_args(["fln-lsp-validate", "--", "--client-lifecycle"].map(OsString::from)),
            Ok(Command::Validate(Config {
                input: PathBuf::from("--client-lifecycle"),
                mode: ValidationMode::Syntax,
            }))
        );
        assert!(
            parse_args(
                [
                    "fln-lsp-validate",
                    "--client-lifecycle",
                    "--client-lifecycle",
                    "-",
                ]
                .map(OsString::from)
            )
            .unwrap_err()
            .contains("at most once")
        );
    }

    #[test]
    fn lifecycle_mode_emits_handshake_bound_receipt() {
        let bytes = lifecycle();
        let expected_wire_bytes = u64::try_from(bytes.len()).unwrap();
        let receipt = validate_reader(
            &mut BufReader::new(Cursor::new(bytes)),
            ValidationMode::ClientLifecycle,
        )
        .unwrap();
        assert!(receipt.contains("\"schema\":\"fln.lsp-client-lifecycle/1\""));
        assert!(receipt.contains("\"finalState\":\"exited\""));
        assert!(receipt.contains(&format!("\"wireBytes\":{expected_wire_bytes}")));
        assert!(receipt.contains("\"initializeFrame\":1"));
        assert!(receipt.contains("\"initializedFrame\":2"));
        assert!(receipt.contains("\"shutdownFrame\":3"));
        assert!(receipt.contains("\"exitFrame\":4"));
    }

    #[test]
    fn lifecycle_mode_rejects_empty_or_incomplete_transcripts() {
        for bytes in [
            Vec::new(),
            frame(r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#),
        ] {
            let error = validate_reader(
                &mut BufReader::new(Cursor::new(bytes)),
                ValidationMode::ClientLifecycle,
            )
            .unwrap_err();
            assert!(error.contains("expected exited"), "{error}");
        }
    }
}
