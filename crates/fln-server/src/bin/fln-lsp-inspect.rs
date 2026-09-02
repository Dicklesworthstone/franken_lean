#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub use fln_server::json_string;

#[path = "../json.rs"]
mod json;

const MAX_INPUT_BYTES: u64 = 256 * 1024 * 1024;
const MAX_OUTPUT_BYTES: usize = 256 * 1024 * 1024;
const DEFAULT_MAX_FRAMES: u64 = 1_000_000;
const USAGE: &str = "Usage: fln-lsp-inspect [--max-frames N] [--] INPUT\n\
\n\
Inspect one exact Content-Length-framed JSON-RPC transcript as NDJSON.\n\
Use INPUT=- to read standard input. Document params and source text are not emitted.\n";

#[derive(Debug, Clone, PartialEq, Eq)]
struct Config {
    input: PathBuf,
    max_frames: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Command {
    Help,
    Inspect(Config),
}

fn parse_positive_u64(value: OsString, option: &str) -> Result<u64, String> {
    let value = value
        .into_string()
        .map_err(|_| format!("{option} must be valid UTF-8 decimal text"))?;
    if value.is_empty() || value.bytes().any(|byte| !byte.is_ascii_digit()) {
        return Err(format!("{option} must be a positive decimal integer"));
    }
    let parsed = value
        .parse::<u64>()
        .map_err(|_| format!("{option} is outside the supported integer range"))?;
    if parsed == 0 || parsed > DEFAULT_MAX_FRAMES {
        return Err(format!(
            "{option} must be between 1 and {DEFAULT_MAX_FRAMES}"
        ));
    }
    Ok(parsed)
}

fn parse_args(arguments: impl IntoIterator<Item = OsString>) -> Result<Command, String> {
    let mut arguments = arguments.into_iter();
    let _program = arguments.next();
    let mut max_frames = DEFAULT_MAX_FRAMES;
    let mut max_frames_seen = false;
    let mut input = None;
    let mut options = true;
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            continue;
        }
        if options && matches!(argument.to_str(), Some("-h" | "--help")) {
            if max_frames_seen || input.is_some() || arguments.next().is_some() {
                return Err("--help cannot be combined with inspection arguments".to_string());
            }
            return Ok(Command::Help);
        }
        if options && argument == "--max-frames" {
            if max_frames_seen {
                return Err("--max-frames may be supplied at most once".to_string());
            }
            max_frames_seen = true;
            max_frames = parse_positive_u64(
                arguments
                    .next()
                    .ok_or_else(|| "--max-frames requires a value".to_string())?,
                "--max-frames",
            )?;
            continue;
        }
        if options && argument.to_string_lossy().starts_with('-') && argument != "-" {
            return Err(format!("unknown option: {}", argument.to_string_lossy()));
        }
        if input.replace(PathBuf::from(argument)).is_some() {
            return Err("exactly one transcript is required".to_string());
        }
    }
    Ok(Command::Inspect(Config {
        input: input.ok_or_else(|| "missing input transcript".to_string())?,
        max_frames,
    }))
}

fn inspect_body(body: &[u8], index: u64) -> Result<String, String> {
    let text = std::str::from_utf8(body)
        .map_err(|_| format!("frame {index} body is not valid UTF-8"))?;
    let envelope = json::parse_envelope(text).map_err(|error| match error {
        json::EnvelopeError::MalformedJson => format!("frame {index} contains malformed JSON"),
        json::EnvelopeError::NotObject => format!("frame {index} is not a JSON-RPC object"),
    })?;
    match envelope.jsonrpc {
        json::DecodedField::Valid(version) if version == "2.0" => {}
        json::DecodedField::Missing => {
            return Err(format!("frame {index} is missing jsonrpc=2.0"));
        }
        json::DecodedField::Valid(version) => {
            return Err(format!(
                "frame {index} has unsupported JSON-RPC version {version:?}"
            ));
        }
        json::DecodedField::Invalid => {
            return Err(format!("frame {index} has a non-string jsonrpc field"));
        }
    }
    let method = match envelope.method {
        json::DecodedField::Valid(method) => method,
        json::DecodedField::Missing => return Err(format!("frame {index} is missing a method")),
        json::DecodedField::Invalid => {
            return Err(format!("frame {index} has a non-string method"));
        }
    };
    let (role, id) = match envelope.id {
        json::RequestIdField::Absent => ("notification", "null".to_string()),
        json::RequestIdField::Valid(id) => ("request", id.as_json()),
        json::RequestIdField::Invalid => {
            return Err(format!("frame {index} has an invalid request id"));
        }
    };
    Ok(format!(
        concat!(
            "{{\"schema\":\"fln.lsp-frame/1\",\"index\":{},",
            "\"role\":{},\"method\":{},\"id\":{},\"bodyBytes\":{}}}\n"
        ),
        index,
        json_string(role),
        json_string(&method),
        id,
        body.len()
    ))
}

fn inspect_reader(input: &mut dyn BufRead, max_frames: u64) -> Result<String, String> {
    let mut output = String::new();
    let mut frames = 0u64;
    let mut body_bytes = 0u64;
    loop {
        let Some(body) = fln_server::transport::read_message(input)
            .map_err(|error| format!("frame {} transport failure: {error}", frames + 1))?
        else {
            break;
        };
        frames = frames
            .checked_add(1)
            .ok_or_else(|| "frame count overflow".to_string())?;
        if frames > max_frames {
            return Err(format!(
                "transcript exceeds the selected {max_frames}-frame ceiling"
            ));
        }
        body_bytes = body_bytes
            .checked_add(u64::try_from(body.len()).unwrap_or(u64::MAX))
            .ok_or_else(|| "input byte accounting overflow".to_string())?;
        if body_bytes > MAX_INPUT_BYTES {
            return Err(format!(
                "transcript bodies exceed the {MAX_INPUT_BYTES}-byte aggregate ceiling"
            ));
        }
        let row = inspect_body(&body, frames)?;
        let next_len = output
            .len()
            .checked_add(row.len())
            .ok_or_else(|| "inspection output length overflow".to_string())?;
        if next_len > MAX_OUTPUT_BYTES {
            return Err(format!(
                "inspection output exceeds the {MAX_OUTPUT_BYTES}-byte ceiling"
            ));
        }
        output.push_str(&row);
    }
    Ok(output)
}

fn inspect_path(config: &Config) -> Result<String, String> {
    if config.input == Path::new("-") {
        let stdin = io::stdin();
        return inspect_reader(&mut BufReader::new(stdin.lock()), config.max_frames);
    }
    let metadata = std::fs::metadata(&config.input)
        .map_err(|error| format!("could not inspect {}: {error}", config.input.display()))?;
    if metadata.len() > MAX_INPUT_BYTES {
        return Err(format!(
            "{} is {} bytes; the input ceiling is {MAX_INPUT_BYTES}",
            config.input.display(),
            metadata.len()
        ));
    }
    let file = File::open(&config.input)
        .map_err(|error| format!("could not open {}: {error}", config.input.display()))?;
    inspect_reader(&mut BufReader::new(file), config.max_frames)
}

fn main() -> ExitCode {
    let command = match parse_args(std::env::args_os()) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("fln-lsp-inspect: {error}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match command {
        Command::Help => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Command::Inspect(config) => match inspect_path(&config) {
            Ok(output) => {
                if let Err(error) = io::stdout()
                    .lock()
                    .write_all(output.as_bytes())
                    .and_then(|()| io::stdout().lock().flush())
                {
                    eprintln!("fln-lsp-inspect: could not write output: {error}");
                    return ExitCode::from(1);
                }
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("fln-lsp-inspect: {error}");
                ExitCode::from(1)
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    fn frame(body: &str) -> Vec<u8> {
        let mut framed = Vec::new();
        fln_server::transport::write_message(&mut framed, body.as_bytes()).unwrap();
        framed
    }

    #[test]
    fn inspection_is_deterministic_and_omits_params() {
        let body = r#"{"jsonrpc":"2.0","id":"req-1","method":"textDocument/didOpen","params":{"textDocument":{"text":"secret source"}}}"#;
        let first = inspect_reader(&mut BufReader::new(Cursor::new(frame(body))), 10).unwrap();
        let second = inspect_reader(&mut BufReader::new(Cursor::new(frame(body))), 10).unwrap();
        assert_eq!(first, second);
        assert!(first.contains("\"role\":\"request\""));
        assert!(first.contains("\"id\":\"req-1\""));
        assert!(first.contains("\"method\":\"textDocument/didOpen\""));
        assert!(!first.contains("secret source"));
        assert!(!first.contains("params"));
    }

    #[test]
    fn notification_and_null_id_request_are_distinct() {
        let notification = inspect_body(
            br#"{"jsonrpc":"2.0","method":"initialized"}"#,
            1,
        )
        .unwrap();
        let request = inspect_body(
            br#"{"jsonrpc":"2.0","id":null,"method":"shutdown"}"#,
            2,
        )
        .unwrap();
        assert!(notification.contains("\"role\":\"notification\""));
        assert!(request.contains("\"role\":\"request\""));
        assert!(request.contains("\"id\":null"));
    }

    #[test]
    fn output_is_failure_atomic_when_a_later_frame_is_invalid() {
        let mut transcript = frame(r#"{"jsonrpc":"2.0","method":"initialized"}"#);
        transcript.extend(frame(r#"{"jsonrpc":"2.0","method":3}"#));
        let error = inspect_reader(&mut BufReader::new(Cursor::new(transcript)), 10).unwrap_err();
        assert!(error.contains("frame 2"));
    }

    #[test]
    fn selected_frame_limit_is_a_refusal_not_truncation() {
        let mut transcript = frame(r#"{"jsonrpc":"2.0","method":"one"}"#);
        transcript.extend(frame(r#"{"jsonrpc":"2.0","method":"two"}"#));
        assert!(
            inspect_reader(&mut BufReader::new(Cursor::new(transcript)), 1)
                .unwrap_err()
                .contains("1-frame ceiling")
        );
    }

    #[test]
    fn argument_parser_honors_end_of_options_and_rejects_duplicates() {
        assert_eq!(
            parse_args(
                ["fln-lsp-inspect", "--max-frames", "12", "--", "--capture"]
                    .map(OsString::from)
            ),
            Ok(Command::Inspect(Config {
                input: PathBuf::from("--capture"),
                max_frames: 12,
            }))
        );
        assert!(
            parse_args(
                [
                    "fln-lsp-inspect",
                    "--max-frames",
                    "1",
                    "--max-frames",
                    "2",
                    "input",
                ]
                .map(OsString::from)
            )
            .is_err()
        );
    }
}
