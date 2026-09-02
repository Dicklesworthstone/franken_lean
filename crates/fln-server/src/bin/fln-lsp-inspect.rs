#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub use fln_server::{json_string, transport};

#[path = "../json.rs"]
mod json;
#[path = "../transcript.rs"]
pub mod transcript;

const MAX_OUTPUT_BYTES: usize = 256 * 1024 * 1024;
const DEFAULT_MAX_FRAMES: u64 = transcript::MAX_TRANSCRIPT_FRAMES;
const USAGE: &str = "Usage: fln-lsp-inspect [--max-frames N] [--] INPUT\n\
\n\
Inspect one exact Content-Length-framed JSON-RPC transcript as NDJSON.\n\
Use INPUT=- to read standard input. Parameter contents and source text are not\n\
emitted; each row exposes only the validated params container kind.\n";

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

fn params_kind_name(kind: transcript::TranscriptParamsKind) -> &'static str {
    match kind {
        transcript::TranscriptParamsKind::Missing => "missing",
        transcript::TranscriptParamsKind::Object => "object",
        transcript::TranscriptParamsKind::Array => "array",
        transcript::TranscriptParamsKind::Null => "null",
    }
}

fn render_frame(frame: &transcript::TranscriptFrame) -> String {
    let role = match frame.role {
        transcript::TranscriptRole::Request => "request",
        transcript::TranscriptRole::Notification => "notification",
    };
    let id = frame.id_json.as_deref().unwrap_or("null");
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-frame/2\",\"index\":{},",
            "\"role\":{},\"method\":{},\"id\":{},",
            "\"paramsKind\":{},\"bodyBytes\":{}}}\n"
        ),
        frame.index,
        json_string(role),
        json_string(&frame.method),
        id,
        json_string(params_kind_name(frame.params_kind)),
        frame.body_bytes
    )
}

fn inspect_reader(input: &mut dyn BufRead, max_frames: u64) -> Result<String, String> {
    let mut output = String::new();
    transcript::visit_reader(input, max_frames, |frame| {
        let row = render_frame(frame);
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
        Ok(())
    })?;
    Ok(output)
}

fn inspect_path(config: &Config) -> Result<String, String> {
    if config.input == Path::new("-") {
        let stdin = io::stdin();
        return inspect_reader(&mut BufReader::new(stdin.lock()), config.max_frames);
    }
    let metadata = std::fs::metadata(&config.input)
        .map_err(|error| format!("could not inspect {}: {error}", config.input.display()))?;
    if metadata.len() > transcript::MAX_TRANSCRIPT_BYTES {
        return Err(format!(
            "{} is {} bytes; the input ceiling is {}",
            config.input.display(),
            metadata.len(),
            transcript::MAX_TRANSCRIPT_BYTES
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
    fn inspection_is_deterministic_and_omits_parameter_contents() {
        let body = r#"{"jsonrpc":"2.0","id":"req-1","method":"textDocument/didOpen","params":{"textDocument":{"text":"secret source"}}}"#;
        let first = inspect_reader(&mut BufReader::new(Cursor::new(frame(body))), 10).unwrap();
        let second = inspect_reader(&mut BufReader::new(Cursor::new(frame(body))), 10).unwrap();
        assert_eq!(first, second);
        assert!(first.contains("\"schema\":\"fln.lsp-frame/2\""));
        assert!(first.contains("\"role\":\"request\""));
        assert!(first.contains("\"id\":\"req-1\""));
        assert!(first.contains("\"method\":\"textDocument/didOpen\""));
        assert!(first.contains("\"paramsKind\":\"object\""));
        assert!(!first.contains("secret source"));
        assert!(!first.contains("\"params\":"));
    }

    #[test]
    fn role_id_and_parameter_kind_remain_distinct() {
        let notification = render_frame(
            &transcript::validate_frame(
                br#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
                1,
            )
            .unwrap(),
        );
        let request = render_frame(
            &transcript::validate_frame(
                br#"{"jsonrpc":"2.0","id":null,"method":"shutdown"}"#,
                2,
            )
            .unwrap(),
        );
        let array = render_frame(
            &transcript::validate_frame(
                br#"{"jsonrpc":"2.0","method":"extension/example","params":[]}"#,
                3,
            )
            .unwrap(),
        );
        assert!(notification.contains("\"role\":\"notification\""));
        assert!(notification.contains("\"paramsKind\":\"null\""));
        assert!(request.contains("\"role\":\"request\""));
        assert!(request.contains("\"id\":null"));
        assert!(request.contains("\"paramsKind\":\"missing\""));
        assert!(array.contains("\"paramsKind\":\"array\""));
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
    fn invalid_scalar_params_follow_shared_validation() {
        let error = inspect_reader(
            &mut BufReader::new(Cursor::new(frame(
                r#"{"jsonrpc":"2.0","method":"initialized","params":null}"#,
            ))),
            10,
        )
        .unwrap_err();
        assert!(error.contains("only shutdown/exit may use null"));
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
