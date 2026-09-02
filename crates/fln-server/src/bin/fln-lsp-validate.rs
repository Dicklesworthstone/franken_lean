#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Cursor};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub use fln_server::json_string;

#[path = "../json.rs"]
mod json;

const MAX_TRANSCRIPT_BYTES: u64 = 256 * 1024 * 1024;
const MAX_FRAMES: u64 = 1_000_000;
const USAGE: &str = "Usage: fln-lsp-validate [--] INPUT\n\
\n\
Validate one exact Content-Length-framed JSON-RPC client transcript.\n\
Use INPUT=- to read standard input.\n";

#[derive(Debug, Clone, PartialEq, Eq)]
enum Command {
    Help,
    Validate(PathBuf),
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct Stats {
    frames: u64,
    requests: u64,
    notifications: u64,
    body_bytes: u64,
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

fn validate_envelope(body: &[u8], frame: u64) -> Result<bool, String> {
    let text = std::str::from_utf8(body)
        .map_err(|_| format!("frame {frame} body is not valid UTF-8"))?;
    let envelope = json::parse_envelope(text).map_err(|error| match error {
        json::EnvelopeError::MalformedJson => format!("frame {frame} contains malformed JSON"),
        json::EnvelopeError::NotObject => {
            format!("frame {frame} is not a JSON-RPC object")
        }
    })?;
    match envelope.jsonrpc {
        json::DecodedField::Valid(version) if version == "2.0" => {}
        json::DecodedField::Missing => {
            return Err(format!("frame {frame} is missing jsonrpc=2.0"));
        }
        json::DecodedField::Valid(version) => {
            return Err(format!(
                "frame {frame} has unsupported JSON-RPC version {version:?}"
            ));
        }
        json::DecodedField::Invalid => {
            return Err(format!("frame {frame} has a non-string jsonrpc field"));
        }
    }
    match envelope.method {
        json::DecodedField::Valid(_) => {}
        json::DecodedField::Missing => {
            return Err(format!("frame {frame} is missing a method"));
        }
        json::DecodedField::Invalid => {
            return Err(format!("frame {frame} has a non-string method"));
        }
    }
    match envelope.params {
        json::RawField::Missing => {}
        json::RawField::Value(value)
            if matches!(value.trim_start().as_bytes().first(), Some(b'{' | b'[')) => {}
        json::RawField::Value(_) => {
            return Err(format!(
                "frame {frame} params must be an object or array when present"
            ));
        }
        json::RawField::Invalid => {
            return Err(format!("frame {frame} has ambiguous params"));
        }
    }
    match envelope.id {
        json::RequestIdField::Absent => Ok(false),
        json::RequestIdField::Valid(_) => Ok(true),
        json::RequestIdField::Invalid => Err(format!("frame {frame} has an invalid request id")),
    }
}

fn validate_reader(input: &mut dyn BufRead) -> Result<Stats, String> {
    let mut stats = Stats::default();
    loop {
        let Some(body) = fln_server::transport::read_message(input)
            .map_err(|error| format!("frame {} transport failure: {error}", stats.frames + 1))?
        else {
            break;
        };
        stats.frames = stats
            .frames
            .checked_add(1)
            .ok_or_else(|| "frame count overflow".to_string())?;
        if stats.frames > MAX_FRAMES {
            return Err(format!("transcript exceeds the {MAX_FRAMES}-frame ceiling"));
        }
        stats.body_bytes = stats
            .body_bytes
            .checked_add(u64::try_from(body.len()).unwrap_or(u64::MAX))
            .ok_or_else(|| "transcript byte accounting overflow".to_string())?;
        if stats.body_bytes > MAX_TRANSCRIPT_BYTES {
            return Err(format!(
                "transcript bodies exceed the {MAX_TRANSCRIPT_BYTES}-byte aggregate ceiling"
            ));
        }
        if validate_envelope(&body, stats.frames)? {
            stats.requests = stats
                .requests
                .checked_add(1)
                .ok_or_else(|| "request count overflow".to_string())?;
        } else {
            stats.notifications = stats
                .notifications
                .checked_add(1)
                .ok_or_else(|| "notification count overflow".to_string())?;
        }
    }
    Ok(stats)
}

fn validate_path(path: &Path) -> Result<Stats, String> {
    if path == Path::new("-") {
        let stdin = io::stdin();
        return validate_reader(&mut BufReader::new(stdin.lock()));
    }
    let metadata = std::fs::metadata(path)
        .map_err(|error| format!("could not inspect {}: {error}", path.display()))?;
    if metadata.len() > MAX_TRANSCRIPT_BYTES {
        return Err(format!(
            "{} is {} bytes; the transcript ceiling is {MAX_TRANSCRIPT_BYTES}",
            path.display(),
            metadata.len()
        ));
    }
    let file = File::open(path)
        .map_err(|error| format!("could not open {}: {error}", path.display()))?;
    validate_reader(&mut BufReader::new(file))
}

fn render(stats: Stats) -> String {
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-transcript-validation/1\",",
            "\"frames\":{},\"requests\":{},\"notifications\":{},",
            "\"bodyBytes\":{}}}\n"
        ),
        stats.frames, stats.requests, stats.notifications, stats.body_bytes
    )
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
                print!("{}", render(stats));
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

    fn frame(body: &str) -> Vec<u8> {
        let mut framed = Vec::new();
        fln_server::transport::write_message(&mut framed, body.as_bytes()).unwrap();
        framed
    }

    #[test]
    fn validates_requests_and_notifications_without_normalizing_ids() {
        let mut transcript = Vec::new();
        transcript.extend(frame(
            r#"{"jsonrpc":"2.0","id":1.25e2,"method":"initialize","params":{}}"#,
        ));
        transcript.extend(frame(
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        ));
        transcript.extend(frame(
            r#"{"jsonrpc":"2.0","id":null,"method":"shutdown"}"#,
        ));
        let stats = validate_reader(&mut BufReader::new(Cursor::new(transcript))).unwrap();
        assert_eq!(
            stats,
            Stats {
                frames: 3,
                requests: 2,
                notifications: 1,
                body_bytes: 199,
            }
        );
        assert_eq!(
            render(stats),
            "{\"schema\":\"fln.lsp-transcript-validation/1\",\"frames\":3,\"requests\":2,\"notifications\":1,\"bodyBytes\":199}\n"
        );
    }

    #[test]
    fn names_the_first_invalid_frame_and_reason() {
        for (body, reason) in [
            (r#"{"jsonrpc":"2.0","method":3}"#, "non-string method"),
            (r#"{"jsonrpc":"1.0","method":"x"}"#, "unsupported JSON-RPC version"),
            (r#"{"jsonrpc":"2.0","method":"x","params":3}"#, "params must be an object or array"),
            (r#"[]"#, "not a JSON-RPC object"),
            (r#"{"jsonrpc":"2.0","method":"x",}"#, "malformed JSON"),
        ] {
            let error = validate_reader(&mut BufReader::new(Cursor::new(frame(body)))).unwrap_err();
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
