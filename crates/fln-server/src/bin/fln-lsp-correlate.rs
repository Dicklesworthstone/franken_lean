#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub use fln_server::{json_string, transport};

#[path = "../json.rs"]
mod json;
#[allow(dead_code)]
#[path = "../session_transcript.rs"]
mod session_transcript;
#[allow(dead_code, unused_imports)]
#[path = "../server_transcript.rs"]
mod server_transcript;
#[path = "../transcript.rs"]
pub mod transcript;
#[path = "../correlation.rs"]
mod correlation;

const MAX_TRANSCRIPT_BYTES: u64 = transcript::MAX_TRANSCRIPT_BYTES;
const USAGE: &str = "Usage: fln-lsp-correlate [--] CLIENT SERVER\n\
\n\
Join one strict document-semantic client transcript to one server transcript.\n\
Every unique canonical request ID must have exactly one result/error response,\n\
and the server may not emit unsolicited or duplicate responses. Number lexemes\n\
remain exact; string IDs compare by decoded value and canonical JSON escaping.\n\
The client pass also requires each cancellation to target one prior non-null\n\
request and carries wait/cancellation classes into the joined receipt.\n\
This proves identity and accounting correlation, not cross-stream timing.\n";

#[derive(Debug, Clone, PartialEq, Eq)]
struct Config {
    client: PathBuf,
    server: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Command {
    Help,
    Correlate(Config),
}

fn parse_args(arguments: impl IntoIterator<Item = OsString>) -> Result<Command, String> {
    let mut arguments = arguments.into_iter();
    let _program = arguments.next();
    let mut options = true;
    let mut paths = Vec::new();
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            continue;
        }
        if options && matches!(argument.to_str(), Some("-h" | "--help")) {
            if !paths.is_empty() || arguments.next().is_some() {
                return Err("--help cannot be combined with correlation arguments".to_string());
            }
            return Ok(Command::Help);
        }
        if options && argument.to_string_lossy().starts_with('-') {
            return Err(format!("unknown option: {}", argument.to_string_lossy()));
        }
        paths.push(PathBuf::from(argument));
        if paths.len() > 2 {
            return Err("exactly two transcripts are required".to_string());
        }
    }
    if paths.len() != 2 {
        return Err("exactly two transcripts are required".to_string());
    }
    let server = paths.pop().expect("length checked");
    let client = paths.pop().expect("length checked");
    if client == server {
        return Err("CLIENT and SERVER must be distinct paths".to_string());
    }
    Ok(Command::Correlate(Config { client, server }))
}

fn read_bounded(path: &Path, label: &str) -> Result<Vec<u8>, String> {
    let metadata = std::fs::metadata(path)
        .map_err(|error| format!("could not inspect {label} {}: {error}", path.display()))?;
    if metadata.len() > MAX_TRANSCRIPT_BYTES {
        return Err(format!(
            "{label} {} is {} bytes; the transcript ceiling is {MAX_TRANSCRIPT_BYTES}",
            path.display(),
            metadata.len()
        ));
    }
    let file = File::open(path)
        .map_err(|error| format!("could not open {label} {}: {error}", path.display()))?;
    let mut bytes = Vec::with_capacity(
        usize::try_from(metadata.len())
            .unwrap_or(usize::MAX)
            .min(1024 * 1024),
    );
    file.take(MAX_TRANSCRIPT_BYTES.saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|error| format!("could not read {label} {}: {error}", path.display()))?;
    if u64::try_from(bytes.len()).unwrap_or(u64::MAX) > MAX_TRANSCRIPT_BYTES {
        return Err(format!(
            "{label} {} grew beyond the transcript ceiling while being read",
            path.display()
        ));
    }
    Ok(bytes)
}

fn execute(config: &Config) -> Result<String, String> {
    let client = read_bounded(&config.client, "client transcript")?;
    let server = read_bounded(&config.server, "server transcript")?;
    correlation::correlate_transcripts(&client, &server).map(correlation::render_correlation)
}

fn main() -> ExitCode {
    let command = match parse_args(std::env::args_os()) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("fln-lsp-correlate: {error}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match command {
        Command::Help => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Command::Correlate(config) => match execute(&config) {
            Ok(receipt) => {
                print!("{receipt}");
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("fln-lsp-correlate: {error}");
                ExitCode::from(1)
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parser_is_exact_and_honors_end_of_options() {
        assert_eq!(
            parse_args(
                ["fln-lsp-correlate", "client.frames", "server.frames"]
                    .map(OsString::from)
            ),
            Ok(Command::Correlate(Config {
                client: PathBuf::from("client.frames"),
                server: PathBuf::from("server.frames"),
            }))
        );
        assert_eq!(
            parse_args(
                [
                    "fln-lsp-correlate",
                    "--",
                    "--client.frames",
                    "--server.frames",
                ]
                .map(OsString::from)
            ),
            Ok(Command::Correlate(Config {
                client: PathBuf::from("--client.frames"),
                server: PathBuf::from("--server.frames"),
            }))
        );
        for arguments in [
            vec!["fln-lsp-correlate"],
            vec!["fln-lsp-correlate", "one"],
            vec!["fln-lsp-correlate", "one", "two", "three"],
            vec!["fln-lsp-correlate", "same", "same"],
            vec!["fln-lsp-correlate", "--unknown", "one", "two"],
        ] {
            assert!(parse_args(arguments.into_iter().map(OsString::from)).is_err());
        }
    }
}
