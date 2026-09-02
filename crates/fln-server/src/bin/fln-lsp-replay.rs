#![forbid(unsafe_code)]

use std::ffi::OsString;
use std::fs::{self, File, OpenOptions};
use std::io::{self, BufRead, BufReader, Cursor, Read, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub use fln_server::{json_string, transport};

#[path = "../json.rs"]
mod json;
#[path = "../session_transcript.rs"]
mod session_transcript;
#[path = "../transcript.rs"]
pub mod transcript;

const MAX_TRANSCRIPT_BYTES: u64 = 256 * 1024 * 1024;
const MAX_REPLAY_OUTPUT_BYTES: usize = 256 * 1024 * 1024;
const USAGE: &str = "Usage: fln-lsp-replay [--client-lifecycle | --client-session] [--expect PATH] [--output PATH] [--] INPUT\n\
\n\
Replay one exact Content-Length-framed LSP client stream through FrankenLean.\n\
--client-lifecycle validates known method roles and a complete client handshake.\n\
--client-session additionally validates Full-sync document/version semantics.\n\
Both strict modes run before server execution, comparison, or output publication.\n\
--expect compares the complete server stream byte-for-byte.\n\
--output writes the actual server stream with create-new semantics.\n";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClientPreflight {
    None,
    Lifecycle,
    Session,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct Config {
    input: PathBuf,
    expect: Option<PathBuf>,
    output: Option<PathBuf>,
    preflight: ClientPreflight,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Command {
    Help,
    Replay(Config),
}

#[derive(Debug)]
struct BoundedOutput {
    bytes: Vec<u8>,
    max_bytes: usize,
}

impl BoundedOutput {
    fn new(max_bytes: usize) -> Self {
        Self {
            bytes: Vec::with_capacity(max_bytes.min(1024 * 1024)),
            max_bytes,
        }
    }

    fn into_bytes(self) -> Vec<u8> {
        self.bytes
    }
}

impl Write for BoundedOutput {
    fn write(&mut self, buffer: &[u8]) -> io::Result<usize> {
        let next_len = self
            .bytes
            .len()
            .checked_add(buffer.len())
            .ok_or_else(|| io::Error::other("replay output length overflow"))?;
        if next_len > self.max_bytes {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "replay output exceeds the {}-byte ceiling",
                    self.max_bytes
                ),
            ));
        }
        self.bytes.extend_from_slice(buffer);
        Ok(buffer.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn parse_args(arguments: impl IntoIterator<Item = OsString>) -> Result<Command, String> {
    let mut arguments = arguments.into_iter();
    let _program = arguments.next();
    let mut expect = None;
    let mut output = None;
    let mut input = None;
    let mut preflight = ClientPreflight::None;
    let mut strict_mode_seen = false;
    let mut options = true;

    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            continue;
        }
        if options && matches!(argument.to_str(), Some("-h" | "--help")) {
            if strict_mode_seen
                || expect.is_some()
                || output.is_some()
                || input.is_some()
                || arguments.next().is_some()
            {
                return Err("--help cannot be combined with replay arguments".to_string());
            }
            return Ok(Command::Help);
        }
        if options
            && matches!(
                argument.to_str(),
                Some("--client-lifecycle" | "--client-session")
            )
        {
            if strict_mode_seen {
                return Err(
                    "--client-lifecycle and --client-session are mutually exclusive and may be supplied at most once"
                        .to_string(),
                );
            }
            strict_mode_seen = true;
            preflight = if argument == "--client-session" {
                ClientPreflight::Session
            } else {
                ClientPreflight::Lifecycle
            };
            continue;
        }
        if options && argument == "--expect" {
            if expect.is_some() {
                return Err("--expect may be supplied at most once".to_string());
            }
            expect = Some(PathBuf::from(
                arguments
                    .next()
                    .ok_or_else(|| "--expect requires a path".to_string())?,
            ));
            continue;
        }
        if options && argument == "--output" {
            if output.is_some() {
                return Err("--output may be supplied at most once".to_string());
            }
            output = Some(PathBuf::from(
                arguments
                    .next()
                    .ok_or_else(|| "--output requires a path".to_string())?,
            ));
            continue;
        }
        if options && argument.to_string_lossy().starts_with('-') {
            return Err(format!("unknown option: {}", argument.to_string_lossy()));
        }
        if input.replace(PathBuf::from(argument)).is_some() {
            return Err("exactly one input transcript is required".to_string());
        }
    }

    let input = input.ok_or_else(|| "missing input transcript".to_string())?;
    if expect.as_ref().is_some_and(|path| path == &input) {
        return Err("--expect must not alias the input path".to_string());
    }
    if output.as_ref().is_some_and(|path| path == &input)
        || output
            .as_ref()
            .zip(expect.as_ref())
            .is_some_and(|(actual, expected)| actual == expected)
    {
        return Err("--output must not alias an input or expected transcript".to_string());
    }
    Ok(Command::Replay(Config {
        input,
        expect,
        output,
        preflight,
    }))
}

fn read_bounded(path: &Path, label: &str) -> Result<Vec<u8>, String> {
    let metadata = fs::metadata(path)
        .map_err(|error| format!("could not inspect {label} {}: {error}", path.display()))?;
    if metadata.len() > MAX_TRANSCRIPT_BYTES {
        return Err(format!(
            "{label} {} is {} bytes; the replay ceiling is {MAX_TRANSCRIPT_BYTES}",
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
            "{label} {} grew beyond the replay ceiling while being read",
            path.display()
        ));
    }
    Ok(bytes)
}

fn validate_client_transcript(input: &[u8], preflight: ClientPreflight) -> Result<(), String> {
    match preflight {
        ClientPreflight::None => Ok(()),
        ClientPreflight::Lifecycle => transcript::validate_client_lifecycle_bytes(input)
            .map(|_| ())
            .map_err(|error| format!("client lifecycle validation failed: {error}")),
        ClientPreflight::Session => session_transcript::validate_client_session_bytes(input)
            .map(|_| ())
            .map_err(|error| format!("client session validation failed: {error}")),
    }
}

fn replay_with_output_limit(input: &[u8], max_output_bytes: usize) -> Result<Vec<u8>, String> {
    let mut reader = BufReader::new(Cursor::new(input));
    let mut actual = BoundedOutput::new(max_output_bytes);
    let mut document_callback = |uri: &str, _text: &str| {
        vec![format!(
            concat!(
                "{{\"jsonrpc\":\"2.0\",",
                "\"method\":\"textDocument/publishDiagnostics\",",
                "\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}"
            ),
            fln_server::json_string(uri)
        )]
    };
    let outcome = fln_server::dispatch::serve(&mut reader, &mut actual, &mut document_callback)
        .map_err(|error| format!("Lantern rejected the replay stream: {error}"))?;
    if !outcome.clean {
        return Err("replay ended without the shutdown/exit handshake".to_string());
    }
    if !reader
        .fill_buf()
        .map_err(|error| format!("could not inspect replay tail: {error}"))?
        .is_empty()
    {
        return Err("replay contains bytes after the exit notification".to_string());
    }
    Ok(actual.into_bytes())
}

fn replay(input: &[u8]) -> Result<Vec<u8>, String> {
    replay_with_output_limit(input, MAX_REPLAY_OUTPUT_BYTES)
}

fn first_difference(actual: &[u8], expected: &[u8]) -> Option<usize> {
    actual
        .iter()
        .zip(expected)
        .position(|(left, right)| left != right)
        .or_else(|| (actual.len() != expected.len()).then_some(actual.len().min(expected.len())))
}

fn write_output(path: Option<&Path>, bytes: &[u8]) -> Result<(), String> {
    match path {
        Some(path) => {
            let mut output = OpenOptions::new()
                .create_new(true)
                .write(true)
                .open(path)
                .map_err(|error| {
                    format!(
                        "could not create output {} without overwriting it: {error}",
                        path.display()
                    )
                })?;
            output
                .write_all(bytes)
                .and_then(|()| output.sync_all())
                .map_err(|error| format!("could not publish output {}: {error}", path.display()))
        }
        None => {
            let stdout = io::stdout();
            let mut output = stdout.lock();
            output
                .write_all(bytes)
                .and_then(|()| output.flush())
                .map_err(|error| format!("could not write replay output: {error}"))
        }
    }
}

fn execute(config: &Config) -> Result<(), String> {
    let input = read_bounded(&config.input, "input transcript")?;
    validate_client_transcript(&input, config.preflight)?;
    let actual = replay(&input)?;
    let mismatch = if let Some(expected_path) = config.expect.as_deref() {
        let expected = read_bounded(expected_path, "expected transcript")?;
        first_difference(&actual, &expected).map(|offset| (offset, expected.len()))
    } else {
        None
    };
    write_output(config.output.as_deref(), &actual)?;
    if let Some((offset, expected_len)) = mismatch {
        return Err(format!(
            "server transcript diverged at byte {offset}: actual length {}, expected length {expected_len}",
            actual.len()
        ));
    }
    Ok(())
}

fn main() -> ExitCode {
    let command = match parse_args(std::env::args_os()) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("fln-lsp-replay: {error}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match command {
        Command::Help => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Command::Replay(config) => match execute(&config) {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("fln-lsp-replay: {error}");
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

    fn framed(bodies: &[&str]) -> Vec<u8> {
        let mut input = Vec::new();
        for body in bodies {
            input.extend(frame(body));
        }
        input
    }

    fn clean_session() -> Vec<u8> {
        framed(&[
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ])
    }

    #[test]
    fn argument_parser_is_deterministic_and_honors_end_of_options() {
        assert_eq!(
            parse_args(["fln-lsp-replay", "--", "--client.frames"].map(OsString::from)),
            Ok(Command::Replay(Config {
                input: PathBuf::from("--client.frames"),
                expect: None,
                output: None,
                preflight: ClientPreflight::None,
            }))
        );
        assert_eq!(
            parse_args(
                ["fln-lsp-replay", "--client-lifecycle", "input.frames"]
                    .map(OsString::from)
            ),
            Ok(Command::Replay(Config {
                input: PathBuf::from("input.frames"),
                expect: None,
                output: None,
                preflight: ClientPreflight::Lifecycle,
            }))
        );
        assert_eq!(
            parse_args(
                ["fln-lsp-replay", "--client-session", "input.frames"]
                    .map(OsString::from)
            ),
            Ok(Command::Replay(Config {
                input: PathBuf::from("input.frames"),
                expect: None,
                output: None,
                preflight: ClientPreflight::Session,
            }))
        );
        for arguments in [
            vec!["fln-lsp-replay"],
            vec!["fln-lsp-replay", "--expect"],
            vec!["fln-lsp-replay", "--expect", "a", "--expect", "b", "c"],
            vec!["fln-lsp-replay", "--output", "a", "--output", "b", "c"],
            vec![
                "fln-lsp-replay",
                "--client-lifecycle",
                "--client-lifecycle",
                "c",
            ],
            vec![
                "fln-lsp-replay",
                "--client-session",
                "--client-session",
                "c",
            ],
            vec![
                "fln-lsp-replay",
                "--client-lifecycle",
                "--client-session",
                "c",
            ],
            vec!["fln-lsp-replay", "--unknown", "c"],
            vec!["fln-lsp-replay", "a", "b"],
        ] {
            assert!(
                parse_args(arguments.into_iter().map(OsString::from)).is_err(),
                "accepted ambiguous arguments"
            );
        }
    }

    #[test]
    fn bounded_output_refuses_before_mutating_the_failing_write() {
        let mut output = BoundedOutput::new(3);
        output.write_all(b"abc").unwrap();
        let error = output.write_all(b"d").unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert_eq!(output.into_bytes(), b"abc");
    }

    #[test]
    fn clean_transcript_replays_deterministically() {
        let input = clean_session();
        let first = replay(&input).unwrap();
        let second = replay(&input).unwrap();
        assert_eq!(first, second);
        assert!(
            first
                .windows(b"FrankenLean".len())
                .any(|window| window == b"FrankenLean")
        );
        assert!(validate_client_transcript(&input, ClientPreflight::Lifecycle).is_ok());
        assert!(validate_client_transcript(&input, ClientPreflight::Session).is_ok());
    }

    #[test]
    fn lifecycle_preflight_rejects_role_inversion_but_default_replay_remains_available() {
        let input = framed(&[
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"bad-open","method":"textDocument/didOpen","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        assert!(replay(&input).is_ok());
        let error = validate_client_transcript(&input, ClientPreflight::Lifecycle).unwrap_err();
        assert!(error.contains("notification-only method"), "{error}");
    }

    #[test]
    fn session_preflight_rejects_document_state_that_lifecycle_mode_allows() {
        let input = framed(&[
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///A","version":2},"contentChanges":[{"text":"source"}]}}"#,
            r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        assert!(validate_client_transcript(&input, ClientPreflight::Lifecycle).is_ok());
        let error = validate_client_transcript(&input, ClientPreflight::Session).unwrap_err();
        assert!(error.contains("targets unopened document"), "{error}");
    }

    #[test]
    fn replay_output_is_bounded_independently_of_input() {
        let error = replay_with_output_limit(&clean_session(), 1).unwrap_err();
        assert!(error.contains("replay output exceeds the 1-byte ceiling"));
    }

    #[test]
    fn unclean_and_post_exit_transcripts_are_refused() {
        let mut unclean = Vec::new();
        unclean.extend(frame(
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        ));
        assert!(replay(&unclean).unwrap_err().contains("shutdown/exit"));

        let mut trailing = clean_session();
        trailing.extend(frame(
            r#"{"jsonrpc":"2.0","id":3,"method":"shutdown"}"#,
        ));
        assert!(replay(&trailing).unwrap_err().contains("after the exit"));
    }

    #[test]
    fn first_difference_covers_content_and_length_divergence() {
        assert_eq!(first_difference(b"abc", b"abc"), None);
        assert_eq!(first_difference(b"abc", b"axc"), Some(1));
        assert_eq!(first_difference(b"abc", b"abcd"), Some(3));
        assert_eq!(first_difference(b"abcd", b"abc"), Some(3));
    }
}
