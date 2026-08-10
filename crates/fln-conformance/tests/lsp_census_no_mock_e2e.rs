//! Real pinned-Reference proof for the LSP wire census (bead `fln-i9so`).
//!
//! The fixture half runs Lean's own `Lean.Server.Test.Runner` against the real
//! `lean --server` child and compares the normalized bytes with upstream's
//! checked-in goldens. The protocol half starts a second real server with a
//! deliberately minimal, non-VS-Code capability profile: unknown initialize
//! fields and nullable optional fields are accepted, unknown/malformed requests
//! return errors, and a valid request afterward proves the same process remains
//! usable.

#![forbid(unsafe_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsString;
use std::io::{BufRead, BufReader, Read, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

use fln_conformance::lsp_census::{
    LspInventory, MessageDirection, MessageFamily, ProtocolMethod, SemanticDisposition,
    SemanticEvent, TelemetryEvent, TranscriptBundle, fixture_content_hash,
    normalize_reference_transcript,
};
use fln_conformance::pin;

const FIXTURES: &[&str] = &[
    "cancellation.lean",
    "inlayHints.lean",
    "interactiveDiagnostics.lean",
    "moduleHierarchyImports.lean",
    "plainGoal.lean",
    "plainTermGoal.lean",
    "semanticTokens.lean",
    "userWidget.lean",
];

fn toolchain_path(lean: &Path) -> Result<OsString, String> {
    let bin = lean
        .parent()
        .ok_or_else(|| format!("pinned lean path has no parent: {}", lean.display()))?;
    let mut paths = vec![bin.to_path_buf()];
    if let Some(ambient) = std::env::var_os("PATH") {
        paths.extend(std::env::split_paths(&ambient));
    }
    std::env::join_paths(paths).map_err(|error| format!("construct pinned PATH: {error}"))
}

fn toolchain_root(lean: &Path) -> Result<&Path, String> {
    lean.parent()
        .and_then(Path::parent)
        .ok_or_else(|| format!("pinned lean path has no toolchain root: {}", lean.display()))
}

fn run_reference_fixture(
    lean: &Path,
    path: &OsString,
    fixture_root: &Path,
    fixture: &str,
) -> Result<(String, u64), String> {
    let started = Instant::now();
    let output = Command::new(lean)
        .args(["-Dlinter.all=false", "--run", "run_test.lean", fixture])
        .env("PATH", path)
        .current_dir(fixture_root)
        .output()
        .map_err(|error| format!("run pinned Reference fixture {fixture}: {error}"))?;
    let elapsed = started.elapsed().as_micros().min(u128::from(u64::MAX)) as u64;
    if !output.status.success() {
        return Err(format!(
            "pinned Reference fixture {fixture} exited {:?}: {}",
            output.status.code(),
            String::from_utf8_lossy(&output.stderr)
        ));
    }
    if !output.stdout.is_empty() {
        return Err(format!(
            "pinned Reference fixture {fixture} wrote {} unexpected stdout bytes",
            output.stdout.len()
        ));
    }
    let stderr = String::from_utf8(output.stderr)
        .map_err(|_| format!("pinned Reference fixture {fixture} emitted non-UTF-8"))?;
    Ok((stderr, elapsed))
}

struct ServerHarness {
    child: Child,
    input: ChildStdin,
    frames: Receiver<Result<String, String>>,
    reader: Option<JoinHandle<()>>,
    transcript: Vec<String>,
}

impl ServerHarness {
    fn start(lean: &Path, path: &OsString, cwd: &Path) -> Result<Self, String> {
        let mut child = Command::new(lean)
            .args([
                "--server",
                "-DstderrAsMessages=false",
                "-Dexperimental.module=true",
            ])
            .env("PATH", path)
            .current_dir(cwd)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|error| format!("start pinned lean --server: {error}"))?;
        let input = child
            .stdin
            .take()
            .ok_or_else(|| "pinned server has no stdin".to_string())?;
        let output = child
            .stdout
            .take()
            .ok_or_else(|| "pinned server has no stdout".to_string())?;
        let (sender, frames) = mpsc::channel();
        let reader = std::thread::spawn(move || {
            let mut reader = BufReader::new(output);
            loop {
                let result = read_frame(&mut reader);
                let terminal = result
                    .as_ref()
                    .is_err_and(|error| error == "server stream closed");
                if sender.send(result).is_err() || terminal {
                    break;
                }
            }
        });
        Ok(Self {
            child,
            input,
            frames,
            reader: Some(reader),
            transcript: Vec::new(),
        })
    }

    fn send(&mut self, json: &str) -> Result<(), String> {
        if json.contains(['\r', '\n']) {
            return Err("outbound JSON-RPC frame is not one canonical line".to_string());
        }
        write!(self.input, "Content-Length: {}\r\n\r\n{json}", json.len())
            .map_err(|error| format!("write pinned server frame: {error}"))?;
        self.input
            .flush()
            .map_err(|error| format!("flush pinned server frame: {error}"))
    }

    fn response(&mut self, id: u64) -> Result<String, String> {
        let deadline = Instant::now() + Duration::from_secs(20);
        let expected_id = id.to_string();
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            let Some(compact) = self.next_frame(remaining)? else {
                return Err(format!("timed out waiting for pinned server response {id}"));
            };
            if jsonrpc_id_token(&compact).as_deref() == Some(expected_id.as_str()) {
                return Ok(compact);
            }
        }
    }

    fn next_frame(&mut self, timeout: Duration) -> Result<Option<String>, String> {
        let frame = match self.frames.recv_timeout(timeout) {
            Ok(frame) => frame?,
            Err(mpsc::RecvTimeoutError::Timeout) => return Ok(None),
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                return Err("pinned server frame reader disconnected".to_string());
            }
        };
        let compact = compact_json(&frame);
        self.transcript.push(frame);
        for method in [
            "client/registerCapability",
            "workspace/inlayHint/refresh",
            "workspace/semanticTokens/refresh",
        ] {
            if compact.contains(&format!("\"method\":\"{method}\""))
                && let Some(id) = jsonrpc_id_token(&compact)
            {
                self.send(&format!(
                    "{{\"jsonrpc\":\"2.0\",\"id\":{id},\"result\":null}}"
                ))?;
            }
        }
        Ok(Some(compact))
    }

    fn first_frame_for_method(&self, method: &str) -> Option<String> {
        let needle = format!("\"method\":\"{method}\"");
        self.transcript
            .iter()
            .map(|frame| compact_json(frame))
            .find(|frame| frame.contains(&needle))
    }

    fn wait_for_method(&mut self, method: &str, timeout: Duration) -> Result<String, String> {
        if let Some(frame) = self.first_frame_for_method(method) {
            return Ok(frame);
        }
        let needle = format!("\"method\":\"{method}\"");
        let deadline = Instant::now() + timeout;
        loop {
            let remaining = deadline.saturating_duration_since(Instant::now());
            let Some(frame) = self.next_frame(remaining)? else {
                return Err(format!(
                    "timed out waiting for pinned server method {method}"
                ));
            };
            if frame.contains(&needle) {
                return Ok(frame);
            }
        }
    }

    fn finish(mut self) -> Result<Vec<String>, String> {
        let deadline = Instant::now() + Duration::from_secs(20);
        loop {
            if let Some(status) = self
                .child
                .try_wait()
                .map_err(|error| format!("poll pinned server: {error}"))?
            {
                if !status.success() {
                    return Err(format!("pinned server exited {:?}", status.code()));
                }
                break;
            }
            if Instant::now() >= deadline {
                self.child
                    .kill()
                    .map_err(|error| format!("stop unresponsive pinned server: {error}"))?;
                let _ = self.child.wait();
                return Err("pinned server did not exit after the exit notification".to_string());
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        if let Some(reader) = self.reader.take() {
            reader
                .join()
                .map_err(|_| "pinned server frame reader did not join".to_string())?;
        }
        Ok(std::mem::take(&mut self.transcript))
    }
}

fn jsonrpc_id_token(json: &str) -> Option<String> {
    let start = json.find("\"id\":")? + "\"id\":".len();
    let tail = &json[start..];
    if let Some(tail_without_quote) = tail.strip_prefix('"') {
        let mut escaped = false;
        for (offset, character) in tail_without_quote.char_indices() {
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                return Some(tail[..offset + 2].to_string());
            }
        }
        return None;
    }
    let end = tail.find([',', '}']).unwrap_or(tail.len());
    let token = &tail[..end];
    (!token.is_empty()
        && (token == "null"
            || token
                .strip_prefix('-')
                .unwrap_or(token)
                .bytes()
                .all(|byte| byte.is_ascii_digit())))
    .then(|| token.to_string())
}

impl Drop for ServerHarness {
    fn drop(&mut self) {
        if self.child.try_wait().ok().flatten().is_none() {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
        if let Some(reader) = self.reader.take() {
            let _ = reader.join();
        }
    }
}

fn read_frame(reader: &mut BufReader<impl Read>) -> Result<String, String> {
    let mut content_length = None;
    loop {
        let mut header = String::new();
        let bytes = reader
            .read_line(&mut header)
            .map_err(|error| format!("read server frame header: {error}"))?;
        if bytes == 0 {
            return Err("server stream closed".to_string());
        }
        if header == "\r\n" || header == "\n" {
            break;
        }
        let (name, value) = header
            .trim_end_matches(['\r', '\n'])
            .split_once(':')
            .ok_or_else(|| format!("malformed server frame header {header:?}"))?;
        if name.eq_ignore_ascii_case("Content-Length") {
            let parsed = value
                .trim()
                .parse::<usize>()
                .map_err(|_| format!("malformed Content-Length {value:?}"))?;
            if content_length.replace(parsed).is_some() {
                return Err("server frame repeats Content-Length".to_string());
            }
        }
    }
    let content_length =
        content_length.ok_or_else(|| "server frame has no Content-Length".to_string())?;
    if content_length > 16 * 1024 * 1024 {
        return Err(format!(
            "server frame exceeds 16 MiB bound: {content_length} bytes"
        ));
    }
    let mut payload = vec![0; content_length];
    reader
        .read_exact(&mut payload)
        .map_err(|error| format!("read server frame body: {error}"))?;
    String::from_utf8(payload).map_err(|_| "server frame body is not UTF-8".to_string())
}

fn compact_json(json: &str) -> String {
    let mut output = String::with_capacity(json.len());
    let mut in_string = false;
    let mut escaped = false;
    for character in json.chars() {
        if in_string {
            output.push(character);
            if escaped {
                escaped = false;
            } else if character == '\\' {
                escaped = true;
            } else if character == '"' {
                in_string = false;
            }
        } else if character == '"' {
            output.push(character);
            in_string = true;
        } else if !character.is_whitespace() {
            output.push(character);
        }
    }
    output
}

fn json_quote(value: &str) -> String {
    let mut output = String::with_capacity(value.len() + 2);
    output.push('"');
    for character in value.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            '\u{08}' => output.push_str("\\b"),
            '\u{0c}' => output.push_str("\\f"),
            '\n' => output.push_str("\\n"),
            '\r' => output.push_str("\\r"),
            '\t' => output.push_str("\\t"),
            character if character <= '\u{1f}' => {
                use std::fmt::Write as _;
                let _ = write!(output, "\\u{:04x}", u32::from(character));
            }
            character => output.push(character),
        }
    }
    output.push('"');
    output
}

fn request_frame(id: u64, method: &str, params: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{id},\"method\":{},\"params\":{params}}}",
        json_quote(method)
    )
}

fn notification_frame(method: &str, params: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":{},\"params\":{params}}}",
        json_quote(method)
    )
}

fn wait_for_diagnostics(
    server: &mut ServerHarness,
    id: u64,
    document_uri: &str,
    version: u64,
) -> Result<String, String> {
    let params = format!(
        "{{\"uri\":{},\"version\":{version}}}",
        json_quote(document_uri)
    );
    server.send(&request_frame(
        id,
        "textDocument/waitForDiagnostics",
        &params,
    ))?;
    let response = server.response(id)?;
    if response_disposition(&response) != SemanticDisposition::Result {
        return Err(format!(
            "diagnostics barrier for version {version} failed: {response}"
        ));
    }
    Ok(response)
}

fn normalized_probe_message(
    message: &str,
    workspace_root: &Path,
    toolchain_root: &Path,
) -> Result<String, String> {
    let compact = normalize_session_ids(&compact_json(message));
    let normalized = normalize_reference_transcript(&compact, toolchain_root)
        .map_err(|error| format!("normalize live protocol message: {error}"))?;
    let workspace = workspace_root.to_string_lossy().replace('\\', "/");
    Ok(normalized.replace(&workspace, "/workspace"))
}

fn normalize_session_ids(message: &str) -> String {
    const FIELD: &str = "\"sessionId\":";
    let mut output = String::with_capacity(message.len());
    let mut remainder = message;
    while let Some(offset) = remainder.find(FIELD) {
        output.push_str(&remainder[..offset + FIELD.len()]);
        remainder = &remainder[offset + FIELD.len()..];
        let (quoted, digits) = if let Some(quoted) = remainder.strip_prefix('"') {
            (true, quoted.bytes().take_while(u8::is_ascii_digit).count())
        } else {
            (
                false,
                remainder.bytes().take_while(u8::is_ascii_digit).count(),
            )
        };
        let consumed = digits + usize::from(quoted);
        let closes_quote = !quoted || remainder.as_bytes().get(consumed) == Some(&b'"');
        if digits == 0 || !closes_quote {
            continue;
        }
        output.push_str("\"SESSION\"");
        remainder = &remainder[consumed + usize::from(quoted)..];
    }
    output.push_str(remainder);
    output
}

const NORMALIZED_SERVER_REQUEST_ID: &str = "SERVER_REQUEST";

fn normalize_server_request_id(message: &str) -> Result<String, String> {
    let compact = compact_json(message);
    let id = jsonrpc_id_token(&compact)
        .ok_or_else(|| "server-to-client request has no JSON-RPC id".to_string())?;
    let field = format!("\"id\":{id}");
    let offset = compact
        .find(&field)
        .ok_or_else(|| "server-to-client request id is not a top-level field".to_string())?;
    let mut normalized = String::with_capacity(compact.len());
    normalized.push_str(&compact[..offset]);
    normalized.push_str("\"id\":\"");
    normalized.push_str(NORMALIZED_SERVER_REQUEST_ID);
    normalized.push('"');
    normalized.push_str(&compact[offset + field.len()..]);
    Ok(normalized)
}

fn response_error_code(response: &str) -> String {
    let Some(error) = response.find("\"error\":") else {
        return "none".to_string();
    };
    let tail = &response[error..];
    let Some(code) = tail.find("\"code\":") else {
        return "error-without-code".to_string();
    };
    let tail = &tail[code + "\"code\":".len()..];
    let end = tail.find([',', '}']).unwrap_or(tail.len());
    tail[..end].to_string()
}

fn response_disposition(response: &str) -> SemanticDisposition {
    if response.contains("\"error\":") {
        SemanticDisposition::Error
    } else {
        SemanticDisposition::Result
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct MethodObservation {
    method_key: String,
    request_id: String,
    disposition: SemanticDisposition,
    error_code: String,
    message_root: String,
}

fn insert_observation(
    observations: &mut BTreeMap<String, MethodObservation>,
    method: &ProtocolMethod,
    request_id: impl Into<String>,
    disposition: SemanticDisposition,
    error_code: impl Into<String>,
    message: &str,
    roots: (&Path, &Path),
) -> Result<(), String> {
    let mut normalized_id_message = None;
    let mut request_id = request_id.into();
    if method.family == MessageFamily::Request
        && method.direction == MessageDirection::ServerToClient
    {
        // The pinned server maps per-worker request IDs into a process-wide
        // counter in worker-arrival order. The live harness still answers with
        // the actual ID, proving correlation; the semantic digest binds only
        // the fact that the server supplied an ID, not its schedule-dependent
        // spelling.
        normalized_id_message = Some(normalize_server_request_id(message)?);
        request_id = NORMALIZED_SERVER_REQUEST_ID.to_string();
    }
    let message = normalized_id_message.as_deref().unwrap_or(message);
    let normalized = normalized_probe_message(message, roots.0, roots.1)?;
    let observation = MethodObservation {
        method_key: method.key.clone(),
        request_id,
        disposition,
        error_code: error_code.into(),
        message_root: fixture_content_hash(normalized.as_bytes()),
    };
    if observations
        .insert(method.key.clone(), observation)
        .is_some()
    {
        return Err(format!("method {} was observed more than once", method.key));
    }
    Ok(())
}

#[test]
fn server_request_id_normalization_erases_only_the_correlator() -> Result<(), String> {
    let first = r#"{"jsonrpc":"2.0","id":12,"method":"workspace/semanticTokens/refresh","params":{"id":99}}"#;
    let second = r#"{"jsonrpc":"2.0","id":13,"method":"workspace/semanticTokens/refresh","params":{"id":99}}"#;
    let changed_payload = r#"{"jsonrpc":"2.0","id":13,"method":"workspace/semanticTokens/refresh","params":{"id":100}}"#;

    let normalized = normalize_server_request_id(first)?;
    assert_eq!(normalized, normalize_server_request_id(second)?);
    assert_ne!(normalized, normalize_server_request_id(changed_payload)?);
    assert!(normalized.contains("\"id\":\"SERVER_REQUEST\""));
    assert!(normalized.contains("\"params\":{\"id\":99}"));
    assert_eq!(jsonrpc_id_token(first).as_deref(), Some("12"));
    assert!(normalize_server_request_id(r#"{"jsonrpc":"2.0","method":"exit"}"#).is_err());
    Ok(())
}

fn method<'a>(
    inventory: &'a LspInventory,
    family: MessageFamily,
    name: &str,
) -> Result<&'a ProtocolMethod, String> {
    inventory
        .methods
        .iter()
        .find(|method| method.family == family && method.method == name)
        .ok_or_else(|| format!("{family:?} method {name:?} is absent from the census"))
}

fn parse_session_id(response: &str) -> Result<u64, String> {
    let start = response
        .find("\"sessionId\":")
        .ok_or_else(|| format!("RPC connect response has no sessionId: {response}"))?
        + "\"sessionId\":".len();
    let tail = response[start..]
        .strip_prefix('"')
        .unwrap_or(&response[start..]);
    let digits = tail.bytes().take_while(u8::is_ascii_digit).count();
    if digits == 0 {
        return Err(format!(
            "RPC connect response has malformed sessionId: {response}"
        ));
    }
    tail[..digits]
        .parse::<u64>()
        .map_err(|error| format!("parse RPC session id: {error}"))
}

fn probe_document() -> String {
    use std::fmt::Write as _;

    let mut text = "import Lean\n\n".to_string();
    for ordinal in 0..20_000 {
        let _ = writeln!(text, "def lspCensusProbe{ordinal} : Nat := {ordinal}");
    }
    text
}

fn manifest_probe(
    lean: &Path,
    path: &OsString,
    cwd: &Path,
    workspace_root: &Path,
    toolchain_root: &Path,
    inventory: &LspInventory,
) -> Result<Vec<MethodObservation>, String> {
    let mut server = ServerHarness::start(lean, path, cwd)?;
    let mut observations = BTreeMap::new();
    let initialize_frame = request_frame(
        0,
        "initialize",
        "{\"processId\":null,\"rootUri\":null,\"capabilities\":{\
         \"lean\":{\"incrementalDiagnosticSupport\":true,\
         \"silentDiagnosticSupport\":true,\"rpcWireFormat\":\"v1\"}},\
         \"futureClientField\":{\"accepted\":true}}",
    );
    server.send(&initialize_frame)?;
    let initialize = server.response(0)?;
    if !initialize.contains("\"result\"") || initialize.contains("\"error\"") {
        return Err(format!(
            "minimal-profile initialize was not accepted: {initialize}"
        ));
    }
    insert_observation(
        &mut observations,
        method(inventory, MessageFamily::Request, "initialize")?,
        "0",
        SemanticDisposition::Result,
        "none",
        &initialize,
        (workspace_root, toolchain_root),
    )?;
    let initialized_frame = notification_frame("initialized", "{}");
    server.send(&initialized_frame)?;
    insert_observation(
        &mut observations,
        method(inventory, MessageFamily::Notification, "initialized")?,
        "none",
        SemanticDisposition::Notification,
        "none",
        &initialized_frame,
        (workspace_root, toolchain_root),
    )?;

    let document_uri = "file:///tmp/fln-lsp-census-probe.lean";
    let document_text = probe_document();
    let open_params = format!(
        "{{\"textDocument\":{{\"uri\":{},\"languageId\":\"lean4\",\
         \"version\":1,\"text\":{}}}}}",
        json_quote(document_uri),
        json_quote(&document_text)
    );
    let open_frame = notification_frame("textDocument/didOpen", &open_params);
    server.send(&open_frame)?;
    insert_observation(
        &mut observations,
        method(
            inventory,
            MessageFamily::Notification,
            "textDocument/didOpen",
        )?,
        "none",
        SemanticDisposition::Notification,
        "none",
        &open_frame,
        (workspace_root, toolchain_root),
    )?;

    // This is the Reference server's synchronization surface: its response is
    // delayed until both diagnostics and every command snapshot for this
    // document version have finished.  Dispatching document requests before
    // this point races the worker and makes identical fresh processes observe
    // different call-hierarchy and ILean outcomes.
    let diagnostics_response = wait_for_diagnostics(&mut server, 1, document_uri, 1)?;
    insert_observation(
        &mut observations,
        method(
            inventory,
            MessageFamily::Request,
            "textDocument/waitForDiagnostics",
        )?,
        "1",
        SemanticDisposition::Result,
        "none",
        &diagnostics_response,
        (workspace_root, toolchain_root),
    )?;

    let semantic_params = format!(
        "{{\"textDocument\":{{\"uri\":{}}}}}",
        json_quote(document_uri)
    );
    let semantic_frame = request_frame(2, "textDocument/semanticTokens/full", &semantic_params);
    server.send(&semantic_frame)?;
    let semantic_response = server.response(2)?;
    if response_error_code(&semantic_response) == "-32601" {
        return Err(format!(
            "known semantic-token method was reported absent: {semantic_response}"
        ));
    }
    insert_observation(
        &mut observations,
        method(
            inventory,
            MessageFamily::Request,
            "textDocument/semanticTokens/full",
        )?,
        "2",
        response_disposition(&semantic_response),
        response_error_code(&semantic_response),
        &semantic_response,
        (workspace_root, toolchain_root),
    )?;

    let line_count = document_text.lines().count();
    let inlay_params = format!(
        "{{\"textDocument\":{{\"uri\":{}}},\"range\":{{\"start\":{{\"line\":0,\
         \"character\":0}},\"end\":{{\"line\":{line_count},\"character\":0}}}}}}",
        json_quote(document_uri)
    );
    let inlay_frame = request_frame(3, "textDocument/inlayHint", &inlay_params);
    server.send(&inlay_frame)?;
    let inlay_response = server.response(3)?;
    if response_error_code(&inlay_response) == "-32601" {
        return Err(format!(
            "known inlay-hint method was reported absent: {inlay_response}"
        ));
    }
    insert_observation(
        &mut observations,
        method(inventory, MessageFamily::Request, "textDocument/inlayHint")?,
        "3",
        response_disposition(&inlay_response),
        response_error_code(&inlay_response),
        &inlay_response,
        (workspace_root, toolchain_root),
    )?;

    server.send(&request_frame(
        4,
        "$/lean/notARealMethod",
        "{\"future\":true}",
    ))?;
    let unknown = server.response(4)?;
    if !unknown.contains("\"error\"") || response_error_code(&unknown) != "-32601" {
        return Err(format!("unknown method was not rejected: {unknown}"));
    }
    let mut next_id = 5_u64;
    for protocol_method in &inventory.methods {
        if protocol_method.family != MessageFamily::Request
            || protocol_method.direction != MessageDirection::ClientToServer
            || observations.contains_key(&protocol_method.key)
            || matches!(
                protocol_method.method.as_str(),
                "$/lean/rpc/connect" | "$/lean/rpc/call" | "shutdown"
            )
        {
            continue;
        }
        let frame = request_frame(next_id, &protocol_method.method, "{}");
        server.send(&frame)?;
        let response = server.response(next_id)?;
        let error_code = response_error_code(&response);
        if error_code == "-32601" {
            return Err(format!(
                "censused request {} was reported absent: {response}",
                protocol_method.key
            ));
        }
        insert_observation(
            &mut observations,
            protocol_method,
            next_id.to_string(),
            response_disposition(&response),
            error_code,
            &response,
            (workspace_root, toolchain_root),
        )?;
        next_id += 1;
    }

    let connect_params = format!("{{\"uri\":{}}}", json_quote(document_uri));
    let connect_frame = request_frame(next_id, "$/lean/rpc/connect", &connect_params);
    server.send(&connect_frame)?;
    let connect_response = server.response(next_id)?;
    if response_disposition(&connect_response) != SemanticDisposition::Result {
        return Err(format!("RPC connection failed: {connect_response}"));
    }
    let session_id = parse_session_id(&connect_response)?;
    insert_observation(
        &mut observations,
        method(inventory, MessageFamily::Request, "$/lean/rpc/connect")?,
        next_id.to_string(),
        SemanticDisposition::Result,
        "none",
        &connect_response,
        (workspace_root, toolchain_root),
    )?;
    next_id += 1;

    for protocol_method in inventory
        .methods
        .iter()
        .filter(|method| method.family == MessageFamily::RpcRequest)
    {
        let params = format!(
            "{{\"textDocument\":{{\"uri\":{}}},\"position\":{{\"line\":0,\
             \"character\":0}},\"sessionId\":\"{session_id}\",\"method\":{},\"params\":{{}}}}",
            json_quote(document_uri),
            json_quote(&protocol_method.method)
        );
        let frame = request_frame(next_id, "$/lean/rpc/call", &params);
        server.send(&frame)?;
        let response = server.response(next_id)?;
        let error_code = response_error_code(&response);
        if error_code == "-32601" {
            return Err(format!(
                "censused RPC {} was reported absent: {response}",
                protocol_method.key
            ));
        }
        if !observations.contains_key("request:$/lean/rpc/call") {
            insert_observation(
                &mut observations,
                method(inventory, MessageFamily::Request, "$/lean/rpc/call")?,
                next_id.to_string(),
                response_disposition(&response),
                error_code.clone(),
                &response,
                (workspace_root, toolchain_root),
            )?;
        }
        insert_observation(
            &mut observations,
            protocol_method,
            next_id.to_string(),
            response_disposition(&response),
            error_code,
            &response,
            (workspace_root, toolchain_root),
        )?;
        next_id += 1;
    }

    let notification_params = [
        ("$/cancelRequest", format!("{{\"id\":{}}}", u64::MAX)),
        (
            "$/lean/rpc/keepAlive",
            format!(
                "{{\"uri\":{},\"sessionId\":\"{session_id}\"}}",
                json_quote(document_uri)
            ),
        ),
        (
            "$/lean/rpc/release",
            format!(
                "{{\"uri\":{},\"sessionId\":\"{session_id}\",\"refs\":[]}}",
                json_quote(document_uri)
            ),
        ),
        (
            "workspace/didChangeWatchedFiles",
            "{\"changes\":[]}".to_string(),
        ),
        (
            "textDocument/didChange",
            format!(
                "{{\"textDocument\":{{\"uri\":{},\"version\":2}},\
                 \"contentChanges\":[{{\"text\":{}}}]}}",
                json_quote(document_uri),
                json_quote(&document_text)
            ),
        ),
        (
            "textDocument/didSave",
            format!(
                "{{\"textDocument\":{{\"uri\":{}}}}}",
                json_quote(document_uri)
            ),
        ),
    ];
    for (name, params) in notification_params {
        let frame = notification_frame(name, &params);
        server.send(&frame)?;
        insert_observation(
            &mut observations,
            method(inventory, MessageFamily::Notification, name)?,
            "none",
            SemanticDisposition::Notification,
            "none",
            &frame,
            (workspace_root, toolchain_root),
        )?;
    }

    for protocol_method in inventory
        .methods
        .iter()
        .filter(|method| method.direction == MessageDirection::ServerToClient)
    {
        let frame = server.wait_for_method(&protocol_method.method, Duration::from_secs(20))?;
        let disposition = if protocol_method.family == MessageFamily::Request {
            SemanticDisposition::Request
        } else {
            SemanticDisposition::Notification
        };
        insert_observation(
            &mut observations,
            protocol_method,
            jsonrpc_id_token(&frame).unwrap_or_else(|| "none".to_string()),
            disposition,
            "none",
            &frame,
            (workspace_root, toolchain_root),
        )?;
    }

    let close_params = format!(
        "{{\"textDocument\":{{\"uri\":{}}}}}",
        json_quote(document_uri)
    );
    let close_frame = notification_frame("textDocument/didClose", &close_params);
    server.send(&close_frame)?;
    insert_observation(
        &mut observations,
        method(
            inventory,
            MessageFamily::Notification,
            "textDocument/didClose",
        )?,
        "none",
        SemanticDisposition::Notification,
        "none",
        &close_frame,
        (workspace_root, toolchain_root),
    )?;

    let shutdown_frame = request_frame(next_id, "shutdown", "null");
    server.send(&shutdown_frame)?;
    let shutdown = server.response(next_id)?;
    if !shutdown.contains("\"result\":null") {
        return Err(format!("shutdown response is not canonical: {shutdown}"));
    }
    insert_observation(
        &mut observations,
        method(inventory, MessageFamily::Request, "shutdown")?,
        next_id.to_string(),
        SemanticDisposition::Result,
        "none",
        &shutdown,
        (workspace_root, toolchain_root),
    )?;
    let exit_frame = notification_frame("exit", "null");
    server.send(&exit_frame)?;
    insert_observation(
        &mut observations,
        method(inventory, MessageFamily::Notification, "exit")?,
        "none",
        SemanticDisposition::Notification,
        "none",
        &exit_frame,
        (workspace_root, toolchain_root),
    )?;
    server.finish()?;

    let expected = inventory
        .methods
        .iter()
        .map(|method| method.key.clone())
        .collect::<BTreeSet<_>>();
    let actual = observations.keys().cloned().collect::<BTreeSet<_>>();
    if actual != expected {
        return Err(format!(
            "real method manifest is incomplete: missing={:?} extra={:?}",
            expected.difference(&actual).collect::<Vec<_>>(),
            actual.difference(&expected).collect::<Vec<_>>()
        ));
    }
    Ok(inventory
        .methods
        .iter()
        .map(|method| {
            observations
                .remove(&method.key)
                .expect("the exact key set was checked")
        })
        .collect())
}

fn method_semantic_event(
    sequence: u64,
    inventory: &LspInventory,
    method: &ProtocolMethod,
    expected: &MethodObservation,
    actual: &MethodObservation,
) -> SemanticEvent {
    let document_bound = matches!(method.policy.lifecycle.as_str(), "document" | "rpc_session");
    SemanticEvent {
        sequence,
        epoch_id: inventory.reference.commit.clone(),
        client_id: method.policy.client.clone(),
        capability_id: "lean-v1-minimal-plus-refresh".to_string(),
        session_id: if method.policy.lifecycle == "rpc_session" {
            "rpc-session-0"
        } else {
            "lsp-session-0"
        }
        .to_string(),
        document_id: if document_bound {
            "file:///tmp/fln-lsp-census-probe.lean"
        } else {
            "none"
        }
        .to_string(),
        document_version: u64::from(document_bound) * 2,
        request_id: actual.request_id.clone(),
        fixture_id: method.fixture.clone(),
        comparison_id: method.policy.comparison.clone(),
        direction: method.direction,
        method_id: method.key.clone(),
        parameter_schema_id: method.parameter_type.clone(),
        response_schema_id: method.response_type.clone(),
        expected_disposition: expected.disposition,
        actual_disposition: actual.disposition,
        expected_message_root: expected.message_root.clone(),
        actual_message_root: actual.message_root.clone(),
        expected_error_code: expected.error_code.clone(),
        actual_error_code: actual.error_code.clone(),
        authority_root: inventory.inventory_root.clone(),
        resource_state: format!(
            "support={};platform={};probe={}",
            method.policy.support, method.policy.platform, method.probe
        ),
        cleanup_state: "document=closed;rpc=released;server=exited".to_string(),
        final_state: "manifest-complete".to_string(),
    }
}

#[test]
fn lsp_census_no_mock_e2e() -> Result<(), String> {
    let run = pin::RigRun::new(pin::PinRig::LspCensusNoMockE2e);
    let Some(lean) = pin::pinned_lean() else {
        let notice = run.typed_skip().map_err(|error| error.to_string())?;
        eprintln!("{notice}");
        return Ok(());
    };
    let root = pin::workspace_root();
    let inventory = LspInventory::load_embedded().map_err(|error| error.to_string())?;
    inventory
        .validate_workspace_sources(&root)
        .map_err(|error| error.to_string())?;
    let path = toolchain_path(&lean).map_err(|error| error.to_string())?;
    let toolchain_root = toolchain_root(&lean).map_err(|error| error.to_string())?;
    let fixture_root = root.join("vendor/lean4-src/tests/server_interactive");

    let version = Command::new(&lean)
        .arg("--version")
        .env("PATH", &path)
        .output()
        .map_err(|error| format!("query pinned Lean version: {error}"))?;
    assert!(version.status.success());
    assert!(
        String::from_utf8_lossy(&version.stdout).contains(&inventory.reference.tag[1..]),
        "pinned binary version does not name {}: {}",
        inventory.reference.tag,
        String::from_utf8_lossy(&version.stdout)
    );

    let mut semantic = Vec::new();
    let mut telemetry = Vec::new();
    for (sequence, fixture_name) in FIXTURES.iter().enumerate() {
        let fixture = inventory
            .fixture(fixture_name)
            .ok_or_else(|| format!("fixture {fixture_name} is absent from the census"))?;
        assert_eq!(fixture.normalizer, "lean-test-suite-normalized-v1");
        let (actual, elapsed_micros) =
            run_reference_fixture(&lean, &path, &fixture_root, fixture_name)
                .map_err(|error| error.to_string())?;
        let normalized = normalize_reference_transcript(&actual, toolchain_root)
            .map_err(|error| format!("normalize {fixture_name}: {error}"))?;
        let expected_raw = std::fs::read_to_string(root.join(&fixture.expected))
            .map_err(|error| format!("read {}: {error}", fixture.expected))?;
        assert_eq!(
            fixture_content_hash(expected_raw.as_bytes()),
            fixture.expected_hash,
            "checked-in golden transcript drifted for {fixture_name}"
        );
        let expected = normalize_reference_transcript(&expected_raw, toolchain_root)
            .map_err(|error| format!("normalize golden {fixture_name}: {error}"))?;
        assert_eq!(
            normalized, expected,
            "real pinned Reference transcript drifted for {fixture_name}"
        );
        let actual_root = fixture_content_hash(normalized.as_bytes());
        let expected_root = fixture_content_hash(expected.as_bytes());
        semantic.push(SemanticEvent {
            sequence: sequence as u64,
            epoch_id: inventory.reference.commit.clone(),
            client_id: "Lean.Server.Test.Runner".to_string(),
            capability_id: "runner-lean-v1".to_string(),
            session_id: format!("fixture-session:{fixture_name}"),
            document_id: fixture.source.clone(),
            document_version: 2,
            request_id: "runner-managed".to_string(),
            fixture_id: fixture.name.clone(),
            comparison_id: "normalized".to_string(),
            direction: MessageDirection::ServerToClient,
            method_id: format!("fixture-directives:{}", fixture.directives),
            parameter_schema_id: "Lean.Server.Test.Runner.Directive".to_string(),
            response_schema_id: "normalized-golden-transcript".to_string(),
            expected_disposition: SemanticDisposition::Result,
            actual_disposition: SemanticDisposition::Result,
            expected_message_root: expected_root,
            actual_message_root: actual_root,
            expected_error_code: "none".to_string(),
            actual_error_code: "none".to_string(),
            authority_root: inventory.inventory_root.clone(),
            resource_state: "real-pinned-reference-process".to_string(),
            cleanup_state: "runner-child-exited-zero".to_string(),
            final_state: "golden-match".to_string(),
        });
        telemetry.push(TelemetryEvent {
            sequence: sequence as u64,
            elapsed_micros,
            worker: "pinned-reference".to_string(),
            detail: "Lean.Server.Test.Runner".to_string(),
        });
    }

    let first_started = Instant::now();
    let first_manifest = manifest_probe(
        &lean,
        &path,
        &fixture_root,
        &root,
        toolchain_root,
        &inventory,
    )
    .map_err(|error| format!("first complete method manifest: {error}"))?;
    telemetry.push(TelemetryEvent {
        sequence: telemetry.len() as u64,
        elapsed_micros: first_started
            .elapsed()
            .as_micros()
            .min(u128::from(u64::MAX)) as u64,
        worker: "pinned-reference".to_string(),
        detail: "manifest-complete-pass-1".to_string(),
    });
    let second_started = Instant::now();
    let second_manifest = manifest_probe(
        &lean,
        &path,
        &fixture_root,
        &root,
        toolchain_root,
        &inventory,
    )
    .map_err(|error| format!("second complete method manifest: {error}"))?;
    telemetry.push(TelemetryEvent {
        sequence: telemetry.len() as u64,
        elapsed_micros: second_started
            .elapsed()
            .as_micros()
            .min(u128::from(u64::MAX)) as u64,
        worker: "pinned-reference".to_string(),
        detail: "manifest-complete-pass-2".to_string(),
    });
    assert_eq!(
        first_manifest, second_manifest,
        "two fresh real Reference processes produced different method observations"
    );
    assert_eq!(first_manifest.len(), inventory.methods.len());

    let first_events = inventory
        .methods
        .iter()
        .zip(&first_manifest)
        .enumerate()
        .map(|(sequence, (method, observation))| {
            method_semantic_event(
                sequence as u64,
                &inventory,
                method,
                observation,
                observation,
            )
        })
        .collect::<Vec<_>>();
    let second_events = inventory
        .methods
        .iter()
        .zip(&second_manifest)
        .enumerate()
        .map(|(sequence, (method, observation))| {
            method_semantic_event(
                sequence as u64,
                &inventory,
                method,
                observation,
                observation,
            )
        })
        .collect::<Vec<_>>();
    let first_manifest_root = TranscriptBundle::new(first_events, Vec::new())
        .expect("first method manifest is sequential")
        .semantic_root();
    let second_manifest_root = TranscriptBundle::new(second_events, Vec::new())
        .expect("second method manifest is sequential")
        .semantic_root();
    assert_eq!(
        first_manifest_root, second_manifest_root,
        "two complete real method manifests have different semantic roots"
    );
    for ((method, expected), actual) in inventory
        .methods
        .iter()
        .zip(&first_manifest)
        .zip(&second_manifest)
    {
        semantic.push(method_semantic_event(
            semantic.len() as u64,
            &inventory,
            method,
            expected,
            actual,
        ));
    }

    let bundle =
        TranscriptBundle::new(semantic, telemetry).expect("build strict separated transcripts");
    assert_eq!(
        TranscriptBundle::from_ndjson(&bundle.semantic_ndjson(), &bundle.telemetry_ndjson()),
        Ok(bundle.clone())
    );
    assert_eq!(
        bundle.semantic_events().len(),
        FIXTURES.len() + inventory.methods.len()
    );
    assert_eq!(bundle.telemetry_events().len(), FIXTURES.len() + 2);
    assert_eq!(bundle.semantic_root().len(), 64);
    assert_eq!(bundle.telemetry_root().len(), 64);
    inventory
        .validate_semantic_manifest(bundle.semantic_events())
        .expect("strict semantic transcript is complete and authority-bound");
    let manifest_keys = bundle
        .semantic_events()
        .iter()
        .filter(|event| event.fixture_id == "lsp-census-no-mock-e2e")
        .map(|event| event.method_id.clone())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        manifest_keys,
        inventory
            .methods
            .iter()
            .map(|method| method.key.clone())
            .collect()
    );
    run.executed().map_err(|error| error.to_string())?;
    Ok(())
}
