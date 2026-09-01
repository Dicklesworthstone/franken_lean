//! Minimal JSON-RPC dispatch for the LSP lifecycle and document events.
//!
//! This module parses just enough JSON to route LSP requests and notifications
//! to handlers. It does not depend on serde or any external JSON library
//! (doctrine D1). The hand-rolled parsing is intentionally narrow: it handles
//! the fixed vocabulary of LSP methods the server currently supports.

use std::io::{self, BufRead, Write};

use crate::json_string;
use crate::transport;

/// Lifecycle state of the LSP server.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ServerState {
    /// Waiting for the `initialize` request.
    Uninitialized,
    /// Between `initialize` response and `initialized` notification.
    Initializing,
    /// Normal operation.
    Running,
    /// `shutdown` received; waiting for `exit`.
    ShuttingDown,
}

/// The result of running the server loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerOutcome {
    /// True if the server exited cleanly (shutdown then exit).
    pub clean: bool,
    /// Number of `textDocument/didOpen` notifications processed.
    pub documents_opened: u64,
    /// Number of `textDocument/didChange` notifications processed.
    pub documents_changed: u64,
    /// Number of `textDocument/didSave` notifications processed.
    pub documents_saved: u64,
}

/// Find an unescaped JSON object-key spelling and return the byte immediately
/// after its closing quote.
///
/// This scanner is deliberately narrow: keys are fixed ASCII protocol tokens,
/// while values are decoded separately. Checking the backslash parity prevents
/// source text such as `\"method\":\"shutdown\"` from being mistaken for the
/// envelope's real `method` field.
fn find_json_key(json: &str, key: &str) -> Option<usize> {
    let needle = format!("\"{key}\"");
    let bytes = json.as_bytes();
    let mut offset = 0usize;
    loop {
        let relative = json.get(offset..)?.find(&needle)?;
        let start = offset.checked_add(relative)?;
        let preceding_backslashes = bytes[..start]
            .iter()
            .rev()
            .take_while(|byte| **byte == b'\\')
            .count();
        let after = start.checked_add(needle.len())?;
        if preceding_backslashes % 2 == 0
            && json
                .get(after..)?
                .trim_start()
                .starts_with(':')
        {
            return Some(after);
        }
        offset = start.checked_add(1)?;
    }
}

fn decode_json_string(after_quote: &str) -> Option<String> {
    fn hex_quad(chars: &mut std::str::Chars<'_>) -> Option<u16> {
        let mut value = 0u16;
        for _ in 0..4 {
            value = value.checked_mul(16)?;
            value = value.checked_add(u16::try_from(chars.next()?.to_digit(16)?).ok()?)?;
        }
        Some(value)
    }

    fn unicode_escape(chars: &mut std::str::Chars<'_>) -> Option<char> {
        let first = hex_quad(chars)?;
        match first {
            0xd800..=0xdbff => {
                if chars.next()? != '\\' || chars.next()? != 'u' {
                    return None;
                }
                let second = hex_quad(chars)?;
                if !(0xdc00..=0xdfff).contains(&second) {
                    return None;
                }
                let high = u32::from(first) - 0xd800;
                let low = u32::from(second) - 0xdc00;
                char::from_u32(0x1_0000 + (high << 10) + low)
            }
            0xdc00..=0xdfff => None,
            scalar => char::from_u32(u32::from(scalar)),
        }
    }

    let mut result = String::new();
    let mut chars = after_quote.chars();
    loop {
        match chars.next()? {
            '"' => return Some(result),
            '\\' => {
                let escaped = chars.next()?;
                result.push(match escaped {
                    '"' => '"',
                    '\\' => '\\',
                    '/' => '/',
                    'b' => '\u{0008}',
                    'f' => '\u{000c}',
                    'n' => '\n',
                    'r' => '\r',
                    't' => '\t',
                    'u' => unicode_escape(&mut chars)?,
                    _ => return None,
                });
            }
            control if control <= '\u{001f}' => return None,
            other => result.push(other),
        }
    }
}

/// Extract and decode a JSON string value for a fixed protocol key.
fn extract_string_field(json: &str, key: &str) -> Option<String> {
    let after_key = &json[find_json_key(json, key)?..];
    let after_colon = after_key.trim_start().strip_prefix(':')?.trim_start();
    let after_quote = after_colon.strip_prefix('"')?;
    decode_json_string(after_quote)
}

/// Extract a JSON integer value for a given key from a flat JSON object.
fn extract_int_field(json: &str, key: &str) -> Option<i64> {
    let after_key = &json[find_json_key(json, key)?..];
    let after_colon = after_key.trim_start().strip_prefix(':')?.trim_start();
    // Parse digits (possibly with leading minus).
    let end = after_colon
        .find(|c: char| !c.is_ascii_digit() && c != '-')
        .unwrap_or(after_colon.len());
    after_colon[..end].parse::<i64>().ok()
}

/// Extract the decoded `uri` from a `textDocument` parameter.
fn extract_text_document_uri(json: &str) -> Option<String> {
    let td_start = find_json_key(json, "textDocument")?;
    extract_string_field(&json[td_start..], "uri")
}

/// Extract a JSON string value starting after a given byte offset. The search
/// begins at `haystack[offset..]` and finds the first unescaped `"text"` key.
fn extract_escaped_text_value(haystack: &str, offset: usize) -> Option<String> {
    let region = haystack.get(offset..)?;
    extract_string_field(region, "text")
}

/// Extract the `text` from the `textDocument` parameter (for didOpen).
fn extract_text_document_text(json: &str) -> Option<String> {
    let td_start = find_json_key(json, "textDocument")?;
    extract_escaped_text_value(json, td_start)
}

/// Extract the full document text from `contentChanges` (for didChange
/// with `TextDocumentSyncKind.Full`). The spec sends
/// `"contentChanges":[{"text":"..."}]`; we extract the `text` from the
/// first element.
fn extract_content_changes_text(json: &str) -> Option<String> {
    let cc_start = find_json_key(json, "contentChanges")?;
    extract_escaped_text_value(json, cc_start)
}

/// Extract the params-level `text` field (for didSave with
/// `includeText: true`). The didSave `textDocument` object contains
/// only `uri` and `version` — no `text` — so the only unescaped `"text"` key
/// in the message is the params-level one we want.
fn extract_save_text(json: &str) -> Option<String> {
    extract_escaped_text_value(json, 0)
}

/// Build the `initialize` response with FrankenLean server capabilities.
fn initialize_response(id: i64) -> String {
    // We use push diagnostics (textDocument/publishDiagnostics) not pull
    // diagnostics (textDocument/diagnostic), so diagnosticProvider is not
    // advertised. textDocumentSync with openClose + change:1 (Full) is
    // what triggers the client to send didOpen/didChange/didClose.
    // save.includeText tells the client to include the full document text
    // in didSave notifications so we can re-check on save.
    format!(
        concat!(
            "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":{{",
            "\"capabilities\":{{",
            "\"textDocumentSync\":{{\"openClose\":true,\"change\":1,",
            "\"save\":{{\"includeText\":true}}}}",
            "}},",
            "\"serverInfo\":{{\"name\":\"FrankenLean\",\"version\":{}}}"
            ,"}}}}"
        ),
        id,
        json_string(env!("CARGO_PKG_VERSION"))
    )
}

/// Build a JSON-RPC error response.
fn error_response(id: i64, code: i32, message: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"error\":{{\"code\":{},\"message\":{}}}}}",
        id,
        code,
        json_string(message)
    )
}

/// LSP's standard `RequestFailed` code. Use it for recognized protocol
/// requests whose implementation is not yet available; fabricating a success
/// response would turn an unsupported capability into false state.
const REQUEST_FAILED_CODE: i32 = -32803;

/// Build a JSON-RPC success response with a null result.
fn null_response(id: i64) -> String {
    format!("{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":null}}", id)
}

/// Build a `$/lean/fileProgress` notification.
///
/// When `processing` is `true`, the notification indicates that the server
/// is actively processing the file. When `false`, it indicates that
/// processing is complete (the VS Code extension clears the spinner).
fn file_progress_notification(uri: &str, processing: bool) -> String {
    let processing_value = if processing {
        "[{\"range\":{\"start\":{\"line\":0,\"character\":0},\"end\":{\"line\":0,\"character\":0}},\"kind\":1}]"
    } else {
        "[]"
    };
    format!(
        concat!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"$/lean/fileProgress\",",
            "\"params\":{{\"textDocument\":{{\"uri\":{}}},",
            "\"processing\":{}}}}}"
        ),
        json_string(uri),
        processing_value
    )
}

/// Callback invoked when a document is opened.
///
/// The callback receives the document URI and text content, and returns
/// zero or more JSON-RPC notification strings to send to the client.
pub type OnDidOpen = dyn FnMut(&str, &str) -> Vec<String>;

/// Run the LSP server loop over the given I/O streams.
///
/// This function blocks until the client sends `exit` or the input stream
/// closes. It handles the full LSP lifecycle (`initialize` / `initialized` /
/// `shutdown` / `exit`) and routes `textDocument/didOpen` notifications
/// through the provided callback.
///
/// The `on_did_open` callback receives `(uri, text)` and should return
/// any JSON-RPC notification bodies (without Content-Length framing) to
/// send back. In production, this runs the source through the checker
/// and projects diagnostics via `fln_server::project`.
pub fn serve(
    input: &mut dyn BufRead,
    output: &mut dyn Write,
    on_did_open: &mut OnDidOpen,
) -> io::Result<ServerOutcome> {
    let mut state = ServerState::Uninitialized;
    let mut documents_opened: u64 = 0;
    let mut documents_changed: u64 = 0;
    let mut documents_saved: u64 = 0;

    loop {
        let Some(message) = transport::read_message(input)? else {
            // EOF — unclean exit if we never got shutdown.
            return Ok(ServerOutcome {
                clean: state == ServerState::ShuttingDown,
                documents_opened,
                documents_changed,
                documents_saved,
            });
        };

        let text = String::from_utf8(message).map_err(|_| {
            io::Error::new(io::ErrorKind::InvalidData, "message is not valid UTF-8")
        })?;

        let method = extract_string_field(&text, "method");
        let id = extract_int_field(&text, "id");

        match (method.as_deref(), id, state) {
            // --- Lifecycle: initialize ---
            (Some("initialize"), Some(req_id), ServerState::Uninitialized) => {
                let response = initialize_response(req_id);
                transport::write_message(output, response.as_bytes())?;
                state = ServerState::Initializing;
            }
            (Some("initialize"), Some(req_id), _) => {
                // Already initialized.
                let response = error_response(req_id, -32600, "server already initialized");
                transport::write_message(output, response.as_bytes())?;
            }

            // --- Lifecycle: initialized ---
            (Some("initialized"), None, ServerState::Initializing) => {
                state = ServerState::Running;
            }

            // --- Lifecycle: shutdown ---
            (Some("shutdown"), Some(req_id), _) => {
                let response = null_response(req_id);
                transport::write_message(output, response.as_bytes())?;
                state = ServerState::ShuttingDown;
            }

            // --- Lifecycle: exit ---
            (Some("exit"), None, _) => {
                return Ok(ServerOutcome {
                    clean: state == ServerState::ShuttingDown,
                    documents_opened,
                    documents_changed,
                    documents_saved,
                });
            }

            // --- textDocument/didOpen ---
            (Some("textDocument/didOpen"), None, ServerState::Running) => {
                if let (Some(uri), Some(content)) = (
                    extract_text_document_uri(&text),
                    extract_text_document_text(&text),
                ) {
                    let started = file_progress_notification(&uri, true);
                    transport::write_message(output, started.as_bytes())?;
                    let notifications = on_did_open(&uri, &content);
                    for notification in &notifications {
                        transport::write_message(output, notification.as_bytes())?;
                    }
                    let done = file_progress_notification(&uri, false);
                    transport::write_message(output, done.as_bytes())?;
                    documents_opened += 1;
                }
            }

            // --- textDocument/didChange (full sync, change kind 1) ---
            (Some("textDocument/didChange"), None, ServerState::Running) => {
                if let (Some(uri), Some(content)) = (
                    extract_text_document_uri(&text),
                    extract_content_changes_text(&text),
                ) {
                    let started = file_progress_notification(&uri, true);
                    transport::write_message(output, started.as_bytes())?;
                    let notifications = on_did_open(&uri, &content);
                    for notification in &notifications {
                        transport::write_message(output, notification.as_bytes())?;
                    }
                    let done = file_progress_notification(&uri, false);
                    transport::write_message(output, done.as_bytes())?;
                    documents_changed += 1;
                }
            }

            // --- textDocument/didSave (with includeText) ---
            (Some("textDocument/didSave"), None, ServerState::Running) => {
                if let (Some(uri), Some(content)) = (
                    extract_text_document_uri(&text),
                    extract_save_text(&text),
                ) {
                    let started = file_progress_notification(&uri, true);
                    transport::write_message(output, started.as_bytes())?;
                    let notifications = on_did_open(&uri, &content);
                    for notification in &notifications {
                        transport::write_message(output, notification.as_bytes())?;
                    }
                    let done = file_progress_notification(&uri, false);
                    transport::write_message(output, done.as_bytes())?;
                    documents_saved += 1;
                }
            }

            // --- textDocument/didClose ---
            (Some("textDocument/didClose"), None, ServerState::Running) => {}

            // --- $/lean/plainGoal (InfoView goal request) ---
            (Some("$/lean/plainGoal"), Some(req_id), ServerState::Running) => {
                let response = null_response(req_id);
                transport::write_message(output, response.as_bytes())?;
            }

            // --- $/lean/plainTermGoal (InfoView term goal request) ---
            (Some("$/lean/plainTermGoal"), Some(req_id), ServerState::Running) => {
                let response = null_response(req_id);
                transport::write_message(output, response.as_bytes())?;
            }

            // --- textDocument/hover ---
            (Some("textDocument/hover"), Some(req_id), ServerState::Running) => {
                let response = null_response(req_id);
                transport::write_message(output, response.as_bytes())?;
            }

            // --- textDocument/completion ---
            (Some("textDocument/completion"), Some(req_id), ServerState::Running) => {
                let response = null_response(req_id);
                transport::write_message(output, response.as_bytes())?;
            }

            // --- textDocument/definition ---
            (Some("textDocument/definition"), Some(req_id), ServerState::Running) => {
                let response = null_response(req_id);
                transport::write_message(output, response.as_bytes())?;
            }

            // --- $/lean/rpc/connect (widget RPC session init) ---
            (Some("$/lean/rpc/connect"), Some(req_id), ServerState::Running) => {
                let response = error_response(
                    req_id,
                    REQUEST_FAILED_CODE,
                    "Lean RPC sessions are not implemented by this FrankenLean server",
                );
                transport::write_message(output, response.as_bytes())?;
            }

            // --- $/lean/rpc/call (widget RPC calls) ---
            (Some("$/lean/rpc/call"), Some(req_id), ServerState::Running) => {
                let response = error_response(
                    req_id,
                    REQUEST_FAILED_CODE,
                    "Lean RPC calls are not implemented by this FrankenLean server",
                );
                transport::write_message(output, response.as_bytes())?;
            }

            // --- Unknown request (has id) → method not found ---
            (_, Some(req_id), _) => {
                let response = error_response(req_id, -32601, "method not found");
                transport::write_message(output, response.as_bytes())?;
            }

            // --- Unknown notification (no id) → silently drop ---
            (_, None, _) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufReader;
    use crate::transport::write_message;

    fn send(buf: &mut Vec<u8>, body: &str) {
        write_message(buf, body.as_bytes()).unwrap();
    }

    fn lifecycle_session(extra_messages: &str) -> (ServerOutcome, String) {
        let mut input_buf = Vec::new();
        send(
            &mut input_buf,
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        );
        send(
            &mut input_buf,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        );
        for line in extra_messages.lines() {
            if !line.trim().is_empty() {
                send(&mut input_buf, line.trim());
            }
        }
        send(
            &mut input_buf,
            r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        );
        send(
            &mut input_buf,
            r#"{"jsonrpc":"2.0","method":"exit"}"#,
        );

        let mut reader = BufReader::new(&input_buf[..]);
        let mut output_buf = Vec::new();
        let outcome = serve(
            &mut reader,
            &mut output_buf,
            &mut |uri, _text| {
                vec![format!(
                    "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
                    json_string(uri)
                )]
            },
        )
        .unwrap();
        (outcome, String::from_utf8(output_buf).unwrap())
    }

    #[test]
    fn clean_lifecycle() {
        let (outcome, output) = lifecycle_session("");
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 0);
        assert!(output.contains("FrankenLean"));
        assert!(output.contains("\"result\":null"));
    }

    #[test]
    fn did_open_routes_through_callback() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"def x := 42"}}}"#,
        );
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 1);
        assert!(output.contains("publishDiagnostics"));
        assert_eq!(output.matches("$/lean/fileProgress").count(), 2);
    }

    #[test]
    fn did_open_ignores_method_lookalike_inside_document_text() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"\"method\":\"shutdown\""}},"method":"textDocument/didOpen"}"#,
        );
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 1);
        assert!(output.contains("publishDiagnostics"));
    }

    #[test]
    fn unknown_request_returns_method_not_found() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/unknownMethod","params":{}}"#,
        );
        assert!(outcome.clean);
        assert!(output.contains("-32601"));
    }

    #[test]
    fn extract_string_field_works() {
        let json = r#"{"method":"initialize","id":1}"#;
        assert_eq!(extract_string_field(json, "method").as_deref(), Some("initialize"));
    }

    #[test]
    fn extract_string_field_decodes_escapes_and_skips_escaped_key_lookalikes() {
        let json = r#"{"note":"\"method\":\"shutdown\"","method":"textDocument\/hover"}"#;
        assert_eq!(
            extract_string_field(json, "method").as_deref(),
            Some("textDocument/hover")
        );
    }

    #[test]
    fn extract_int_field_works() {
        let json = r#"{"note":"\"id\":999","method":"initialize","id":42}"#;
        assert_eq!(extract_int_field(json, "id"), Some(42));
    }

    #[test]
    fn extract_text_document_uri_works() {
        let json = r#"{"params":{"textDocument":{"uri":"file:///foo.lean","text":"hello"}}}"#;
        assert_eq!(
            extract_text_document_uri(json),
            Some("file:///foo.lean".to_string())
        );
    }

    #[test]
    fn extract_text_document_uri_decodes_json_escapes() {
        let json = r#"{"params":{"textDocument":{"uri":"file:\/\/\/tmp\/\ud83e\udd16.lean","text":"hello"}}}"#;
        assert_eq!(
            extract_text_document_uri(json),
            Some("file:///tmp/🤖.lean".to_string())
        );
    }

    #[test]
    fn did_change_routes_through_callback() {
        let (outcome, output) = lifecycle_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"def x := 42"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///test.lean","version":2},"contentChanges":[{"text":"def y := 7"}]}}"#,
        ].join("\n"));
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 1);
        assert_eq!(outcome.documents_changed, 1);
        assert_eq!(output.matches("publishDiagnostics").count(), 2);
        assert_eq!(output.matches("$/lean/fileProgress").count(), 4);
    }

    #[test]
    fn extract_content_changes_text_works() {
        let json = r#"{"params":{"textDocument":{"uri":"file:///x.lean","version":2},"contentChanges":[{"text":"def z := 0"}]}}"#;
        assert_eq!(
            extract_content_changes_text(json),
            Some("def z := 0".to_string())
        );
    }

    #[test]
    fn escaped_text_decodes_all_json_escapes_and_surrogate_pairs() {
        let json = r#"{"text":"\ud83e\udd16 a\/b\b\f\n\r\t\\\""}"#;
        assert_eq!(
            extract_escaped_text_value(json, 0).as_deref(),
            Some("🤖 a/b\u{0008}\u{000c}\n\r\t\\\"")
        );
    }

    #[test]
    fn escaped_text_rejects_malformed_json_strings() {
        for json in [
            r#"{"text":"\ud83e"}"#,
            r#"{"text":"\udd16"}"#,
            r#"{"text":"\ud83e\u0041"}"#,
            r#"{"text":"\q"}"#,
            r#"{"text":"\u12xz"}"#,
            "{\"text\":\"line\nfeed\"}",
        ] {
            assert!(
                extract_escaped_text_value(json, 0).is_none(),
                "malformed JSON string was accepted: {json:?}"
            );
        }
    }

    #[test]
    fn did_save_routes_through_callback() {
        let (outcome, output) = lifecycle_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"def x := 42"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///test.lean","version":1},"text":"def x := 42"}}"#,
        ].join("\n"));
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 1);
        assert_eq!(outcome.documents_saved, 1);
        assert_eq!(output.matches("publishDiagnostics").count(), 2);
        assert_eq!(output.matches("$/lean/fileProgress").count(), 4);
    }

    #[test]
    fn extract_save_text_works() {
        let json = r#"{"params":{"textDocument":{"uri":"file:///x.lean","version":1},"text":"def w := 99"}}"#;
        assert_eq!(
            extract_save_text(json),
            Some("def w := 99".to_string())
        );
    }

    #[test]
    fn plain_goal_returns_null_not_method_not_found() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","id":10,"method":"$/lean/plainGoal","params":{"textDocument":{"uri":"file:///test.lean"},"position":{"line":0,"character":0}}}"#,
        );
        assert!(outcome.clean);
        assert!(output.contains("\"id\":10"));
        assert!(output.contains("\"result\":null"));
        assert!(!output.contains("-32601"));
    }

    #[test]
    fn hover_returns_null_gracefully() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","id":11,"method":"textDocument/hover","params":{"textDocument":{"uri":"file:///test.lean"},"position":{"line":0,"character":0}}}"#,
        );
        assert!(outcome.clean);
        assert!(output.contains("\"id\":11"));
        assert!(output.contains("\"result\":null"));
        assert!(!output.contains("-32601"));
    }

    #[test]
    fn rpc_connect_fails_closed_without_fabricating_session() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","id":12,"method":"$/lean/rpc/connect","params":{"uri":"file:///test.lean"}}"#,
        );
        assert!(outcome.clean);
        assert!(output.contains("\"id\":12,\"error\":{\"code\":-32803"));
        assert!(output.contains("Lean RPC sessions are not implemented"));
        assert!(!output.contains("fln-stub-0"));
    }

    #[test]
    fn rpc_call_fails_closed_without_fabricating_result() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","id":13,"method":"$/lean/rpc/call","params":{"sessionId":"missing"}}"#,
        );
        assert!(outcome.clean);
        assert!(output.contains("\"id\":13,\"error\":{\"code\":-32803"));
        assert!(output.contains("Lean RPC calls are not implemented"));
    }

    #[test]
    fn file_progress_notification_format() {
        let started = file_progress_notification("file:///test.lean", true);
        assert!(started.contains("$/lean/fileProgress"));
        assert!(started.contains("\"kind\":1"));
        assert!(started.contains("\"uri\":\"file:///test.lean\""));

        let done = file_progress_notification("file:///test.lean", false);
        assert!(done.contains("$/lean/fileProgress"));
        assert!(done.contains("\"processing\":[]"));
        assert!(done.contains("\"uri\":\"file:///test.lean\""));
    }
}
