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

/// Extract a JSON string value for a given key from a flat JSON object.
///
/// This is intentionally limited: it finds `"key":"value"` or `"key": "value"`
/// patterns in a single-level object. It does not handle nested objects,
/// escaped quotes in values, or non-string value types. For the LSP lifecycle
/// messages we handle, this is sufficient.
fn extract_string_field<'a>(json: &'a str, key: &str) -> Option<&'a str> {
    let needle = format!("\"{key}\"");
    let start = json.find(&needle)?;
    let after_key = &json[start + needle.len()..];
    // Skip optional whitespace and the colon.
    let after_colon = after_key.trim_start().strip_prefix(':')?;
    let after_colon = after_colon.trim_start();
    // The value must be a string.
    let after_quote = after_colon.strip_prefix('"')?;
    let end = after_quote.find('"')?;
    Some(&after_quote[..end])
}

/// Extract a JSON integer value for a given key from a flat JSON object.
fn extract_int_field(json: &str, key: &str) -> Option<i64> {
    let needle = format!("\"{key}\"");
    let start = json.find(&needle)?;
    let after_key = &json[start + needle.len()..];
    let after_colon = after_key.trim_start().strip_prefix(':')?.trim_start();
    // Parse digits (possibly with leading minus).
    let end = after_colon
        .find(|c: char| !c.is_ascii_digit() && c != '-')
        .unwrap_or(after_colon.len());
    after_colon[..end].parse::<i64>().ok()
}

/// Extract the `uri` from a `textDocument` parameter.
///
/// Looks for `"textDocument"` then `"uri"` inside it.
fn extract_text_document_uri(json: &str) -> Option<String> {
    let td_start = json.find("\"textDocument\"")?;
    let rest = &json[td_start..];
    let uri = extract_string_field(rest, "uri")?;
    Some(uri.to_string())
}

/// Extract a JSON string value starting after a given byte offset, parsing
/// escape sequences. The search begins at `haystack[offset..]` and looks
/// for the first `"text"` key.
fn extract_escaped_text_value(haystack: &str, offset: usize) -> Option<String> {
    let region = haystack.get(offset..)?;
    let text_key = "\"text\"";
    let key_start = region.find(text_key)?;
    let after_key = &region[key_start + text_key.len()..];
    let after_colon = after_key.trim_start().strip_prefix(':')?.trim_start();
    let after_quote = after_colon.strip_prefix('"')?;

    let mut result = String::new();
    let mut chars = after_quote.chars();
    loop {
        match chars.next()? {
            '"' => break,
            '\\' => match chars.next()? {
                'n' => result.push('\n'),
                'r' => result.push('\r'),
                't' => result.push('\t'),
                '\\' => result.push('\\'),
                '"' => result.push('"'),
                '/' => result.push('/'),
                'b' => result.push('\u{08}'),
                'f' => result.push('\u{0c}'),
                'u' => {
                    let hex: String = (&mut chars).take(4).collect();
                    if hex.len() == 4 {
                        if let Ok(cp) = u32::from_str_radix(&hex, 16) {
                            if let Some(c) = char::from_u32(cp) {
                                result.push(c);
                            }
                        }
                    }
                }
                _ => {}
            },
            c => result.push(c),
        }
    }
    Some(result)
}

/// Extract the `text` from the `textDocument` parameter (for didOpen).
fn extract_text_document_text(json: &str) -> Option<String> {
    let td_start = json.find("\"textDocument\"")?;
    extract_escaped_text_value(json, td_start)
}

/// Extract the full document text from `contentChanges` (for didChange
/// with `TextDocumentSyncKind.Full`). The spec sends
/// `"contentChanges":[{"text":"..."}]`; we extract the `text` from the
/// first element.
fn extract_content_changes_text(json: &str) -> Option<String> {
    let cc_start = json.find("\"contentChanges\"")?;
    extract_escaped_text_value(json, cc_start)
}

/// Extract the params-level `text` field (for didSave with
/// `includeText: true`). The didSave `textDocument` object contains
/// only `uri` and `version` — no `text` — so the only `"text"` key
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

        match (method, id, state) {
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
                    // Signal that we are processing this file.
                    let started = file_progress_notification(&uri, true);
                    transport::write_message(output, started.as_bytes())?;
                    let notifications = on_did_open(&uri, &content);
                    for notification in &notifications {
                        transport::write_message(output, notification.as_bytes())?;
                    }
                    // Signal that processing is complete.
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
                    // Full sync: re-check the entire document, same as didOpen.
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
                    // Re-check the full document on save, same as didOpen.
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
                // If text is absent (client did not include it), accept
                // silently — the most recent didChange already checked.
            }

            // --- textDocument/didClose ---
            (Some("textDocument/didClose"), None, ServerState::Running) => {
                // Accepted but no action needed yet; the bounded source
                // runner is stateless.
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
        // initialize
        send(
            &mut input_buf,
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        );
        // initialized
        send(
            &mut input_buf,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        );
        // Extra messages go here.
        for line in extra_messages.lines() {
            if !line.trim().is_empty() {
                send(&mut input_buf, line.trim());
            }
        }
        // shutdown
        send(
            &mut input_buf,
            r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        );
        // exit
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

        let output_text = String::from_utf8(output_buf).unwrap();
        (outcome, output_text)
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
        // fileProgress: one "processing" start and one "complete" (empty).
        let progress_count = output.matches("$/lean/fileProgress").count();
        assert_eq!(progress_count, 2);
    }

    #[test]
    fn unknown_request_returns_method_not_found() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/completion","params":{}}"#,
        );
        assert!(outcome.clean);
        assert!(output.contains("-32601"));
    }

    #[test]
    fn extract_string_field_works() {
        let json = r#"{"method":"initialize","id":1}"#;
        assert_eq!(extract_string_field(json, "method"), Some("initialize"));
    }

    #[test]
    fn extract_int_field_works() {
        let json = r#"{"method":"initialize","id":42}"#;
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
    fn did_change_routes_through_callback() {
        let (outcome, output) = lifecycle_session(&[
            // Open first.
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"def x := 42"}}}"#,
            // Then change.
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///test.lean","version":2},"contentChanges":[{"text":"def y := 7"}]}}"#,
        ].join("\n"));
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 1);
        assert_eq!(outcome.documents_changed, 1);
        // Two publishDiagnostics notifications expected.
        let diag_count = output.matches("publishDiagnostics").count();
        assert_eq!(diag_count, 2);
        // Four fileProgress notifications: start+done for open, start+done for change.
        let progress_count = output.matches("$/lean/fileProgress").count();
        assert_eq!(progress_count, 4);
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
    fn did_save_routes_through_callback() {
        let (outcome, output) = lifecycle_session(&[
            // Open first.
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"def x := 42"}}}"#,
            // Save with included text.
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///test.lean","version":1},"text":"def x := 42"}}"#,
        ].join("\n"));
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 1);
        assert_eq!(outcome.documents_saved, 1);
        let diag_count = output.matches("publishDiagnostics").count();
        assert_eq!(diag_count, 2);
        // Four fileProgress notifications: start+done for open, start+done for save.
        let progress_count = output.matches("$/lean/fileProgress").count();
        assert_eq!(progress_count, 4);
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
