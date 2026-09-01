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
    Uninitialized,
    Initializing,
    Running,
    ShuttingDown,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerOutcome {
    pub clean: bool,
    pub documents_opened: u64,
    pub documents_changed: u64,
    pub documents_saved: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum RequestId {
    Integer(i64),
    Text(String),
}

impl RequestId {
    fn as_json(&self) -> String {
        match self {
            Self::Integer(value) => value.to_string(),
            Self::Text(value) => json_string(value),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum RequestIdField {
    Absent,
    Valid(RequestId),
    Invalid,
}

/// Find an unescaped JSON key at any depth. This is used only after the caller
/// has already selected the relevant nested protocol region.
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
            && json.get(after..)?.trim_start().starts_with(':')
        {
            return Some(after);
        }
        offset = start.checked_add(1)?;
    }
}

/// Find a literal ASCII key on the root JSON object's own field plane.
///
/// JSON-RPC `method` and `id` belong to the envelope, not arbitrary nested
/// objects. A flat substring search lets `params.id` or `params.method` hijack
/// routing when that nested key appears first. This scanner tracks container
/// depth while skipping complete string literals; escaped key spellings are
/// deliberately not normalized, so unfamiliar envelope syntax fails closed.
fn find_top_level_json_key(json: &str, key: &str) -> Option<usize> {
    let bytes = json.as_bytes();
    let mut index = 0usize;
    let mut depth = 0usize;

    while index < bytes.len() {
        match bytes[index] {
            b'{' | b'[' => {
                depth = depth.checked_add(1)?;
                index += 1;
            }
            b'}' | b']' => {
                depth = depth.checked_sub(1)?;
                index += 1;
            }
            b'"' => {
                let start = index.checked_add(1)?;
                index = start;
                while index < bytes.len() {
                    match bytes[index] {
                        b'\\' => {
                            index = index.checked_add(2)?;
                        }
                        b'"' => break,
                        _ => index += 1,
                    }
                }
                if index >= bytes.len() {
                    return None;
                }
                if depth == 1
                    && json.get(start..index)? == key
                    && json
                        .get(index.checked_add(1)?..)?
                        .trim_start()
                        .starts_with(':')
                {
                    return index.checked_add(1);
                }
                index += 1;
            }
            _ => index += 1,
        }
    }
    None
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

fn encoded_json_string_len(after_quote: &str) -> Option<usize> {
    let bytes = after_quote.as_bytes();
    let mut index = 0usize;
    while index < bytes.len() {
        match bytes[index] {
            b'"' => return index.checked_add(1),
            b'\\' => {
                index = index.checked_add(2)?;
            }
            _ => index += 1,
        }
    }
    None
}

fn json_value_has_terminator(rest: &str) -> bool {
    matches!(
        rest.trim_start().as_bytes().first().copied(),
        None | Some(b',') | Some(b'}') | Some(b']')
    )
}

fn string_value_after_key(json: &str, after_key: usize) -> Option<String> {
    let after_key = json.get(after_key..)?;
    let after_colon = after_key.trim_start().strip_prefix(':')?.trim_start();
    let after_quote = after_colon.strip_prefix('"')?;
    decode_json_string(after_quote)
}

fn extract_string_field(json: &str, key: &str) -> Option<String> {
    string_value_after_key(json, find_json_key(json, key)?)
}

fn extract_top_level_string_field(json: &str, key: &str) -> Option<String> {
    string_value_after_key(json, find_top_level_json_key(json, key)?)
}

fn extract_integer_value(after_colon: &str) -> Option<i64> {
    let bytes = after_colon.as_bytes();
    let mut index = 0usize;
    if bytes.first().copied() == Some(b'-') {
        index = 1;
    }
    let first_digit = *bytes.get(index)?;
    match first_digit {
        b'0' => {
            index += 1;
            if bytes.get(index).is_some_and(u8::is_ascii_digit) {
                return None;
            }
        }
        b'1'..=b'9' => {
            index += 1;
            while bytes.get(index).is_some_and(u8::is_ascii_digit) {
                index += 1;
            }
        }
        _ => return None,
    }
    if !json_value_has_terminator(after_colon.get(index..)?) {
        return None;
    }
    after_colon.get(..index)?.parse::<i64>().ok()
}

fn extract_request_id(json: &str) -> RequestIdField {
    let Some(after_key_index) = find_top_level_json_key(json, "id") else {
        return RequestIdField::Absent;
    };
    let Some(after_key) = json.get(after_key_index..) else {
        return RequestIdField::Invalid;
    };
    let Some(after_colon) = after_key.trim_start().strip_prefix(':').map(str::trim_start) else {
        return RequestIdField::Invalid;
    };
    if let Some(after_quote) = after_colon.strip_prefix('"') {
        let Some(value) = decode_json_string(after_quote) else {
            return RequestIdField::Invalid;
        };
        let Some(encoded_len) = encoded_json_string_len(after_quote) else {
            return RequestIdField::Invalid;
        };
        let Some(rest) = after_quote.get(encoded_len..) else {
            return RequestIdField::Invalid;
        };
        if !json_value_has_terminator(rest) {
            return RequestIdField::Invalid;
        }
        return RequestIdField::Valid(RequestId::Text(value));
    }
    match extract_integer_value(after_colon) {
        Some(value) => RequestIdField::Valid(RequestId::Integer(value)),
        None => RequestIdField::Invalid,
    }
}

fn extract_text_document_uri(json: &str) -> Option<String> {
    let td_start = find_json_key(json, "textDocument")?;
    extract_string_field(&json[td_start..], "uri")
}

fn extract_escaped_text_value(haystack: &str, offset: usize) -> Option<String> {
    extract_string_field(haystack.get(offset..)?, "text")
}

fn extract_text_document_text(json: &str) -> Option<String> {
    let td_start = find_json_key(json, "textDocument")?;
    extract_escaped_text_value(json, td_start)
}

fn extract_content_changes_text(json: &str) -> Option<String> {
    let cc_start = find_json_key(json, "contentChanges")?;
    extract_escaped_text_value(json, cc_start)
}

fn extract_save_text(json: &str) -> Option<String> {
    extract_escaped_text_value(json, 0)
}

fn initialize_response(id: &RequestId) -> String {
    format!(
        concat!(
            "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":{{",
            "\"capabilities\":{{",
            "\"textDocumentSync\":{{\"openClose\":true,\"change\":1,",
            "\"save\":{{\"includeText\":true}}}}",
            "}},",
            "\"serverInfo\":{{\"name\":\"FrankenLean\",\"version\":{}}}",
            "}}}}"
        ),
        id.as_json(),
        json_string(env!("CARGO_PKG_VERSION"))
    )
}

fn error_response(id: &RequestId, code: i32, message: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"error\":{{\"code\":{},\"message\":{}}}}}",
        id.as_json(),
        code,
        json_string(message)
    )
}

fn error_response_null_id(code: i32, message: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":null,\"error\":{{\"code\":{},\"message\":{}}}}}",
        code,
        json_string(message)
    )
}

const REQUEST_FAILED_CODE: i32 = -32803;

fn null_response(id: &RequestId) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":null}}",
        id.as_json()
    )
}

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

pub type OnDidOpen = dyn FnMut(&str, &str) -> Vec<String>;

pub fn serve(
    input: &mut dyn BufRead,
    output: &mut dyn Write,
    on_did_open: &mut OnDidOpen,
) -> io::Result<ServerOutcome> {
    let mut state = ServerState::Uninitialized;
    let mut documents_opened = 0u64;
    let mut documents_changed = 0u64;
    let mut documents_saved = 0u64;

    loop {
        let Some(message) = transport::read_message(input)? else {
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
        let method = extract_top_level_string_field(&text, "method");
        let id = match extract_request_id(&text) {
            RequestIdField::Absent => None,
            RequestIdField::Valid(id) => Some(id),
            RequestIdField::Invalid => {
                let response = error_response_null_id(-32600, "invalid JSON-RPC request id");
                transport::write_message(output, response.as_bytes())?;
                continue;
            }
        };

        match (method.as_deref(), id.as_ref(), state) {
            (Some("initialize"), Some(req_id), ServerState::Uninitialized) => {
                transport::write_message(output, initialize_response(req_id).as_bytes())?;
                state = ServerState::Initializing;
            }
            (Some("initialize"), Some(req_id), _) => {
                transport::write_message(
                    output,
                    error_response(req_id, -32600, "server already initialized").as_bytes(),
                )?;
            }
            (Some("initialized"), None, ServerState::Initializing) => {
                state = ServerState::Running;
            }
            (Some("shutdown"), Some(req_id), _) => {
                transport::write_message(output, null_response(req_id).as_bytes())?;
                state = ServerState::ShuttingDown;
            }
            (Some("exit"), None, _) => {
                return Ok(ServerOutcome {
                    clean: state == ServerState::ShuttingDown,
                    documents_opened,
                    documents_changed,
                    documents_saved,
                });
            }
            (Some("textDocument/didOpen"), None, ServerState::Running) => {
                if let (Some(uri), Some(content)) = (
                    extract_text_document_uri(&text),
                    extract_text_document_text(&text),
                ) {
                    transport::write_message(
                        output,
                        file_progress_notification(&uri, true).as_bytes(),
                    )?;
                    for notification in on_did_open(&uri, &content) {
                        transport::write_message(output, notification.as_bytes())?;
                    }
                    transport::write_message(
                        output,
                        file_progress_notification(&uri, false).as_bytes(),
                    )?;
                    documents_opened += 1;
                }
            }
            (Some("textDocument/didChange"), None, ServerState::Running) => {
                if let (Some(uri), Some(content)) = (
                    extract_text_document_uri(&text),
                    extract_content_changes_text(&text),
                ) {
                    transport::write_message(
                        output,
                        file_progress_notification(&uri, true).as_bytes(),
                    )?;
                    for notification in on_did_open(&uri, &content) {
                        transport::write_message(output, notification.as_bytes())?;
                    }
                    transport::write_message(
                        output,
                        file_progress_notification(&uri, false).as_bytes(),
                    )?;
                    documents_changed += 1;
                }
            }
            (Some("textDocument/didSave"), None, ServerState::Running) => {
                if let (Some(uri), Some(content)) = (
                    extract_text_document_uri(&text),
                    extract_save_text(&text),
                ) {
                    transport::write_message(
                        output,
                        file_progress_notification(&uri, true).as_bytes(),
                    )?;
                    for notification in on_did_open(&uri, &content) {
                        transport::write_message(output, notification.as_bytes())?;
                    }
                    transport::write_message(
                        output,
                        file_progress_notification(&uri, false).as_bytes(),
                    )?;
                    documents_saved += 1;
                }
            }
            (Some("textDocument/didClose"), None, ServerState::Running) => {}
            (Some("$/lean/plainGoal"), Some(req_id), ServerState::Running)
            | (Some("$/lean/plainTermGoal"), Some(req_id), ServerState::Running)
            | (Some("textDocument/hover"), Some(req_id), ServerState::Running)
            | (Some("textDocument/completion"), Some(req_id), ServerState::Running)
            | (Some("textDocument/definition"), Some(req_id), ServerState::Running) => {
                transport::write_message(output, null_response(req_id).as_bytes())?;
            }
            (Some("$/lean/rpc/connect"), Some(req_id), ServerState::Running) => {
                transport::write_message(
                    output,
                    error_response(
                        req_id,
                        REQUEST_FAILED_CODE,
                        "Lean RPC sessions are not implemented by this FrankenLean server",
                    )
                    .as_bytes(),
                )?;
            }
            (Some("$/lean/rpc/call"), Some(req_id), ServerState::Running) => {
                transport::write_message(
                    output,
                    error_response(
                        req_id,
                        REQUEST_FAILED_CODE,
                        "Lean RPC calls are not implemented by this FrankenLean server",
                    )
                    .as_bytes(),
                )?;
            }
            (_, Some(req_id), _) => {
                transport::write_message(
                    output,
                    error_response(req_id, -32601, "method not found").as_bytes(),
                )?;
            }
            (_, None, _) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::transport::write_message;
    use std::io::BufReader;

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
    }

    #[test]
    fn request_id_parser_preserves_integer_and_string_ids() {
        assert_eq!(
            extract_request_id(r#"{"id":42}"#),
            RequestIdField::Valid(RequestId::Integer(42))
        );
        assert_eq!(
            extract_request_id(r#"{"id":-1}"#),
            RequestIdField::Valid(RequestId::Integer(-1))
        );
        assert_eq!(
            extract_request_id(r#"{"id":"req-\ud83e\udd16"}"#),
            RequestIdField::Valid(RequestId::Text("req-🤖".to_string()))
        );
        assert_eq!(extract_request_id(r#"{"method":"exit"}"#), RequestIdField::Absent);
    }

    #[test]
    fn malformed_request_ids_are_distinct_from_notifications() {
        for json in [
            r#"{"id":1.5}"#,
            r#"{"id":1e2}"#,
            r#"{"id":01}"#,
            r#"{"id":-}"#,
            r#"{"id":null}"#,
            r#"{"id":{}}"#,
            r#"{"id":9223372036854775808}"#,
            r#"{"id":"x"true}"#,
        ] {
            assert_eq!(
                extract_request_id(json),
                RequestIdField::Invalid,
                "malformed request id was accepted or erased: {json}"
            );
        }
    }

    #[test]
    fn malformed_request_id_returns_invalid_request_with_null_id() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","id":1.5,"method":"textDocument/hover","params":{}}"#,
        );
        assert!(outcome.clean);
        assert!(output.contains("\"id\":null,\"error\":{\"code\":-32600"));
        assert!(output.contains("invalid JSON-RPC request id"));
        assert!(!output.contains("\"id\":1,\"result\":null"));
    }

    #[test]
    fn envelope_fields_ignore_nested_lookalikes() {
        let json = r#"{"params":{"id":"shadow","method":"shutdown"},"id":"actual","method":"textDocument/hover"}"#;
        assert_eq!(
            extract_request_id(json),
            RequestIdField::Valid(RequestId::Text("actual".to_string()))
        );
        assert_eq!(
            extract_top_level_string_field(json, "method").as_deref(),
            Some("textDocument/hover")
        );
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
    fn nested_method_cannot_shutdown_server() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","id":14,"params":{"method":"shutdown"},"method":"textDocument/hover"}"#,
        );
        assert!(outcome.clean);
        assert!(output.contains("\"id\":14,\"result\":null"));
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
    fn string_request_id_is_preserved_in_response() {
        let (outcome, output) = lifecycle_session(
            r#"{"jsonrpc":"2.0","id":"hover-\ud83e\udd16","method":"textDocument/hover","params":{"textDocument":{"uri":"file:///test.lean"},"position":{"line":0,"character":0}}}"#,
        );
        assert!(outcome.clean);
        assert!(output.contains("\"id\":\"hover-🤖\",\"result\":null"));
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
