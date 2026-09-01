//! Minimal JSON-RPC dispatch for the LSP lifecycle and document events.
//!
//! This module intentionally implements only the bounded LSP surface FrankenLean
//! currently owns. It does not depend on serde or another JSON library (doctrine
//! D1), so the parser below is small, structural, iterative, and fail-closed.
//!
//! Two distinctions are load-bearing:
//! - JSON-RPC envelope fields are read only from the root object.
//! - LSP document fields are read from their exact `params` / `textDocument`
//!   containers, never by searching arbitrary nested text for a matching key.
//!
//! Full document synchronization retains a bounded copy of the latest source so
//! a textless `didSave` can still re-check the exact document last supplied by
//! the client. Cache refusal is visible and never suppresses a check for source
//! that arrived in the current notification.

use std::collections::BTreeMap;
use std::io::{self, BufRead, Write};

use crate::json_string;
use crate::transport;

const MAX_JSON_NESTING: usize = 256;
const MAX_OPEN_DOCUMENTS: usize = 1024;
const MAX_OPEN_DOCUMENT_BYTES: usize = 256 * 1024 * 1024;
const REQUEST_FAILED_CODE: i32 = -32803;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Field<'a> {
    Missing,
    Value(&'a str),
    Invalid,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CacheRefusal {
    DocumentLimit,
    ByteLimit,
    AccountingOverflow,
}

impl CacheRefusal {
    const fn message(self) -> &'static str {
        match self {
            Self::DocumentLimit => {
                "FrankenLean source cache is full; current source was checked but not retained"
            }
            Self::ByteLimit => {
                "FrankenLean source cache byte budget is exhausted; current source was checked but not retained"
            }
            Self::AccountingOverflow => {
                "FrankenLean source cache accounting overflowed; current source was checked but not retained"
            }
        }
    }
}

#[derive(Debug)]
struct DocumentCache {
    documents: BTreeMap<String, String>,
    total_bytes: usize,
    max_documents: usize,
    max_bytes: usize,
}

impl DocumentCache {
    fn new() -> Self {
        Self::with_limits(MAX_OPEN_DOCUMENTS, MAX_OPEN_DOCUMENT_BYTES)
    }

    fn with_limits(max_documents: usize, max_bytes: usize) -> Self {
        Self {
            documents: BTreeMap::new(),
            total_bytes: 0,
            max_documents,
            max_bytes,
        }
    }

    fn store(&mut self, uri: String, text: String) -> Result<(), CacheRefusal> {
        let old = self.documents.remove(&uri);
        let old_len = old.as_ref().map_or(0, String::len);
        self.total_bytes = self
            .total_bytes
            .checked_sub(old_len)
            .ok_or(CacheRefusal::AccountingOverflow)?;

        if old.is_none() && self.documents.len() >= self.max_documents {
            return Err(CacheRefusal::DocumentLimit);
        }
        let next_total = self
            .total_bytes
            .checked_add(text.len())
            .ok_or(CacheRefusal::AccountingOverflow)?;
        if next_total > self.max_bytes {
            return Err(CacheRefusal::ByteLimit);
        }
        self.documents.insert(uri, text);
        self.total_bytes = next_total;
        Ok(())
    }

    fn get(&self, uri: &str) -> Option<&str> {
        self.documents.get(uri).map(String::as_str)
    }

    fn remove(&mut self, uri: &str) -> Result<(), CacheRefusal> {
        let Some(text) = self.documents.remove(uri) else {
            return Ok(());
        };
        self.total_bytes = self
            .total_bytes
            .checked_sub(text.len())
            .ok_or(CacheRefusal::AccountingOverflow)?;
        Ok(())
    }
}

fn skip_ws(bytes: &[u8], mut index: usize) -> usize {
    while matches!(
        bytes.get(index).copied(),
        Some(b' ') | Some(b'\t') | Some(b'\r') | Some(b'\n')
    ) {
        index += 1;
    }
    index
}

fn scan_string_end(bytes: &[u8], start: usize) -> Option<usize> {
    if bytes.get(start).copied()? != b'"' {
        return None;
    }
    let mut index = start.checked_add(1)?;
    while index < bytes.len() {
        match bytes[index] {
            b'"' => return index.checked_add(1),
            b'\\' => {
                index = index.checked_add(2)?;
                if index > bytes.len() {
                    return None;
                }
            }
            0x00..=0x1f => return None,
            _ => index += 1,
        }
    }
    None
}

/// Return the exclusive end of one JSON value without recursively descending.
///
/// This is a structural boundary scanner, not a generic JSON decoder. Root and
/// selected object fields are validated separately. The fixed stack bounds
/// adversarial nesting while preserving arbitrary strings and nested values.
fn scan_value_end(json: &str, start: usize) -> Option<usize> {
    let bytes = json.as_bytes();
    let start = skip_ws(bytes, start);
    match bytes.get(start).copied()? {
        b'"' => scan_string_end(bytes, start),
        b'{' | b'[' => {
            let mut stack = [0u8; MAX_JSON_NESTING];
            let mut depth = 0usize;
            let mut index = start;
            while index < bytes.len() {
                match bytes[index] {
                    b'"' => {
                        index = scan_string_end(bytes, index)?;
                    }
                    opener @ (b'{' | b'[') => {
                        if depth == MAX_JSON_NESTING {
                            return None;
                        }
                        stack[depth] = opener;
                        depth += 1;
                        index += 1;
                    }
                    closer @ (b'}' | b']') => {
                        let opener = *stack.get(depth.checked_sub(1)?)?;
                        let expected = match opener {
                            b'{' => b'}',
                            b'[' => b']',
                            _ => return None,
                        };
                        if closer != expected {
                            return None;
                        }
                        depth -= 1;
                        index += 1;
                        if depth == 0 {
                            return Some(index);
                        }
                    }
                    _ => index += 1,
                }
            }
            None
        }
        _ => {
            let mut index = start;
            while let Some(byte) = bytes.get(index).copied() {
                if matches!(byte, b',' | b'}' | b']' | b' ' | b'\t' | b'\r' | b'\n') {
                    break;
                }
                index += 1;
            }
            (index > start).then_some(index)
        }
    }
}

/// Read one literal ASCII key from one exact JSON object.
///
/// Duplicate selected keys, escaped keys, malformed separators, mismatched
/// containers, excessive nesting, and trailing bytes all return `Invalid`.
/// The parser deliberately scans through the closing brace even after finding a
/// match so a duplicate cannot be hidden later in the object.
fn object_field<'a>(json: &'a str, wanted: &str) -> Field<'a> {
    let bytes = json.as_bytes();
    let mut index = skip_ws(bytes, 0);
    if bytes.get(index).copied() != Some(b'{') {
        return Field::Invalid;
    }
    index += 1;
    let mut found: Option<&str> = None;

    loop {
        index = skip_ws(bytes, index);
        match bytes.get(index).copied() {
            Some(b'}') => {
                index += 1;
                if skip_ws(bytes, index) != bytes.len() {
                    return Field::Invalid;
                }
                return found.map_or(Field::Missing, Field::Value);
            }
            Some(b'"') => {}
            _ => return Field::Invalid,
        }

        let key_end = match scan_string_end(bytes, index) {
            Some(value) => value,
            None => return Field::Invalid,
        };
        let key_raw = match json.get(index + 1..key_end - 1) {
            Some(value) => value,
            None => return Field::Invalid,
        };
        if key_raw.contains('\\') {
            return Field::Invalid;
        }
        index = skip_ws(bytes, key_end);
        if bytes.get(index).copied() != Some(b':') {
            return Field::Invalid;
        }
        index += 1;
        index = skip_ws(bytes, index);
        let value_start = index;
        let value_end = match scan_value_end(json, value_start) {
            Some(value) => value,
            None => return Field::Invalid,
        };

        if key_raw == wanted {
            if found.is_some() {
                return Field::Invalid;
            }
            found = json.get(value_start..value_end);
            if found.is_none() {
                return Field::Invalid;
            }
        }

        index = skip_ws(bytes, value_end);
        match bytes.get(index).copied() {
            Some(b',') => {
                index += 1;
                if bytes.get(skip_ws(bytes, index)).copied() == Some(b'}') {
                    return Field::Invalid;
                }
            }
            Some(b'}') => {}
            _ => return Field::Invalid,
        }
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

fn decode_json_string_value(value: &str) -> Option<String> {
    let value = value.trim();
    let after_quote = value.strip_prefix('"')?;
    let encoded_len = scan_string_end(value.as_bytes(), 0)?;
    if encoded_len != value.len() {
        return None;
    }
    decode_json_string(after_quote)
}

fn extract_integer_value(value: &str) -> Option<i64> {
    let value = value.trim();
    let bytes = value.as_bytes();
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
    if index != bytes.len() {
        return None;
    }
    value.parse::<i64>().ok()
}

fn extract_request_id(json: &str) -> RequestIdField {
    match object_field(json, "id") {
        Field::Missing => RequestIdField::Absent,
        Field::Invalid => RequestIdField::Invalid,
        Field::Value(value) => {
            if value.trim_start().starts_with('"') {
                decode_json_string_value(value)
                    .map(RequestId::Text)
                    .map_or(RequestIdField::Invalid, RequestIdField::Valid)
            } else {
                extract_integer_value(value)
                    .map(RequestId::Integer)
                    .map_or(RequestIdField::Invalid, RequestIdField::Valid)
            }
        }
    }
}

fn extract_top_level_string_field(json: &str, key: &str) -> Option<String> {
    match object_field(json, key) {
        Field::Value(value) => decode_json_string_value(value),
        Field::Missing | Field::Invalid => None,
    }
}

fn params_object(json: &str) -> Option<&str> {
    match object_field(json, "params") {
        Field::Value(value) if value.trim_start().starts_with('{') => Some(value),
        Field::Missing | Field::Value(_) | Field::Invalid => None,
    }
}

fn text_document_object(json: &str) -> Option<&str> {
    let params = params_object(json)?;
    match object_field(params, "textDocument") {
        Field::Value(value) if value.trim_start().starts_with('{') => Some(value),
        Field::Missing | Field::Value(_) | Field::Invalid => None,
    }
}

fn extract_text_document_uri(json: &str) -> Option<String> {
    let text_document = text_document_object(json)?;
    match object_field(text_document, "uri") {
        Field::Value(value) => decode_json_string_value(value),
        Field::Missing | Field::Invalid => None,
    }
}

fn extract_text_document_text(json: &str) -> Option<String> {
    let text_document = text_document_object(json)?;
    match object_field(text_document, "text") {
        Field::Value(value) => decode_json_string_value(value),
        Field::Missing | Field::Invalid => None,
    }
}

fn extract_save_text(json: &str) -> Option<String> {
    let params = params_object(json)?;
    match object_field(params, "text") {
        Field::Value(value) => decode_json_string_value(value),
        Field::Missing | Field::Invalid => None,
    }
}

fn single_array_element(value: &str) -> Option<&str> {
    let bytes = value.as_bytes();
    let mut index = skip_ws(bytes, 0);
    if bytes.get(index).copied() != Some(b'[') {
        return None;
    }
    index += 1;
    index = skip_ws(bytes, index);
    if bytes.get(index).copied() == Some(b']') {
        return None;
    }
    let start = index;
    let end = scan_value_end(value, start)?;
    index = skip_ws(bytes, end);
    if bytes.get(index).copied() != Some(b']') {
        return None;
    }
    index += 1;
    if skip_ws(bytes, index) != bytes.len() {
        return None;
    }
    value.get(start..end)
}

fn extract_content_changes_text(json: &str) -> Option<String> {
    let params = params_object(json)?;
    let changes = match object_field(params, "contentChanges") {
        Field::Value(value) => value,
        Field::Missing | Field::Invalid => return None,
    };
    let change = single_array_element(changes)?;
    match object_field(change, "text") {
        Field::Value(value) => decode_json_string_value(value),
        Field::Missing | Field::Invalid => None,
    }
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

fn clear_diagnostics_notification(uri: &str) -> String {
    format!(
        concat!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",",
            "\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}"
        ),
        json_string(uri)
    )
}

fn log_warning(message: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"window/logMessage\",\"params\":{{\"type\":2,\"message\":{}}}}}",
        json_string(message)
    )
}

fn check_document(
    output: &mut dyn Write,
    uri: &str,
    content: &str,
    on_did_open: &mut OnDidOpen,
) -> io::Result<()> {
    transport::write_message(output, file_progress_notification(uri, true).as_bytes())?;
    for notification in on_did_open(uri, content) {
        transport::write_message(output, notification.as_bytes())?;
    }
    transport::write_message(output, file_progress_notification(uri, false).as_bytes())
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
    let mut documents = DocumentCache::new();

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
                    if let Err(refusal) = documents.store(uri.clone(), content.clone()) {
                        transport::write_message(output, log_warning(refusal.message()).as_bytes())?;
                    }
                    check_document(output, &uri, &content, on_did_open)?;
                    documents_opened = documents_opened.saturating_add(1);
                }
            }
            (Some("textDocument/didChange"), None, ServerState::Running) => {
                if let (Some(uri), Some(content)) = (
                    extract_text_document_uri(&text),
                    extract_content_changes_text(&text),
                ) {
                    if let Err(refusal) = documents.store(uri.clone(), content.clone()) {
                        transport::write_message(output, log_warning(refusal.message()).as_bytes())?;
                    }
                    check_document(output, &uri, &content, on_did_open)?;
                    documents_changed = documents_changed.saturating_add(1);
                }
            }
            (Some("textDocument/didSave"), None, ServerState::Running) => {
                if let Some(uri) = extract_text_document_uri(&text) {
                    if let Some(content) = extract_save_text(&text) {
                        if let Err(refusal) = documents.store(uri.clone(), content.clone()) {
                            transport::write_message(output, log_warning(refusal.message()).as_bytes())?;
                        }
                        check_document(output, &uri, &content, on_did_open)?;
                        documents_saved = documents_saved.saturating_add(1);
                    } else if let Some(content) = documents.get(&uri) {
                        check_document(output, &uri, content, on_did_open)?;
                        documents_saved = documents_saved.saturating_add(1);
                    } else {
                        transport::write_message(
                            output,
                            log_warning(
                                "FrankenLean could not re-check textless didSave because no retained source exists",
                            )
                            .as_bytes(),
                        )?;
                    }
                }
            }
            (Some("textDocument/didClose"), None, ServerState::Running) => {
                if let Some(uri) = extract_text_document_uri(&text) {
                    if let Err(refusal) = documents.remove(&uri) {
                        transport::write_message(output, log_warning(refusal.message()).as_bytes())?;
                    }
                    transport::write_message(
                        output,
                        clear_diagnostics_notification(&uri).as_bytes(),
                    )?;
                }
            }
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

    fn run_session(extra_messages: &str) -> (ServerOutcome, String, Vec<(String, String)>) {
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
        let mut seen = Vec::new();
        let outcome = serve(
            &mut reader,
            &mut output_buf,
            &mut |uri, text| {
                seen.push((uri.to_string(), text.to_string()));
                vec![format!(
                    "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[{{\"message\":{}}}]}}}}",
                    json_string(uri),
                    json_string(text)
                )]
            },
        )
        .unwrap();
        (
            outcome,
            String::from_utf8(output_buf).unwrap(),
            seen,
        )
    }

    fn lifecycle_session(extra_messages: &str) -> (ServerOutcome, String) {
        let (outcome, output, _) = run_session(extra_messages);
        (outcome, output)
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
        assert_eq!(
            extract_request_id(r#"{"method":"exit"}"#),
            RequestIdField::Absent
        );
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
            r#"{"id":1,"id":2}"#,
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
    fn structural_object_field_rejects_duplicate_and_mismatched_containers() {
        assert_eq!(object_field(r#"{"x":1,"x":2}"#, "x"), Field::Invalid);
        assert_eq!(object_field(r#"{"x":[1}}"#, "x"), Field::Invalid);
        assert_eq!(object_field(r#"{"x":1,}"#, "x"), Field::Invalid);

        let nested = format!(
            "{}{}",
            "[".repeat(MAX_JSON_NESTING + 1),
            "]".repeat(MAX_JSON_NESTING + 1)
        );
        let deep = format!("{{\"x\":{nested}}}");
        assert_eq!(object_field(&deep, "x"), Field::Invalid);
    }

    #[test]
    fn did_open_routes_through_callback() {
        let (outcome, output, seen) = run_session(
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"def x := 42"}}}"#,
        );
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 1);
        assert_eq!(
            seen,
            vec![("file:///test.lean".to_string(), "def x := 42".to_string())]
        );
        assert!(output.contains("publishDiagnostics"));
        assert_eq!(output.matches("$/lean/fileProgress").count(), 2);
    }

    #[test]
    fn document_fields_are_bound_to_exact_params_structure() {
        let json = r#"{"textDocument":{"uri":"file:///wrong.lean","text":"wrong"},"params":{"metadata":{"textDocument":{"uri":"file:///also-wrong.lean"}},"textDocument":{"uri":"file:///right.lean","text":"right"}}}"#;
        assert_eq!(
            extract_text_document_uri(json).as_deref(),
            Some("file:///right.lean")
        );
        assert_eq!(extract_text_document_text(json).as_deref(), Some("right"));
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
    fn text_document_uri_decodes_json_escapes() {
        let json = r#"{"params":{"textDocument":{"uri":"file:\/\/\/tmp\/\ud83e\udd16.lean","text":"hello"}}}"#;
        assert_eq!(
            extract_text_document_uri(json),
            Some("file:///tmp/🤖.lean".to_string())
        );
    }

    #[test]
    fn did_change_routes_full_document_through_callback() {
        let (outcome, output, seen) = run_session(
            &[
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"def x := 42"}}}"#,
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///test.lean","version":2},"contentChanges":[{"text":"def y := 7"}]}}"#,
            ]
            .join("\n"),
        );
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 1);
        assert_eq!(outcome.documents_changed, 1);
        assert_eq!(
            seen.last(),
            Some(&("file:///test.lean".to_string(), "def y := 7".to_string()))
        );
        assert_eq!(output.matches("publishDiagnostics").count(), 2);
        assert_eq!(output.matches("$/lean/fileProgress").count(), 4);
    }

    #[test]
    fn full_sync_refuses_empty_or_multiple_content_changes() {
        for json in [
            r#"{"params":{"textDocument":{"uri":"file:///x.lean"},"contentChanges":[]}}"#,
            r#"{"params":{"textDocument":{"uri":"file:///x.lean"},"contentChanges":[{"text":"a"},{"text":"b"}]}}"#,
        ] {
            assert_eq!(
                extract_content_changes_text(json),
                None,
                "invalid Full-sync change array was accepted: {json}"
            );
        }
    }

    #[test]
    fn escaped_text_decodes_all_json_escapes_and_surrogate_pairs() {
        let json = r#"{"params":{"textDocument":{"text":"\ud83e\udd16 a\/b\b\f\n\r\t\\\""}}}"#;
        assert_eq!(
            extract_text_document_text(json).as_deref(),
            Some("🤖 a/b\u{0008}\u{000c}\n\r\t\\\"")
        );
    }

    #[test]
    fn escaped_text_rejects_malformed_json_strings() {
        for value in [
            r#""\ud83e""#,
            r#""\udd16""#,
            r#""\ud83e\u0041""#,
            r#""\q""#,
            r#""\u12xz""#,
            "\"line\nfeed\"",
        ] {
            assert!(
                decode_json_string_value(value).is_none(),
                "malformed JSON string was accepted: {value:?}"
            );
        }
    }

    #[test]
    fn did_save_with_text_routes_through_callback() {
        let (outcome, output, seen) = run_session(
            &[
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"old"}}}"#,
                r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///test.lean","version":1},"text":"saved"}}"#,
            ]
            .join("\n"),
        );
        assert!(outcome.clean);
        assert_eq!(outcome.documents_saved, 1);
        assert_eq!(
            seen.last(),
            Some(&("file:///test.lean".to_string(), "saved".to_string()))
        );
        assert_eq!(output.matches("$/lean/fileProgress").count(), 4);
    }

    #[test]
    fn textless_save_rechecks_latest_cached_full_document() {
        let (outcome, _output, seen) = run_session(
            &[
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"old"}}}"#,
                r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///test.lean","version":2},"contentChanges":[{"text":"latest"}]}}"#,
                r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///test.lean","version":2}}}"#,
            ]
            .join("\n"),
        );
        assert!(outcome.clean);
        assert_eq!(outcome.documents_saved, 1);
        assert_eq!(
            seen.last(),
            Some(&("file:///test.lean".to_string(), "latest".to_string()))
        );
    }

    #[test]
    fn textless_save_without_retained_source_is_visible_and_not_counted() {
        let (outcome, output, seen) = run_session(
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///missing.lean"}}}"#,
        );
        assert!(outcome.clean);
        assert_eq!(outcome.documents_saved, 0);
        assert!(seen.is_empty());
        assert!(output.contains("window/logMessage"));
        assert!(output.contains("no retained source exists"));
    }

    #[test]
    fn did_close_evicts_source_and_clears_push_diagnostics() {
        let (outcome, output, seen) = run_session(
            &[
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///test.lean","languageId":"lean4","version":1,"text":"open"}}}"#,
                r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///test.lean"}}}"#,
                r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///test.lean"}}}"#,
            ]
            .join("\n"),
        );
        assert!(outcome.clean);
        assert_eq!(seen.len(), 1, "closed source must not be reused by didSave");
        assert!(output.contains("\"uri\":\"file:///test.lean\",\"diagnostics\":[]"));
        assert!(output.contains("no retained source exists"));
    }

    #[test]
    fn document_cache_is_failure_atomic_at_both_limits() {
        let mut count_limited = DocumentCache::with_limits(1, 100);
        count_limited
            .store("a".to_string(), "one".to_string())
            .unwrap();
        assert_eq!(
            count_limited.store("b".to_string(), "two".to_string()),
            Err(CacheRefusal::DocumentLimit)
        );
        assert_eq!(count_limited.get("a"), Some("one"));
        assert_eq!(count_limited.get("b"), None);

        let mut byte_limited = DocumentCache::with_limits(2, 5);
        byte_limited
            .store("a".to_string(), "1234".to_string())
            .unwrap();
        assert_eq!(
            byte_limited.store("b".to_string(), "12".to_string()),
            Err(CacheRefusal::ByteLimit)
        );
        assert_eq!(byte_limited.total_bytes, 4);
        assert_eq!(
            byte_limited.store("a".to_string(), "123456".to_string()),
            Err(CacheRefusal::ByteLimit)
        );
        assert_eq!(
            byte_limited.get("a"),
            None,
            "a rejected replacement must invalidate the now-stale cached text"
        );
        assert_eq!(byte_limited.total_bytes, 0);
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
