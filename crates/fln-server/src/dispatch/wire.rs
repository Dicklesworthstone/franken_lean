use crate::{LSP_POSITION_ENCODING, json_string};

use super::json::RequestId;

pub(super) const REQUEST_FAILED_CODE: i32 = -32803;
pub(super) const SERVER_NOT_INITIALIZED_CODE: i32 = -32002;

pub(super) fn initialize_response(id: &RequestId) -> String {
    format!(
        concat!(
            "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":{{",
            "\"capabilities\":{{\"positionEncoding\":{},",
            "\"textDocumentSync\":{{\"openClose\":true,\"change\":1,",
            "\"save\":{{\"includeText\":true}}}}}},",
            "\"serverInfo\":{{\"name\":\"FrankenLean\",\"version\":{}}}",
            "}}}}"
        ),
        id.as_json(),
        json_string(LSP_POSITION_ENCODING),
        json_string(env!("CARGO_PKG_VERSION"))
    )
}

pub(super) fn error_response(id: &RequestId, code: i32, message: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"error\":{{\"code\":{},\"message\":{}}}}}",
        id.as_json(),
        code,
        json_string(message)
    )
}

pub(super) fn error_response_null_id(code: i32, message: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":null,\"error\":{{\"code\":{},\"message\":{}}}}}",
        code,
        json_string(message)
    )
}

pub(super) fn invalid_request_response(id: Option<&RequestId>, message: &str) -> String {
    match id {
        Some(id) => error_response(id, -32600, message),
        None => error_response_null_id(-32600, message),
    }
}

pub(super) fn null_response(id: &RequestId) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":null}}",
        id.as_json()
    )
}

pub(super) fn file_progress_notification(uri: &str, processing: bool) -> String {
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

pub(super) fn clear_diagnostics_notification(uri: &str) -> String {
    format!(
        concat!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",",
            "\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}"
        ),
        json_string(uri)
    )
}

pub(super) fn log_warning(message: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"window/logMessage\",\"params\":{{\"type\":2,\"message\":{}}}}}",
        json_string(message)
    )
}
