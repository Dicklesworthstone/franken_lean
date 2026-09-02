use fln_core::diag::DIAGNOSTIC_PROJECTION_SCHEMA;

use crate::{LSP_POSITION_ENCODING, json_string};

use super::json::RequestId;

pub(super) const REQUEST_CANCELLED_CODE: i32 = -32800;
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

pub(super) fn empty_object_response(id: &RequestId) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"id\":{},\"result\":{{}}}}",
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

pub(super) fn diagnostic_callback_failure_notification(uri: &str) -> String {
    format!(
        concat!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"$/lean/diagnosticOutcome\",",
            "\"params\":{{\"schema\":{},\"outcome\":\"internal_fault\",",
            "\"authority\":false,\"invariant\":\"diagnostic-callback-terminal-message\",",
            "\"uri\":{},\"detail\":{{\"text\":",
            "\"document check returned no terminal diagnostic outcome\",",
            "\"truncated\":false}}}}}}"
        ),
        json_string(DIAGNOSTIC_PROJECTION_SCHEMA),
        json_string(uri)
    )
}

pub(super) fn log_warning(message: &str) -> String {
    format!(
        "{{\"jsonrpc\":\"2.0\",\"method\":\"window/logMessage\",\"params\":{{\"type\":2,\"message\":{}}}}}",
        json_string(message)
    )
}

#[cfg(test)]
mod tests {
    use super::super::json::{DecodedField, RequestIdField, parse_envelope};
    use super::*;

    fn assert_valid_envelope(message: &str) {
        let envelope = parse_envelope(message).expect("wire encoder must emit valid JSON");
        assert_eq!(envelope.jsonrpc, DecodedField::Valid("2.0".to_string()));
    }

    #[test]
    fn initialize_advertises_the_actual_full_sync_coordinate_contract() {
        let message = initialize_response(&RequestId::Number("17".to_string()));
        assert_valid_envelope(&message);
        assert!(message.contains("\"id\":17"));
        assert!(message.contains("\"positionEncoding\":\"utf-16\""));
        assert!(message.contains("\"change\":1"));
        assert!(message.contains("\"includeText\":true"));
    }

    #[test]
    fn every_wire_shape_round_trips_through_the_strict_envelope_parser() {
        let number = RequestId::Number("-1.25e+2".to_string());
        let text = RequestId::Text("request-🤖".to_string());
        let messages = [
            error_response(&number, -32601, "unknown \"method\""),
            error_response(&text, REQUEST_CANCELLED_CODE, "request cancelled"),
            error_response_null_id(-32700, "parse error"),
            invalid_request_response(Some(&text), "invalid request"),
            null_response(&text),
            empty_object_response(&number),
            file_progress_notification("file:///tmp/a b.lean", true),
            file_progress_notification("file:///tmp/a b.lean", false),
            clear_diagnostics_notification("file:///tmp/a b.lean"),
            diagnostic_callback_failure_notification("file:///tmp/a b.lean"),
            log_warning("warning with \n and 🤖"),
        ];
        for message in messages {
            assert_valid_envelope(&message);
        }

        let null_number = null_response(&number);
        let response = parse_envelope(&null_number).expect("valid response");
        assert_eq!(response.id, RequestIdField::Valid(number.clone()));
        let empty_number = empty_object_response(&number);
        let response = parse_envelope(&empty_number).expect("valid response");
        assert_eq!(response.id, RequestIdField::Valid(number));
        let null_text = null_response(&text);
        let response = parse_envelope(&null_text).expect("valid response");
        assert_eq!(response.id, RequestIdField::Valid(text));
    }

    #[test]
    fn missing_terminal_diagnostic_is_non_authoritative_and_uri_bound() {
        let message = diagnostic_callback_failure_notification("file:///x y.lean");
        assert_valid_envelope(&message);
        assert!(message.contains("\"outcome\":\"internal_fault\""));
        assert!(message.contains("\"authority\":false"));
        assert!(message.contains("diagnostic-callback-terminal-message"));
        assert!(message.contains("file:///x y.lean"));
    }
}
