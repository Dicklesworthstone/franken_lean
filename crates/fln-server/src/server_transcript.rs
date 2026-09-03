use std::io::{BufRead, Cursor, Read};

use fln_core::diag::DIAGNOSTIC_PROJECTION_SCHEMA;

use crate::json::{
    BooleanField, DecodedField, EnvelopeError, RawField, RequestIdField, VersionField, direct_uri,
    object_boolean_member, object_integer_member, object_member, object_string_member,
    parse_envelope, response_error, response_error_code, response_error_message, response_result,
    text_document_uri,
};
use crate::transcript::{MAX_TRANSCRIPT_BYTES, MAX_TRANSCRIPT_FRAMES};

/// Variable decoded method/response-ID bytes retained beside the immutable wire.
///
/// Fixed per-frame struct overhead is separately bounded by
/// [`MAX_TRANSCRIPT_FRAMES`]. This ceiling prevents a valid 256 MiB recording
/// from being duplicated wholesale into decoded `String` storage.
pub const MAX_SERVER_TRANSCRIPT_METADATA_BYTES: u64 = 32 * 1024 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ServerResponseKind {
    Result,
    Error,
}

#[cfg(test)]
impl ServerResponseKind {
    const fn name(self) -> &'static str {
        match self {
            Self::Result => "result",
            Self::Error => "error",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ServerFrameRole {
    Response(ServerResponseKind),
    Notification,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerTranscriptFrame {
    pub index: u64,
    pub role: ServerFrameRole,
    pub method: Option<String>,
    /// Deterministic request-ID JSON: number lexemes are preserved, strings are
    /// decoded and canonically re-escaped, and null remains null.
    pub id_json: Option<String>,
    pub body_bytes: u64,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ServerTranscriptStats {
    pub frames: u64,
    pub responses: u64,
    pub result_responses: u64,
    pub error_responses: u64,
    pub notifications: u64,
    pub diagnostic_publications: u64,
    pub diagnostic_outcomes: u64,
    pub file_progress_notifications: u64,
    pub log_messages: u64,
    pub other_notifications: u64,
    pub wire_bytes: u64,
    pub body_bytes: u64,
    /// Decoded method and canonical response-ID string bytes retained in frames.
    pub metadata_bytes: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ServerTranscriptEvidence {
    pub stats: ServerTranscriptStats,
    pub frames: Vec<ServerTranscriptFrame>,
}

fn notification_params_are_supported(params: RawField<'_>) -> bool {
    match params {
        RawField::Missing => true,
        RawField::Value(value) => {
            matches!(value.trim_start().as_bytes().first(), Some(b'{' | b'['))
        }
        RawField::Invalid => false,
    }
}

fn notification_error(frame: u64, method: &str, detail: &str) -> String {
    format!("frame {frame} notification {method:?} {detail}")
}

fn required_nonempty_string(
    params: RawField<'_>,
    key: &str,
    frame: u64,
    method: &str,
) -> Result<String, String> {
    match object_string_member(params, key) {
        DecodedField::Valid(value) if !value.is_empty() => Ok(value),
        DecodedField::Valid(_) => Err(notification_error(
            frame,
            method,
            &format!("requires nonempty string field {key:?}"),
        )),
        DecodedField::Missing => Err(notification_error(
            frame,
            method,
            &format!("requires string field {key:?}"),
        )),
        DecodedField::Invalid => Err(notification_error(
            frame,
            method,
            &format!("has malformed or duplicate string field {key:?}"),
        )),
    }
}

fn required_array(params: RawField<'_>, key: &str, frame: u64, method: &str) -> Result<(), String> {
    match object_member(params, key) {
        RawField::Value(value) if value.trim_start().starts_with('[') => Ok(()),
        RawField::Missing => Err(notification_error(
            frame,
            method,
            &format!("requires array field {key:?}"),
        )),
        RawField::Value(_) => Err(notification_error(
            frame,
            method,
            &format!("field {key:?} must be an array"),
        )),
        RawField::Invalid => Err(notification_error(
            frame,
            method,
            &format!("has malformed or duplicate field {key:?}"),
        )),
    }
}

fn optional_integer_or_null(
    params: RawField<'_>,
    key: &str,
    frame: u64,
    method: &str,
) -> Result<(), String> {
    match object_member(params, key) {
        RawField::Missing => Ok(()),
        RawField::Value(value) if value.trim() == "null" => Ok(()),
        RawField::Value(_) => match object_integer_member(params, key) {
            VersionField::Valid(_) => Ok(()),
            VersionField::Missing | VersionField::Invalid => Err(notification_error(
                frame,
                method,
                &format!("field {key:?} must be an integer or null"),
            )),
        },
        RawField::Invalid => Err(notification_error(
            frame,
            method,
            &format!("has malformed or duplicate field {key:?}"),
        )),
    }
}

fn validate_publish_diagnostics(params: RawField<'_>, frame: u64) -> Result<(), String> {
    let method = "textDocument/publishDiagnostics";
    match direct_uri(params) {
        DecodedField::Valid(uri) if !uri.is_empty() => {}
        DecodedField::Valid(_) => {
            return Err(notification_error(frame, method, "requires a nonempty uri"));
        }
        DecodedField::Missing => {
            return Err(notification_error(frame, method, "requires uri"));
        }
        DecodedField::Invalid => {
            return Err(notification_error(
                frame,
                method,
                "has a malformed or duplicate uri",
            ));
        }
    }
    required_array(params, "diagnostics", frame, method)?;
    optional_integer_or_null(params, "version", frame, method)
}

fn validate_file_progress(params: RawField<'_>, frame: u64) -> Result<(), String> {
    let method = "$/lean/fileProgress";
    match text_document_uri(params) {
        DecodedField::Valid(uri) if !uri.is_empty() => {}
        DecodedField::Valid(_) => {
            return Err(notification_error(
                frame,
                method,
                "requires a nonempty textDocument.uri",
            ));
        }
        DecodedField::Missing => {
            return Err(notification_error(
                frame,
                method,
                "requires textDocument.uri",
            ));
        }
        DecodedField::Invalid => {
            return Err(notification_error(
                frame,
                method,
                "has a malformed or duplicate textDocument.uri",
            ));
        }
    }
    required_array(params, "processing", frame, method)
}

fn validate_log_message(params: RawField<'_>, frame: u64) -> Result<(), String> {
    let method = "window/logMessage";
    match object_integer_member(params, "type") {
        VersionField::Valid(1..=4) => {}
        VersionField::Valid(_) => {
            return Err(notification_error(
                frame,
                method,
                "field \"type\" must be an LSP MessageType integer from 1 through 4",
            ));
        }
        VersionField::Missing => {
            return Err(notification_error(
                frame,
                method,
                "requires integer field \"type\"",
            ));
        }
        VersionField::Invalid => {
            return Err(notification_error(
                frame,
                method,
                "has a malformed or duplicate integer field \"type\"",
            ));
        }
    }
    required_nonempty_string(params, "message", frame, method).map(|_| ())
}

fn validate_diagnostic_outcome(params: RawField<'_>, frame: u64) -> Result<(), String> {
    let method = "$/lean/diagnosticOutcome";
    let schema = required_nonempty_string(params, "schema", frame, method)?;
    if schema != DIAGNOSTIC_PROJECTION_SCHEMA {
        return Err(notification_error(
            frame,
            method,
            "uses an unsupported diagnostic projection schema",
        ));
    }
    let outcome = required_nonempty_string(params, "outcome", frame, method)?;
    let authority = match object_boolean_member(params, "authority") {
        BooleanField::Valid(authority) => authority,
        BooleanField::Missing => {
            return Err(notification_error(
                frame,
                method,
                "requires boolean field \"authority\"",
            ));
        }
        BooleanField::Invalid => {
            return Err(notification_error(
                frame,
                method,
                "has a malformed or duplicate boolean field \"authority\"",
            ));
        }
    };
    let diagnostic_count = object_integer_member(params, "diagnosticCount");
    match (outcome.as_str(), authority, diagnostic_count) {
        ("complete", true, VersionField::Valid(0)) => Ok(()),
        ("inconclusive" | "internal_fault", false, VersionField::Missing) => Ok(()),
        ("complete", _, _) => Err(notification_error(
            frame,
            method,
            "complete outcome requires authority=true and exact integer diagnosticCount=0",
        )),
        ("inconclusive" | "internal_fault", _, _) => Err(notification_error(
            frame,
            method,
            "non-authoritative outcome requires authority=false and no diagnosticCount",
        )),
        _ => Err(notification_error(
            frame,
            method,
            "uses an unsupported outcome class",
        )),
    }
}

fn validate_known_notification(
    method: &str,
    params: RawField<'_>,
    frame: u64,
) -> Result<(), String> {
    match method {
        "textDocument/publishDiagnostics" => validate_publish_diagnostics(params, frame),
        "$/lean/fileProgress" => validate_file_progress(params, frame),
        "window/logMessage" => validate_log_message(params, frame),
        "$/lean/diagnosticOutcome" => validate_diagnostic_outcome(params, frame),
        _ => Ok(()),
    }
}

fn response_kind(json: &str, frame: u64) -> Result<ServerResponseKind, String> {
    let result = response_result(json);
    let error = response_error(json);
    if matches!(result, RawField::Invalid) || matches!(error, RawField::Invalid) {
        return Err(format!(
            "frame {frame} has duplicate or malformed result/error fields"
        ));
    }
    match (result, error) {
        (RawField::Value(_), RawField::Missing) => Ok(ServerResponseKind::Result),
        (RawField::Missing, RawField::Value(error)) => {
            match response_error_code(RawField::Value(error)) {
                VersionField::Valid(code) if i32::try_from(code).is_ok() => {}
                VersionField::Valid(_) => {
                    return Err(format!(
                        "frame {frame} error.code is outside the signed 32-bit JSON-RPC range"
                    ));
                }
                VersionField::Missing => {
                    return Err(format!("frame {frame} error.code is required"));
                }
                VersionField::Invalid => {
                    return Err(format!(
                        "frame {frame} error.code must be one unambiguous integer"
                    ));
                }
            }
            match response_error_message(RawField::Value(error)) {
                DecodedField::Valid(_) => Ok(ServerResponseKind::Error),
                DecodedField::Missing => Err(format!("frame {frame} error.message is required")),
                DecodedField::Invalid => Err(format!(
                    "frame {frame} error.message must be one unambiguous string"
                )),
            }
        }
        (RawField::Missing, RawField::Missing) => Err(format!(
            "frame {frame} response requires exactly one result or error field"
        )),
        (RawField::Value(_), RawField::Value(_)) => Err(format!(
            "frame {frame} response must not contain both result and error"
        )),
        (RawField::Invalid, _) | (_, RawField::Invalid) => unreachable!(),
    }
}

pub fn validate_server_frame(body: &[u8], frame: u64) -> Result<ServerTranscriptFrame, String> {
    let json =
        std::str::from_utf8(body).map_err(|_| format!("frame {frame} body is not valid UTF-8"))?;
    let envelope = parse_envelope(json).map_err(|error| match error {
        EnvelopeError::MalformedJson => format!("frame {frame} contains malformed JSON"),
        EnvelopeError::NotObject => format!("frame {frame} is not a JSON-RPC object"),
    })?;
    match &envelope.jsonrpc {
        DecodedField::Valid(version) if version == "2.0" => {}
        DecodedField::Missing => return Err(format!("frame {frame} is missing jsonrpc=2.0")),
        DecodedField::Valid(version) => {
            return Err(format!(
                "frame {frame} has unsupported JSON-RPC version {version:?}"
            ));
        }
        DecodedField::Invalid => {
            return Err(format!("frame {frame} has a non-string jsonrpc field"));
        }
    }

    let body_bytes = u64::try_from(body.len())
        .map_err(|_| format!("frame {frame} body length does not fit u64"))?;
    match (&envelope.method, &envelope.id) {
        (DecodedField::Valid(method), RequestIdField::Absent) => {
            if method.is_empty() {
                return Err(format!(
                    "frame {frame} notification method must not be empty"
                ));
            }
            if !matches!(response_result(json), RawField::Missing)
                || !matches!(response_error(json), RawField::Missing)
            {
                return Err(format!(
                    "frame {frame} notification must not contain result or error"
                ));
            }
            if !notification_params_are_supported(envelope.params) {
                return Err(format!(
                    "frame {frame} notification params must be missing, an object, or an array"
                ));
            }
            validate_known_notification(method, envelope.params, frame)?;
            Ok(ServerTranscriptFrame {
                index: frame,
                role: ServerFrameRole::Notification,
                method: Some(method.clone()),
                id_json: None,
                body_bytes,
            })
        }
        (DecodedField::Missing, RequestIdField::Valid(id)) => {
            if !matches!(envelope.params, RawField::Missing) {
                return Err(format!("frame {frame} response must not contain params"));
            }
            let kind = response_kind(json, frame)?;
            Ok(ServerTranscriptFrame {
                index: frame,
                role: ServerFrameRole::Response(kind),
                method: None,
                id_json: Some(id.as_json()),
                body_bytes,
            })
        }
        (DecodedField::Valid(method), RequestIdField::Valid(_)) => Err(format!(
            "frame {frame} is a server-initiated request for {method:?}; the bounded correlation profile currently permits only server notifications and responses"
        )),
        (DecodedField::Missing, RequestIdField::Absent) => Err(format!(
            "frame {frame} is neither a server notification nor a response"
        )),
        (DecodedField::Invalid, _) => Err(format!(
            "frame {frame} has a non-string or ambiguous method"
        )),
        (_, RequestIdField::Invalid) => Err(format!(
            "frame {frame} has an invalid or ambiguous response id"
        )),
    }
}

fn frame_metadata_bytes(frame: &ServerTranscriptFrame) -> Result<u64, String> {
    let method_bytes = frame.method.as_ref().map_or(Ok(0), |method| {
        u64::try_from(method.len())
            .map_err(|_| format!("frame {} method length does not fit u64", frame.index))
    })?;
    let id_bytes = frame.id_json.as_ref().map_or(Ok(0), |id| {
        u64::try_from(id.len())
            .map_err(|_| format!("frame {} response-ID length does not fit u64", frame.index))
    })?;
    method_bytes
        .checked_add(id_bytes)
        .ok_or_else(|| format!("frame {} metadata-byte accounting overflow", frame.index))
}

fn validate_server_transcript_with_limits(
    bytes: &[u8],
    max_frames: u64,
    max_metadata_bytes: u64,
) -> Result<ServerTranscriptEvidence, String> {
    if u64::try_from(bytes.len()).unwrap_or(u64::MAX) > MAX_TRANSCRIPT_BYTES {
        return Err(format!(
            "server transcript exceeds the {MAX_TRANSCRIPT_BYTES}-byte aggregate ceiling"
        ));
    }
    let mut input = Cursor::new(bytes);
    let mut stats = ServerTranscriptStats::default();
    let mut frames = Vec::new();
    loop {
        let index = stats
            .frames
            .checked_add(1)
            .ok_or_else(|| "server transcript frame count overflow".to_string())?;
        let Some(body) = crate::transport::read_message(&mut input)
            .map_err(|error| format!("frame {index} transport failure: {error}"))?
        else {
            break;
        };
        if index > max_frames {
            return Err(format!(
                "server transcript exceeds the {max_frames}-frame ceiling"
            ));
        }
        let frame = validate_server_frame(&body, index)?;
        let next_metadata_bytes = stats
            .metadata_bytes
            .checked_add(frame_metadata_bytes(&frame)?)
            .ok_or_else(|| "server transcript metadata-byte accounting overflow".to_string())?;
        if next_metadata_bytes > max_metadata_bytes {
            return Err(format!(
                "server transcript decoded metadata exceeds the {max_metadata_bytes}-byte ceiling while reading frame {index}"
            ));
        }
        stats.frames = index;
        stats.body_bytes = stats
            .body_bytes
            .checked_add(frame.body_bytes)
            .ok_or_else(|| "server transcript body-byte accounting overflow".to_string())?;
        stats.metadata_bytes = next_metadata_bytes;
        match frame.role {
            ServerFrameRole::Notification => {
                stats.notifications = stats
                    .notifications
                    .checked_add(1)
                    .ok_or_else(|| "server notification count overflow".to_string())?;
                match frame.method.as_deref() {
                    Some("textDocument/publishDiagnostics") => {
                        stats.diagnostic_publications = stats
                            .diagnostic_publications
                            .checked_add(1)
                            .ok_or_else(|| "diagnostic-publication count overflow".to_string())?;
                    }
                    Some("$/lean/diagnosticOutcome") => {
                        stats.diagnostic_outcomes = stats
                            .diagnostic_outcomes
                            .checked_add(1)
                            .ok_or_else(|| "diagnostic-outcome count overflow".to_string())?;
                    }
                    Some("$/lean/fileProgress") => {
                        stats.file_progress_notifications = stats
                            .file_progress_notifications
                            .checked_add(1)
                            .ok_or_else(|| "file-progress count overflow".to_string())?;
                    }
                    Some("window/logMessage") => {
                        stats.log_messages = stats
                            .log_messages
                            .checked_add(1)
                            .ok_or_else(|| "log-message count overflow".to_string())?;
                    }
                    Some(_) => {
                        stats.other_notifications = stats
                            .other_notifications
                            .checked_add(1)
                            .ok_or_else(|| "other-notification count overflow".to_string())?;
                    }
                    None => {
                        return Err(format!(
                            "frame {index} notification lost its decoded method before accounting"
                        ));
                    }
                }
            }
            ServerFrameRole::Response(kind) => {
                stats.responses = stats
                    .responses
                    .checked_add(1)
                    .ok_or_else(|| "server response count overflow".to_string())?;
                match kind {
                    ServerResponseKind::Result => {
                        stats.result_responses = stats
                            .result_responses
                            .checked_add(1)
                            .ok_or_else(|| "server result-response count overflow".to_string())?;
                    }
                    ServerResponseKind::Error => {
                        stats.error_responses = stats
                            .error_responses
                            .checked_add(1)
                            .ok_or_else(|| "server error-response count overflow".to_string())?;
                    }
                }
            }
        }
        frames.push(frame);
    }
    stats.wire_bytes = input.position();
    if stats.wire_bytes != u64::try_from(bytes.len()).unwrap_or(u64::MAX) {
        return Err("server transcript wire-byte accounting mismatch".to_string());
    }
    Ok(ServerTranscriptEvidence { stats, frames })
}

pub fn validate_server_transcript_bytes(bytes: &[u8]) -> Result<ServerTranscriptEvidence, String> {
    validate_server_transcript_with_limits(
        bytes,
        MAX_TRANSCRIPT_FRAMES,
        MAX_SERVER_TRANSCRIPT_METADATA_BYTES,
    )
}

pub fn validate_server_transcript_reader(
    input: &mut dyn BufRead,
) -> Result<ServerTranscriptEvidence, String> {
    let mut bytes = Vec::new();
    input
        .take(MAX_TRANSCRIPT_BYTES.saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|error| format!("could not read server transcript: {error}"))?;
    validate_server_transcript_bytes(&bytes)
}

pub fn render_server_transcript_validation(stats: ServerTranscriptStats) -> String {
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-server-transcript/3\",",
            "\"frames\":{},\"responses\":{},\"resultResponses\":{},",
            "\"errorResponses\":{},\"notifications\":{},",
            "\"diagnosticPublications\":{},\"diagnosticOutcomes\":{},",
            "\"fileProgressNotifications\":{},\"logMessages\":{},",
            "\"otherNotifications\":{},\"wireBytes\":{},\"bodyBytes\":{},",
            "\"metadataBytes\":{},\"frameCeiling\":{},",
            "\"metadataByteCeiling\":{}}}\n"
        ),
        stats.frames,
        stats.responses,
        stats.result_responses,
        stats.error_responses,
        stats.notifications,
        stats.diagnostic_publications,
        stats.diagnostic_outcomes,
        stats.file_progress_notifications,
        stats.log_messages,
        stats.other_notifications,
        stats.wire_bytes,
        stats.body_bytes,
        stats.metadata_bytes,
        MAX_TRANSCRIPT_FRAMES,
        MAX_SERVER_TRANSCRIPT_METADATA_BYTES
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn frame(body: &str) -> Vec<u8> {
        let mut framed = Vec::new();
        crate::transport::write_message(&mut framed, body.as_bytes()).unwrap();
        framed
    }

    fn framed(bodies: &[&str]) -> Vec<u8> {
        let mut bytes = Vec::new();
        for body in bodies {
            bytes.extend(frame(body));
        }
        bytes
    }

    #[test]
    fn validates_notifications_results_errors_and_canonical_ids() {
        let bytes = framed(&[
            r#"{"jsonrpc":"2.0","id":1.25e2,"result":{"capabilities":{}}}"#,
            r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":3,"message":"ok"}}"#,
            r#"{"jsonrpc":"2.0","id":"wait","error":{"code":-32800,"message":"request cancelled"}}"#,
        ]);
        let evidence = validate_server_transcript_bytes(&bytes).unwrap();
        assert_eq!(evidence.stats.frames, 3);
        assert_eq!(evidence.stats.responses, 2);
        assert_eq!(evidence.stats.result_responses, 1);
        assert_eq!(evidence.stats.error_responses, 1);
        assert_eq!(evidence.stats.notifications, 1);
        assert_eq!(evidence.stats.log_messages, 1);
        assert_eq!(evidence.frames[0].id_json.as_deref(), Some("1.25e2"));
        assert_eq!(evidence.frames[2].id_json.as_deref(), Some("\"wait\""));
        assert_eq!(
            evidence.stats.wire_bytes,
            u64::try_from(bytes.len()).unwrap()
        );
        assert_eq!(
            evidence.stats.metadata_bytes,
            u64::try_from("1.25e2".len() + "window/logMessage".len() + "\"wait\"".len()).unwrap()
        );
        let receipt = render_server_transcript_validation(evidence.stats);
        assert!(receipt.contains("\"schema\":\"fln.lsp-server-transcript/3\""));
        assert!(receipt.contains("\"errorResponses\":1"));
        assert!(receipt.contains("\"logMessages\":1"));
        assert!(receipt.contains("\"metadataBytes\":"));
    }

    #[test]
    fn validates_current_lantern_notification_schemas() {
        let bytes = framed(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///A.lean","version":null,"diagnostics":[]}}"#,
            r#"{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"textDocument":{"uri":"file:///A.lean"},"processing":[]}}"#,
            r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":2,"message":"bounded warning"}}"#,
            r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":0}}"#,
            r#"{"jsonrpc":"2.0","method":"workspace/unknown","params":{"future":true}}"#,
        ]);
        let evidence = validate_server_transcript_bytes(&bytes).unwrap();
        assert_eq!(evidence.stats.diagnostic_publications, 1);
        assert_eq!(evidence.stats.file_progress_notifications, 1);
        assert_eq!(evidence.stats.log_messages, 1);
        assert_eq!(evidence.stats.diagnostic_outcomes, 1);
        assert_eq!(evidence.stats.other_notifications, 1);
    }

    #[test]
    fn rejects_malformed_known_notification_payloads() {
        let cases = [
            (
                r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"","diagnostics":[]}}"#,
                "nonempty uri",
            ),
            (
                r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///A","diagnostics":{}}}"#,
                "must be an array",
            ),
            (
                r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///A","version":1.5,"diagnostics":[]}}"#,
                "integer or null",
            ),
            (
                r#"{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"textDocument":{"uri":"file:///A"},"processing":{}}}"#,
                "must be an array",
            ),
            (
                r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":5,"message":"bad"}}"#,
                "from 1 through 4",
            ),
            (
                r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":2,"message":""}}"#,
                "nonempty string",
            ),
            (
                r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true}}"#,
                "diagnosticCount=0",
            ),
            (
                r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"internal_fault","authority":true}}"#,
                "authority=false",
            ),
        ];
        for (body, expected) in cases {
            let error = validate_server_transcript_bytes(&frame(body)).unwrap_err();
            assert!(error.contains(expected), "expected {expected:?}: {error}");
        }
    }

    #[test]
    fn rejects_ambiguous_or_malformed_responses() {
        for (body, expected) in [
            (
                r#"{"jsonrpc":"2.0","id":1,"result":null,"error":{"code":-1,"message":"bad"}}"#,
                "both result and error",
            ),
            (r#"{"jsonrpc":"2.0","id":1}"#, "exactly one result or error"),
            (
                r#"{"jsonrpc":"2.0","id":1,"error":{"message":"bad"}}"#,
                "error.code is required",
            ),
            (
                r#"{"jsonrpc":"2.0","id":1,"error":{"code":-1,"message":3}}"#,
                "error.message",
            ),
            (
                r#"{"jsonrpc":"2.0","id":1,"method":"workspace/configuration","params":{}}"#,
                "server-initiated request",
            ),
        ] {
            let error = validate_server_transcript_bytes(&frame(body)).unwrap_err();
            assert!(error.contains(expected), "expected {expected:?}: {error}");
        }
    }

    #[test]
    fn rejects_response_params_and_notification_result_fields() {
        for body in [
            r#"{"jsonrpc":"2.0","id":1,"result":null,"params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{},"result":null}"#,
        ] {
            assert!(validate_server_transcript_bytes(&frame(body)).is_err());
        }
    }

    #[test]
    fn error_codes_are_bounded_to_the_json_rpc_integer_surface() {
        let error = validate_server_transcript_bytes(&frame(
            r#"{"jsonrpc":"2.0","id":1,"error":{"code":2147483648,"message":"bad"}}"#,
        ))
        .unwrap_err();
        assert!(error.contains("signed 32-bit"));
    }

    #[test]
    fn metadata_ceiling_refuses_before_retaining_the_failing_frame() {
        let bytes = framed(&[
            r#"{"jsonrpc":"2.0","method":"ok","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"too-long","params":{}}"#,
        ]);
        let error = validate_server_transcript_with_limits(&bytes, 10, 3).unwrap_err();
        assert!(error.contains("3-byte ceiling"));
        assert!(error.contains("frame 2"));
    }

    #[test]
    fn frame_ceiling_is_independent_of_wire_bytes() {
        let bytes = framed(&[
            r#"{"jsonrpc":"2.0","method":"one","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"two","params":{}}"#,
        ]);
        let error =
            validate_server_transcript_with_limits(&bytes, 1, MAX_SERVER_TRANSCRIPT_METADATA_BYTES)
                .unwrap_err();
        assert!(error.contains("1-frame ceiling"));
    }

    #[test]
    fn response_kind_names_are_stable() {
        assert_eq!(ServerResponseKind::Result.name(), "result");
        assert_eq!(ServerResponseKind::Error.name(), "error");
    }
}
