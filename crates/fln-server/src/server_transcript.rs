use std::io::{BufRead, Cursor, Read};

use crate::json::{
    DecodedField, EnvelopeError, RawField, RequestIdField, VersionField, parse_envelope,
    response_error, response_error_code, response_error_message, response_result,
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
        RawField::Value(value) => matches!(value.trim_start().as_bytes().first(), Some(b'{' | b'[')),
        RawField::Invalid => false,
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
    let json = std::str::from_utf8(body)
        .map_err(|_| format!("frame {frame} body is not valid UTF-8"))?;
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
                return Err(format!("frame {frame} notification method must not be empty"));
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
        (DecodedField::Invalid, _) => {
            Err(format!("frame {frame} has a non-string or ambiguous method"))
        }
        (_, RequestIdField::Invalid) => {
            Err(format!("frame {frame} has an invalid or ambiguous response id"))
        }
    }
}

fn frame_metadata_bytes(frame: &ServerTranscriptFrame) -> Result<u64, String> {
    frame
        .method
        .as_ref()
        .map_or(Ok(0), |method| {
            u64::try_from(method.len())
                .map_err(|_| format!("frame {} method length does not fit u64", frame.index))
        })?
        .checked_add(frame.id_json.as_ref().map_or(0, |id| {
            u64::try_from(id.len()).unwrap_or(u64::MAX)
        }))
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

pub fn validate_server_transcript_bytes(
    bytes: &[u8],
) -> Result<ServerTranscriptEvidence, String> {
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
            "{{\"schema\":\"fln.lsp-server-transcript/2\",",
            "\"frames\":{},\"responses\":{},\"resultResponses\":{},",
            "\"errorResponses\":{},\"notifications\":{},",
            "\"wireBytes\":{},\"bodyBytes\":{},\"metadataBytes\":{},",
            "\"frameCeiling\":{},\"metadataByteCeiling\":{}}}\n"
        ),
        stats.frames,
        stats.responses,
        stats.result_responses,
        stats.error_responses,
        stats.notifications,
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
        assert_eq!(evidence.frames[0].id_json.as_deref(), Some("1.25e2"));
        assert_eq!(evidence.frames[2].id_json.as_deref(), Some("\"wait\""));
        assert_eq!(evidence.stats.wire_bytes, u64::try_from(bytes.len()).unwrap());
        assert_eq!(
            evidence.stats.metadata_bytes,
            u64::try_from("1.25e2".len() + "window/logMessage".len() + "\"wait\"".len())
                .unwrap()
        );
        let receipt = render_server_transcript_validation(evidence.stats);
        assert!(receipt.contains("\"schema\":\"fln.lsp-server-transcript/2\""));
        assert!(receipt.contains("\"errorResponses\":1"));
        assert!(receipt.contains("\"metadataBytes\":"));
    }

    #[test]
    fn rejects_ambiguous_or_malformed_responses() {
        for (body, expected) in [
            (
                r#"{"jsonrpc":"2.0","id":1,"result":null,"error":{"code":-1,"message":"bad"}}"#,
                "both result and error",
            ),
            (
                r#"{"jsonrpc":"2.0","id":1}"#,
                "exactly one result or error",
            ),
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
        let error = validate_server_transcript_with_limits(
            &bytes,
            1,
            MAX_SERVER_TRANSCRIPT_METADATA_BYTES,
        )
        .unwrap_err();
        assert!(error.contains("1-frame ceiling"));
    }

    #[test]
    fn response_kind_names_are_stable() {
        assert_eq!(ServerResponseKind::Result.name(), "result");
        assert_eq!(ServerResponseKind::Error.name(), "error");
    }
}
