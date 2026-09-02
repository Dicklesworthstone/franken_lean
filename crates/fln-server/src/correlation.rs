use std::collections::BTreeMap;
use std::io::Cursor;

use crate::json::{
    DecodedField, EnvelopeError, RawField, RequestId, RequestIdField, VersionField,
    direct_request_id, parse_envelope, response_error, response_error_code, response_result,
};
use crate::server_transcript::{
    ServerFrameRole, ServerTranscriptEvidence, ServerTranscriptStats,
    validate_server_transcript_bytes,
};
use crate::session_transcript::{
    ClientSessionStats, MAX_SESSION_REQUEST_ID_BYTES, MAX_SESSION_REQUEST_IDS,
    validate_client_session_bytes,
};
use crate::transcript::{self, TranscriptRole};

/// Maximum unique request IDs retained on either side of one correlation join.
pub const MAX_CORRELATED_REQUESTS: usize = MAX_SESSION_REQUEST_IDS;
/// Maximum canonical request-ID bytes retained in each side's join index.
pub const MAX_CORRELATION_ID_BYTES: u64 = MAX_SESSION_REQUEST_ID_BYTES as u64;
const REQUEST_CANCELLED_CODE: i64 = -32800;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CorrelationStats {
    pub client: ClientSessionStats,
    pub server: ServerTranscriptStats,
    pub matched_responses: u64,
    pub client_request_id_bytes: u64,
    pub server_response_id_bytes: u64,
    pub cancellation_target_id_bytes: u64,
    pub cancelled_target_request_cancelled_responses: u64,
    pub cancelled_target_result_responses: u64,
    pub cancelled_target_other_error_responses: u64,
}

#[derive(Debug)]
struct IdIndex {
    frames: BTreeMap<String, u64>,
    id_bytes: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ResponseDisposition {
    Result,
    RequestCancelled,
    OtherError,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
struct CancellationResponseStats {
    request_cancelled: u64,
    result: u64,
    other_error: u64,
}

impl CancellationResponseStats {
    fn total(self) -> Option<u64> {
        self.request_cancelled
            .checked_add(self.result)?
            .checked_add(self.other_error)
    }
}

fn insert_unique_id(
    index: &mut IdIndex,
    id: String,
    frame: u64,
    side: &str,
    max_ids: usize,
    max_id_bytes: u64,
) -> Result<(), String> {
    if let Some(first) = index.frames.get(&id) {
        return Err(format!(
            "{side} ID {id} is repeated at frames {first} and {frame}; bidirectional correlation requires unique canonical IDs"
        ));
    }
    if index.frames.len() >= max_ids {
        return Err(format!(
            "{side} index exceeds the {max_ids}-request-ID ceiling at frame {frame}"
        ));
    }
    let id_len = u64::try_from(id.len())
        .map_err(|_| format!("{side} frame {frame} request-ID length does not fit u64"))?;
    let next_id_bytes = index
        .id_bytes
        .checked_add(id_len)
        .ok_or_else(|| format!("{side} request-ID byte accounting overflow at frame {frame}"))?;
    if next_id_bytes > max_id_bytes {
        return Err(format!(
            "{side} canonical request-ID bytes exceed the {max_id_bytes}-byte ceiling at frame {frame}"
        ));
    }
    index.frames.insert(id, frame);
    index.id_bytes = next_id_bytes;
    Ok(())
}

/// The shared parser's deterministic request-ID identity.
///
/// JSON numbers retain their exact source lexeme, strings compare by decoded
/// Unicode value and are re-escaped canonically, and null remains null. This is
/// also the representation the live dispatcher emits in response IDs.
fn client_request_ids_with_limits(
    bytes: &[u8],
    max_ids: usize,
    max_id_bytes: u64,
) -> Result<IdIndex, String> {
    let mut requests = IdIndex {
        frames: BTreeMap::new(),
        id_bytes: 0,
    };
    transcript::visit_reader(
        &mut Cursor::new(bytes),
        transcript::MAX_TRANSCRIPT_FRAMES,
        |frame| {
            if frame.role != TranscriptRole::Request {
                return Ok(());
            }
            let id = frame.id_json.clone().ok_or_else(|| {
                format!(
                    "client frame {} is request-shaped without a retained request-ID key",
                    frame.index
                )
            })?;
            insert_unique_id(
                &mut requests,
                id,
                frame.index,
                "client request",
                max_ids,
                max_id_bytes,
            )
        },
    )?;
    Ok(requests)
}

fn client_request_ids(bytes: &[u8]) -> Result<IdIndex, String> {
    client_request_ids_with_limits(
        bytes,
        MAX_CORRELATED_REQUESTS,
        MAX_CORRELATION_ID_BYTES,
    )
}

fn client_cancellation_targets_with_limits(
    bytes: &[u8],
    max_ids: usize,
    max_id_bytes: u64,
) -> Result<IdIndex, String> {
    let mut targets = IdIndex {
        frames: BTreeMap::new(),
        id_bytes: 0,
    };
    let mut input = Cursor::new(bytes);
    let mut frame = 0u64;
    while let Some(body) = crate::transport::read_message(&mut input)
        .map_err(|error| format!("client cancellation pass transport failure: {error}"))?
    {
        frame = frame
            .checked_add(1)
            .ok_or_else(|| "client cancellation frame count overflow".to_string())?;
        let text = std::str::from_utf8(&body)
            .map_err(|_| format!("client frame {frame} body is not valid UTF-8"))?;
        let envelope = parse_envelope(text).map_err(|error| match error {
            EnvelopeError::MalformedJson => {
                format!("client frame {frame} contains malformed JSON")
            }
            EnvelopeError::NotObject => {
                format!("client frame {frame} is not a JSON-RPC object")
            }
        })?;
        if !matches!(
            &envelope.method,
            DecodedField::Valid(method) if method == "$/cancelRequest"
        ) {
            continue;
        }
        let id = match direct_request_id(envelope.params) {
            RequestIdField::Valid(id @ (RequestId::Number(_) | RequestId::Text(_))) => {
                id.as_json()
            }
            RequestIdField::Valid(RequestId::Null) => {
                return Err(format!(
                    "client frame {frame} cancelRequest target must not be null"
                ));
            }
            RequestIdField::Absent => {
                return Err(format!(
                    "client frame {frame} cancelRequest target is missing"
                ));
            }
            RequestIdField::Invalid => {
                return Err(format!(
                    "client frame {frame} cancelRequest target is malformed or ambiguous"
                ));
            }
        };
        insert_unique_id(
            &mut targets,
            id,
            frame,
            "client cancellation target",
            max_ids,
            max_id_bytes,
        )?;
    }
    Ok(targets)
}

fn client_cancellation_targets(bytes: &[u8]) -> Result<IdIndex, String> {
    client_cancellation_targets_with_limits(
        bytes,
        MAX_CORRELATED_REQUESTS,
        MAX_CORRELATION_ID_BYTES,
    )
}

fn server_response_ids_with_limits(
    evidence: &ServerTranscriptEvidence,
    client: &BTreeMap<String, u64>,
    max_ids: usize,
    max_id_bytes: u64,
) -> Result<IdIndex, String> {
    let mut responses = IdIndex {
        frames: BTreeMap::new(),
        id_bytes: 0,
    };
    for frame in &evidence.frames {
        if !matches!(frame.role, ServerFrameRole::Response(_)) {
            continue;
        }
        let id = frame.id_json.clone().ok_or_else(|| {
            format!(
                "server frame {} is response-shaped without a retained request-ID key",
                frame.index
            )
        })?;
        if !client.contains_key(&id) {
            return Err(format!(
                "server frame {} responds to unknown canonical request ID {id}",
                frame.index
            ));
        }
        insert_unique_id(
            &mut responses,
            id,
            frame.index,
            "server response",
            max_ids,
            max_id_bytes,
        )?;
    }
    Ok(responses)
}

fn server_response_ids(
    evidence: &ServerTranscriptEvidence,
    client: &BTreeMap<String, u64>,
) -> Result<IdIndex, String> {
    server_response_ids_with_limits(
        evidence,
        client,
        MAX_CORRELATED_REQUESTS,
        MAX_CORRELATION_ID_BYTES,
    )
}

fn response_disposition(json: &str, frame: u64) -> Result<ResponseDisposition, String> {
    match (response_result(json), response_error(json)) {
        (RawField::Value(_), RawField::Missing) => Ok(ResponseDisposition::Result),
        (RawField::Missing, RawField::Value(error)) => {
            match response_error_code(RawField::Value(error)) {
                VersionField::Valid(REQUEST_CANCELLED_CODE) => {
                    Ok(ResponseDisposition::RequestCancelled)
                }
                VersionField::Valid(_) => Ok(ResponseDisposition::OtherError),
                VersionField::Missing | VersionField::Invalid => Err(format!(
                    "server frame {frame} lost its validated error code during cancellation classification"
                )),
            }
        }
        _ => Err(format!(
            "server frame {frame} lost its validated result/error shape during cancellation classification"
        )),
    }
}

fn classify_cancelled_target_responses(
    server_bytes: &[u8],
    targets: &IdIndex,
) -> Result<CancellationResponseStats, String> {
    let mut stats = CancellationResponseStats::default();
    let mut input = Cursor::new(server_bytes);
    let mut frame = 0u64;
    while let Some(body) = crate::transport::read_message(&mut input)
        .map_err(|error| format!("server cancellation pass transport failure: {error}"))?
    {
        frame = frame
            .checked_add(1)
            .ok_or_else(|| "server cancellation frame count overflow".to_string())?;
        let text = std::str::from_utf8(&body)
            .map_err(|_| format!("server frame {frame} body is not valid UTF-8"))?;
        let envelope = parse_envelope(text).map_err(|error| match error {
            EnvelopeError::MalformedJson => {
                format!("server frame {frame} contains malformed JSON")
            }
            EnvelopeError::NotObject => {
                format!("server frame {frame} is not a JSON-RPC object")
            }
        })?;
        let id = match (&envelope.method, &envelope.id) {
            (DecodedField::Missing, RequestIdField::Valid(id)) => id.as_json(),
            _ => continue,
        };
        if !targets.frames.contains_key(&id) {
            continue;
        }
        match response_disposition(text, frame)? {
            ResponseDisposition::Result => {
                stats.result = stats
                    .result
                    .checked_add(1)
                    .ok_or_else(|| "cancelled-target result count overflow".to_string())?;
            }
            ResponseDisposition::RequestCancelled => {
                stats.request_cancelled = stats
                    .request_cancelled
                    .checked_add(1)
                    .ok_or_else(|| "RequestCancelled response count overflow".to_string())?;
            }
            ResponseDisposition::OtherError => {
                stats.other_error = stats
                    .other_error
                    .checked_add(1)
                    .ok_or_else(|| "cancelled-target other-error count overflow".to_string())?;
            }
        }
    }
    let classified = stats
        .total()
        .ok_or_else(|| "cancelled-target response classification overflow".to_string())?;
    let expected = u64::try_from(targets.frames.len())
        .map_err(|_| "cancellation-target count does not fit u64".to_string())?;
    if classified != expected {
        return Err(format!(
            "cancellation-response accounting mismatch: {expected} targets, {classified} classified responses"
        ));
    }
    Ok(stats)
}

fn validate_client_index_consistency(
    client: &ClientSessionStats,
    requests: &IdIndex,
    cancellations: &IdIndex,
) -> Result<(), String> {
    let indexed = u64::try_from(requests.frames.len())
        .map_err(|_| "correlation client request-ID count does not fit u64".to_string())?;
    if indexed != client.unique_request_ids {
        return Err(format!(
            "client request-ID count differs across validation passes: session {}, correlation {indexed}",
            client.unique_request_ids
        ));
    }
    if requests.id_bytes != client.request_id_bytes {
        return Err(format!(
            "client request-ID bytes differ across validation passes: session {}, correlation {}",
            client.request_id_bytes, requests.id_bytes
        ));
    }
    let cancellation_count = u64::try_from(cancellations.frames.len())
        .map_err(|_| "correlation cancellation-target count does not fit u64".to_string())?;
    if cancellation_count != client.cancellations {
        return Err(format!(
            "client cancellation count differs across validation passes: session {}, correlation {cancellation_count}",
            client.cancellations
        ));
    }
    for (id, cancel_frame) in &cancellations.frames {
        let Some(request_frame) = requests.frames.get(id) else {
            return Err(format!(
                "cancellation target {id} at frame {cancel_frame} is absent from the client request index"
            ));
        };
        if request_frame >= cancel_frame {
            return Err(format!(
                "cancellation target {id} at frame {cancel_frame} does not refer to an earlier request frame"
            ));
        }
    }
    Ok(())
}

pub fn correlate_transcripts(
    client_bytes: &[u8],
    server_bytes: &[u8],
) -> Result<CorrelationStats, String> {
    let client = validate_client_session_bytes(client_bytes)
        .map_err(|error| format!("client session validation failed: {error}"))?;
    let requests = client_request_ids(client_bytes)?;
    let cancellations = client_cancellation_targets(client_bytes)?;
    validate_client_index_consistency(&client, &requests, &cancellations)?;
    let server = validate_server_transcript_bytes(server_bytes)
        .map_err(|error| format!("server transcript validation failed: {error}"))?;
    let responses = server_response_ids(&server, &requests.frames)?;

    if let Some((id, frame)) = requests
        .frames
        .iter()
        .filter(|(id, _)| !responses.frames.contains_key(*id))
        .min_by_key(|(_, frame)| **frame)
    {
        return Err(format!(
            "client request frame {frame} with canonical ID {id} has no server response"
        ));
    }
    let matched_responses = u64::try_from(responses.frames.len())
        .map_err(|_| "matched response count does not fit u64".to_string())?;
    if matched_responses != server.stats.responses {
        return Err(format!(
            "server response accounting mismatch: joined {matched_responses}, validated {}",
            server.stats.responses
        ));
    }
    if matched_responses != client.lifecycle.transcript.requests {
        return Err(format!(
            "client request accounting mismatch: joined {matched_responses}, validated {}",
            client.lifecycle.transcript.requests
        ));
    }
    let cancellation_responses =
        classify_cancelled_target_responses(server_bytes, &cancellations)?;
    Ok(CorrelationStats {
        client,
        server: server.stats,
        matched_responses,
        client_request_id_bytes: requests.id_bytes,
        server_response_id_bytes: responses.id_bytes,
        cancellation_target_id_bytes: cancellations.id_bytes,
        cancelled_target_request_cancelled_responses: cancellation_responses.request_cancelled,
        cancelled_target_result_responses: cancellation_responses.result,
        cancelled_target_other_error_responses: cancellation_responses.other_error,
    })
}

pub fn render_correlation(stats: CorrelationStats) -> String {
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-client-server-correlation/4\",",
            "\"clientSessionSchema\":\"fln.lsp-client-session/3\",",
            "\"serverTranscriptSchema\":\"fln.lsp-server-transcript/3\",",
            "\"idPolicy\":\"number-lexeme-string-value-v1\",",
            "\"clientFrames\":{},\"serverFrames\":{},",
            "\"clientRequests\":{},\"serverResponses\":{},",
            "\"matchedResponses\":{},\"unmatchedClientRequests\":0,",
            "\"unsolicitedServerResponses\":0,\"duplicateRequestIds\":0,",
            "\"duplicateResponseIds\":0,\"resultResponses\":{},",
            "\"errorResponses\":{},\"serverNotifications\":{},",
            "\"clientWireBytes\":{},\"serverWireBytes\":{},",
            "\"serverMetadataBytes\":{},",
            "\"clientSessionRequestIdBytes\":{},",
            "\"clientRequestIdBytes\":{},\"serverResponseIdBytes\":{},",
            "\"clientUniqueRequestIds\":{},",
            "\"requestIdCountCeiling\":{},\"requestIdByteCeiling\":{},",
            "\"documentsOpened\":{},\"documentsChanged\":{},",
            "\"documentsSaved\":{},\"documentsClosed\":{},",
            "\"diagnosticWaits\":{},\"coveredVersionWaits\":{},",
            "\"futureVersionWaits\":{},\"cancellations\":{},",
            "\"diagnosticWaitCancellationTargets\":{},",
            "\"otherRequestCancellationTargets\":{},",
            "\"cancellationTargetIdBytes\":{},",
            "\"cancelledTargetRequestCancelledResponses\":{},",
            "\"cancelledTargetResultResponses\":{},",
            "\"cancelledTargetOtherErrorResponses\":{},",
            "\"finalOpenDocuments\":{}}}\n"
        ),
        stats.client.lifecycle.transcript.frames,
        stats.server.frames,
        stats.client.lifecycle.transcript.requests,
        stats.server.responses,
        stats.matched_responses,
        stats.server.result_responses,
        stats.server.error_responses,
        stats.server.notifications,
        stats.client.lifecycle.transcript.wire_bytes,
        stats.server.wire_bytes,
        stats.server.metadata_bytes,
        stats.client.request_id_bytes,
        stats.client_request_id_bytes,
        stats.server_response_id_bytes,
        stats.client.unique_request_ids,
        MAX_CORRELATED_REQUESTS,
        MAX_CORRELATION_ID_BYTES,
        stats.client.documents_opened,
        stats.client.documents_changed,
        stats.client.documents_saved,
        stats.client.documents_closed,
        stats.client.diagnostic_waits,
        stats.client.covered_version_waits,
        stats.client.future_version_waits,
        stats.client.cancellations,
        stats.client.diagnostic_wait_cancellation_targets,
        stats.client.other_request_cancellation_targets,
        stats.cancellation_target_id_bytes,
        stats.cancelled_target_request_cancelled_responses,
        stats.cancelled_target_result_responses,
        stats.cancelled_target_other_error_responses,
        stats.client.final_open_documents
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

    fn client() -> Vec<u8> {
        framed(&[
            r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":1.25e2,"method":"textDocument/hover","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ])
    }

    fn server() -> Vec<u8> {
        framed(&[
            r#"{"jsonrpc":"2.0","id":"init","result":{"capabilities":{}}}"#,
            r#"{"jsonrpc":"2.0","id":1.25e2,"result":null}"#,
            r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":3,"message":"bounded"}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
        ])
    }

    #[test]
    fn correlates_unique_canonical_ids_and_renders_zero_unmatched_evidence() {
        let stats = correlate_transcripts(&client(), &server()).unwrap();
        assert_eq!(stats.matched_responses, 3);
        assert_eq!(stats.server.result_responses, 3);
        assert_eq!(stats.server.notifications, 1);
        assert_eq!(stats.client_request_id_bytes, stats.client.request_id_bytes);
        assert_eq!(stats.client_request_id_bytes, stats.server_response_id_bytes);
        assert_eq!(stats.cancellation_target_id_bytes, 0);
        let receipt = render_correlation(stats);
        assert!(receipt.contains("\"schema\":\"fln.lsp-client-server-correlation/4\""));
        assert!(receipt.contains("\"clientSessionSchema\":\"fln.lsp-client-session/3\""));
        assert!(receipt.contains("\"serverTranscriptSchema\":\"fln.lsp-server-transcript/3\""));
        assert!(receipt.contains("\"idPolicy\":\"number-lexeme-string-value-v1\""));
        assert!(receipt.contains("\"matchedResponses\":3"));
        assert!(receipt.contains("\"unmatchedClientRequests\":0"));
        assert!(receipt.contains("\"unsolicitedServerResponses\":0"));
        assert!(receipt.contains("\"clientUniqueRequestIds\":3"));
        assert!(receipt.contains("\"requestIdCountCeiling\":262144"));
        assert!(receipt.contains("\"requestIdByteCeiling\":33554432"));
        assert!(receipt.contains("\"cancelledTargetRequestCancelledResponses\":0"));
        assert!(receipt.contains("\"cancelledTargetResultResponses\":0"));
        assert!(receipt.contains("\"cancelledTargetOtherErrorResponses\":0"));
    }

    #[test]
    fn client_indexes_must_match_session_evidence() {
        let mut client_stats = validate_client_session_bytes(&client()).unwrap();
        let requests = client_request_ids(&client()).unwrap();
        let cancellations = client_cancellation_targets(&client()).unwrap();
        validate_client_index_consistency(&client_stats, &requests, &cancellations).unwrap();

        client_stats.unique_request_ids += 1;
        assert!(
            validate_client_index_consistency(&client_stats, &requests, &cancellations)
                .unwrap_err()
                .contains("count differs across validation passes")
        );
        client_stats.unique_request_ids -= 1;
        client_stats.request_id_bytes += 1;
        assert!(
            validate_client_index_consistency(&client_stats, &requests, &cancellations)
                .unwrap_err()
                .contains("bytes differ across validation passes")
        );
        client_stats.request_id_bytes -= 1;
        client_stats.cancellations += 1;
        assert!(
            validate_client_index_consistency(&client_stats, &requests, &cancellations)
                .unwrap_err()
                .contains("cancellation count differs across validation passes")
        );
    }

    fn cancelled_wait_pair(response: &str) -> (Vec<u8>, Vec<u8>) {
        let client = framed(&[
            r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A","version":1,"text":"a"}}}"#,
            r#"{"jsonrpc":"2.0","id":"wait","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///A","version":2}}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"wait"}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        let server = framed(&[
            r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
            response,
            r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
        ]);
        (client, server)
    }

    #[test]
    fn cancelled_target_responses_are_classified_without_timing_inference() {
        let cases = [
            (
                r#"{"jsonrpc":"2.0","id":"wait","error":{"code":-32800,"message":"request cancelled"}}"#,
                (1, 0, 0),
            ),
            (
                r#"{"jsonrpc":"2.0","id":"wait","result":{}}"#,
                (0, 1, 0),
            ),
            (
                r#"{"jsonrpc":"2.0","id":"wait","error":{"code":-32803,"message":"request failed"}}"#,
                (0, 0, 1),
            ),
        ];
        for (response, expected) in cases {
            let (client, server) = cancelled_wait_pair(response);
            let stats = correlate_transcripts(&client, &server).unwrap();
            assert_eq!(
                (
                    stats.cancelled_target_request_cancelled_responses,
                    stats.cancelled_target_result_responses,
                    stats.cancelled_target_other_error_responses,
                ),
                expected
            );
            assert_eq!(stats.client.cancellations, 1);
            assert_eq!(stats.client.diagnostic_wait_cancellation_targets, 1);
        }
    }

    #[test]
    fn cancellation_target_index_is_independently_bounded() {
        let bytes = framed(&[
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"one"}}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"two"}}"#,
        ]);
        let count_error = client_cancellation_targets_with_limits(&bytes, 1, 100).unwrap_err();
        assert!(count_error.contains("1-request-ID ceiling"));
        assert!(count_error.contains("frame 2"));
        let byte_error = client_cancellation_targets_with_limits(&bytes, 10, 4).unwrap_err();
        assert!(byte_error.contains("4-byte ceiling"));
        assert!(byte_error.contains("frame 1"));
    }

    #[test]
    fn rejects_missing_unsolicited_and_duplicate_responses() {
        let missing = framed(&[
            r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
            r#"{"jsonrpc":"2.0","id":1.25e2,"result":null}"#,
        ]);
        assert!(
            correlate_transcripts(&client(), &missing)
                .unwrap_err()
                .contains("has no server response")
        );

        let unsolicited = framed(&[
            r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
            r#"{"jsonrpc":"2.0","id":1.25e2,"result":null}"#,
            r#"{"jsonrpc":"2.0","id":"unknown","result":null}"#,
        ]);
        assert!(
            correlate_transcripts(&client(), &unsolicited)
                .unwrap_err()
                .contains("unknown canonical request ID")
        );

        let duplicate = framed(&[
            r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
            r#"{"jsonrpc":"2.0","id":1.25e2,"result":null}"#,
            r#"{"jsonrpc":"2.0","id":1.25e2,"error":{"code":-1,"message":"duplicate"}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
        ]);
        assert!(
            correlate_transcripts(&client(), &duplicate)
                .unwrap_err()
                .contains("server response ID 1.25e2 is repeated")
        );
    }

    #[test]
    fn numeric_lexemes_are_not_normalized() {
        let normalized = framed(&[
            r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
            r#"{"jsonrpc":"2.0","id":125,"result":null}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
        ]);
        let error = correlate_transcripts(&client(), &normalized).unwrap_err();
        assert!(error.contains("unknown canonical request ID 125"));
    }

    #[test]
    fn equivalent_string_escapes_share_one_canonical_identity() {
        let client = framed(&[
            r#"{"jsonrpc":"2.0","id":"\u0069nit","method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        let server = framed(&[
            r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
        ]);
        assert!(correlate_transcripts(&client, &server).is_ok());
    }

    #[test]
    fn aliasing_string_spellings_are_duplicate_semantic_ids() {
        let client = framed(&[
            r#"{"jsonrpc":"2.0","id":"\u0069nit","method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"init","method":"textDocument/hover","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        let error = correlate_transcripts(&client, &server()).unwrap_err();
        assert!(error.contains("requires unique canonical IDs"));
    }

    #[test]
    fn repeated_client_ids_are_refused_as_temporally_ambiguous() {
        let client = framed(&[
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":1,"method":"textDocument/hover","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        let error = correlate_transcripts(&client, &server()).unwrap_err();
        assert!(error.contains("requires unique canonical IDs"));
    }

    #[test]
    fn request_index_count_and_byte_limits_fail_before_retention() {
        let bytes = framed(&[
            r#"{"jsonrpc":"2.0","id":"one","method":"first","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"two","method":"second","params":{}}"#,
        ]);
        let count_error = client_request_ids_with_limits(&bytes, 1, 100).unwrap_err();
        assert!(count_error.contains("1-request-ID ceiling"));
        assert!(count_error.contains("frame 2"));

        let byte_error = client_request_ids_with_limits(&bytes, 10, 4).unwrap_err();
        assert!(byte_error.contains("4-byte ceiling"));
        assert!(byte_error.contains("frame 1"));
    }

    #[test]
    fn response_index_has_independent_limits() {
        let evidence = validate_server_transcript_bytes(&server()).unwrap();
        let requests = client_request_ids(&client()).unwrap();
        let error = server_response_ids_with_limits(&evidence, &requests.frames, 2, 100)
            .unwrap_err();
        assert!(error.contains("2-request-ID ceiling"));
    }

    #[test]
    fn error_responses_are_correlated_without_becoming_successes() {
        let server = framed(&[
            r#"{"jsonrpc":"2.0","id":"init","result":{}}"#,
            r#"{"jsonrpc":"2.0","id":1.25e2,"error":{"code":-32601,"message":"method not found"}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
        ]);
        let stats = correlate_transcripts(&client(), &server).unwrap();
        assert_eq!(stats.server.result_responses, 2);
        assert_eq!(stats.server.error_responses, 1);
    }
}
