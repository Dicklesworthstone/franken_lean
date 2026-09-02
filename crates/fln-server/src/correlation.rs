use std::collections::BTreeMap;
use std::io::Cursor;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CorrelationStats {
    pub client: ClientSessionStats,
    pub server: ServerTranscriptStats,
    pub matched_responses: u64,
    pub client_request_id_bytes: u64,
    pub server_response_id_bytes: u64,
}

#[derive(Debug)]
struct IdIndex {
    frames: BTreeMap<String, u64>,
    id_bytes: u64,
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

fn validate_client_index_consistency(
    client: &ClientSessionStats,
    requests: &IdIndex,
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
    Ok(())
}

pub fn correlate_transcripts(
    client_bytes: &[u8],
    server_bytes: &[u8],
) -> Result<CorrelationStats, String> {
    let client = validate_client_session_bytes(client_bytes)
        .map_err(|error| format!("client session validation failed: {error}"))?;
    let requests = client_request_ids(client_bytes)?;
    validate_client_index_consistency(&client, &requests)?;
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
    Ok(CorrelationStats {
        client,
        server: server.stats,
        matched_responses,
        client_request_id_bytes: requests.id_bytes,
        server_response_id_bytes: responses.id_bytes,
    })
}

pub fn render_correlation(stats: CorrelationStats) -> String {
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-client-server-correlation/3\",",
            "\"clientSessionSchema\":\"fln.lsp-client-session/3\",",
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
        let receipt = render_correlation(stats);
        assert!(receipt.contains("\"schema\":\"fln.lsp-client-server-correlation/3\""));
        assert!(receipt.contains("\"clientSessionSchema\":\"fln.lsp-client-session/3\""));
        assert!(receipt.contains("\"idPolicy\":\"number-lexeme-string-value-v1\""));
        assert!(receipt.contains("\"matchedResponses\":3"));
        assert!(receipt.contains("\"unmatchedClientRequests\":0"));
        assert!(receipt.contains("\"unsolicitedServerResponses\":0"));
        assert!(receipt.contains("\"clientUniqueRequestIds\":3"));
        assert!(receipt.contains("\"requestIdCountCeiling\":262144"));
        assert!(receipt.contains("\"requestIdByteCeiling\":33554432"));
    }

    #[test]
    fn client_index_must_match_session_evidence() {
        let mut client_stats = validate_client_session_bytes(&client()).unwrap();
        let index = client_request_ids(&client()).unwrap();
        validate_client_index_consistency(&client_stats, &index).unwrap();

        client_stats.unique_request_ids += 1;
        assert!(
            validate_client_index_consistency(&client_stats, &index)
                .unwrap_err()
                .contains("count differs across validation passes")
        );
        client_stats.unique_request_ids -= 1;
        client_stats.request_id_bytes += 1;
        assert!(
            validate_client_index_consistency(&client_stats, &index)
                .unwrap_err()
                .contains("bytes differ across validation passes")
        );
    }

    #[test]
    fn joined_receipt_carries_wait_and_cancellation_classes() {
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
            r#"{"jsonrpc":"2.0","id":"wait","error":{"code":-32800,"message":"request cancelled"}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
        ]);
        let receipt = render_correlation(correlate_transcripts(&client, &server).unwrap());
        assert!(receipt.contains("\"futureVersionWaits\":1"));
        assert!(receipt.contains("\"cancellations\":1"));
        assert!(receipt.contains("\"diagnosticWaitCancellationTargets\":1"));
        assert!(receipt.contains("\"otherRequestCancellationTargets\":0"));
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
