use std::collections::BTreeMap;
use std::io::Cursor;

use crate::server_transcript::{
    ServerFrameRole, ServerTranscriptEvidence, ServerTranscriptStats,
    validate_server_transcript_bytes,
};
use crate::session_transcript::{ClientSessionStats, validate_client_session_bytes};
use crate::transcript::{self, TranscriptRole};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CorrelationStats {
    pub client: ClientSessionStats,
    pub server: ServerTranscriptStats,
    pub matched_responses: u64,
}

/// The shared parser's deterministic request-ID identity.
///
/// JSON numbers retain their exact source lexeme, strings compare by decoded
/// Unicode value and are re-escaped canonically, and null remains null. This is
/// also the representation the live dispatcher emits in response IDs.
fn client_request_ids(bytes: &[u8]) -> Result<BTreeMap<String, u64>, String> {
    let mut requests = BTreeMap::new();
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
            if let Some(first) = requests.insert(id.clone(), frame.index) {
                return Err(format!(
                    "client request ID {id} is repeated at frames {first} and {}; bidirectional correlation requires unique canonical IDs",
                    frame.index
                ));
            }
            Ok(())
        },
    )?;
    Ok(requests)
}

fn server_response_ids(
    evidence: &ServerTranscriptEvidence,
    client: &BTreeMap<String, u64>,
) -> Result<BTreeMap<String, u64>, String> {
    let mut responses = BTreeMap::new();
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
        if let Some(first) = responses.insert(id.clone(), frame.index) {
            return Err(format!(
                "server response ID {id} is repeated at frames {first} and {}",
                frame.index
            ));
        }
        if !client.contains_key(&id) {
            return Err(format!(
                "server frame {} responds to unknown canonical request ID {id}",
                frame.index
            ));
        }
    }
    Ok(responses)
}

pub fn correlate_transcripts(
    client_bytes: &[u8],
    server_bytes: &[u8],
) -> Result<CorrelationStats, String> {
    let client = validate_client_session_bytes(client_bytes)
        .map_err(|error| format!("client session validation failed: {error}"))?;
    let requests = client_request_ids(client_bytes)?;
    let server = validate_server_transcript_bytes(server_bytes)
        .map_err(|error| format!("server transcript validation failed: {error}"))?;
    let responses = server_response_ids(&server, &requests)?;

    if let Some((id, frame)) = requests
        .iter()
        .filter(|(id, _)| !responses.contains_key(*id))
        .min_by_key(|(_, frame)| **frame)
    {
        return Err(format!(
            "client request frame {frame} with canonical ID {id} has no server response"
        ));
    }
    let matched_responses = u64::try_from(responses.len())
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
    })
}

pub fn render_correlation(stats: CorrelationStats) -> String {
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-client-server-correlation/1\",",
            "\"idPolicy\":\"number-lexeme-string-value-v1\",",
            "\"clientFrames\":{},\"serverFrames\":{},",
            "\"clientRequests\":{},\"serverResponses\":{},",
            "\"matchedResponses\":{},\"unmatchedClientRequests\":0,",
            "\"unsolicitedServerResponses\":0,\"duplicateRequestIds\":0,",
            "\"duplicateResponseIds\":0,\"resultResponses\":{},",
            "\"errorResponses\":{},\"serverNotifications\":{},",
            "\"clientWireBytes\":{},\"serverWireBytes\":{},",
            "\"documentsOpened\":{},\"documentsChanged\":{},",
            "\"documentsSaved\":{},\"documentsClosed\":{},",
            "\"diagnosticWaits\":{},\"cancellations\":{},",
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
        stats.client.documents_opened,
        stats.client.documents_changed,
        stats.client.documents_saved,
        stats.client.documents_closed,
        stats.client.diagnostic_waits,
        stats.client.cancellations,
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
        let receipt = render_correlation(stats);
        assert!(receipt.contains("\"schema\":\"fln.lsp-client-server-correlation/1\""));
        assert!(receipt.contains("\"idPolicy\":\"number-lexeme-string-value-v1\""));
        assert!(receipt.contains("\"matchedResponses\":3"));
        assert!(receipt.contains("\"unmatchedClientRequests\":0"));
        assert!(receipt.contains("\"unsolicitedServerResponses\":0"));
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
