use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Cursor, Read};

use crate::json::{
    DecodedField, EnvelopeError, RawField, RequestId, RequestIdField, VersionField,
    content_changes_text, direct_request_id, direct_uri, direct_version, parse_envelope, save_text,
    text_document_text, text_document_uri, text_document_version,
};
use crate::transcript::{self, ClientLifecycleStats};

pub const MAX_SESSION_DOCUMENTS: usize = 1024;
pub const MAX_SESSION_URI_BYTES: usize = 4 * 1024 * 1024;
pub const MAX_SESSION_REQUEST_IDS: usize = 262_144;
pub const MAX_SESSION_REQUEST_ID_BYTES: usize = 32 * 1024 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClientSessionStats {
    pub lifecycle: ClientLifecycleStats,
    pub documents_opened: u64,
    pub documents_changed: u64,
    pub documents_saved: u64,
    pub documents_closed: u64,
    pub diagnostic_waits: u64,
    pub covered_version_waits: u64,
    pub future_version_waits: u64,
    pub cancellations: u64,
    pub diagnostic_wait_cancellation_targets: u64,
    pub other_request_cancellation_targets: u64,
    pub unique_request_ids: u64,
    pub request_id_bytes: u64,
    pub peak_open_documents: u64,
    pub final_open_documents: u64,
    pub peak_open_uri_bytes: u64,
    pub final_open_uri_bytes: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DocumentEvent {
    Open { uri: String, version: i64 },
    Change { uri: String, version: i64 },
    Save { uri: String },
    Close { uri: String },
    Wait { uri: String, version: i64 },
    Cancel { id: String },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RequestKind {
    DiagnosticWait,
    Other,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RequestRecord {
    frame: u64,
    kind: RequestKind,
}

fn decoded_uri(field: DecodedField, label: &str) -> Result<String, String> {
    match field {
        DecodedField::Valid(uri) if !uri.is_empty() => Ok(uri),
        DecodedField::Valid(_) => Err(format!("{label} must not be empty")),
        DecodedField::Missing => Err(format!("{label} is required")),
        DecodedField::Invalid => Err(format!("{label} is malformed or ambiguous")),
    }
}

fn decoded_version(field: VersionField, label: &str) -> Result<i64, String> {
    match field {
        VersionField::Valid(version) => Ok(version),
        VersionField::Missing => Err(format!("{label} is required")),
        VersionField::Invalid => Err(format!("{label} must be one unambiguous integer")),
    }
}

fn document_event(method: &str, params: RawField<'_>) -> Result<Option<DocumentEvent>, String> {
    match method {
        "textDocument/didOpen" => {
            let uri = decoded_uri(text_document_uri(params), "didOpen textDocument.uri")?;
            let version = decoded_version(
                text_document_version(params),
                "didOpen textDocument.version",
            )?;
            match text_document_text(params) {
                DecodedField::Valid(_) => {}
                DecodedField::Missing => {
                    return Err("didOpen requires complete textDocument.text".to_string());
                }
                DecodedField::Invalid => {
                    return Err(
                        "didOpen textDocument.text is malformed or ambiguous".to_string(),
                    );
                }
            }
            Ok(Some(DocumentEvent::Open { uri, version }))
        }
        "textDocument/didChange" => {
            let uri = decoded_uri(text_document_uri(params), "didChange textDocument.uri")?;
            let version = decoded_version(
                text_document_version(params),
                "didChange textDocument.version",
            )?;
            match content_changes_text(params) {
                DecodedField::Valid(_) => {}
                DecodedField::Missing => {
                    return Err(
                        "didChange requires exactly one complete Full-sync content change"
                            .to_string(),
                    );
                }
                DecodedField::Invalid => {
                    return Err(
                        "didChange requires one unambiguous unranged Full-sync text change"
                            .to_string(),
                    );
                }
            }
            Ok(Some(DocumentEvent::Change { uri, version }))
        }
        "textDocument/didSave" => {
            let uri = decoded_uri(text_document_uri(params), "didSave textDocument.uri")?;
            if matches!(save_text(params), DecodedField::Invalid) {
                return Err("didSave text is malformed or ambiguous".to_string());
            }
            Ok(Some(DocumentEvent::Save { uri }))
        }
        "textDocument/didClose" => {
            let uri = decoded_uri(text_document_uri(params), "didClose textDocument.uri")?;
            Ok(Some(DocumentEvent::Close { uri }))
        }
        "textDocument/waitForDiagnostics" => {
            let uri = decoded_uri(direct_uri(params), "waitForDiagnostics uri")?;
            let version = decoded_version(direct_version(params), "waitForDiagnostics version")?;
            if version < 0 {
                return Err(
                    "waitForDiagnostics version must be a nonnegative integer".to_string(),
                );
            }
            Ok(Some(DocumentEvent::Wait { uri, version }))
        }
        "$/cancelRequest" => match direct_request_id(params) {
            RequestIdField::Valid(id @ (RequestId::Number(_) | RequestId::Text(_))) => {
                Ok(Some(DocumentEvent::Cancel { id: id.as_json() }))
            }
            RequestIdField::Valid(RequestId::Null) => {
                Err("$/cancelRequest id must not be null".to_string())
            }
            RequestIdField::Absent => Err("$/cancelRequest id is required".to_string()),
            RequestIdField::Invalid => {
                Err("$/cancelRequest id is malformed or ambiguous".to_string())
            }
        },
        _ => Ok(None),
    }
}

#[derive(Debug)]
struct ClientSessionValidator {
    documents: BTreeMap<String, i64>,
    requests: BTreeMap<String, RequestRecord>,
    cancelled_requests: BTreeMap<String, u64>,
    open_uri_bytes: usize,
    request_id_bytes: usize,
    max_documents: usize,
    max_uri_bytes: usize,
    max_request_ids: usize,
    max_request_id_bytes: usize,
    documents_opened: u64,
    documents_changed: u64,
    documents_saved: u64,
    documents_closed: u64,
    diagnostic_waits: u64,
    covered_version_waits: u64,
    future_version_waits: u64,
    cancellations: u64,
    diagnostic_wait_cancellation_targets: u64,
    other_request_cancellation_targets: u64,
    peak_open_documents: usize,
    peak_open_uri_bytes: usize,
}

impl ClientSessionValidator {
    fn new() -> Self {
        Self::with_all_limits(
            MAX_SESSION_DOCUMENTS,
            MAX_SESSION_URI_BYTES,
            MAX_SESSION_REQUEST_IDS,
            MAX_SESSION_REQUEST_ID_BYTES,
        )
    }

    fn with_limits(max_documents: usize, max_uri_bytes: usize) -> Self {
        Self::with_all_limits(
            max_documents,
            max_uri_bytes,
            MAX_SESSION_REQUEST_IDS,
            MAX_SESSION_REQUEST_ID_BYTES,
        )
    }

    fn with_all_limits(
        max_documents: usize,
        max_uri_bytes: usize,
        max_request_ids: usize,
        max_request_id_bytes: usize,
    ) -> Self {
        Self {
            documents: BTreeMap::new(),
            requests: BTreeMap::new(),
            cancelled_requests: BTreeMap::new(),
            open_uri_bytes: 0,
            request_id_bytes: 0,
            max_documents,
            max_uri_bytes,
            max_request_ids,
            max_request_id_bytes,
            documents_opened: 0,
            documents_changed: 0,
            documents_saved: 0,
            documents_closed: 0,
            diagnostic_waits: 0,
            covered_version_waits: 0,
            future_version_waits: 0,
            cancellations: 0,
            diagnostic_wait_cancellation_targets: 0,
            other_request_cancellation_targets: 0,
            peak_open_documents: 0,
            peak_open_uri_bytes: 0,
        }
    }

    fn bump(counter: &mut u64, label: &str) -> Result<(), String> {
        *counter = counter
            .checked_add(1)
            .ok_or_else(|| format!("{label} counter overflow"))?;
        Ok(())
    }

    fn observe_request_id(
        &mut self,
        frame: u64,
        method: &str,
        id: &RequestIdField,
    ) -> Result<(), String> {
        let id = match id {
            RequestIdField::Absent => return Ok(()),
            RequestIdField::Invalid => {
                return Err(format!(
                    "frame {frame} method {method:?} has an invalid or ambiguous request id"
                ));
            }
            RequestIdField::Valid(id) => id.as_json(),
        };
        if let Some(first) = self.requests.get(&id) {
            return Err(format!(
                "frame {frame} request ID {id} aliases the canonical ID first used at frame {}; client-session evidence requires unique canonical IDs",
                first.frame
            ));
        }
        if self.requests.len() >= self.max_request_ids {
            return Err(format!(
                "frame {frame} exceeds the {}-request-ID session ceiling",
                self.max_request_ids
            ));
        }
        let next_bytes = self
            .request_id_bytes
            .checked_add(id.len())
            .ok_or_else(|| format!("frame {frame} request-ID byte accounting overflow"))?;
        if next_bytes > self.max_request_id_bytes {
            return Err(format!(
                "frame {frame} exceeds the {}-byte canonical request-ID ceiling",
                self.max_request_id_bytes
            ));
        }
        self.request_id_bytes = next_bytes;
        self.requests.insert(
            id,
            RequestRecord {
                frame,
                kind: if method == "textDocument/waitForDiagnostics" {
                    RequestKind::DiagnosticWait
                } else {
                    RequestKind::Other
                },
            },
        );
        Ok(())
    }

    fn observe(
        &mut self,
        frame: u64,
        id: &RequestIdField,
        method: &str,
        params: RawField<'_>,
    ) -> Result<(), String> {
        self.observe_request_id(frame, method, id)?;
        let event = document_event(method, params)
            .map_err(|error| format!("frame {frame} method {method:?}: {error}"))?;
        match event {
            None => Ok(()),
            Some(DocumentEvent::Open { uri, version }) => {
                if self.documents.contains_key(&uri) {
                    return Err(format!(
                        "frame {frame} didOpen duplicates already-open document {uri:?}"
                    ));
                }
                if self.documents.len() >= self.max_documents {
                    return Err(format!(
                        "frame {frame} didOpen exceeds the {}-document session ceiling",
                        self.max_documents
                    ));
                }
                let next_uri_bytes = self
                    .open_uri_bytes
                    .checked_add(uri.len())
                    .ok_or_else(|| format!("frame {frame} document URI accounting overflow"))?;
                if next_uri_bytes > self.max_uri_bytes {
                    return Err(format!(
                        "frame {frame} didOpen exceeds the {}-byte open-document URI ceiling",
                        self.max_uri_bytes
                    ));
                }
                self.open_uri_bytes = next_uri_bytes;
                self.documents.insert(uri, version);
                self.peak_open_documents = self.peak_open_documents.max(self.documents.len());
                self.peak_open_uri_bytes = self.peak_open_uri_bytes.max(self.open_uri_bytes);
                Self::bump(&mut self.documents_opened, "didOpen")
            }
            Some(DocumentEvent::Change { uri, version }) => {
                let Some(current) = self.documents.get_mut(&uri) else {
                    return Err(format!(
                        "frame {frame} didChange targets unopened document {uri:?}"
                    ));
                };
                if version <= *current {
                    return Err(format!(
                        "frame {frame} didChange version {version} is not newer than authoritative version {} for {uri:?}",
                        *current
                    ));
                }
                *current = version;
                Self::bump(&mut self.documents_changed, "didChange")
            }
            Some(DocumentEvent::Save { uri }) => {
                if !self.documents.contains_key(&uri) {
                    return Err(format!(
                        "frame {frame} didSave targets unopened document {uri:?}"
                    ));
                }
                Self::bump(&mut self.documents_saved, "didSave")
            }
            Some(DocumentEvent::Close { uri }) => {
                if self.documents.remove(&uri).is_none() {
                    return Err(format!(
                        "frame {frame} didClose targets unopened document {uri:?}"
                    ));
                }
                self.open_uri_bytes = self
                    .open_uri_bytes
                    .checked_sub(uri.len())
                    .ok_or_else(|| format!("frame {frame} document URI accounting underflow"))?;
                Self::bump(&mut self.documents_closed, "didClose")
            }
            Some(DocumentEvent::Wait { uri, version }) => {
                let Some(current) = self.documents.get(&uri).copied() else {
                    return Err(format!(
                        "frame {frame} waitForDiagnostics targets unopened document {uri:?}"
                    ));
                };
                Self::bump(&mut self.diagnostic_waits, "waitForDiagnostics")?;
                if version <= current {
                    Self::bump(&mut self.covered_version_waits, "covered-version wait")
                } else {
                    Self::bump(&mut self.future_version_waits, "future-version wait")
                }
            }
            Some(DocumentEvent::Cancel { id }) => {
                let Some(target) = self.requests.get(&id).copied() else {
                    return Err(format!(
                        "frame {frame} cancelRequest targets unknown prior canonical request ID {id}"
                    ));
                };
                if let Some(first_cancel) = self.cancelled_requests.get(&id) {
                    return Err(format!(
                        "frame {frame} repeats cancellation of request ID {id}; first cancellation was frame {first_cancel}"
                    ));
                }
                self.cancelled_requests.insert(id, frame);
                Self::bump(&mut self.cancellations, "cancelRequest")?;
                match target.kind {
                    RequestKind::DiagnosticWait => Self::bump(
                        &mut self.diagnostic_wait_cancellation_targets,
                        "diagnostic-wait cancellation target",
                    ),
                    RequestKind::Other => Self::bump(
                        &mut self.other_request_cancellation_targets,
                        "other-request cancellation target",
                    ),
                }
            }
        }
    }

    fn finish(self, lifecycle: ClientLifecycleStats) -> Result<ClientSessionStats, String> {
        let classified_waits = self
            .covered_version_waits
            .checked_add(self.future_version_waits)
            .ok_or_else(|| "diagnostic-wait classification overflow".to_string())?;
        if classified_waits != self.diagnostic_waits {
            return Err(format!(
                "diagnostic-wait accounting mismatch: total {}, classified {classified_waits}",
                self.diagnostic_waits
            ));
        }
        let classified_cancellations = self
            .diagnostic_wait_cancellation_targets
            .checked_add(self.other_request_cancellation_targets)
            .ok_or_else(|| "cancellation-target classification overflow".to_string())?;
        if classified_cancellations != self.cancellations {
            return Err(format!(
                "cancellation-target accounting mismatch: total {}, classified {classified_cancellations}",
                self.cancellations
            ));
        }
        let unique_request_ids = u64::try_from(self.requests.len())
            .map_err(|_| "unique request-ID count does not fit u64".to_string())?;
        if unique_request_ids != lifecycle.transcript.requests {
            return Err(format!(
                "request-ID accounting mismatch: retained {unique_request_ids}, lifecycle recorded {} requests",
                lifecycle.transcript.requests
            ));
        }
        Ok(ClientSessionStats {
            lifecycle,
            documents_opened: self.documents_opened,
            documents_changed: self.documents_changed,
            documents_saved: self.documents_saved,
            documents_closed: self.documents_closed,
            diagnostic_waits: self.diagnostic_waits,
            covered_version_waits: self.covered_version_waits,
            future_version_waits: self.future_version_waits,
            cancellations: self.cancellations,
            diagnostic_wait_cancellation_targets: self.diagnostic_wait_cancellation_targets,
            other_request_cancellation_targets: self.other_request_cancellation_targets,
            unique_request_ids,
            request_id_bytes: u64::try_from(self.request_id_bytes)
                .map_err(|_| "canonical request-ID bytes do not fit u64".to_string())?,
            peak_open_documents: u64::try_from(self.peak_open_documents)
                .map_err(|_| "peak open-document count does not fit u64".to_string())?,
            final_open_documents: u64::try_from(self.documents.len())
                .map_err(|_| "final open-document count does not fit u64".to_string())?,
            peak_open_uri_bytes: u64::try_from(self.peak_open_uri_bytes)
                .map_err(|_| "peak open-document URI bytes do not fit u64".to_string())?,
            final_open_uri_bytes: u64::try_from(self.open_uri_bytes)
                .map_err(|_| "final open-document URI bytes do not fit u64".to_string())?,
        })
    }
}

pub fn validate_client_session_bytes(bytes: &[u8]) -> Result<ClientSessionStats, String> {
    let lifecycle = transcript::validate_client_lifecycle_bytes(bytes)?;
    let mut reader = BufReader::new(Cursor::new(bytes));
    let mut validator = ClientSessionValidator::new();
    let mut frame = 0u64;
    while let Some(body) = crate::transport::read_message(&mut reader)
        .map_err(|error| format!("session semantic pass transport failure: {error}"))?
    {
        frame = frame
            .checked_add(1)
            .ok_or_else(|| "session semantic frame count overflow".to_string())?;
        let text = std::str::from_utf8(&body)
            .map_err(|_| format!("frame {frame} body is not valid UTF-8"))?;
        let envelope = parse_envelope(text).map_err(|error| match error {
            EnvelopeError::MalformedJson => format!("frame {frame} contains malformed JSON"),
            EnvelopeError::NotObject => format!("frame {frame} is not a JSON-RPC object"),
        })?;
        let method = match &envelope.method {
            DecodedField::Valid(method) => method.clone(),
            DecodedField::Missing => return Err(format!("frame {frame} is missing a method")),
            DecodedField::Invalid => {
                return Err(format!("frame {frame} has a non-string method"));
            }
        };
        validator.observe(frame, &envelope.id, &method, envelope.params)?;
    }
    if frame != lifecycle.transcript.frames {
        return Err(format!(
            "session semantic pass observed {frame} frames but lifecycle evidence recorded {}",
            lifecycle.transcript.frames
        ));
    }
    validator.finish(lifecycle)
}

pub fn validate_client_session_reader(
    input: &mut dyn BufRead,
) -> Result<ClientSessionStats, String> {
    let limit = transcript::MAX_TRANSCRIPT_BYTES.saturating_add(1);
    let mut bytes = Vec::new();
    input
        .take(limit)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("could not read client session transcript: {error}"))?;
    if u64::try_from(bytes.len()).unwrap_or(u64::MAX) > transcript::MAX_TRANSCRIPT_BYTES {
        return Err(format!(
            "client session transcript exceeds the {}-byte aggregate ceiling",
            transcript::MAX_TRANSCRIPT_BYTES
        ));
    }
    validate_client_session_bytes(&bytes)
}

pub fn render_client_session_validation(stats: ClientSessionStats) -> String {
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-client-session/3\",\"finalState\":\"exited\",",
            "\"idPolicy\":\"number-lexeme-string-value-v1\",",
            "\"frames\":{},\"requests\":{},\"notifications\":{},",
            "\"wireBytes\":{},\"bodyBytes\":{},",
            "\"initializeFrame\":{},\"initializedFrame\":{},",
            "\"shutdownFrame\":{},\"exitFrame\":{},",
            "\"documentsOpened\":{},\"documentsChanged\":{},",
            "\"documentsSaved\":{},\"documentsClosed\":{},",
            "\"diagnosticWaits\":{},\"coveredVersionWaits\":{},",
            "\"futureVersionWaits\":{},\"cancellations\":{},",
            "\"diagnosticWaitCancellationTargets\":{},",
            "\"otherRequestCancellationTargets\":{},",
            "\"uniqueRequestIds\":{},\"requestIdBytes\":{},",
            "\"requestIdCountCeiling\":{},\"requestIdByteCeiling\":{},",
            "\"peakOpenDocuments\":{},\"finalOpenDocuments\":{},",
            "\"peakOpenUriBytes\":{},\"finalOpenUriBytes\":{}}}\n"
        ),
        stats.lifecycle.transcript.frames,
        stats.lifecycle.transcript.requests,
        stats.lifecycle.transcript.notifications,
        stats.lifecycle.transcript.wire_bytes,
        stats.lifecycle.transcript.body_bytes,
        stats.lifecycle.initialize_frame,
        stats.lifecycle.initialized_frame,
        stats.lifecycle.shutdown_frame,
        stats.lifecycle.exit_frame,
        stats.documents_opened,
        stats.documents_changed,
        stats.documents_saved,
        stats.documents_closed,
        stats.diagnostic_waits,
        stats.covered_version_waits,
        stats.future_version_waits,
        stats.cancellations,
        stats.diagnostic_wait_cancellation_targets,
        stats.other_request_cancellation_targets,
        stats.unique_request_ids,
        stats.request_id_bytes,
        MAX_SESSION_REQUEST_IDS,
        MAX_SESSION_REQUEST_ID_BYTES,
        stats.peak_open_documents,
        stats.final_open_documents,
        stats.peak_open_uri_bytes,
        stats.final_open_uri_bytes
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

    fn session(events: &[&str]) -> Vec<u8> {
        let mut bodies = vec![
            r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        ];
        bodies.extend_from_slice(events);
        bodies.extend([
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        framed(&bodies)
    }

    #[test]
    fn validates_full_document_session_and_renders_resource_evidence() {
        let bytes = session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A.lean","version":1,"text":"def a := 1"}}}"#,
            r#"{"jsonrpc":"2.0","id":"wait","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///A.lean","version":2}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///A.lean","version":2},"contentChanges":[{"text":"def a := 2"}]}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///A.lean"}}}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"wait"}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///A.lean"}}}"#,
        ]);
        let stats = validate_client_session_bytes(&bytes).unwrap();
        assert_eq!(stats.documents_opened, 1);
        assert_eq!(stats.documents_changed, 1);
        assert_eq!(stats.documents_saved, 1);
        assert_eq!(stats.documents_closed, 1);
        assert_eq!(stats.diagnostic_waits, 1);
        assert_eq!(stats.covered_version_waits, 0);
        assert_eq!(stats.future_version_waits, 1);
        assert_eq!(stats.cancellations, 1);
        assert_eq!(stats.diagnostic_wait_cancellation_targets, 1);
        assert_eq!(stats.other_request_cancellation_targets, 0);
        assert_eq!(stats.unique_request_ids, 3);
        assert_eq!(stats.peak_open_documents, 1);
        assert_eq!(stats.final_open_documents, 0);
        assert_eq!(stats.final_open_uri_bytes, 0);
        let receipt = render_client_session_validation(stats);
        assert!(receipt.contains("\"schema\":\"fln.lsp-client-session/3\""));
        assert!(receipt.contains("\"idPolicy\":\"number-lexeme-string-value-v1\""));
        assert!(receipt.contains("\"futureVersionWaits\":1"));
        assert!(receipt.contains("\"diagnosticWaitCancellationTargets\":1"));
        assert!(receipt.contains("\"requestIdCountCeiling\":262144"));
        assert!(receipt.contains("\"requestIdByteCeiling\":33554432"));
    }

    #[test]
    fn cancellation_targets_prior_canonical_request_identity() {
        let escaped = framed(&[
            r#"{"jsonrpc":"2.0","id":"\u0069nit","method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"init"}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        let stats = validate_client_session_bytes(&escaped).unwrap();
        assert_eq!(stats.cancellations, 1);
        assert_eq!(stats.other_request_cancellation_targets, 1);

        let numeric_alias = framed(&[
            r#"{"jsonrpc":"2.0","id":1.25e2,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":125}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        assert!(
            validate_client_session_bytes(&numeric_alias)
                .unwrap_err()
                .contains("unknown prior canonical request ID 125")
        );
    }

    #[test]
    fn unknown_and_duplicate_cancellations_are_refused() {
        let unknown = session(&[r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"missing"}}"#]);
        assert!(
            validate_client_session_bytes(&unknown)
                .unwrap_err()
                .contains("unknown prior canonical request ID")
        );

        let duplicate = session(&[
            r#"{"jsonrpc":"2.0","id":"wait","method":"textDocument/hover","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"wait"}}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"wait"}}"#,
        ]);
        assert!(
            validate_client_session_bytes(&duplicate)
                .unwrap_err()
                .contains("repeats cancellation")
        );
    }

    #[test]
    fn canonical_request_ids_are_unique_and_bounded() {
        let duplicate = framed(&[
            r#"{"jsonrpc":"2.0","id":"\u0069nit","method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"init","method":"textDocument/hover","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ]);
        assert!(
            validate_client_session_bytes(&duplicate)
                .unwrap_err()
                .contains("requires unique canonical IDs")
        );

        let mut validator = ClientSessionValidator::with_all_limits(1, 16, 1, 4);
        validator
            .observe(
                1,
                &RequestIdField::Valid(RequestId::Number("1".to_string())),
                "initialize",
                RawField::Value("{}"),
            )
            .unwrap();
        let error = validator
            .observe(
                2,
                &RequestIdField::Valid(RequestId::Text("x".to_string())),
                "textDocument/hover",
                RawField::Value("{}"),
            )
            .unwrap_err();
        assert!(error.contains("1-request-ID session ceiling"));
        assert_eq!(validator.requests.len(), 1);
        assert_eq!(validator.request_id_bytes, 1);
    }

    #[test]
    fn refuses_duplicate_unopened_and_nonmonotone_document_events() {
        let cases = [
            (
                session(&[
                    r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A","version":1,"text":"a"}}}"#,
                    r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A","version":2,"text":"b"}}}"#,
                ]),
                "duplicates already-open",
            ),
            (
                session(&[r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///A","version":2},"contentChanges":[{"text":"b"}]}}"#]),
                "targets unopened document",
            ),
            (
                session(&[
                    r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A","version":2,"text":"a"}}}"#,
                    r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///A","version":2},"contentChanges":[{"text":"b"}]}}"#,
                ]),
                "is not newer",
            ),
            (
                session(&[r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///A"}}}"#]),
                "targets unopened document",
            ),
            (
                session(&[r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///A"}}}"#]),
                "targets unopened document",
            ),
        ];
        for (bytes, expected) in cases {
            let error = validate_client_session_bytes(&bytes).unwrap_err();
            assert!(error.contains(expected), "expected {expected:?}: {error}");
        }
    }

    #[test]
    fn refuses_malformed_document_payloads_after_lifecycle_validation() {
        let cases = [
            (
                session(&[r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A","version":1}}}"#]),
                "requires complete textDocument.text",
            ),
            (
                session(&[r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"","version":1,"text":"a"}}}"#]),
                "must not be empty",
            ),
            (
                session(&[
                    r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A","version":1,"text":"a"}}}"#,
                    r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///A","version":2},"contentChanges":[{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":1}},"text":"b"}]}}"#,
                ]),
                "unranged Full-sync",
            ),
            (
                session(&[r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":null}}"#]),
                "must not be null",
            ),
        ];
        for (bytes, expected) in cases {
            let error = validate_client_session_bytes(&bytes).unwrap_err();
            assert!(error.contains(expected), "expected {expected:?}: {error}");
        }
    }

    #[test]
    fn wait_requires_an_open_document_and_classifies_target_version() {
        let valid = session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A","version":3,"text":"a"}}}"#,
            r#"{"jsonrpc":"2.0","id":7,"method":"textDocument/waitForDiagnostics","params":{"uri":"file:///A","version":2}}"#,
            r#"{"jsonrpc":"2.0","id":8,"method":"textDocument/waitForDiagnostics","params":{"uri":"file:///A","version":99}}"#,
        ]);
        let stats = validate_client_session_bytes(&valid).unwrap();
        assert_eq!(stats.diagnostic_waits, 2);
        assert_eq!(stats.covered_version_waits, 1);
        assert_eq!(stats.future_version_waits, 1);

        let invalid = session(&[r#"{"jsonrpc":"2.0","id":7,"method":"textDocument/waitForDiagnostics","params":{"uri":"file:///A","version":1}}"#]);
        assert!(
            validate_client_session_bytes(&invalid)
                .unwrap_err()
                .contains("targets unopened document")
        );
    }

    #[test]
    fn uri_capacity_is_checked_before_document_membership_changes() {
        let mut validator = ClientSessionValidator::with_limits(2, 3);
        let error = validator
            .observe(
                1,
                &RequestIdField::Absent,
                "textDocument/didOpen",
                RawField::Value(
                    r#"{"textDocument":{"uri":"four","version":1,"text":"source"}}"#,
                ),
            )
            .unwrap_err();
        assert!(error.contains("3-byte open-document URI ceiling"));
        assert!(validator.documents.is_empty());
        assert_eq!(validator.open_uri_bytes, 0);

        validator
            .observe(
                2,
                &RequestIdField::Absent,
                "textDocument/didOpen",
                RawField::Value(
                    r#"{"textDocument":{"uri":"ok","version":1,"text":"source"}}"#,
                ),
            )
            .unwrap();
        assert_eq!(validator.documents.len(), 1);
        assert_eq!(validator.open_uri_bytes, 2);
    }

    #[test]
    fn shutdown_may_leave_documents_open_but_receipt_discloses_them() {
        let bytes = session(&[r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A","version":1,"text":"a"}}}"#]);
        let stats = validate_client_session_bytes(&bytes).unwrap();
        assert_eq!(stats.final_open_documents, 1);
        assert_eq!(stats.final_open_uri_bytes, 9);
    }
}
