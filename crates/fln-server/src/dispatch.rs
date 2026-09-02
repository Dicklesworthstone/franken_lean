//! Bounded JSON-RPC dispatch for the LSP lifecycle and Full document sync.
//!
//! JSON syntax, document-session authority, pending diagnostic waits, and
//! deterministic wire encoding live in dedicated submodules. The dispatcher is
//! intentionally synchronous: it owns protocol ordering and delegates source
//! checking through one callback.

use std::io::{self, BufRead, Write};

use crate::transport;

mod json;
mod session;
mod wait;
mod wire;

use json::{
    DecodedField, Envelope, EnvelopeError, RawField, RequestId, RequestIdField, VersionField,
    content_changes_text, direct_request_id, direct_uri, direct_version, parse_envelope,
    save_text, text_document_text, text_document_uri, text_document_version,
};
use session::{DocumentSession, RetentionOutcome, SessionRefusal};
use wait::{PendingDiagnosticWaits, WaitRefusal};
use wire::{
    REQUEST_CANCELLED_CODE, REQUEST_FAILED_CODE, SERVER_NOT_INITIALIZED_CODE,
    clear_diagnostics_notification, diagnostic_callback_failure_notification,
    empty_object_response, error_response, error_response_null_id, file_progress_notification,
    initialize_response, invalid_request_response, log_warning, null_response,
};

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
struct PublishedVersion {
    uri: String,
    version: i64,
}

pub type OnDidOpen = dyn FnMut(&str, &str) -> Vec<String>;

fn write_protocol_message(output: &mut dyn Write, message: String) -> io::Result<()> {
    transport::write_message(output, message.as_bytes())
}

fn write_warning(output: &mut dyn Write, message: &str) -> io::Result<()> {
    write_protocol_message(output, log_warning(message))
}

fn write_retention_outcome(
    output: &mut dyn Write,
    retention: RetentionOutcome,
) -> io::Result<()> {
    if let RetentionOutcome::NotRetained(refusal) = retention {
        write_warning(output, refusal.message())?;
    }
    Ok(())
}

fn is_terminal_diagnostic_message(message: &str) -> bool {
    message.contains("\"method\":\"textDocument/publishDiagnostics\"")
        || message.contains("\"method\":\"$/lean/diagnosticOutcome\"")
}

fn check_document(
    output: &mut dyn Write,
    uri: &str,
    content: &str,
    on_did_open: &mut OnDidOpen,
) -> io::Result<()> {
    write_protocol_message(output, file_progress_notification(uri, true))?;
    let notifications = on_did_open(uri, content);
    let has_terminal_outcome = notifications
        .iter()
        .any(|message| is_terminal_diagnostic_message(message));
    for notification in notifications {
        transport::write_message(output, notification.as_bytes())?;
    }
    if !has_terminal_outcome {
        write_protocol_message(output, clear_diagnostics_notification(uri))?;
        write_protocol_message(output, diagnostic_callback_failure_notification(uri))?;
    }
    write_protocol_message(output, file_progress_notification(uri, false))
}

fn complete_waits(output: &mut dyn Write, ids: Vec<RequestId>) -> io::Result<()> {
    for id in ids {
        write_protocol_message(output, empty_object_response(&id))?;
    }
    Ok(())
}

fn fail_waits(output: &mut dyn Write, ids: Vec<RequestId>, message: &str) -> io::Result<()> {
    for id in ids {
        write_protocol_message(output, error_response(&id, REQUEST_FAILED_CODE, message))?;
    }
    Ok(())
}

fn invalidate_source_and_clear(
    output: &mut dyn Write,
    session: &mut DocumentSession,
    uri: &str,
    reason: &str,
) -> io::Result<()> {
    match session.invalidate_text(uri) {
        Ok(()) | Err(SessionRefusal::NotOpen) => {}
        Err(refusal) => write_warning(output, refusal.message())?,
    }
    write_protocol_message(output, clear_diagnostics_notification(uri))?;
    write_warning(output, reason)
}

fn decoded_uri(params: RawField<'_>) -> Result<String, &'static str> {
    match text_document_uri(params) {
        DecodedField::Valid(uri) if !uri.is_empty() => Ok(uri),
        DecodedField::Valid(_) => Err("LSP textDocument.uri must not be empty"),
        DecodedField::Missing => Err("LSP textDocument.uri is required"),
        DecodedField::Invalid => Err("LSP textDocument.uri is malformed or ambiguous"),
    }
}

fn decoded_version(params: RawField<'_>) -> Result<i64, &'static str> {
    match text_document_version(params) {
        VersionField::Valid(version) => Ok(version),
        VersionField::Missing => Err("LSP textDocument.version is required"),
        VersionField::Invalid => Err("LSP textDocument.version must be one unambiguous integer"),
    }
}

fn decoded_open_text(params: RawField<'_>) -> Result<String, &'static str> {
    match text_document_text(params) {
        DecodedField::Valid(text) => Ok(text),
        DecodedField::Missing => Err("LSP didOpen requires the complete document text"),
        DecodedField::Invalid => Err("LSP didOpen text is malformed or ambiguous"),
    }
}

fn decoded_change_text(params: RawField<'_>) -> Result<String, &'static str> {
    match content_changes_text(params) {
        DecodedField::Valid(text) => Ok(text),
        DecodedField::Missing => {
            Err("LSP didChange requires exactly one Full-sync content change")
        }
        DecodedField::Invalid => Err(
            "LSP didChange requires exactly one unambiguous, unranged Full-sync text change",
        ),
    }
}

fn decoded_wait_target(params: RawField<'_>) -> Result<(String, i64), &'static str> {
    let uri = match direct_uri(params) {
        DecodedField::Valid(uri) if !uri.is_empty() => uri,
        DecodedField::Valid(_) => {
            return Err("waitForDiagnostics uri must not be empty");
        }
        DecodedField::Missing => {
            return Err("waitForDiagnostics requires uri");
        }
        DecodedField::Invalid => {
            return Err("waitForDiagnostics uri is malformed or ambiguous");
        }
    };
    let version = match direct_version(params) {
        VersionField::Valid(version) if version >= 0 => version,
        VersionField::Valid(_) => {
            return Err("waitForDiagnostics version must be a nonnegative integer");
        }
        VersionField::Missing => {
            return Err("waitForDiagnostics requires version");
        }
        VersionField::Invalid => {
            return Err("waitForDiagnostics version is malformed or ambiguous");
        }
    };
    Ok((uri, version))
}

fn handle_open(
    output: &mut dyn Write,
    session: &mut DocumentSession,
    params: RawField<'_>,
    on_did_open: &mut OnDidOpen,
) -> io::Result<Option<PublishedVersion>> {
    let uri = match decoded_uri(params) {
        Ok(uri) => uri,
        Err(message) => {
            write_warning(output, message)?;
            return Ok(None);
        }
    };
    let version = match decoded_version(params) {
        Ok(version) => version,
        Err(message) => {
            write_warning(output, message)?;
            return Ok(None);
        }
    };
    let text = match decoded_open_text(params) {
        Ok(text) => text,
        Err(message) => {
            write_warning(output, message)?;
            return Ok(None);
        }
    };

    match session.open(uri.clone(), version, text.clone()) {
        Ok(retention) => {
            write_retention_outcome(output, retention)?;
            check_document(output, &uri, &text, on_did_open)?;
            Ok(Some(PublishedVersion { uri, version }))
        }
        Err(refusal) => {
            write_warning(output, refusal.message())?;
            Ok(None)
        }
    }
}

fn handle_change(
    output: &mut dyn Write,
    session: &mut DocumentSession,
    params: RawField<'_>,
    on_did_open: &mut OnDidOpen,
) -> io::Result<Option<PublishedVersion>> {
    let uri = match decoded_uri(params) {
        Ok(uri) => uri,
        Err(message) => {
            write_warning(output, message)?;
            return Ok(None);
        }
    };
    if !session.is_open(&uri) {
        write_warning(output, SessionRefusal::NotOpen.message())?;
        return Ok(None);
    }
    let version = match decoded_version(params) {
        Ok(version) => version,
        Err(message) => {
            invalidate_source_and_clear(output, session, &uri, message)?;
            return Ok(None);
        }
    };
    let text = match decoded_change_text(params) {
        Ok(text) => text,
        Err(message) => {
            invalidate_source_and_clear(output, session, &uri, message)?;
            return Ok(None);
        }
    };

    match session.change(&uri, version, text.clone()) {
        Ok(retention) => {
            write_retention_outcome(output, retention)?;
            check_document(output, &uri, &text, on_did_open)?;
            Ok(Some(PublishedVersion { uri, version }))
        }
        Err(refusal) => {
            write_warning(output, refusal.message())?;
            Ok(None)
        }
    }
}

fn handle_save(
    output: &mut dyn Write,
    session: &mut DocumentSession,
    params: RawField<'_>,
    on_did_open: &mut OnDidOpen,
) -> io::Result<bool> {
    let uri = match decoded_uri(params) {
        Ok(uri) => uri,
        Err(message) => {
            write_warning(output, message)?;
            return Ok(false);
        }
    };
    if !session.is_open(&uri) {
        write_warning(output, SessionRefusal::NotOpen.message())?;
        return Ok(false);
    }

    match save_text(params) {
        DecodedField::Valid(text) => match session.save_with_text(&uri, text.clone()) {
            Ok(retention) => {
                write_retention_outcome(output, retention)?;
                check_document(output, &uri, &text, on_did_open)?;
                Ok(true)
            }
            Err(refusal) => {
                write_warning(output, refusal.message())?;
                Ok(false)
            }
        },
        DecodedField::Missing => {
            let Some(text) = session.text(&uri).map(str::to_owned) else {
                write_protocol_message(output, clear_diagnostics_notification(&uri))?;
                write_warning(
                    output,
                    "FrankenLean could not re-check textless didSave because no retained source exists",
                )?;
                return Ok(false);
            };
            check_document(output, &uri, &text, on_did_open)?;
            Ok(true)
        }
        DecodedField::Invalid => {
            invalidate_source_and_clear(
                output,
                session,
                &uri,
                "FrankenLean refused malformed didSave text; retained source was invalidated",
            )?;
            Ok(false)
        }
    }
}

fn handle_close(
    output: &mut dyn Write,
    session: &mut DocumentSession,
    params: RawField<'_>,
) -> io::Result<Option<String>> {
    let uri = match decoded_uri(params) {
        Ok(uri) => uri,
        Err(message) => {
            write_warning(output, message)?;
            return Ok(None);
        }
    };
    match session.close(&uri) {
        Ok(true) => {}
        Ok(false) => write_warning(
            output,
            "FrankenLean received didClose for a document that was not open",
        )?,
        Err(refusal) => write_warning(output, refusal.message())?,
    }
    write_protocol_message(output, clear_diagnostics_notification(&uri))?;
    Ok(Some(uri))
}

fn handle_wait_for_diagnostics(
    output: &mut dyn Write,
    session: &DocumentSession,
    waits: &mut PendingDiagnosticWaits,
    id: &RequestId,
    params: RawField<'_>,
) -> io::Result<()> {
    if waits.contains(id) {
        return write_protocol_message(
            output,
            error_response(id, -32600, WaitRefusal::DuplicateId.message()),
        );
    }
    let (uri, version) = match decoded_wait_target(params) {
        Ok(target) => target,
        Err(message) => {
            return write_protocol_message(output, error_response(id, -32602, message));
        }
    };
    if !session.is_open(&uri) {
        return write_protocol_message(
            output,
            error_response(
                id,
                REQUEST_FAILED_CODE,
                "waitForDiagnostics requires an open document",
            ),
        );
    }
    if session
        .version(&uri)
        .is_some_and(|current| current >= version)
    {
        return write_protocol_message(output, empty_object_response(id));
    }
    match waits.register(id.clone(), uri, version) {
        Ok(()) => Ok(()),
        Err(WaitRefusal::DuplicateId) => write_protocol_message(
            output,
            error_response(id, -32600, WaitRefusal::DuplicateId.message()),
        ),
        Err(WaitRefusal::Capacity) => write_protocol_message(
            output,
            error_response(id, REQUEST_FAILED_CODE, WaitRefusal::Capacity.message()),
        ),
    }
}

fn handle_cancel_request(
    output: &mut dyn Write,
    waits: &mut PendingDiagnosticWaits,
    params: RawField<'_>,
) -> io::Result<()> {
    let id = match direct_request_id(params) {
        RequestIdField::Valid(RequestId::Null) => {
            return write_warning(
                output,
                "FrankenLean ignored $/cancelRequest with a null request id",
            );
        }
        RequestIdField::Valid(id) => id,
        RequestIdField::Absent => {
            return write_warning(
                output,
                "FrankenLean ignored $/cancelRequest without a request id",
            );
        }
        RequestIdField::Invalid => {
            return write_warning(
                output,
                "FrankenLean ignored $/cancelRequest with a malformed or ambiguous request id",
            );
        }
    };
    if let Some(id) = waits.cancel(&id) {
        write_protocol_message(
            output,
            error_response(&id, REQUEST_CANCELLED_CODE, "request cancelled"),
        )?;
    }
    Ok(())
}

fn request_id(envelope: &Envelope<'_>) -> Result<Option<&RequestId>, String> {
    match &envelope.id {
        RequestIdField::Absent => Ok(None),
        RequestIdField::Valid(id) => Ok(Some(id)),
        RequestIdField::Invalid => Err(error_response_null_id(
            -32600,
            "invalid or ambiguous JSON-RPC request id",
        )),
    }
}

fn method(envelope: &Envelope<'_>, id: Option<&RequestId>) -> Result<String, String> {
    match &envelope.method {
        DecodedField::Valid(method) if !method.is_empty() => Ok(method.clone()),
        DecodedField::Valid(_) => Err(invalid_request_response(
            id,
            "JSON-RPC method must not be empty",
        )),
        DecodedField::Missing => Err(invalid_request_response(
            id,
            "JSON-RPC method is required",
        )),
        DecodedField::Invalid => Err(invalid_request_response(
            id,
            "JSON-RPC method must be one unambiguous string",
        )),
    }
}

fn validate_version(envelope: &Envelope<'_>, id: Option<&RequestId>) -> Result<(), String> {
    match &envelope.jsonrpc {
        DecodedField::Valid(version) if version == "2.0" => Ok(()),
        DecodedField::Valid(_) => Err(invalid_request_response(
            id,
            "unsupported JSON-RPC version; expected 2.0",
        )),
        DecodedField::Missing => Err(invalid_request_response(
            id,
            "missing JSON-RPC version; expected 2.0",
        )),
        DecodedField::Invalid => Err(invalid_request_response(
            id,
            "JSON-RPC version must be one unambiguous string",
        )),
    }
}

fn is_notification_method(method: &str) -> bool {
    matches!(
        method,
        "initialized"
            | "exit"
            | "$/cancelRequest"
            | "$/lean/rpc/keepAlive"
            | "$/lean/rpc/release"
            | "textDocument/didOpen"
            | "textDocument/didChange"
            | "textDocument/didSave"
            | "textDocument/didClose"
    )
}

fn is_request_method(method: &str) -> bool {
    matches!(
        method,
        "initialize"
            | "shutdown"
            | "$/lean/plainGoal"
            | "$/lean/plainTermGoal"
            | "$/lean/rpc/connect"
            | "$/lean/rpc/call"
            | "textDocument/completion"
            | "textDocument/definition"
            | "textDocument/hover"
            | "textDocument/waitForDiagnostics"
    )
}

fn validate_method_role(
    output: &mut dyn Write,
    method: &str,
    id: Option<&RequestId>,
) -> io::Result<bool> {
    if is_notification_method(method) && id.is_some() {
        write_protocol_message(
            output,
            invalid_request_response(id, "this LSP method is a notification, not a request"),
        )?;
        return Ok(false);
    }
    if is_request_method(method) && id.is_none() {
        write_warning(
            output,
            "FrankenLean ignored a request-only LSP method sent as a notification",
        )?;
        return Ok(false);
    }
    Ok(true)
}

fn running_request(
    output: &mut dyn Write,
    state: ServerState,
    id: &RequestId,
) -> io::Result<bool> {
    match state {
        ServerState::Running => Ok(true),
        ServerState::Uninitialized | ServerState::Initializing => {
            write_protocol_message(
                output,
                error_response(
                    id,
                    SERVER_NOT_INITIALIZED_CODE,
                    "server is not initialized",
                ),
            )?;
            Ok(false)
        }
        ServerState::ShuttingDown => {
            write_protocol_message(
                output,
                error_response(id, -32600, "server is shutting down"),
            )?;
            Ok(false)
        }
    }
}

pub fn serve(
    input: &mut dyn BufRead,
    output: &mut dyn Write,
    on_did_open: &mut OnDidOpen,
) -> io::Result<ServerOutcome> {
    let mut state = ServerState::Uninitialized;
    let mut documents_opened = 0u64;
    let mut documents_changed = 0u64;
    let mut documents_saved = 0u64;
    let mut session = DocumentSession::new();
    let mut waits = PendingDiagnosticWaits::new();

    loop {
        let Some(message) = transport::read_message(input)? else {
            return Ok(ServerOutcome {
                clean: state == ServerState::ShuttingDown,
                documents_opened,
                documents_changed,
                documents_saved,
            });
        };
        let text = match String::from_utf8(message) {
            Ok(text) => text,
            Err(_) => {
                write_protocol_message(
                    output,
                    error_response_null_id(-32700, "message body is not valid UTF-8 JSON"),
                )?;
                continue;
            }
        };
        let envelope = match parse_envelope(&text) {
            Ok(envelope) => envelope,
            Err(EnvelopeError::MalformedJson) => {
                write_protocol_message(output, error_response_null_id(-32700, "parse error"))?;
                continue;
            }
            Err(EnvelopeError::NotObject) => {
                write_protocol_message(
                    output,
                    error_response_null_id(-32600, "JSON-RPC request must be an object"),
                )?;
                continue;
            }
        };
        let id = match request_id(&envelope) {
            Ok(id) => id,
            Err(response) => {
                write_protocol_message(output, response)?;
                continue;
            }
        };
        if let Err(response) = validate_version(&envelope, id) {
            write_protocol_message(output, response)?;
            continue;
        }
        let method = match method(&envelope, id) {
            Ok(method) => method,
            Err(response) => {
                write_protocol_message(output, response)?;
                continue;
            }
        };
        if !validate_method_role(output, &method, id)? {
            continue;
        }
        if method != "textDocument/waitForDiagnostics" {
            if let Some(request_id) = id {
                if waits.contains(request_id) {
                    write_protocol_message(
                        output,
                        error_response(
                            request_id,
                            -32600,
                            "FrankenLean refused a duplicate outstanding JSON-RPC request id",
                        ),
                    )?;
                    continue;
                }
            }
        }

        match (method.as_str(), id, state) {
            ("initialize", Some(request_id), ServerState::Uninitialized) => {
                write_protocol_message(output, initialize_response(request_id))?;
                state = ServerState::Initializing;
            }
            ("initialize", Some(request_id), _) => {
                write_protocol_message(
                    output,
                    error_response(request_id, -32600, "server already initialized"),
                )?;
            }
            ("initialized", None, ServerState::Initializing) => {
                state = ServerState::Running;
            }
            ("initialized", None, _) => {
                write_warning(output, "FrankenLean ignored initialized outside initialization")?;
            }
            ("shutdown", Some(request_id), ServerState::Running) => {
                fail_waits(
                    output,
                    waits.drain_all(),
                    "server shut down before the requested diagnostics version was published",
                )?;
                write_protocol_message(output, null_response(request_id))?;
                state = ServerState::ShuttingDown;
            }
            ("shutdown", Some(request_id), _) => {
                if !running_request(output, state, request_id)? {
                    continue;
                }
            }
            ("exit", None, _) => {
                return Ok(ServerOutcome {
                    clean: state == ServerState::ShuttingDown,
                    documents_opened,
                    documents_changed,
                    documents_saved,
                });
            }
            ("textDocument/didOpen", None, ServerState::Running) => {
                if let Some(published) =
                    handle_open(output, &mut session, envelope.params, on_did_open)?
                {
                    documents_opened = documents_opened.saturating_add(1);
                    complete_waits(
                        output,
                        waits.complete_ready(&published.uri, published.version),
                    )?;
                }
            }
            ("textDocument/didChange", None, ServerState::Running) => {
                if let Some(published) =
                    handle_change(output, &mut session, envelope.params, on_did_open)?
                {
                    documents_changed = documents_changed.saturating_add(1);
                    complete_waits(
                        output,
                        waits.complete_ready(&published.uri, published.version),
                    )?;
                }
            }
            ("textDocument/didSave", None, ServerState::Running) => {
                if handle_save(output, &mut session, envelope.params, on_did_open)? {
                    documents_saved = documents_saved.saturating_add(1);
                }
            }
            ("textDocument/didClose", None, ServerState::Running) => {
                if let Some(uri) = handle_close(output, &mut session, envelope.params)? {
                    fail_waits(
                        output,
                        waits.drain_uri(&uri),
                        "document closed before the requested diagnostics version was published",
                    )?;
                }
            }
            ("textDocument/waitForDiagnostics", Some(request_id), state) => {
                if running_request(output, state, request_id)? {
                    handle_wait_for_diagnostics(
                        output,
                        &session,
                        &mut waits,
                        request_id,
                        envelope.params,
                    )?;
                }
            }
            ("$/cancelRequest", None, ServerState::Running) => {
                handle_cancel_request(output, &mut waits, envelope.params)?;
            }
            ("$/lean/rpc/keepAlive", None, ServerState::Running)
            | ("$/lean/rpc/release", None, ServerState::Running) => {}
            (method, None, state) if is_notification_method(method) => {
                let message = match state {
                    ServerState::Uninitialized | ServerState::Initializing => {
                        "FrankenLean ignored an LSP notification before initialization completed"
                    }
                    ServerState::ShuttingDown => {
                        "FrankenLean ignored an LSP notification after shutdown"
                    }
                    ServerState::Running => "FrankenLean ignored an unsupported LSP notification",
                };
                write_warning(output, message)?;
            }
            ("$/lean/plainGoal", Some(request_id), state)
            | ("$/lean/plainTermGoal", Some(request_id), state)
            | ("textDocument/hover", Some(request_id), state)
            | ("textDocument/completion", Some(request_id), state)
            | ("textDocument/definition", Some(request_id), state) => {
                if running_request(output, state, request_id)? {
                    write_protocol_message(output, null_response(request_id))?;
                }
            }
            ("$/lean/rpc/connect", Some(request_id), state)
            | ("$/lean/rpc/call", Some(request_id), state) => {
                if running_request(output, state, request_id)? {
                    write_protocol_message(
                        output,
                        error_response(
                            request_id,
                            REQUEST_FAILED_CODE,
                            "Lean RPC sessions are not implemented by this FrankenLean server",
                        ),
                    )?;
                }
            }
            (_, Some(request_id), state) => {
                if running_request(output, state, request_id)? {
                    write_protocol_message(
                        output,
                        error_response(request_id, -32601, "method not found"),
                    )?;
                }
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

    fn send(buffer: &mut Vec<u8>, body: &str) {
        write_message(buffer, body.as_bytes()).expect("frame test message");
    }

    fn run_session(messages: &[&str]) -> (ServerOutcome, String, Vec<(String, String)>) {
        let mut input = Vec::new();
        send(
            &mut input,
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        );
        send(
            &mut input,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        );
        for message in messages {
            send(&mut input, message);
        }
        send(
            &mut input,
            r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        );
        send(&mut input, r#"{"jsonrpc":"2.0","method":"exit"}"#);

        let mut reader = BufReader::new(input.as_slice());
        let mut output = Vec::new();
        let mut seen = Vec::new();
        let outcome = serve(&mut reader, &mut output, &mut |uri, text| {
            seen.push((uri.to_string(), text.to_string()));
            vec![format!(
                "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",\"params\":{{\"uri\":{},\"diagnostics\":[]}}}}",
                crate::json_string(uri)
            )]
        })
        .expect("serve test session");
        (
            outcome,
            String::from_utf8(output).expect("UTF-8 protocol output"),
            seen,
        )
    }

    #[test]
    fn clean_lifecycle_advertises_full_sync_and_utf16() {
        let (outcome, output, seen) = run_session(&[]);
        assert!(outcome.clean);
        assert!(seen.is_empty());
        assert!(output.contains("\"positionEncoding\":\"utf-16\""));
        assert!(output.contains("\"change\":1"));
    }

    #[test]
    fn full_document_lifecycle_rechecks_latest_source() {
        let (outcome, output, seen) = run_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x.lean","version":1,"text":"v1"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x.lean","version":2},"contentChanges":[{"text":"v2"}]}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///x.lean"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///x.lean"}}}"#,
        ]);
        assert!(outcome.clean);
        assert_eq!(outcome.documents_opened, 1);
        assert_eq!(outcome.documents_changed, 1);
        assert_eq!(outcome.documents_saved, 1);
        assert_eq!(
            seen,
            vec![
                ("file:///x.lean".to_string(), "v1".to_string()),
                ("file:///x.lean".to_string(), "v2".to_string()),
                ("file:///x.lean".to_string(), "v2".to_string()),
            ]
        );
        assert!(output.contains("\"uri\":\"file:///x.lean\",\"diagnostics\":[]"));
    }

    #[test]
    fn duplicate_open_and_unopened_events_are_refused() {
        let (outcome, output, seen) = run_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"first"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":2,"text":"second"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///missing","version":2},"contentChanges":[{"text":"bad"}]}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///missing"}}}"#,
        ]);
        assert!(outcome.clean);
        assert_eq!(seen, vec![("file:///x".to_string(), "first".to_string())]);
        assert!(output.contains("refused duplicate didOpen"));
        assert!(output.matches("document is not open").count() >= 2);
    }

    #[test]
    fn stale_change_does_not_replace_authoritative_source() {
        let (outcome, output, seen) = run_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":3,"text":"v3"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":3},"contentChanges":[{"text":"stale"}]}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///x"}}}"#,
        ]);
        assert!(outcome.clean);
        assert_eq!(outcome.documents_changed, 0);
        assert_eq!(outcome.documents_saved, 1);
        assert_eq!(
            seen,
            vec![
                ("file:///x".to_string(), "v3".to_string()),
                ("file:///x".to_string(), "v3".to_string()),
            ]
        );
        assert!(output.contains("non-monotone didChange version"));
    }

    #[test]
    fn malformed_change_invalidates_text_and_clears_diagnostics() {
        let (outcome, output, seen) = run_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"old"}}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":2},"contentChanges":[{"range":{},"text":"fragment"}]}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didSave","params":{"textDocument":{"uri":"file:///x"}}}"#,
        ]);
        assert!(outcome.clean);
        assert_eq!(seen, vec![("file:///x".to_string(), "old".to_string())]);
        assert_eq!(outcome.documents_changed, 0);
        assert_eq!(outcome.documents_saved, 0);
        assert!(output.contains("unranged Full-sync text change"));
        assert!(output.contains("no retained source exists"));
        assert!(output.contains("\"uri\":\"file:///x\",\"diagnostics\":[]"));
    }

    #[test]
    fn parser_errors_are_recoverable_and_use_null_id() {
        let (outcome, output, _) = run_session(&[
            r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{"bad":tru}}"#,
            r#"{"jsonrpc":"2.0","id":6,"method":"textDocument/hover","params":{}}"#,
        ]);
        assert!(outcome.clean);
        assert!(output.contains("\"id\":null,\"error\":{\"code\":-32700"));
        assert!(output.contains("\"id\":6,\"result\":null"));
    }

    #[test]
    fn missing_or_wrong_jsonrpc_version_is_invalid_request() {
        let (outcome, output, _) = run_session(&[
            r#"{"id":"a","method":"textDocument/hover","params":{}}"#,
            r#"{"jsonrpc":"1.0","id":7,"method":"textDocument/hover","params":{}}"#,
        ]);
        assert!(outcome.clean);
        assert!(output.contains("\"id\":\"a\",\"error\":{\"code\":-32600"));
        assert!(output.contains("\"id\":7,\"error\":{\"code\":-32600"));
    }

    #[test]
    fn request_and_notification_roles_are_enforced() {
        let (outcome, output, _) = run_session(&[
            r#"{"jsonrpc":"2.0","id":10,"method":"textDocument/didOpen","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/hover","params":{}}"#,
        ]);
        assert!(outcome.clean);
        assert!(output.contains("\"id\":10,\"error\":{\"code\":-32600"));
        assert!(output.contains("request-only LSP method sent as a notification"));
    }

    #[test]
    fn unsupported_rpc_is_a_typed_request_failure() {
        let (outcome, output, _) = run_session(&[
            r#"{"jsonrpc":"2.0","id":"rpc","method":"$/lean/rpc/connect","params":{}}"#,
        ]);
        assert!(outcome.clean);
        assert!(output.contains("\"id\":\"rpc\",\"error\":{\"code\":-32803"));
        assert!(output.contains("Lean RPC sessions are not implemented"));
    }

    #[test]
    fn wait_for_diagnostics_completes_immediately_and_after_version_advance() {
        let (outcome, output, _) = run_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"v1"}}}"#,
            r#"{"jsonrpc":"2.0","id":"ready","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":1}}"#,
            r#"{"jsonrpc":"2.0","id":"future","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":3}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":2},"contentChanges":[{"text":"v2"}]}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didChange","params":{"textDocument":{"uri":"file:///x","version":3},"contentChanges":[{"text":"v3"}]}}"#,
        ]);
        assert!(outcome.clean);
        assert!(output.contains("\"id\":\"ready\",\"result\":{}"));
        assert!(output.contains("\"id\":\"future\",\"result\":{}"));
        assert!(!output.contains("\"id\":\"future\",\"error\""));
    }

    #[test]
    fn pending_wait_can_be_cancelled_by_exact_lexical_id() {
        let (outcome, output, _) = run_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"v1"}}}"#,
            r#"{"jsonrpc":"2.0","id":"cancel-me","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":9}}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"cancel-me"}}"#,
        ]);
        assert!(outcome.clean);
        assert!(output.contains(
            "\"id\":\"cancel-me\",\"error\":{\"code\":-32800,\"message\":\"request cancelled\"}"
        ));
        assert_eq!(output.matches("\"id\":\"cancel-me\"").count(), 1);
    }

    #[test]
    fn closing_a_document_fails_its_pending_waits() {
        let (outcome, output, _) = run_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"v1"}}}"#,
            r#"{"jsonrpc":"2.0","id":21,"method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":9}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didClose","params":{"textDocument":{"uri":"file:///x"}}}"#,
        ]);
        assert!(outcome.clean);
        assert!(output.contains("\"id\":21,\"error\":{\"code\":-32803"));
        assert!(output.contains("document closed before the requested diagnostics version"));
    }

    #[test]
    fn invalid_and_duplicate_waits_fail_closed() {
        let (outcome, output, _) = run_session(&[
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"v1"}}}"#,
            r#"{"jsonrpc":"2.0","id":"negative","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":-1}}"#,
            r#"{"jsonrpc":"2.0","id":"duplicate","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":9}}"#,
            r#"{"jsonrpc":"2.0","id":"duplicate","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///x","version":10}}"#,
        ]);
        assert!(outcome.clean);
        assert!(output.contains("\"id\":\"negative\",\"error\":{\"code\":-32602"));
        assert!(output.contains("\"id\":\"duplicate\",\"error\":{\"code\":-32600"));
        assert!(output.contains("duplicate outstanding JSON-RPC request id"));
    }

    #[test]
    fn empty_diagnostic_callback_is_visible_and_clears_stale_state() {
        let mut input = Vec::new();
        for message in [
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///x","version":1,"text":"source"}}}"#,
            r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
            r#"{"jsonrpc":"2.0","method":"exit"}"#,
        ] {
            send(&mut input, message);
        }
        let mut reader = BufReader::new(input.as_slice());
        let mut output = Vec::new();
        let outcome = serve(&mut reader, &mut output, &mut |_, _| Vec::new())
            .expect("serve test session");
        let output = String::from_utf8(output).expect("UTF-8 protocol output");
        assert!(outcome.clean);
        assert!(output.contains("diagnostic-callback-terminal-message"));
        assert!(output.contains("\"authority\":false"));
        assert!(output.contains("\"uri\":\"file:///x\",\"diagnostics\":[]"));
    }

    #[test]
    fn requests_before_initialize_are_server_not_initialized() {
        let mut input = Vec::new();
        send(
            &mut input,
            r#"{"jsonrpc":"2.0","id":5,"method":"textDocument/hover","params":{}}"#,
        );
        send(
            &mut input,
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        );
        send(
            &mut input,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
        );
        send(
            &mut input,
            r#"{"jsonrpc":"2.0","id":99,"method":"shutdown"}"#,
        );
        send(&mut input, r#"{"jsonrpc":"2.0","method":"exit"}"#);
        let mut reader = BufReader::new(input.as_slice());
        let mut output = Vec::new();
        let outcome = serve(&mut reader, &mut output, &mut |_, _| Vec::new())
            .expect("serve test session");
        let output = String::from_utf8(output).expect("UTF-8 protocol output");
        assert!(outcome.clean);
        assert!(output.contains("\"id\":5,\"error\":{\"code\":-32002"));
    }
}
