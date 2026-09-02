use std::io::{self, BufRead, BufReader, Cursor, Read};

use crate::json::{DecodedField, EnvelopeError, RawField, RequestIdField};

/// Maximum aggregate bytes consumed from one complete framed transcript.
///
/// This covers extension headers, Content-Length framing, separators, and JSON
/// bodies. Counting bodies alone would let many legal per-frame headers evade
/// the aggregate resource ceiling.
pub const MAX_TRANSCRIPT_BYTES: u64 = 256 * 1024 * 1024;
pub const MAX_TRANSCRIPT_FRAMES: u64 = 1_000_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TranscriptRole {
    Request,
    Notification,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TranscriptParamsKind {
    Missing,
    Object,
    Array,
    Null,
}

impl TranscriptParamsKind {
    const fn name(self) -> &'static str {
        match self {
            Self::Missing => "missing",
            Self::Object => "object",
            Self::Array => "array",
            Self::Null => "null",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TranscriptFrame {
    pub index: u64,
    pub role: TranscriptRole,
    pub method: String,
    /// Exact JSON representation of a request ID; absent for notifications.
    pub id_json: Option<String>,
    pub params_kind: TranscriptParamsKind,
    pub body_bytes: u64,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TranscriptStats {
    pub frames: u64,
    pub requests: u64,
    pub notifications: u64,
    /// Complete bytes consumed from the framed wire, including headers and separators.
    pub wire_bytes: u64,
    /// JSON body bytes only, retained separately to expose framing overhead.
    pub body_bytes: u64,
}

/// Evidence that one client transcript completed the bounded LSP lifecycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClientLifecycleStats {
    pub transcript: TranscriptStats,
    pub initialize_frame: u64,
    pub initialized_frame: u64,
    pub shutdown_frame: u64,
    pub exit_frame: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KnownMethodRole {
    Request,
    Notification,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum KnownParamsContract {
    Object,
    OptionalEmpty,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct KnownMethodContract {
    role: KnownMethodRole,
    params: KnownParamsContract,
}

const fn request(params: KnownParamsContract) -> KnownMethodContract {
    KnownMethodContract {
        role: KnownMethodRole::Request,
        params,
    }
}

const fn notification(params: KnownParamsContract) -> KnownMethodContract {
    KnownMethodContract {
        role: KnownMethodRole::Notification,
        params,
    }
}

fn known_method_contract(method: &str) -> Option<KnownMethodContract> {
    match method {
        "initialize"
        | "$/lean/plainGoal"
        | "$/lean/plainTermGoal"
        | "$/lean/rpc/connect"
        | "$/lean/rpc/call"
        | "textDocument/completion"
        | "textDocument/definition"
        | "textDocument/hover"
        | "textDocument/waitForDiagnostics" => Some(request(KnownParamsContract::Object)),
        "shutdown" => Some(request(KnownParamsContract::OptionalEmpty)),
        "initialized"
        | "$/cancelRequest"
        | "$/lean/rpc/keepAlive"
        | "$/lean/rpc/release"
        | "textDocument/didOpen"
        | "textDocument/didChange"
        | "textDocument/didSave"
        | "textDocument/didClose" => Some(notification(KnownParamsContract::Object)),
        "exit" => Some(notification(KnownParamsContract::OptionalEmpty)),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ClientLifecycleState {
    BeforeInitialize,
    AwaitingInitialized,
    Running,
    AwaitingExit,
    Exited,
}

impl ClientLifecycleState {
    const fn name(self) -> &'static str {
        match self {
            Self::BeforeInitialize => "before-initialize",
            Self::AwaitingInitialized => "awaiting-initialized",
            Self::Running => "running",
            Self::AwaitingExit => "awaiting-exit",
            Self::Exited => "exited",
        }
    }
}

#[derive(Debug)]
struct ClientLifecycleValidator {
    state: ClientLifecycleState,
    initialize_frame: Option<u64>,
    initialized_frame: Option<u64>,
    shutdown_frame: Option<u64>,
    exit_frame: Option<u64>,
}

impl ClientLifecycleValidator {
    fn new() -> Self {
        Self {
            state: ClientLifecycleState::BeforeInitialize,
            initialize_frame: None,
            initialized_frame: None,
            shutdown_frame: None,
            exit_frame: None,
        }
    }

    fn validate_contract(frame: &TranscriptFrame) -> Result<(), String> {
        let Some(contract) = known_method_contract(&frame.method) else {
            return Ok(());
        };
        match (contract.role, frame.role) {
            (KnownMethodRole::Request, TranscriptRole::Notification) => {
                return Err(format!(
                    "frame {} sends request-only method {:?} as a notification",
                    frame.index, frame.method
                ));
            }
            (KnownMethodRole::Notification, TranscriptRole::Request) => {
                return Err(format!(
                    "frame {} sends notification-only method {:?} as a request",
                    frame.index, frame.method
                ));
            }
            _ => {}
        }
        match (contract.params, frame.params_kind) {
            (KnownParamsContract::Object, TranscriptParamsKind::Object)
            | (
                KnownParamsContract::OptionalEmpty,
                TranscriptParamsKind::Missing | TranscriptParamsKind::Null,
            ) => Ok(()),
            (KnownParamsContract::Object, observed) => Err(format!(
                "frame {} method {:?} requires object params, observed {}",
                frame.index,
                frame.method,
                observed.name()
            )),
            (KnownParamsContract::OptionalEmpty, observed) => Err(format!(
                "frame {} method {:?} permits only missing or null params, observed {}",
                frame.index,
                frame.method,
                observed.name()
            )),
        }
    }

    fn observe(&mut self, frame: &TranscriptFrame) -> Result<(), String> {
        Self::validate_contract(frame)?;
        match self.state {
            ClientLifecycleState::BeforeInitialize => {
                if frame.method != "initialize" {
                    return Err(format!(
                        "frame {} method {:?} appears before the initialize request",
                        frame.index, frame.method
                    ));
                }
                self.initialize_frame = Some(frame.index);
                self.state = ClientLifecycleState::AwaitingInitialized;
            }
            ClientLifecycleState::AwaitingInitialized => {
                if frame.method == "$/cancelRequest" {
                    return Ok(());
                }
                if frame.method != "initialized" {
                    return Err(format!(
                        "frame {} method {:?} appears before the initialized notification",
                        frame.index, frame.method
                    ));
                }
                self.initialized_frame = Some(frame.index);
                self.state = ClientLifecycleState::Running;
            }
            ClientLifecycleState::Running => match frame.method.as_str() {
                "initialize" | "initialized" => {
                    return Err(format!(
                        "frame {} repeats initialization while the client is running",
                        frame.index
                    ));
                }
                "exit" => {
                    return Err(format!(
                        "frame {} exits before the shutdown request",
                        frame.index
                    ));
                }
                "shutdown" => {
                    self.shutdown_frame = Some(frame.index);
                    self.state = ClientLifecycleState::AwaitingExit;
                }
                _ => {}
            },
            ClientLifecycleState::AwaitingExit => {
                if frame.method != "exit" {
                    return Err(format!(
                        "frame {} method {:?} appears after shutdown; expected exit",
                        frame.index, frame.method
                    ));
                }
                self.exit_frame = Some(frame.index);
                self.state = ClientLifecycleState::Exited;
            }
            ClientLifecycleState::Exited => {
                return Err(format!(
                    "frame {} method {:?} appears after the terminal exit notification",
                    frame.index, frame.method
                ));
            }
        }
        Ok(())
    }

    fn finish(self, transcript: TranscriptStats) -> Result<ClientLifecycleStats, String> {
        if self.state != ClientLifecycleState::Exited {
            return Err(format!(
                "transcript ended in client lifecycle state {}; expected exited",
                self.state.name()
            ));
        }
        Ok(ClientLifecycleStats {
            transcript,
            initialize_frame: self
                .initialize_frame
                .ok_or_else(|| "missing initialize-frame evidence".to_string())?,
            initialized_frame: self
                .initialized_frame
                .ok_or_else(|| "missing initialized-frame evidence".to_string())?,
            shutdown_frame: self
                .shutdown_frame
                .ok_or_else(|| "missing shutdown-frame evidence".to_string())?,
            exit_frame: self
                .exit_frame
                .ok_or_else(|| "missing exit-frame evidence".to_string())?,
        })
    }
}

struct CountingBufRead<'a> {
    inner: &'a mut dyn BufRead,
    wire_bytes: u64,
    overflowed: bool,
}

impl<'a> CountingBufRead<'a> {
    fn new(inner: &'a mut dyn BufRead) -> Self {
        Self {
            inner,
            wire_bytes: 0,
            overflowed: false,
        }
    }

    fn record(&mut self, amount: usize) {
        let Ok(amount) = u64::try_from(amount) else {
            self.overflowed = true;
            self.wire_bytes = u64::MAX;
            return;
        };
        let Some(next) = self.wire_bytes.checked_add(amount) else {
            self.overflowed = true;
            self.wire_bytes = u64::MAX;
            return;
        };
        self.wire_bytes = next;
    }
}

impl Read for CountingBufRead<'_> {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        let amount = self.inner.read(buffer)?;
        self.record(amount);
        Ok(amount)
    }
}

impl BufRead for CountingBufRead<'_> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        self.inner.fill_buf()
    }

    fn consume(&mut self, amount: usize) {
        self.inner.consume(amount);
        self.record(amount);
    }
}

pub fn validate_frame(body: &[u8], frame: u64) -> Result<TranscriptFrame, String> {
    let text = std::str::from_utf8(body)
        .map_err(|_| format!("frame {frame} body is not valid UTF-8"))?;
    let envelope = crate::json::parse_envelope(text).map_err(|error| match error {
        EnvelopeError::MalformedJson => format!("frame {frame} contains malformed JSON"),
        EnvelopeError::NotObject => format!("frame {frame} is not a JSON-RPC object"),
    })?;
    match envelope.jsonrpc {
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
    let method = match envelope.method {
        DecodedField::Valid(method) => method,
        DecodedField::Missing => return Err(format!("frame {frame} is missing a method")),
        DecodedField::Invalid => {
            return Err(format!("frame {frame} has a non-string method"));
        }
    };
    let params_kind = match envelope.params {
        RawField::Missing => TranscriptParamsKind::Missing,
        RawField::Value(value) if value.trim_start().starts_with('{') => {
            TranscriptParamsKind::Object
        }
        RawField::Value(value) if value.trim_start().starts_with('[') => {
            TranscriptParamsKind::Array
        }
        RawField::Value(value)
            if value.trim() == "null" && matches!(method.as_str(), "shutdown" | "exit") =>
        {
            TranscriptParamsKind::Null
        }
        RawField::Value(_) => {
            return Err(format!(
                "frame {frame} params must be an object or array when present; only shutdown/exit may use null"
            ));
        }
        RawField::Invalid => return Err(format!("frame {frame} has ambiguous params")),
    };
    let (role, id_json) = match envelope.id {
        RequestIdField::Absent => (TranscriptRole::Notification, None),
        RequestIdField::Valid(id) => (TranscriptRole::Request, Some(id.as_json())),
        RequestIdField::Invalid => {
            return Err(format!("frame {frame} has an invalid request id"));
        }
    };
    let body_bytes = u64::try_from(body.len())
        .map_err(|_| format!("frame {frame} body length does not fit u64"))?;
    Ok(TranscriptFrame {
        index: frame,
        role,
        method,
        id_json,
        params_kind,
        body_bytes,
    })
}

fn visit_reader_with_limits<F>(
    input: &mut dyn BufRead,
    max_wire_bytes: u64,
    max_frames: u64,
    mut visitor: F,
) -> Result<TranscriptStats, String>
where
    F: FnMut(&TranscriptFrame) -> Result<(), String>,
{
    let mut input = CountingBufRead::new(input);
    let mut stats = TranscriptStats::default();
    loop {
        let frame_index = stats
            .frames
            .checked_add(1)
            .ok_or_else(|| "frame count overflow".to_string())?;
        let Some(body) = crate::transport::read_message(&mut input)
            .map_err(|error| format!("frame {frame_index} transport failure: {error}"))?
        else {
            break;
        };
        if frame_index > max_frames {
            return Err(format!(
                "transcript exceeds the {max_frames}-frame ceiling"
            ));
        }
        if input.overflowed {
            return Err("transcript wire-byte accounting overflow".to_string());
        }
        if input.wire_bytes > max_wire_bytes {
            return Err(format!(
                "transcript wire bytes exceed the {max_wire_bytes}-byte aggregate ceiling while reading frame {frame_index}"
            ));
        }
        let frame = validate_frame(&body, frame_index)?;
        visitor(&frame)?;
        stats.frames = frame_index;
        stats.wire_bytes = input.wire_bytes;
        stats.body_bytes = stats
            .body_bytes
            .checked_add(frame.body_bytes)
            .ok_or_else(|| "transcript body-byte accounting overflow".to_string())?;
        match frame.role {
            TranscriptRole::Request => {
                stats.requests = stats
                    .requests
                    .checked_add(1)
                    .ok_or_else(|| "request count overflow".to_string())?;
            }
            TranscriptRole::Notification => {
                stats.notifications = stats
                    .notifications
                    .checked_add(1)
                    .ok_or_else(|| "notification count overflow".to_string())?;
            }
        }
    }
    Ok(stats)
}

pub fn visit_reader<F>(
    input: &mut dyn BufRead,
    max_frames: u64,
    visitor: F,
) -> Result<TranscriptStats, String>
where
    F: FnMut(&TranscriptFrame) -> Result<(), String>,
{
    visit_reader_with_limits(input, MAX_TRANSCRIPT_BYTES, max_frames, visitor)
}

pub fn validate_reader(input: &mut dyn BufRead) -> Result<TranscriptStats, String> {
    visit_reader(input, MAX_TRANSCRIPT_FRAMES, |_| Ok(()))
}

pub fn validate_bytes(bytes: &[u8]) -> Result<TranscriptStats, String> {
    validate_reader(&mut BufReader::new(Cursor::new(bytes)))
}

/// Validate one complete client transcript through the LSP lifecycle.
///
/// This is intentionally stricter than [`validate_reader`]. Syntax-only
/// validation remains useful for negative replay fixtures; lifecycle validation
/// establishes that the client performed a role-correct initialize, initialized,
/// shutdown, and exit handshake and emitted no frame after exit.
pub fn validate_client_lifecycle_reader(
    input: &mut dyn BufRead,
) -> Result<ClientLifecycleStats, String> {
    let mut lifecycle = ClientLifecycleValidator::new();
    let transcript = visit_reader(input, MAX_TRANSCRIPT_FRAMES, |frame| {
        lifecycle.observe(frame)
    })?;
    lifecycle.finish(transcript)
}

pub fn validate_client_lifecycle_bytes(bytes: &[u8]) -> Result<ClientLifecycleStats, String> {
    validate_client_lifecycle_reader(&mut BufReader::new(Cursor::new(bytes)))
}

pub fn render_validation(stats: TranscriptStats) -> String {
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-transcript-validation/2\",",
            "\"frames\":{},\"requests\":{},\"notifications\":{},",
            "\"wireBytes\":{},\"bodyBytes\":{}}}\n"
        ),
        stats.frames,
        stats.requests,
        stats.notifications,
        stats.wire_bytes,
        stats.body_bytes
    )
}

pub fn render_client_lifecycle_validation(stats: ClientLifecycleStats) -> String {
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-client-lifecycle/1\",",
            "\"finalState\":\"exited\",\"frames\":{},\"requests\":{},",
            "\"notifications\":{},\"wireBytes\":{},\"bodyBytes\":{},",
            "\"initializeFrame\":{},\"initializedFrame\":{},",
            "\"shutdownFrame\":{},\"exitFrame\":{}}}\n"
        ),
        stats.transcript.frames,
        stats.transcript.requests,
        stats.transcript.notifications,
        stats.transcript.wire_bytes,
        stats.transcript.body_bytes,
        stats.initialize_frame,
        stats.initialized_frame,
        stats.shutdown_frame,
        stats.exit_frame
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
        let mut transcript = Vec::new();
        for body in bodies {
            transcript.extend(frame(body));
        }
        transcript
    }

    fn lifecycle() -> Vec<u8> {
        framed(&[
            r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"hover","method":"textDocument/hover","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ])
    }

    fn frame_with_extension(body: &str, padding: usize) -> Vec<u8> {
        format!(
            "X-Padding: {}\r\nContent-Length: {}\r\n\r\n{}",
            "x".repeat(padding),
            body.len(),
            body
        )
        .into_bytes()
    }

    #[test]
    fn validates_requests_and_notifications_without_normalizing_ids() {
        let bodies = [
            r#"{"jsonrpc":"2.0","id":1.25e2,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":null,"method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ];
        let expected_body_bytes = bodies
            .iter()
            .map(|body| u64::try_from(body.len()).unwrap())
            .sum();
        let bytes = framed(&bodies);
        let expected_wire_bytes = u64::try_from(bytes.len()).unwrap();
        assert_eq!(
            validate_bytes(&bytes).unwrap(),
            TranscriptStats {
                frames: 4,
                requests: 2,
                notifications: 2,
                wire_bytes: expected_wire_bytes,
                body_bytes: expected_body_bytes,
            }
        );
    }

    #[test]
    fn frame_summary_preserves_lexical_id_role_and_params_kind() {
        let request = validate_frame(
            br#"{"jsonrpc":"2.0","id":1.25e2,"method":"shutdown","params":null}"#,
            7,
        )
        .unwrap();
        assert_eq!(request.index, 7);
        assert_eq!(request.role, TranscriptRole::Request);
        assert_eq!(request.method, "shutdown");
        assert_eq!(request.id_json.as_deref(), Some("1.25e2"));
        assert_eq!(request.params_kind, TranscriptParamsKind::Null);

        let notification = validate_frame(
            br#"{"jsonrpc":"2.0","method":"exit"}"#,
            8,
        )
        .unwrap();
        assert_eq!(notification.role, TranscriptRole::Notification);
        assert_eq!(notification.id_json, None);
        assert_eq!(notification.params_kind, TranscriptParamsKind::Missing);

        let object = validate_frame(
            br#"{"jsonrpc":"2.0","id":9,"method":"initialize","params":{}}"#,
            9,
        )
        .unwrap();
        assert_eq!(object.params_kind, TranscriptParamsKind::Object);

        let array = validate_frame(
            br#"{"jsonrpc":"2.0","id":10,"method":"extension/method","params":[]}"#,
            10,
        )
        .unwrap();
        assert_eq!(array.params_kind, TranscriptParamsKind::Array);
    }

    #[test]
    fn optional_empty_null_params_are_lifecycle_specific() {
        for body in [
            r#"{"jsonrpc":"2.0","id":1,"method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
        ] {
            validate_bytes(&frame(body)).expect("pinned lifecycle null params are valid");
        }
        for body in [
            r#"{"jsonrpc":"2.0","method":"initialized","params":null}"#,
            r#"{"jsonrpc":"2.0","id":1,"method":"textDocument/hover","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit","params":false}"#,
        ] {
            let error = validate_bytes(&frame(body)).unwrap_err();
            assert!(error.contains("only shutdown/exit may use null"), "{error}");
        }
    }

    #[test]
    fn names_the_first_invalid_frame_and_reason() {
        for (body, reason) in [
            (r#"{"jsonrpc":"2.0","method":3}"#, "non-string method"),
            (
                r#"{"jsonrpc":"1.0","method":"x"}"#,
                "unsupported JSON-RPC version",
            ),
            (
                r#"{"jsonrpc":"2.0","method":"x","params":3}"#,
                "params must be an object or array",
            ),
            (r#"[]"#, "not a JSON-RPC object"),
            (r#"{"jsonrpc":"2.0","method":"x",}"#, "malformed JSON"),
        ] {
            let error = validate_bytes(&frame(body)).unwrap_err();
            assert!(error.contains("frame 1"));
            assert!(error.contains(reason), "{error}");
        }
    }

    #[test]
    fn visitor_observes_validated_frames_in_wire_order() {
        let mut transcript = frame(r#"{"jsonrpc":"2.0","id":"a","method":"first"}"#);
        transcript.extend(frame(r#"{"jsonrpc":"2.0","method":"second"}"#));
        let expected_wire_bytes = u64::try_from(transcript.len()).unwrap();
        let mut observed = Vec::new();
        let stats = visit_reader(
            &mut BufReader::new(Cursor::new(transcript)),
            10,
            |frame| {
                observed.push((frame.index, frame.role, frame.method.clone()));
                Ok(())
            },
        )
        .unwrap();
        assert_eq!(
            observed,
            vec![
                (1, TranscriptRole::Request, "first".to_string()),
                (2, TranscriptRole::Notification, "second".to_string()),
            ]
        );
        assert_eq!(stats.frames, 2);
        assert_eq!(stats.wire_bytes, expected_wire_bytes);
    }

    #[test]
    fn aggregate_limit_counts_extension_headers_and_framing() {
        let body = r#"{"jsonrpc":"2.0","method":"initialized"}"#;
        let one = frame_with_extension(body, 64);
        let one_len = u64::try_from(one.len()).unwrap();
        let mut transcript = one.clone();
        transcript.extend_from_slice(&one);

        let error = visit_reader_with_limits(
            &mut BufReader::new(Cursor::new(transcript)),
            one_len + 1,
            10,
            |_| Ok(()),
        )
        .unwrap_err();
        assert!(error.contains("wire bytes"));
        assert!(error.contains("frame 2"));

        let stats = visit_reader_with_limits(
            &mut BufReader::new(Cursor::new(one)),
            one_len,
            10,
            |_| Ok(()),
        )
        .unwrap();
        assert_eq!(stats.frames, 1);
        assert_eq!(stats.wire_bytes, one_len);
        assert_eq!(stats.body_bytes, u64::try_from(body.len()).unwrap());
    }

    #[test]
    fn client_lifecycle_receipt_binds_all_handshake_frames() {
        let bytes = lifecycle();
        let stats = validate_client_lifecycle_bytes(&bytes).unwrap();
        assert_eq!(stats.transcript.frames, 5);
        assert_eq!(stats.initialize_frame, 1);
        assert_eq!(stats.initialized_frame, 2);
        assert_eq!(stats.shutdown_frame, 4);
        assert_eq!(stats.exit_frame, 5);
        assert_eq!(
            stats.transcript.wire_bytes,
            u64::try_from(bytes.len()).unwrap()
        );
        assert!(
            render_client_lifecycle_validation(stats)
                .contains("\"schema\":\"fln.lsp-client-lifecycle/1\"")
        );
    }

    #[test]
    fn client_lifecycle_rejects_known_role_inversions() {
        for bodies in [
            vec![r#"{"jsonrpc":"2.0","method":"initialize","params":{}}"#],
            vec![
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                r#"{"jsonrpc":"2.0","id":2,"method":"initialized","params":{}}"#,
            ],
            vec![
                r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
                r#"{"jsonrpc":"2.0","id":3,"method":"textDocument/didOpen","params":{}}"#,
            ],
        ] {
            let error = validate_client_lifecycle_bytes(&framed(&bodies)).unwrap_err();
            assert!(
                error.contains("request-only") || error.contains("notification-only"),
                "{error}"
            );
        }
    }

    #[test]
    fn client_lifecycle_rejects_known_parameter_shape_mismatches() {
        let cases = [
            (
                vec![r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":[]}"#],
                "requires object params",
            ),
            (
                vec![
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                    r#"{"jsonrpc":"2.0","method":"initialized"}"#,
                ],
                "requires object params",
            ),
            (
                vec![
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                    r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
                    r#"{"jsonrpc":"2.0","id":2,"method":"textDocument/hover","params":[]}"#,
                ],
                "requires object params",
            ),
            (
                vec![
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                    r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
                    r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":{}}"#,
                ],
                "permits only missing or null params",
            ),
            (
                vec![
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                    r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
                    r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#,
                    r#"{"jsonrpc":"2.0","method":"exit","params":{}}"#,
                ],
                "permits only missing or null params",
            ),
        ];
        for (bodies, expected) in cases {
            let error = validate_client_lifecycle_bytes(&framed(&bodies)).unwrap_err();
            assert!(error.contains(expected), "expected {expected:?}: {error}");
        }
    }

    #[test]
    fn client_lifecycle_rejects_ordering_and_incomplete_eof() {
        let cases = [
            (
                vec![r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#],
                "before the initialize request",
            ),
            (
                vec![
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                    r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#,
                ],
                "before the initialized notification",
            ),
            (
                vec![
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                    r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
                    r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
                ],
                "exits before the shutdown request",
            ),
            (
                vec![
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                    r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
                    r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#,
                ],
                "expected exited",
            ),
            (
                vec![
                    r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
                    r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
                    r#"{"jsonrpc":"2.0","id":2,"method":"shutdown","params":null}"#,
                    r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
                    r#"{"jsonrpc":"2.0","method":"workspace/didChangeConfiguration","params":{}}"#,
                ],
                "after the terminal exit notification",
            ),
        ];
        for (bodies, expected) in cases {
            let error = validate_client_lifecycle_bytes(&framed(&bodies)).unwrap_err();
            assert!(error.contains(expected), "expected {expected:?}: {error}");
        }
    }

    #[test]
    fn syntax_only_mode_still_accepts_negative_lifecycle_fixtures() {
        let bytes = frame(r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#);
        assert!(validate_bytes(&bytes).is_ok());
        assert!(validate_client_lifecycle_bytes(&bytes).is_err());
    }

    #[test]
    fn cancellation_may_precede_initialized_but_unknown_running_methods_are_extensible() {
        let bytes = framed(&[
            r#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":1}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"workspace/futureNotification","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":2,"method":"workspace/futureRequest","params":[]}"#,
            r#"{"jsonrpc":"2.0","id":3,"method":"shutdown","params":null}"#,
            r#"{"jsonrpc":"2.0","method":"exit"}"#,
        ]);
        assert!(validate_client_lifecycle_bytes(&bytes).is_ok());
    }
}
