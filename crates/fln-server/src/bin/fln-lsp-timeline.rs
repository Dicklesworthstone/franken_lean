#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fs::File;
use std::io::{Cursor, Read};
use std::path::{Path, PathBuf};
use std::process::ExitCode;

pub use fln_server::{json_string, transport};

#[path = "../json.rs"]
mod json;
#[allow(dead_code)]
#[path = "../session_transcript.rs"]
mod session_transcript;
#[allow(dead_code, unused_imports)]
#[path = "../server_transcript.rs"]
mod server_transcript;
#[path = "../transcript.rs"]
pub mod transcript;
#[path = "../correlation.rs"]
mod correlation;

use json::{
    DecodedField, EnvelopeError, RawField, RequestId, RequestIdField, direct_request_id,
    object_member, object_string_member, parse_envelope, response_error, response_result,
};
use server_transcript::{ServerFrameRole, validate_server_frame};
use transcript::TranscriptRole;

const EVENT_SCHEMA: &str = "fln.lsp-interleaved-event/1";
const TIMELINE_SCHEMA: &str = "fln.lsp-interleaved-timeline/1";
const CAUSALITY_SCHEMA: &str = "fln.lsp-cross-stream-causality/1";
const MAX_TIMELINE_BYTES: u64 = transcript::MAX_TRANSCRIPT_BYTES;
const MAX_TIMELINE_EVENTS: u64 = transcript::MAX_TRANSCRIPT_FRAMES;
const MAX_INNER_WIRE_BYTES: u64 = transcript::MAX_TRANSCRIPT_BYTES;
const USAGE: &str = "Usage: fln-lsp-timeline [--] TIMELINE\n\
\n\
Validate one Content-Length-framed interleaved LSP recording. Every outer frame\n\
must be {\"schema\":\"fln.lsp-interleaved-event/1\",\"direction\":\"client\"|\"server\",\"message\":<JSON-RPC object>}.\n\
The client and server projections must independently satisfy the strict session,\n\
server-transcript, canonical-ID, cancellation, and method-response contracts.\n\
Record order additionally proves that each response follows its request,\n\
initialized follows the initialize response, exit follows the shutdown response,\n\
and every cancellation precedes its target's response. This is event-order\n\
evidence, not a wall-clock, duration, scheduler, or active-work-cancellation claim.\n";

#[derive(Debug, Clone, PartialEq, Eq)]
struct Config {
    timeline: PathBuf,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Command {
    Help,
    Validate(Config),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Direction {
    Client,
    Server,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LifecycleRequest {
    Initialize,
    Shutdown,
    Other,
}

impl LifecycleRequest {
    fn for_method(method: &str) -> Self {
        match method {
            "initialize" => Self::Initialize,
            "shutdown" => Self::Shutdown,
            _ => Self::Other,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RequestEvent {
    request_event: u64,
    lifecycle: LifecycleRequest,
    cancellation_event: Option<u64>,
    response_event: Option<u64>,
}

#[derive(Debug)]
struct TimelineValidator {
    events: u64,
    client_events: u64,
    server_events: u64,
    outer_body_bytes: u64,
    inner_wire_bytes: u64,
    request_id_bytes: u64,
    cancellations: u64,
    cancellations_before_response: u64,
    requests: BTreeMap<String, RequestEvent>,
    client_wire: Vec<u8>,
    server_wire: Vec<u8>,
    initialize_request_event: Option<u64>,
    initialize_response_event: Option<u64>,
    initialized_event: Option<u64>,
    shutdown_request_event: Option<u64>,
    shutdown_response_event: Option<u64>,
    exit_event: Option<u64>,
}

#[derive(Debug, Clone, Copy)]
struct TimelineEvidence {
    events: u64,
    client_events: u64,
    server_events: u64,
    outer_wire_bytes: u64,
    outer_body_bytes: u64,
    inner_wire_bytes: u64,
    request_id_bytes: u64,
    cancellations: u64,
    cancellations_before_response: u64,
    initialize_request_event: u64,
    initialize_response_event: u64,
    initialized_event: u64,
    shutdown_request_event: u64,
    shutdown_response_event: u64,
    exit_event: u64,
    correlation: correlation::CorrelationStats,
}

fn parse_args(arguments: impl IntoIterator<Item = OsString>) -> Result<Command, String> {
    let mut arguments = arguments.into_iter();
    let _program = arguments.next();
    let mut options = true;
    let mut path = None;
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            continue;
        }
        if options && matches!(argument.to_str(), Some("-h" | "--help")) {
            if path.is_some() || arguments.next().is_some() {
                return Err("--help cannot be combined with timeline arguments".to_owned());
            }
            return Ok(Command::Help);
        }
        if options && argument.to_string_lossy().starts_with('-') {
            return Err(format!("unknown option: {}", argument.to_string_lossy()));
        }
        if argument.is_empty() {
            return Err("TIMELINE path must not be empty".to_owned());
        }
        if path.replace(PathBuf::from(argument)).is_some() {
            return Err("exactly one TIMELINE path is required".to_owned());
        }
    }
    let timeline = path.ok_or_else(|| "exactly one TIMELINE path is required".to_owned())?;
    Ok(Command::Validate(Config { timeline }))
}

fn read_bounded(path: &Path) -> Result<Vec<u8>, String> {
    let metadata = std::fs::symlink_metadata(path)
        .map_err(|error| format!("could not inspect timeline {}: {error}", path.display()))?;
    if metadata.file_type().is_symlink() {
        return Err(format!("refusing symlink timeline {}", path.display()));
    }
    if !metadata.is_file() {
        return Err(format!("timeline {} is not a regular file", path.display()));
    }
    if metadata.len() > MAX_TIMELINE_BYTES {
        return Err(format!(
            "timeline {} is {} bytes; the timeline ceiling is {MAX_TIMELINE_BYTES}",
            path.display(),
            metadata.len()
        ));
    }
    let file = File::open(path)
        .map_err(|error| format!("could not open timeline {}: {error}", path.display()))?;
    let mut bytes = Vec::with_capacity(
        usize::try_from(metadata.len())
            .unwrap_or(usize::MAX)
            .min(1024 * 1024),
    );
    file.take(MAX_TIMELINE_BYTES.saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|error| format!("could not read timeline {}: {error}", path.display()))?;
    if u64::try_from(bytes.len()).unwrap_or(u64::MAX) > MAX_TIMELINE_BYTES {
        return Err(format!(
            "timeline {} grew beyond the timeline ceiling while being read",
            path.display()
        ));
    }
    Ok(bytes)
}

fn parsed_event(body: &[u8], event: u64) -> Result<(Direction, &str), String> {
    let text = std::str::from_utf8(body)
        .map_err(|_| format!("event {event} outer body is not valid UTF-8"))?;
    let envelope = parse_envelope(text).map_err(|error| match error {
        EnvelopeError::MalformedJson => format!("event {event} outer body contains malformed JSON"),
        EnvelopeError::NotObject => format!("event {event} outer body is not an object"),
    })?;
    if !matches!(envelope.jsonrpc, DecodedField::Missing)
        || !matches!(envelope.method, DecodedField::Missing)
        || !matches!(envelope.id, RequestIdField::Absent)
        || !matches!(envelope.params, RawField::Missing)
        || !matches!(response_result(text), RawField::Missing)
        || !matches!(response_error(text), RawField::Missing)
    {
        return Err(format!(
            "event {event} outer wrapper must not contain JSON-RPC envelope fields"
        ));
    }
    match object_string_member(RawField::Value(text), "schema") {
        DecodedField::Valid(schema) if schema == EVENT_SCHEMA => {}
        DecodedField::Valid(schema) => {
            return Err(format!(
                "event {event} uses unsupported wrapper schema {schema:?}"
            ));
        }
        DecodedField::Missing => {
            return Err(format!("event {event} outer wrapper is missing schema"));
        }
        DecodedField::Invalid => {
            return Err(format!(
                "event {event} outer wrapper has malformed or duplicate schema"
            ));
        }
    }
    let direction = match object_string_member(RawField::Value(text), "direction") {
        DecodedField::Valid(direction) if direction == "client" => Direction::Client,
        DecodedField::Valid(direction) if direction == "server" => Direction::Server,
        DecodedField::Valid(direction) => {
            return Err(format!(
                "event {event} has unsupported direction {direction:?}"
            ));
        }
        DecodedField::Missing => {
            return Err(format!("event {event} outer wrapper is missing direction"));
        }
        DecodedField::Invalid => {
            return Err(format!(
                "event {event} outer wrapper has malformed or duplicate direction"
            ));
        }
    };
    let message = match object_member(RawField::Value(text), "message") {
        RawField::Value(message) if message.trim_start().starts_with('{') => message,
        RawField::Value(_) => {
            return Err(format!(
                "event {event} message must be a JSON-RPC object"
            ));
        }
        RawField::Missing => {
            return Err(format!("event {event} outer wrapper is missing message"));
        }
        RawField::Invalid => {
            return Err(format!(
                "event {event} outer wrapper has malformed or duplicate message"
            ));
        }
    };
    Ok((direction, message))
}

fn append_inner_wire(
    target: &mut Vec<u8>,
    message: &str,
    retained: &mut u64,
    event: u64,
) -> Result<(), String> {
    let mut framed = Vec::new();
    transport::write_message(&mut framed, message.as_bytes())
        .map_err(|error| format!("event {event} inner framing failed: {error}"))?;
    let frame_bytes = u64::try_from(framed.len())
        .map_err(|_| format!("event {event} inner frame length does not fit u64"))?;
    let next = retained
        .checked_add(frame_bytes)
        .ok_or_else(|| format!("event {event} inner wire-byte accounting overflow"))?;
    if next > MAX_INNER_WIRE_BYTES {
        return Err(format!(
            "event {event} projected client/server wire exceeds the {MAX_INNER_WIRE_BYTES}-byte ceiling"
        ));
    }
    target
        .try_reserve_exact(framed.len())
        .map_err(|_| format!("event {event} could not reserve inner framed bytes"))?;
    target.extend_from_slice(&framed);
    *retained = next;
    Ok(())
}

impl TimelineValidator {
    fn new() -> Self {
        Self {
            events: 0,
            client_events: 0,
            server_events: 0,
            outer_body_bytes: 0,
            inner_wire_bytes: 0,
            request_id_bytes: 0,
            cancellations: 0,
            cancellations_before_response: 0,
            requests: BTreeMap::new(),
            client_wire: Vec::new(),
            server_wire: Vec::new(),
            initialize_request_event: None,
            initialize_response_event: None,
            initialized_event: None,
            shutdown_request_event: None,
            shutdown_response_event: None,
            exit_event: None,
        }
    }

    fn observe(
        &mut self,
        direction: Direction,
        message: &str,
        body_bytes: usize,
    ) -> Result<(), String> {
        let event = self
            .events
            .checked_add(1)
            .ok_or_else(|| "timeline event count overflow".to_owned())?;
        if event > MAX_TIMELINE_EVENTS {
            return Err(format!(
                "timeline exceeds the {MAX_TIMELINE_EVENTS}-event ceiling"
            ));
        }
        if let Some(exit_event) = self.exit_event {
            return Err(format!(
                "event {event} appears after the terminal client exit event {exit_event}"
            ));
        }
        let body_bytes = u64::try_from(body_bytes)
            .map_err(|_| format!("event {event} outer body length does not fit u64"))?;
        self.outer_body_bytes = self
            .outer_body_bytes
            .checked_add(body_bytes)
            .ok_or_else(|| "timeline outer body-byte accounting overflow".to_owned())?;
        match direction {
            Direction::Client => self.observe_client(message, event)?,
            Direction::Server => self.observe_server(message, event)?,
        }
        self.events = event;
        Ok(())
    }

    fn observe_client(&mut self, message: &str, event: u64) -> Result<(), String> {
        let frame_index = self
            .client_events
            .checked_add(1)
            .ok_or_else(|| "client event count overflow".to_owned())?;
        let frame = transcript::validate_frame(message.as_bytes(), frame_index)
            .map_err(|error| format!("event {event} client frame invalid: {error}"))?;
        let envelope = parse_envelope(message).map_err(|error| match error {
            EnvelopeError::MalformedJson => {
                format!("event {event} client message contains malformed JSON")
            }
            EnvelopeError::NotObject => {
                format!("event {event} client message is not a JSON-RPC object")
            }
        })?;

        match frame.role {
            TranscriptRole::Request => {
                let id = frame.id_json.clone().ok_or_else(|| {
                    format!("event {event} client request lost its canonical ID")
                })?;
                if let Some(first) = self.requests.get(&id) {
                    return Err(format!(
                        "event {event} repeats canonical client request ID {id}; first request event was {}",
                        first.request_event
                    ));
                }
                if self.requests.len() >= correlation::MAX_CORRELATED_REQUESTS {
                    return Err(format!(
                        "event {event} exceeds the {}-request-ID ceiling",
                        correlation::MAX_CORRELATED_REQUESTS
                    ));
                }
                let id_bytes = u64::try_from(id.len())
                    .map_err(|_| format!("event {event} request-ID length does not fit u64"))?;
                let next_id_bytes = self
                    .request_id_bytes
                    .checked_add(id_bytes)
                    .ok_or_else(|| format!("event {event} request-ID byte accounting overflow"))?;
                if next_id_bytes > correlation::MAX_CORRELATION_ID_BYTES {
                    return Err(format!(
                        "event {event} canonical request-ID bytes exceed the {}-byte ceiling",
                        correlation::MAX_CORRELATION_ID_BYTES
                    ));
                }
                let lifecycle = LifecycleRequest::for_method(&frame.method);
                match lifecycle {
                    LifecycleRequest::Initialize => {
                        if let Some(first) = self.initialize_request_event {
                            return Err(format!(
                                "event {event} repeats initialize; first initialize request was event {first}"
                            ));
                        }
                        self.initialize_request_event = Some(event);
                    }
                    LifecycleRequest::Shutdown => {
                        if let Some(first) = self.shutdown_request_event {
                            return Err(format!(
                                "event {event} repeats shutdown; first shutdown request was event {first}"
                            ));
                        }
                        self.shutdown_request_event = Some(event);
                    }
                    LifecycleRequest::Other => {}
                }
                self.requests.insert(
                    id,
                    RequestEvent {
                        request_event: event,
                        lifecycle,
                        cancellation_event: None,
                        response_event: None,
                    },
                );
                self.request_id_bytes = next_id_bytes;
            }
            TranscriptRole::Notification => match frame.method.as_str() {
                "initialized" => {
                    let response = self.initialize_response_event.ok_or_else(|| {
                        format!(
                            "event {event} sends initialized before the server initialize response"
                        )
                    })?;
                    if let Some(first) = self.initialized_event {
                        return Err(format!(
                            "event {event} repeats initialized; first initialized event was {first}"
                        ));
                    }
                    if response >= event {
                        return Err(format!(
                            "event {event} initialized does not follow initialize response event {response}"
                        ));
                    }
                    self.initialized_event = Some(event);
                }
                "exit" => {
                    let response = self.shutdown_response_event.ok_or_else(|| {
                        format!(
                            "event {event} sends exit before the server shutdown response"
                        )
                    })?;
                    if response >= event {
                        return Err(format!(
                            "event {event} exit does not follow shutdown response event {response}"
                        ));
                    }
                    self.exit_event = Some(event);
                }
                "$/cancelRequest" => self.observe_cancellation(envelope.params, event)?,
                _ => {}
            },
        }
        append_inner_wire(
            &mut self.client_wire,
            message,
            &mut self.inner_wire_bytes,
            event,
        )?;
        self.client_events = frame_index;
        Ok(())
    }

    fn observe_cancellation(&mut self, params: RawField<'_>, event: u64) -> Result<(), String> {
        let id = match direct_request_id(params) {
            RequestIdField::Valid(id @ (RequestId::Number(_) | RequestId::Text(_))) => id.as_json(),
            RequestIdField::Valid(RequestId::Null) => {
                return Err(format!(
                    "event {event} cancellation target must not be null"
                ));
            }
            RequestIdField::Absent => {
                return Err(format!("event {event} cancellation target is missing"));
            }
            RequestIdField::Invalid => {
                return Err(format!(
                    "event {event} cancellation target is malformed or ambiguous"
                ));
            }
        };
        let request = self.requests.get_mut(&id).ok_or_else(|| {
            format!(
                "event {event} cancellation target {id} has no earlier client request"
            )
        })?;
        if let Some(response) = request.response_event {
            return Err(format!(
                "event {event} cancels request {id} after its server response event {response}"
            ));
        }
        if let Some(first) = request.cancellation_event {
            return Err(format!(
                "event {event} repeats cancellation of request {id}; first cancellation was event {first}"
            ));
        }
        request.cancellation_event = Some(event);
        self.cancellations = self
            .cancellations
            .checked_add(1)
            .ok_or_else(|| "timeline cancellation count overflow".to_owned())?;
        Ok(())
    }

    fn observe_server(&mut self, message: &str, event: u64) -> Result<(), String> {
        let frame_index = self
            .server_events
            .checked_add(1)
            .ok_or_else(|| "server event count overflow".to_owned())?;
        let frame = validate_server_frame(message.as_bytes(), frame_index)
            .map_err(|error| format!("event {event} server frame invalid: {error}"))?;
        if matches!(frame.role, ServerFrameRole::Response(_)) {
            let id = frame
                .id_json
                .as_ref()
                .ok_or_else(|| format!("event {event} server response lost its canonical ID"))?;
            let request = self.requests.get_mut(id).ok_or_else(|| {
                format!(
                    "event {event} server response for canonical ID {id} appears before its client request"
                )
            })?;
            if let Some(first) = request.response_event {
                return Err(format!(
                    "event {event} repeats the response for canonical ID {id}; first response was event {first}"
                ));
            }
            let lifecycle = request.lifecycle;
            let cancellation_event = request.cancellation_event;
            request.response_event = Some(event);
            if cancellation_event.is_some() {
                self.cancellations_before_response = self
                    .cancellations_before_response
                    .checked_add(1)
                    .ok_or_else(|| "cancelled response count overflow".to_owned())?;
            }
            match lifecycle {
                LifecycleRequest::Initialize => {
                    if let Some(first) = self.initialize_response_event {
                        return Err(format!(
                            "event {event} repeats initialize response; first was event {first}"
                        ));
                    }
                    self.initialize_response_event = Some(event);
                }
                LifecycleRequest::Shutdown => {
                    if let Some(first) = self.shutdown_response_event {
                        return Err(format!(
                            "event {event} repeats shutdown response; first was event {first}"
                        ));
                    }
                    self.shutdown_response_event = Some(event);
                }
                LifecycleRequest::Other => {}
            }
        }
        append_inner_wire(
            &mut self.server_wire,
            message,
            &mut self.inner_wire_bytes,
            event,
        )?;
        self.server_events = frame_index;
        Ok(())
    }

    fn finish(self, outer_wire_bytes: u64) -> Result<TimelineEvidence, String> {
        if self.events == 0 {
            return Err("timeline contains no events".to_owned());
        }
        let correlation = correlation::correlate_transcripts(&self.client_wire, &self.server_wire)
            .map_err(|error| format!("projected transcript validation failed: {error}"))?;
        let request_count = u64::try_from(self.requests.len())
            .map_err(|_| "timeline request count does not fit u64".to_owned())?;
        if request_count != correlation.matched_responses {
            return Err(format!(
                "timeline request accounting mismatch: retained {request_count}, correlated {}",
                correlation.matched_responses
            ));
        }
        if self.request_id_bytes != correlation.client_request_id_bytes {
            return Err(format!(
                "timeline request-ID bytes differ from correlation: timeline {}, correlation {}",
                self.request_id_bytes, correlation.client_request_id_bytes
            ));
        }
        if self.cancellations != correlation.client.cancellations {
            return Err(format!(
                "timeline cancellation count differs from client-session evidence: timeline {}, session {}",
                self.cancellations, correlation.client.cancellations
            ));
        }
        if self.cancellations_before_response != self.cancellations {
            return Err(format!(
                "timeline cancellation-response accounting mismatch: {} cancellations, {} responses observed after cancellation",
                self.cancellations, self.cancellations_before_response
            ));
        }
        let projected_inner = u64::try_from(self.client_wire.len())
            .ok()
            .and_then(|client| {
                u64::try_from(self.server_wire.len())
                    .ok()
                    .and_then(|server| client.checked_add(server))
            })
            .ok_or_else(|| "projected inner wire-byte accounting overflow".to_owned())?;
        if projected_inner != self.inner_wire_bytes {
            return Err(format!(
                "timeline inner wire-byte accounting mismatch: retained {projected_inner}, recorded {}",
                self.inner_wire_bytes
            ));
        }
        let event_sum = self
            .client_events
            .checked_add(self.server_events)
            .ok_or_else(|| "timeline direction count overflow".to_owned())?;
        if event_sum != self.events {
            return Err(format!(
                "timeline direction accounting mismatch: {} events, {event_sum} classified",
                self.events
            ));
        }
        let initialize_request_event = self
            .initialize_request_event
            .ok_or_else(|| "timeline has no initialize request event".to_owned())?;
        let initialize_response_event = self
            .initialize_response_event
            .ok_or_else(|| "timeline has no initialize response event".to_owned())?;
        let initialized_event = self
            .initialized_event
            .ok_or_else(|| "timeline has no initialized notification event".to_owned())?;
        let shutdown_request_event = self
            .shutdown_request_event
            .ok_or_else(|| "timeline has no shutdown request event".to_owned())?;
        let shutdown_response_event = self
            .shutdown_response_event
            .ok_or_else(|| "timeline has no shutdown response event".to_owned())?;
        let exit_event = self
            .exit_event
            .ok_or_else(|| "timeline has no exit notification event".to_owned())?;
        if !(initialize_request_event < initialize_response_event
            && initialize_response_event < initialized_event
            && initialized_event < shutdown_request_event
            && shutdown_request_event < shutdown_response_event
            && shutdown_response_event < exit_event)
        {
            return Err(format!(
                "timeline lifecycle order is invalid: initialize request {initialize_request_event}, initialize response {initialize_response_event}, initialized {initialized_event}, shutdown request {shutdown_request_event}, shutdown response {shutdown_response_event}, exit {exit_event}"
            ));
        }
        Ok(TimelineEvidence {
            events: self.events,
            client_events: self.client_events,
            server_events: self.server_events,
            outer_wire_bytes,
            outer_body_bytes: self.outer_body_bytes,
            inner_wire_bytes: self.inner_wire_bytes,
            request_id_bytes: self.request_id_bytes,
            cancellations: self.cancellations,
            cancellations_before_response: self.cancellations_before_response,
            initialize_request_event,
            initialize_response_event,
            initialized_event,
            shutdown_request_event,
            shutdown_response_event,
            exit_event,
            correlation,
        })
    }
}

fn validate_timeline_bytes(bytes: &[u8]) -> Result<TimelineEvidence, String> {
    let outer_wire_bytes = u64::try_from(bytes.len())
        .map_err(|_| "timeline byte length does not fit u64".to_owned())?;
    if outer_wire_bytes > MAX_TIMELINE_BYTES {
        return Err(format!(
            "timeline exceeds the {MAX_TIMELINE_BYTES}-byte aggregate ceiling"
        ));
    }
    let mut input = Cursor::new(bytes);
    let mut validator = TimelineValidator::new();
    loop {
        let event = validator
            .events
            .checked_add(1)
            .ok_or_else(|| "timeline event count overflow".to_owned())?;
        let Some(body) = transport::read_message(&mut input)
            .map_err(|error| format!("event {event} outer transport failure: {error}"))?
        else {
            break;
        };
        let (direction, message) = parsed_event(&body, event)?;
        validator.observe(direction, message, body.len())?;
    }
    if input.position() != outer_wire_bytes {
        return Err(format!(
            "timeline wire-byte accounting mismatch: consumed {}, input {outer_wire_bytes}",
            input.position()
        ));
    }
    validator.finish(outer_wire_bytes)
}

fn render_timeline(evidence: TimelineEvidence) -> String {
    let correlation_json = correlation::render_correlation(evidence.correlation);
    format!(
        concat!(
            "{{\"schema\":{},\"eventSchema\":{},\"causalitySchema\":{},",
            "\"ordering\":\"record-order-v1\",\"events\":{},",
            "\"clientEvents\":{},\"serverEvents\":{},",
            "\"outerWireBytes\":{},\"outerBodyBytes\":{},",
            "\"projectedInnerWireBytes\":{},\"requestIdBytes\":{},",
            "\"eventCeiling\":{},\"timelineByteCeiling\":{},",
            "\"innerWireByteCeiling\":{},\"requestIdCountCeiling\":{},",
            "\"requestIdByteCeiling\":{},",
            "\"initializeRequestEvent\":{},\"initializeResponseEvent\":{},",
            "\"initializedEvent\":{},\"shutdownRequestEvent\":{},",
            "\"shutdownResponseEvent\":{},\"exitEvent\":{},",
            "\"responsesBeforeRequests\":0,",
            "\"initializedBeforeInitializeResponse\":0,",
            "\"exitBeforeShutdownResponse\":0,",
            "\"cancellations\":{},\"cancellationsBeforeResponse\":{},",
            "\"cancellationsAfterResponse\":0,\"eventsAfterExit\":0,",
            "\"correlation\":{}}}\n"
        ),
        json_string(TIMELINE_SCHEMA),
        json_string(EVENT_SCHEMA),
        json_string(CAUSALITY_SCHEMA),
        evidence.events,
        evidence.client_events,
        evidence.server_events,
        evidence.outer_wire_bytes,
        evidence.outer_body_bytes,
        evidence.inner_wire_bytes,
        evidence.request_id_bytes,
        MAX_TIMELINE_EVENTS,
        MAX_TIMELINE_BYTES,
        MAX_INNER_WIRE_BYTES,
        correlation::MAX_CORRELATED_REQUESTS,
        correlation::MAX_CORRELATION_ID_BYTES,
        evidence.initialize_request_event,
        evidence.initialize_response_event,
        evidence.initialized_event,
        evidence.shutdown_request_event,
        evidence.shutdown_response_event,
        evidence.exit_event,
        evidence.cancellations,
        evidence.cancellations_before_response,
        correlation_json.trim_end()
    )
}

fn execute(config: &Config) -> Result<String, String> {
    let bytes = read_bounded(&config.timeline)?;
    validate_timeline_bytes(&bytes).map(render_timeline)
}

fn main() -> ExitCode {
    let command = match parse_args(std::env::args_os()) {
        Ok(command) => command,
        Err(error) => {
            eprintln!("fln-lsp-timeline: {error}\n\n{USAGE}");
            return ExitCode::from(2);
        }
    };
    match command {
        Command::Help => {
            print!("{USAGE}");
            ExitCode::SUCCESS
        }
        Command::Validate(config) => match execute(&config) {
            Ok(receipt) => {
                print!("{receipt}");
                ExitCode::SUCCESS
            }
            Err(error) => {
                eprintln!("fln-lsp-timeline: {error}");
                ExitCode::from(1)
            }
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn outer(direction: &str, message: &str) -> Vec<u8> {
        let body = format!(
            "{{\"schema\":{},\"direction\":{},\"message\":{message}}}",
            json_string(EVENT_SCHEMA),
            json_string(direction)
        );
        let mut framed = Vec::new();
        transport::write_message(&mut framed, body.as_bytes()).unwrap();
        framed
    }

    fn timeline(events: &[(&str, &str)]) -> Vec<u8> {
        let mut bytes = Vec::new();
        for (direction, message) in events {
            bytes.extend(outer(direction, message));
        }
        bytes
    }

    fn valid_events() -> Vec<(&'static str, &'static str)> {
        vec![
            (
                "client",
                r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
            ),
            (
                "server",
                r#"{"jsonrpc":"2.0","id":"init","result":{"capabilities":{}}}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","method":"textDocument/didOpen","params":{"textDocument":{"uri":"file:///A.lean","version":1,"text":"def a := 1"}}}"#,
            ),
            (
                "server",
                r#"{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"textDocument":{"uri":"file:///A.lean"},"processing":[{"kind":1}]}}"#,
            ),
            (
                "server",
                r#"{"jsonrpc":"2.0","method":"textDocument/publishDiagnostics","params":{"uri":"file:///A.lean","diagnostics":[]}}"#,
            ),
            (
                "server",
                r#"{"jsonrpc":"2.0","method":"$/lean/diagnosticOutcome","params":{"schema":"fln.diagnostic-projection/1","outcome":"complete","authority":true,"diagnosticCount":0}}"#,
            ),
            (
                "server",
                r#"{"jsonrpc":"2.0","method":"$/lean/fileProgress","params":{"textDocument":{"uri":"file:///A.lean"},"processing":[]}}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","id":"wait","method":"textDocument/waitForDiagnostics","params":{"uri":"file:///A.lean","version":1}}"#,
            ),
            (
                "server",
                r#"{"jsonrpc":"2.0","id":"wait","result":{}}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","id":"hover","method":"textDocument/hover","params":{}}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"hover"}}"#,
            ),
            (
                "server",
                r#"{"jsonrpc":"2.0","id":"hover","result":null}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            ),
            (
                "server",
                r#"{"jsonrpc":"2.0","id":"shutdown","result":null}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
            ),
        ]
    }

    #[test]
    fn validates_one_interleaved_lifecycle_and_cancellation_order() {
        let bytes = timeline(&valid_events());
        let evidence = validate_timeline_bytes(&bytes).unwrap();
        assert_eq!(evidence.events, 16);
        assert_eq!(evidence.client_events, 8);
        assert_eq!(evidence.server_events, 8);
        assert_eq!(evidence.cancellations, 1);
        assert_eq!(evidence.cancellations_before_response, 1);
        assert_eq!(evidence.initialize_request_event, 1);
        assert_eq!(evidence.initialize_response_event, 2);
        assert_eq!(evidence.initialized_event, 3);
        assert_eq!(evidence.shutdown_request_event, 14);
        assert_eq!(evidence.shutdown_response_event, 15);
        assert_eq!(evidence.exit_event, 16);
        let receipt = render_timeline(evidence);
        assert!(receipt.contains("\"schema\":\"fln.lsp-interleaved-timeline/1\""));
        assert!(receipt.contains("\"causalitySchema\":\"fln.lsp-cross-stream-causality/1\""));
        assert!(receipt.contains("\"cancellationsBeforeResponse\":1"));
        assert!(receipt.contains("\"responsesBeforeRequests\":0"));
        assert!(receipt.contains("\"correlation\":{\"schema\":\"fln.lsp-client-server-correlation/5\""));
    }

    #[test]
    fn rejects_initialized_before_the_initialize_response() {
        let bytes = timeline(&[
            (
                "client",
                r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            ),
        ]);
        let error = validate_timeline_bytes(&bytes).unwrap_err();
        assert!(error.contains("initialized before the server initialize response"));
    }

    #[test]
    fn rejects_a_response_before_its_request() {
        let bytes = timeline(&[(
            "server",
            r#"{"jsonrpc":"2.0","id":"init","result":{"capabilities":{}}}"#,
        )]);
        let error = validate_timeline_bytes(&bytes).unwrap_err();
        assert!(error.contains("appears before its client request"));
    }

    #[test]
    fn rejects_cancellation_after_response() {
        let events = valid_events();
        let mut reordered = events[..11].to_vec();
        reordered.push((
            "server",
            r#"{"jsonrpc":"2.0","id":"hover","result":null}"#,
        ));
        reordered.push((
            "client",
            r#"{"jsonrpc":"2.0","method":"$/cancelRequest","params":{"id":"hover"}}"#,
        ));
        let error = validate_timeline_bytes(&timeline(&reordered)).unwrap_err();
        assert!(error.contains("after its server response event"));
    }

    #[test]
    fn rejects_exit_before_shutdown_response_and_events_after_exit() {
        let exit_too_early = timeline(&[
            (
                "client",
                r#"{"jsonrpc":"2.0","id":"init","method":"initialize","params":{}}"#,
            ),
            (
                "server",
                r#"{"jsonrpc":"2.0","id":"init","result":{"capabilities":{}}}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","id":"shutdown","method":"shutdown","params":null}"#,
            ),
            (
                "client",
                r#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
            ),
        ]);
        assert!(
            validate_timeline_bytes(&exit_too_early)
                .unwrap_err()
                .contains("exit before the server shutdown response")
        );

        let mut after_exit = valid_events();
        after_exit.push((
            "server",
            r#"{"jsonrpc":"2.0","method":"window/logMessage","params":{"type":3,"message":"late"}}"#,
        ));
        assert!(
            validate_timeline_bytes(&timeline(&after_exit))
                .unwrap_err()
                .contains("appears after the terminal client exit event")
        );
    }

    #[test]
    fn outer_wrapper_is_typed_and_not_a_json_rpc_alias() {
        let mut raw = Vec::new();
        transport::write_message(
            &mut raw,
            br#"{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"#,
        )
        .unwrap();
        assert!(
            validate_timeline_bytes(&raw)
                .unwrap_err()
                .contains("must not contain JSON-RPC envelope fields")
        );
    }

    #[test]
    fn argument_parser_is_exact_and_honors_end_of_options() {
        assert_eq!(
            parse_args(["fln-lsp-timeline", "session.timeline"].map(OsString::from)),
            Ok(Command::Validate(Config {
                timeline: PathBuf::from("session.timeline"),
            }))
        );
        assert_eq!(
            parse_args(
                ["fln-lsp-timeline", "--", "--session.timeline"].map(OsString::from)
            ),
            Ok(Command::Validate(Config {
                timeline: PathBuf::from("--session.timeline"),
            }))
        );
        for arguments in [
            vec!["fln-lsp-timeline"],
            vec!["fln-lsp-timeline", "one", "two"],
            vec!["fln-lsp-timeline", "--unknown"],
        ] {
            assert!(parse_args(arguments.into_iter().map(OsString::from)).is_err());
        }
    }
}
