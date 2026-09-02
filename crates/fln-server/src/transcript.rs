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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TranscriptFrame {
    pub index: u64,
    pub role: TranscriptRole,
    pub method: String,
    /// Exact JSON representation of a request ID; absent for notifications.
    pub id_json: Option<String>,
    pub body_bytes: u64,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TranscriptStats {
    pub frames: u64,
    pub requests: u64,
    pub notifications: u64,
    pub body_bytes: u64,
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
    match envelope.params {
        RawField::Missing => {}
        RawField::Value(value)
            if matches!(value.trim_start().as_bytes().first(), Some(b'{' | b'[')) => {}
        RawField::Value(value)
            if value.trim() == "null" && matches!(method.as_str(), "shutdown" | "exit") => {}
        RawField::Value(_) => {
            return Err(format!(
                "frame {frame} params must be an object or array when present; only shutdown/exit may use null"
            ));
        }
        RawField::Invalid => return Err(format!("frame {frame} has ambiguous params")),
    }
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

pub fn render_validation(stats: TranscriptStats) -> String {
    format!(
        concat!(
            "{{\"schema\":\"fln.lsp-transcript-validation/1\",",
            "\"frames\":{},\"requests\":{},\"notifications\":{},",
            "\"bodyBytes\":{}}}\n"
        ),
        stats.frames, stats.requests, stats.notifications, stats.body_bytes
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
        let mut bytes = Vec::new();
        for body in bodies {
            bytes.extend(frame(body));
        }
        assert_eq!(
            validate_bytes(&bytes).unwrap(),
            TranscriptStats {
                frames: 4,
                requests: 2,
                notifications: 2,
                body_bytes: expected_body_bytes,
            }
        );
    }

    #[test]
    fn frame_summary_preserves_lexical_id_and_role() {
        let request = validate_frame(
            br#"{"jsonrpc":"2.0","id":1.25e2,"method":"shutdown","params":null}"#,
            7,
        )
        .unwrap();
        assert_eq!(request.index, 7);
        assert_eq!(request.role, TranscriptRole::Request);
        assert_eq!(request.method, "shutdown");
        assert_eq!(request.id_json.as_deref(), Some("1.25e2"));

        let notification = validate_frame(
            br#"{"jsonrpc":"2.0","method":"exit","params":null}"#,
            8,
        )
        .unwrap();
        assert_eq!(notification.role, TranscriptRole::Notification);
        assert_eq!(notification.id_json, None);
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
        assert_eq!(stats.body_bytes, u64::try_from(body.len()).unwrap());
    }
}
