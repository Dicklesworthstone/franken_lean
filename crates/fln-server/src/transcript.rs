use std::io::{BufRead, BufReader, Cursor};

use crate::json::{DecodedField, EnvelopeError, RawField, RequestIdField};

pub const MAX_TRANSCRIPT_BYTES: u64 = 256 * 1024 * 1024;
pub const MAX_TRANSCRIPT_FRAMES: u64 = 1_000_000;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct TranscriptStats {
    pub frames: u64,
    pub requests: u64,
    pub notifications: u64,
    pub body_bytes: u64,
}

fn validate_envelope(body: &[u8], frame: u64) -> Result<bool, String> {
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
    match envelope.method {
        DecodedField::Valid(_) => {}
        DecodedField::Missing => return Err(format!("frame {frame} is missing a method")),
        DecodedField::Invalid => {
            return Err(format!("frame {frame} has a non-string method"));
        }
    }
    match envelope.params {
        RawField::Missing => {}
        RawField::Value(value)
            if matches!(value.trim_start().as_bytes().first(), Some(b'{' | b'[')) => {}
        RawField::Value(_) => {
            return Err(format!(
                "frame {frame} params must be an object or array when present"
            ));
        }
        RawField::Invalid => return Err(format!("frame {frame} has ambiguous params")),
    }
    match envelope.id {
        RequestIdField::Absent => Ok(false),
        RequestIdField::Valid(_) => Ok(true),
        RequestIdField::Invalid => Err(format!("frame {frame} has an invalid request id")),
    }
}

pub fn validate_reader(input: &mut dyn BufRead) -> Result<TranscriptStats, String> {
    let mut stats = TranscriptStats::default();
    loop {
        let Some(body) = crate::transport::read_message(input)
            .map_err(|error| format!("frame {} transport failure: {error}", stats.frames + 1))?
        else {
            break;
        };
        stats.frames = stats
            .frames
            .checked_add(1)
            .ok_or_else(|| "frame count overflow".to_string())?;
        if stats.frames > MAX_TRANSCRIPT_FRAMES {
            return Err(format!(
                "transcript exceeds the {MAX_TRANSCRIPT_FRAMES}-frame ceiling"
            ));
        }
        stats.body_bytes = stats
            .body_bytes
            .checked_add(u64::try_from(body.len()).unwrap_or(u64::MAX))
            .ok_or_else(|| "transcript byte accounting overflow".to_string())?;
        if stats.body_bytes > MAX_TRANSCRIPT_BYTES {
            return Err(format!(
                "transcript bodies exceed the {MAX_TRANSCRIPT_BYTES}-byte aggregate ceiling"
            ));
        }
        if validate_envelope(&body, stats.frames)? {
            stats.requests = stats
                .requests
                .checked_add(1)
                .ok_or_else(|| "request count overflow".to_string())?;
        } else {
            stats.notifications = stats
                .notifications
                .checked_add(1)
                .ok_or_else(|| "notification count overflow".to_string())?;
        }
    }
    Ok(stats)
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

    #[test]
    fn validates_requests_and_notifications_without_normalizing_ids() {
        let bodies = [
            r#"{"jsonrpc":"2.0","id":1.25e2,"method":"initialize","params":{}}"#,
            r#"{"jsonrpc":"2.0","method":"initialized","params":{}}"#,
            r#"{"jsonrpc":"2.0","id":null,"method":"shutdown"}"#,
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
                frames: 3,
                requests: 2,
                notifications: 1,
                body_bytes: expected_body_bytes,
            }
        );
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
}
