//! LSP base protocol transport: Content-Length-framed JSON-RPC over stdio.
//!
//! This module provides the lowest-level transport for the Language Server
//! Protocol. It reads Content-Length-framed messages from a `BufRead` source
//! and writes Content-Length-framed messages to a `Write` sink. No JSON parsing
//! is attempted here; the framing is purely byte-level.
//!
//! The transport layer is intentionally synchronous and single-threaded: the
//! plan calls for asupersync regions at the elaboration layer, not the wire
//! layer. A long-lived server wraps this in a read loop and dispatches.

use std::io::{self, BufRead, Write};

/// Resource ceilings for one framed LSP message.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TransportLimits {
    pub max_message_bytes: usize,
    pub max_header_bytes: usize,
    pub max_header_fields: usize,
}

impl TransportLimits {
    /// FrankenLean's normal stdio LSP limits.
    pub const LSP_DEFAULT: Self = Self {
        max_message_bytes: 64 * 1024 * 1024,
        max_header_bytes: 16 * 1024,
        max_header_fields: 64,
    };

    pub const fn new(
        max_message_bytes: usize,
        max_header_bytes: usize,
        max_header_fields: usize,
    ) -> Self {
        Self {
            max_message_bytes,
            max_header_bytes,
            max_header_fields,
        }
    }
}

impl Default for TransportLimits {
    fn default() -> Self {
        Self::LSP_DEFAULT
    }
}

fn invalid_data(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn read_header_line(
    input: &mut dyn BufRead,
    byte_budget: usize,
    max_header_bytes: usize,
) -> io::Result<Option<Vec<u8>>> {
    let mut line = Vec::new();
    loop {
        let (consumed, terminated) = {
            let available = input.fill_buf()?;
            if available.is_empty() {
                if line.is_empty() {
                    return Ok(None);
                }
                return Err(io::Error::new(
                    io::ErrorKind::UnexpectedEof,
                    "EOF inside LSP header line",
                ));
            }
            let consumed = available
                .iter()
                .position(|byte| *byte == b'\n')
                .map_or(available.len(), |index| index + 1);
            let next_len = line
                .len()
                .checked_add(consumed)
                .ok_or_else(|| invalid_data("LSP header length overflow"))?;
            if next_len > byte_budget {
                return Err(invalid_data(format!(
                    "LSP header block exceeds {max_header_bytes} bytes"
                )));
            }
            line.extend_from_slice(&available[..consumed]);
            (consumed, available.get(consumed - 1).copied() == Some(b'\n'))
        };
        input.consume(consumed);
        if terminated {
            return Ok(Some(line));
        }
    }
}

fn strip_line_ending(line: &[u8]) -> io::Result<&[u8]> {
    line.strip_suffix(b"\r\n")
        .ok_or_else(|| invalid_data("LSP header line must be CRLF-terminated"))
}

fn is_header_name_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric()
        || matches!(
            byte,
            b'!' | b'#'
                | b'$'
                | b'%'
                | b'&'
                | b'\''
                | b'*'
                | b'+'
                | b'-'
                | b'.'
                | b'^'
                | b'_'
                | b'`'
                | b'|'
                | b'~'
        )
}

fn trim_optional_whitespace(mut value: &[u8]) -> &[u8] {
    while value
        .first()
        .is_some_and(|byte| matches!(*byte, b' ' | b'\t'))
    {
        value = &value[1..];
    }
    while value
        .last()
        .is_some_and(|byte| matches!(*byte, b' ' | b'\t'))
    {
        value = &value[..value.len() - 1];
    }
    value
}

fn parse_content_length(value: &[u8]) -> io::Result<usize> {
    if value.is_empty() || value.iter().any(|byte| !byte.is_ascii_digit()) {
        return Err(invalid_data(format!(
            "invalid Content-Length: {:?}",
            String::from_utf8_lossy(value)
        )));
    }
    value.iter().try_fold(0usize, |length, digit| {
        length
            .checked_mul(10)
            .and_then(|value| value.checked_add(usize::from(*digit - b'0')))
            .ok_or_else(|| invalid_data("Content-Length overflows usize"))
    })
}

fn content_type_parameter_value(value: &[u8]) -> io::Result<&[u8]> {
    let starts_quoted = value.first().copied() == Some(b'"');
    let ends_quoted = value.last().copied() == Some(b'"');
    if starts_quoted != ends_quoted {
        return Err(invalid_data("malformed quoted LSP Content-Type parameter"));
    }
    if !starts_quoted {
        if value.is_empty() || value.iter().any(|byte| !is_header_name_byte(*byte)) {
            return Err(invalid_data("malformed LSP Content-Type parameter value"));
        }
        return Ok(value);
    }
    if value.len() < 3 {
        return Err(invalid_data("empty quoted LSP Content-Type parameter"));
    }
    let inner = &value[1..value.len() - 1];
    if inner
        .iter()
        .any(|byte| !is_header_name_byte(*byte) || matches!(*byte, b'"' | b'\\'))
    {
        return Err(invalid_data("malformed quoted LSP Content-Type parameter"));
    }
    Ok(inner)
}

fn validate_content_type(value: &[u8]) -> io::Result<()> {
    let mut parts = value.split(|byte| *byte == b';');
    let media_type = trim_optional_whitespace(parts.next().unwrap_or_default());
    if !media_type.eq_ignore_ascii_case(b"application/vscode-jsonrpc") {
        return Err(invalid_data(format!(
            "unsupported LSP Content-Type media type: {:?}",
            String::from_utf8_lossy(media_type)
        )));
    }

    let mut charset_seen = false;
    for raw_parameter in parts {
        let parameter = trim_optional_whitespace(raw_parameter);
        let Some(equals) = parameter.iter().position(|byte| *byte == b'=') else {
            return Err(invalid_data("malformed LSP Content-Type parameter"));
        };
        let name = trim_optional_whitespace(&parameter[..equals]);
        let parameter_value = content_type_parameter_value(trim_optional_whitespace(
            &parameter[equals + 1..],
        ))?;
        if name.is_empty() {
            return Err(invalid_data("malformed LSP Content-Type parameter"));
        }
        if !name.eq_ignore_ascii_case(b"charset") {
            return Err(invalid_data(format!(
                "unsupported LSP Content-Type parameter: {:?}",
                String::from_utf8_lossy(name)
            )));
        }
        if charset_seen {
            return Err(invalid_data("duplicate LSP Content-Type charset parameter"));
        }
        charset_seen = true;
        if !parameter_value.eq_ignore_ascii_case(b"utf-8")
            && !parameter_value.eq_ignore_ascii_case(b"utf8")
        {
            return Err(invalid_data(format!(
                "unsupported LSP Content-Type charset: {:?}",
                String::from_utf8_lossy(parameter_value)
            )));
        }
    }
    Ok(())
}

/// Read one Content-Length-framed LSP message with caller-selected ceilings.
///
/// Returns `Ok(None)` only on clean EOF before a new header block begins.
/// Partial, ambiguous, oversized, or malformed header blocks fail closed.
pub fn read_message_with_limits(
    input: &mut dyn BufRead,
    limits: TransportLimits,
) -> io::Result<Option<Vec<u8>>> {
    let mut content_length: Option<usize> = None;
    let mut content_type_seen = false;
    let mut header_bytes = 0usize;
    let mut header_fields = 0usize;

    loop {
        let remaining = limits
            .max_header_bytes
            .checked_sub(header_bytes)
            .ok_or_else(|| invalid_data("LSP header byte accounting overflow"))?;
        let Some(line) = read_header_line(input, remaining, limits.max_header_bytes)? else {
            if header_bytes == 0 {
                return Ok(None);
            }
            return Err(io::Error::new(
                io::ErrorKind::UnexpectedEof,
                "EOF before the blank line terminating LSP headers",
            ));
        };
        header_bytes = header_bytes
            .checked_add(line.len())
            .ok_or_else(|| invalid_data("LSP header byte accounting overflow"))?;
        let line = strip_line_ending(&line)?;
        if line.is_empty() {
            break;
        }
        header_fields = header_fields
            .checked_add(1)
            .ok_or_else(|| invalid_data("LSP header field accounting overflow"))?;
        if header_fields > limits.max_header_fields {
            return Err(invalid_data(format!(
                "LSP header block exceeds {} fields",
                limits.max_header_fields
            )));
        }
        if !line.is_ascii()
            || line
                .iter()
                .any(|byte| (*byte < b' ' && *byte != b'\t') || *byte == 0x7f)
        {
            return Err(invalid_data(
                "LSP header contains invalid control or non-ASCII bytes",
            ));
        }
        if matches!(line.first().copied(), Some(b' ' | b'\t')) {
            return Err(invalid_data("folded LSP header fields are not accepted"));
        }
        let Some(colon) = line.iter().position(|byte| *byte == b':') else {
            return Err(invalid_data("LSP header field is missing ':'"));
        };
        let name = &line[..colon];
        if name.is_empty() || name.iter().any(|byte| !is_header_name_byte(*byte)) {
            return Err(invalid_data("LSP header field name is invalid"));
        }
        let value = trim_optional_whitespace(&line[colon + 1..]);
        if name.eq_ignore_ascii_case(b"Content-Length") {
            if content_length.is_some() {
                return Err(invalid_data("duplicate Content-Length header"));
            }
            content_length = Some(parse_content_length(value)?);
        } else if name.eq_ignore_ascii_case(b"Content-Type") {
            if content_type_seen {
                return Err(invalid_data("duplicate Content-Type header"));
            }
            validate_content_type(value)?;
            content_type_seen = true;
        }
    }

    let length = content_length.ok_or_else(|| invalid_data("missing Content-Length header"))?;
    if length > limits.max_message_bytes {
        return Err(invalid_data(format!(
            "Content-Length {length} exceeds transport ceiling {}",
            limits.max_message_bytes
        )));
    }
    let mut body = vec![0u8; length];
    input.read_exact(&mut body)?;
    Ok(Some(body))
}

/// Read one Content-Length-framed LSP message using FrankenLean's defaults.
pub fn read_message(input: &mut dyn BufRead) -> io::Result<Option<Vec<u8>>> {
    read_message_with_limits(input, TransportLimits::LSP_DEFAULT)
}

/// Write one Content-Length-framed LSP message with caller-selected ceilings.
///
/// Oversized messages are refused before any framing bytes are written.
pub fn write_message_with_limits(
    output: &mut dyn Write,
    body: &[u8],
    limits: TransportLimits,
) -> io::Result<()> {
    if body.len() > limits.max_message_bytes {
        return Err(invalid_data(format!(
            "message length {} exceeds transport ceiling {}",
            body.len(),
            limits.max_message_bytes
        )));
    }
    write!(output, "Content-Length: {}\r\n\r\n", body.len())?;
    output.write_all(body)?;
    output.flush()
}

/// Write one Content-Length-framed LSP message using FrankenLean's defaults.
pub fn write_message(output: &mut dyn Write, body: &[u8]) -> io::Result<()> {
    write_message_with_limits(output, body, TransportLimits::LSP_DEFAULT)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufReader;

    fn read(raw: &[u8]) -> io::Result<Option<Vec<u8>>> {
        read_message(&mut BufReader::new(raw))
    }

    #[test]
    fn round_trip_single_message() {
        let payload = b"{\"jsonrpc\":\"2.0\",\"id\":1}";
        let mut buf = Vec::new();
        write_message(&mut buf, payload).unwrap();
        assert_eq!(read(&buf).unwrap().unwrap(), payload);
    }

    #[test]
    fn round_trip_two_messages() {
        let a = b"first";
        let b_msg = b"second";
        let mut buf = Vec::new();
        write_message(&mut buf, a).unwrap();
        write_message(&mut buf, b_msg).unwrap();

        let mut reader = BufReader::new(&buf[..]);
        assert_eq!(read_message(&mut reader).unwrap().unwrap(), a);
        assert_eq!(read_message(&mut reader).unwrap().unwrap(), b_msg);
        assert!(read_message(&mut reader).unwrap().is_none());
    }

    #[test]
    fn header_names_are_case_insensitive_and_extensions_are_accepted() {
        let raw = concat!(
            "content-length:\t2\r\n",
            "Content-Type: application/vscode-jsonrpc; charset=utf-8\r\n",
            "X-Fln-Test: yes\r\n",
            "\r\n{}"
        )
        .as_bytes();
        assert_eq!(read(raw).unwrap().unwrap(), b"{}");
    }

    #[test]
    fn content_type_accepts_only_vscode_jsonrpc_with_utf8() {
        for value in [
            "application/vscode-jsonrpc",
            "APPLICATION/VSCODE-JSONRPC; CHARSET=UTF-8",
            "application/vscode-jsonrpc;charset=utf8",
            "application/vscode-jsonrpc; charset=\"utf-8\"",
            "application/vscode-jsonrpc; charset = \"UTF8\"",
        ] {
            let raw = format!("Content-Length: 2\r\nContent-Type: {value}\r\n\r\n{{}}");
            assert_eq!(read(raw.as_bytes()).unwrap().unwrap(), b"{}", "value={value:?}");
        }

        for value in [
            "application/json; charset=utf-8",
            "application/vscode-jsonrpc; charset=utf-16",
            "application/vscode-jsonrpc; charset=utf-8; charset=utf-8",
            "application/vscode-jsonrpc; boundary=x",
            "application/vscode-jsonrpc; charset",
            "application/vscode-jsonrpc;",
            "application/vscode-jsonrpc; charset=\"utf-8",
            "application/vscode-jsonrpc; charset=utf-8\"",
            "application/vscode-jsonrpc; charset=\"\"",
            "application/vscode-jsonrpc; charset=\"utf\\-8\"",
        ] {
            let raw = format!("Content-Length: 2\r\nContent-Type: {value}\r\n\r\n{{}}");
            let error = read(raw.as_bytes()).unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::InvalidData, "value={value:?}");
        }
    }

    #[test]
    fn duplicate_semantic_headers_are_rejected() {
        for raw in [
            b"Content-Length: 2\r\ncontent-length: 2\r\n\r\n{}".as_slice(),
            b"Content-Length: 2\r\nContent-Type: application/vscode-jsonrpc\r\ncontent-type: application/vscode-jsonrpc\r\n\r\n{}".as_slice(),
        ] {
            let error = read(raw).unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::InvalidData);
            assert!(error.to_string().contains("duplicate"));
        }
    }

    #[test]
    fn malformed_content_lengths_are_rejected() {
        for value in ["", "+2", "-2", "2x", "2 2"] {
            let raw = format!("Content-Length: {value}\r\n\r\n{{}}");
            let error = read(raw.as_bytes()).unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::InvalidData, "value={value:?}");
        }
    }

    #[test]
    fn malformed_header_fields_are_rejected() {
        for raw in [
            b"Content-Length 2\r\n\r\n{}".as_slice(),
            b" Content-Length: 2\r\n\r\n{}".as_slice(),
            b"Content Length: 2\r\n\r\n{}".as_slice(),
            b"Content-Length:\x01 2\r\n\r\n{}".as_slice(),
            b"Content-Length: 2\n\n{}".as_slice(),
        ] {
            assert_eq!(read(raw).unwrap_err().kind(), io::ErrorKind::InvalidData);
        }
    }

    #[test]
    fn missing_content_length_is_an_error() {
        let error = read(b"Content-Type: application/vscode-jsonrpc\r\n\r\n{}").unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("missing Content-Length"));
    }

    #[test]
    fn clean_eof_returns_none_but_partial_headers_do_not() {
        assert!(read(b"").unwrap().is_none());
        for raw in [
            b"Content-Length: 2".as_slice(),
            b"Content-Length: 2\r\n".as_slice(),
        ] {
            assert_eq!(read(raw).unwrap_err().kind(), io::ErrorKind::UnexpectedEof);
        }
    }

    #[test]
    fn truncated_body_is_an_error() {
        let error = read(b"Content-Length: 3\r\n\r\n{}").unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::UnexpectedEof);
    }

    #[test]
    fn custom_limits_are_enforced_before_body_allocation_or_output() {
        let limits = TransportLimits::new(2, 64, 2);
        let mut input = BufReader::new(b"Content-Length: 3\r\n\r\nabc".as_slice());
        let error = read_message_with_limits(&mut input, limits).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("transport ceiling 2"));

        let mut output = Vec::new();
        let error = write_message_with_limits(&mut output, b"abc", limits).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(output.is_empty());
    }

    #[test]
    fn custom_header_byte_and_field_limits_are_enforced() {
        let mut input = BufReader::new(b"Content-Length: 0\r\n\r\n".as_slice());
        let error = read_message_with_limits(&mut input, TransportLimits::new(8, 8, 8))
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("exceeds 8 bytes"));

        let mut input = BufReader::new(b"X-One: yes\r\nContent-Length: 0\r\n\r\n".as_slice());
        let error = read_message_with_limits(&mut input, TransportLimits::new(8, 128, 1))
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("exceeds 1 fields"));
    }

    #[test]
    fn writer_refuses_oversized_message_before_writing() {
        let mut output = Vec::new();
        let error = write_message_with_limits(
            &mut output,
            b"abc",
            TransportLimits::new(2, 1, 1),
        )
        .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(error.to_string().contains("transport ceiling"));
        assert!(output.is_empty());
    }

    #[test]
    fn header_byte_and_field_budgets_fail_closed() {
        let limits = TransportLimits::LSP_DEFAULT;
        let mut oversized = b"X-Test: ".to_vec();
        oversized.extend(std::iter::repeat_n(b'a', limits.max_header_bytes));
        oversized.extend_from_slice(b"\r\n\r\n");
        assert_eq!(
            read(&oversized).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );

        let mut too_many = Vec::new();
        for index in 0..limits.max_header_fields {
            too_many.extend_from_slice(format!("X-{index}: ok\r\n").as_bytes());
        }
        too_many.extend_from_slice(b"Content-Length: 0\r\n\r\n");
        assert_eq!(
            read(&too_many).unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
    }
}
