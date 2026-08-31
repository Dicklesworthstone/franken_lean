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

/// Maximum message size the transport will accept (64 MiB). This is a
/// transport-level safety ceiling, not a semantic limit.
const MAX_MESSAGE_BYTES: usize = 64 * 1024 * 1024;

/// Read one Content-Length-framed LSP message from `input`.
///
/// Returns `Ok(None)` on clean EOF (no partial header). Returns an error on
/// malformed headers, missing Content-Length, or messages exceeding the
/// transport ceiling.
pub fn read_message(input: &mut dyn BufRead) -> io::Result<Option<Vec<u8>>> {
    let mut content_length: Option<usize> = None;
    loop {
        let mut line = String::new();
        let n = input.read_line(&mut line)?;
        if n == 0 {
            // Clean EOF.
            return Ok(None);
        }
        let trimmed = line.trim_end_matches(['\r', '\n']);
        if trimmed.is_empty() {
            // End of headers.
            break;
        }
        if let Some(value) = trimmed.strip_prefix("Content-Length:") {
            let value = value.trim();
            content_length = Some(value.parse::<usize>().map_err(|_| {
                io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("invalid Content-Length: {value:?}"),
                )
            })?);
        }
        // Content-Type and other headers are accepted and ignored per spec.
    }
    let length = content_length.ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            "missing Content-Length header",
        )
    })?;
    if length > MAX_MESSAGE_BYTES {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("Content-Length {length} exceeds transport ceiling {MAX_MESSAGE_BYTES}"),
        ));
    }
    let mut body = vec![0u8; length];
    input.read_exact(&mut body)?;
    Ok(Some(body))
}

/// Write one Content-Length-framed LSP message to `output`.
pub fn write_message(output: &mut dyn Write, body: &[u8]) -> io::Result<()> {
    write!(output, "Content-Length: {}\r\n\r\n", body.len())?;
    output.write_all(body)?;
    output.flush()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::BufReader;

    #[test]
    fn round_trip_single_message() {
        let payload = b"{\"jsonrpc\":\"2.0\",\"id\":1}";
        let mut buf = Vec::new();
        write_message(&mut buf, payload).unwrap();

        let mut reader = BufReader::new(&buf[..]);
        let got = read_message(&mut reader).unwrap().unwrap();
        assert_eq!(got, payload);
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
    fn missing_content_length_is_an_error() {
        let raw = b"\r\n{\"x\":1}";
        let mut reader = BufReader::new(&raw[..]);
        assert!(read_message(&mut reader).is_err());
    }

    #[test]
    fn clean_eof_returns_none() {
        let mut reader = BufReader::new(&[][..]);
        assert!(read_message(&mut reader).unwrap().is_none());
    }
}
