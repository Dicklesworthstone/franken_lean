#![forbid(unsafe_code)]

use std::cmp;
use std::io::{self, BufRead, Read};

struct Fragmented<'a> {
    bytes: &'a [u8],
    offset: usize,
    width: usize,
    failure: Option<(usize, io::ErrorKind)>,
}

impl<'a> Fragmented<'a> {
    fn new(bytes: &'a [u8], width: usize) -> Self {
        assert!(width > 0);
        Self {
            bytes,
            offset: 0,
            width,
            failure: None,
        }
    }

    fn failing_once(bytes: &'a [u8], at: usize, kind: io::ErrorKind) -> Self {
        Self {
            failure: Some((at, kind)),
            ..Self::new(bytes, 1)
        }
    }
}

impl Read for Fragmented<'_> {
    fn read(&mut self, output: &mut [u8]) -> io::Result<usize> {
        let available = self.fill_buf()?;
        let count = available.len().min(output.len());
        output[..count].copy_from_slice(&available[..count]);
        self.consume(count);
        Ok(count)
    }
}

impl BufRead for Fragmented<'_> {
    fn fill_buf(&mut self) -> io::Result<&[u8]> {
        if let Some((at, kind)) = self.failure
            && at == self.offset
        {
            self.failure = None;
            return Err(io::Error::new(kind, "injected transport read failure"));
        }
        let end = cmp::min(self.bytes.len(), self.offset.saturating_add(self.width));
        Ok(&self.bytes[self.offset..end])
    }

    fn consume(&mut self, amount: usize) {
        self.offset = cmp::min(self.bytes.len(), self.offset.saturating_add(amount));
    }
}

fn frame(body: &[u8]) -> Vec<u8> {
    let mut framed = Vec::new();
    fln_server::transport::write_message(&mut framed, body).unwrap();
    framed
}

#[test]
fn every_small_fragment_width_round_trips_one_frame() {
    let body = br#"{"jsonrpc":"2.0","id":"fragmented","method":"initialize","params":{}}"#;
    let framed = frame(body);
    for width in 1..=64 {
        let mut input = Fragmented::new(&framed, width);
        assert_eq!(
            fln_server::transport::read_message(&mut input)
                .unwrap()
                .as_deref(),
            Some(body.as_slice()),
            "fragment width {width}"
        );
        assert!(
            fln_server::transport::read_message(&mut input)
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn fragmented_concatenated_frames_remain_separate() {
    let bodies: [&[u8]; 3] = [b"{}", b"[]", br#"{"method":"exit"}"#];
    let mut framed = Vec::new();
    for body in bodies {
        framed.extend(frame(body));
    }
    for width in 1..=64 {
        let mut input = Fragmented::new(&framed, width);
        for body in bodies {
            assert_eq!(
                fln_server::transport::read_message(&mut input)
                    .unwrap()
                    .as_deref(),
                Some(body),
                "fragment width {width}"
            );
        }
        assert!(
            fln_server::transport::read_message(&mut input)
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn every_fragment_width_reports_a_truncated_body() {
    let mut framed = b"Content-Length: 9\r\n\r\nshort".to_vec();
    for width in 1..=framed.len() {
        let mut input = Fragmented::new(&framed, width);
        assert_eq!(
            fln_server::transport::read_message(&mut input)
                .unwrap_err()
                .kind(),
            io::ErrorKind::UnexpectedEof,
            "fragment width {width}"
        );
    }
    framed.clear();
}

#[test]
fn interruptions_at_each_frame_boundary_preserve_the_frame_and_clean_eof() {
    let body = br#"{"jsonrpc":"2.0","id":1,"method":"initialize"}"#;
    let framed = frame(body);
    for at in 0..=framed.len() {
        let mut input = Fragmented::failing_once(&framed, at, io::ErrorKind::Interrupted);
        assert_eq!(
            fln_server::transport::read_message(&mut input)
                .unwrap_or_else(|error| panic!("interrupted at byte {at}: {error}"))
                .as_deref(),
            Some(body.as_slice())
        );
        assert!(
            fln_server::transport::read_message(&mut input)
                .unwrap_or_else(|error| panic!("interrupted at EOF byte {at}: {error}"))
                .is_none()
        );
        assert!(input.failure.is_none(), "byte {at} was not reached");
    }
}

#[test]
fn non_interrupt_errors_keep_their_original_kind_and_message() {
    let framed = frame(b"{}");
    let body_start = framed.len() - 2;
    for at in [0, 5, body_start + 1] {
        let mut input = Fragmented::failing_once(&framed, at, io::ErrorKind::PermissionDenied);
        let error = fln_server::transport::read_message(&mut input).unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::PermissionDenied);
        assert_eq!(error.to_string(), "injected transport read failure");
        assert_eq!(input.offset, at, "failure must not consume any later bytes");
    }
}
