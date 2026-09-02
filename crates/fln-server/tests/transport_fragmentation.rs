#![forbid(unsafe_code)]

use std::cmp;
use std::io::{self, BufRead, Read};

struct Fragmented<'a> {
    bytes: &'a [u8],
    offset: usize,
    width: usize,
}

impl<'a> Fragmented<'a> {
    fn new(bytes: &'a [u8], width: usize) -> Self {
        assert!(width > 0);
        Self {
            bytes,
            offset: 0,
            width,
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
        assert!(fln_server::transport::read_message(&mut input)
            .unwrap()
            .is_none());
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
        assert!(fln_server::transport::read_message(&mut input)
            .unwrap()
            .is_none());
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
