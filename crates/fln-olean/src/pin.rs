//! The `.olean` header identity the pinned Reference writes, held byte for byte
//! (bead `fln-fur.1`).
//!
//! The pinned loader (`vendor/lean4-src/src/library/module.cpp:488-497`) refuses an
//! artifact as "incompatible header" when its `flags` differ from the build's own or,
//! with `LEAN_CHECK_OLEAN_VERSION` (set for release builds,
//! `.github/workflows/build-template.yml:138`), when its `githash` differs from
//! `LEAN_GITHASH`. It never reads `lean_version`. This check is at least that
//! strict: it also holds `lean_version`, and every padding byte of both string
//! fields. A pinned artifact differs from another only past these fields.
//!
//! [`crate::region::OleanView::parse`] stays a format decoder and does not apply
//! this: the codec's own fixtures carry other identities. Every door that claims a
//! pinned artifact (`fln check-olean`, `fln olean inspect`, `.olean` imports)
//! applies it before decoding further.
use crate::format::{OLEAN_HEADER_FIELDS, OLEAN_HEADER_SIZE, PIN_COMMIT, PIN_TAG};

/// The pinned toolchain is a release build with GMP (`USE_GMP` defaults to `ON`,
/// `vendor/lean4-src/src/CMakeLists.txt:111`), so it writes flag bit 0 set and no
/// other. Every `.olean` part of the pinned stdlib carries `0x01`.
pub const PINNED_FLAGS: u8 = 0b1;

/// `get_short_version_string()` of the pinned release: its tag without the `v`.
pub fn pinned_lean_version() -> &'static str {
    PIN_TAG.strip_prefix('v').unwrap_or(PIN_TAG)
}

/// One header field that is not the pinned toolchain's.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HeaderPinMismatch {
    /// `flags`, `lean_version` or `githash`.
    pub field: &'static str,
    pub expected: String,
    pub found: String,
}

impl std::fmt::Display for HeaderPinMismatch {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "header field `{}` is {}, but the pinned Reference ({PIN_TAG}, {PIN_COMMIT}) writes {}",
            self.field, self.found, self.expected
        )
    }
}

impl std::error::Error for HeaderPinMismatch {}

fn field(name: &str) -> (usize, usize) {
    let field = OLEAN_HEADER_FIELDS
        .iter()
        .find(|field| field.name == name)
        .expect("a generated header field");
    (field.offset, field.size)
}

/// A string field as the Reference wrote it: `text`, then `\0` to the field's end.
fn padded(text: &str, size: usize) -> Vec<u8> {
    let mut bytes = text.as_bytes().to_vec();
    bytes.resize(size, 0);
    bytes
}

/// A string field as found: its text up to the first `\0`, escaped, and the first
/// nonzero byte after that, if any.
fn render(bytes: &[u8]) -> String {
    let end = bytes.iter().position(|&b| b == 0).unwrap_or(bytes.len());
    let mut text = format!("{:?}", String::from_utf8_lossy(&bytes[..end]));
    if let Some(stray) = bytes[end..].iter().position(|&b| b != 0) {
        text.push_str(&format!(
            " with padding byte {} = 0x{:02x}",
            end + stray,
            bytes[end + stray]
        ));
    }
    text
}

/// Hold `file`'s fixed header to the pin. `file` is any one `.olean` part whose
/// envelope already parsed, so its header is present; a shorter file is refused as
/// a `flags` mismatch rather than read out of bounds.
pub fn check_pinned_header(file: &[u8]) -> Result<(), HeaderPinMismatch> {
    if file.len() < OLEAN_HEADER_SIZE {
        return Err(HeaderPinMismatch {
            field: "flags",
            expected: format!("0x{PINNED_FLAGS:02x}"),
            found: "a truncated header".to_owned(),
        });
    }
    let (offset, _) = field("flags");
    if file[offset] != PINNED_FLAGS {
        return Err(HeaderPinMismatch {
            field: "flags",
            expected: format!("0x{PINNED_FLAGS:02x}"),
            found: format!("0x{:02x}", file[offset]),
        });
    }
    for (name, text) in [
        ("lean_version", pinned_lean_version()),
        ("githash", PIN_COMMIT),
    ] {
        let (offset, size) = field(name);
        let found = &file[offset..offset + size];
        let expected = padded(text, size);
        if found != expected.as_slice() {
            return Err(HeaderPinMismatch {
                field: name,
                expected: render(&expected),
                found: render(found),
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pinned() -> Vec<u8> {
        let mut file = vec![0u8; OLEAN_HEADER_SIZE];
        file[..5].copy_from_slice(b"olean");
        file[5] = 2;
        file[field("flags").0] = PINNED_FLAGS;
        let (offset, size) = field("lean_version");
        file[offset..offset + size].copy_from_slice(&padded(pinned_lean_version(), size));
        let (offset, size) = field("githash");
        file[offset..offset + size].copy_from_slice(&padded(PIN_COMMIT, size));
        file
    }

    #[test]
    fn the_pinned_identity_passes_and_every_identity_byte_is_held() {
        let file = pinned();
        assert_eq!(check_pinned_header(&file), Ok(()));
        assert_eq!(pinned_lean_version(), "4.32.0");
        for name in ["flags", "lean_version", "githash"] {
            let (offset, size) = field(name);
            for index in offset..offset + size.max(1) {
                for bit in 0..8 {
                    let mut flipped = file.clone();
                    flipped[index] ^= 1 << bit;
                    let refused = check_pinned_header(&flipped).unwrap_err();
                    assert_eq!(refused.field, name, "byte {index} bit {bit}");
                    assert_ne!(refused.found, refused.expected);
                }
            }
        }
        // Bytes outside the three fields are other checks' business.
        for index in (0..7).chain(80..OLEAN_HEADER_SIZE) {
            if index == field("flags").0 {
                continue;
            }
            let mut flipped = file.clone();
            flipped[index] ^= 1;
            assert_eq!(check_pinned_header(&flipped), Ok(()), "byte {index}");
        }
        assert!(check_pinned_header(&file[..OLEAN_HEADER_SIZE - 1]).is_err());
    }

    #[test]
    fn a_refusal_names_the_field_and_both_values() {
        let mut file = pinned();
        file[field("lean_version").0] = b'5';
        let refused = check_pinned_header(&file).unwrap_err();
        assert_eq!(refused.field, "lean_version");
        assert_eq!(refused.found, "\"5.32.0\"");
        assert_eq!(refused.expected, "\"4.32.0\"");
        let text = refused.to_string();
        assert!(
            text.contains("`lean_version`") && text.contains(PIN_COMMIT),
            "{text}"
        );

        let mut file = pinned();
        let (offset, _) = field("lean_version");
        file[offset + 20] = 7;
        assert_eq!(
            check_pinned_header(&file).unwrap_err().found,
            "\"4.32.0\" with padding byte 20 = 0x07"
        );
    }
}
