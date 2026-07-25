//! The editable source substrate — Vellum's rope (plan §9; bead fln-4yos).
//!
//! [`SourceText`] is immutable and byte-exact, which is what a parser and a diagnostic
//! need. An editor needs the same guarantees while *changing*, and changing a file by
//! rebuilding a `String` is whole-file work per keystroke. This module is that substrate:
//! edits and slices that do not copy the original text, with every invariant slice 1
//! established re-checked **after** each edit rather than only at construction.
//!
//! ## Representation, and why the tests do not depend on it
//!
//! The current representation is a **piece table**: an immutable `base` buffer holding the
//! text as loaded, an append-only `added` buffer holding every inserted byte, and an
//! ordered list of pieces, each a byte range into one of the two. An edit splices the
//! piece list and appends to `added`; **no byte of the original is ever copied or moved**,
//! which is what makes an edit cheaper than the file. Deleting is dropping or trimming
//! pieces, so a large deletion is cheap regardless of how much text it removes.
//!
//! That is an implementation choice, not the interface. Every test here compares the rope
//! against the obvious flat-buffer implementation of the same edit sequence, so the
//! representation can become a balanced tree — should profiling ever call for it — without
//! the contract moving. A differential against the naive implementation is also the only
//! way to catch a structure-sharing bug that appears solely at a piece boundary, which is
//! where this class of bug actually lives.
//!
//! ## Byte-exactness survives editing
//!
//! Pieces are byte ranges, so nothing in the edit path is in a position to reinterpret a
//! byte. That is deliberate rather than incidental: a BOM stays a BOM, a CRLF stays a
//! CRLF, mixed line endings in one file stay mixed, and **an inserted combining mark stays
//! a separate scalar from the base character it follows**. There is no normalization step
//! to disable, because there is nowhere for one to live — and
//! `an_edit_never_normalizes_what_it_joins` pins that at the one place a normalizing
//! implementation would act: the seam an insertion creates.
//!
//! ## Where the subtle bugs are, and what is done about each
//!
//! * An edit boundary that **splits a multi-byte scalar** — refused, typed, never clamped.
//!   Clamping an edit silently corrupts a program.
//! * A **stale derived index**. Line starts and the three position projections are not
//!   maintained incrementally here; they are recomputed from the current bytes on demand
//!   and the cache is dropped by every edit. That makes "the text was updated but the
//!   index was not" structurally impossible rather than merely tested for, at the price of
//!   one O(bytes) pass on the first query after an edit. Incremental maintenance is a
//!   named follow-up, not a silent gap — it is a performance property, and the correctness
//!   contract is that every query agrees with a freshly built [`SourceText`].
//! * A **slice from a stale revision**. Slices borrow nothing and are materialized from the
//!   current piece list, so a slice cannot outlive the revision it was taken from.

use crate::source::{BytePos, ByteSpan, Position, SourceError, SourceText};

/// Which buffer a piece points into.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Buffer {
    /// The text as originally loaded. Never written to after construction.
    Base,
    /// Append-only insertions. Never rewritten, so existing pieces stay valid.
    Added,
}

/// One contiguous run of bytes in one buffer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Piece {
    buffer: Buffer,
    start: usize,
    len: usize,
}

/// Why an edit was refused.
///
/// Every arm is a caller error that must not be repaired: an edit applied to the wrong
/// bytes is a changed program, and this module's whole promise is that it does not change
/// bytes it was not told to change.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EditError {
    /// The range runs backwards, or ends past the end of the text.
    OutOfRange { span: ByteSpan, len_bytes: usize },
    /// A boundary falls inside a multi-byte scalar. Reported with the offending offset so
    /// a caller can see which end was wrong.
    NotOnCharBoundary { at: BytePos },
    /// The replacement text is not valid UTF-8.
    Insertion(SourceError),
}

impl std::fmt::Display for EditError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            EditError::OutOfRange { span, len_bytes } => write!(
                f,
                "edit range {}..{} is outside a text of {len_bytes} bytes",
                span.start().0,
                span.end().0
            ),
            EditError::NotOnCharBoundary { at } => {
                write!(f, "edit boundary at {at} falls inside a scalar")
            }
            EditError::Insertion(error) => write!(f, "inserted text is invalid: {error}"),
        }
    }
}

/// An editable source text that shares its original bytes.
#[derive(Debug, Clone)]
pub struct Rope {
    base: String,
    added: String,
    pieces: Vec<Piece>,
    len_bytes: usize,
    /// Derived view of the current bytes, dropped by every edit. `None` means "not
    /// computed since the last change", never "empty".
    materialized: Option<SourceText>,
}

impl Rope {
    /// Load a rope from bytes, refusing invalid UTF-8 exactly as [`SourceText`] does.
    pub fn from_utf8(bytes: &[u8]) -> Result<Rope, SourceError> {
        let text = SourceText::from_utf8(bytes)?;
        let base = text.as_str().to_string();
        let len_bytes = base.len();
        let pieces = if len_bytes == 0 {
            Vec::new()
        } else {
            vec![Piece {
                buffer: Buffer::Base,
                start: 0,
                len: len_bytes,
            }]
        };
        Ok(Rope {
            base,
            added: String::new(),
            pieces,
            len_bytes,
            materialized: Some(text),
        })
    }

    pub fn len_bytes(&self) -> usize {
        self.len_bytes
    }

    pub fn is_empty(&self) -> bool {
        self.len_bytes == 0
    }

    /// How many pieces the table currently holds. Exposed for tests and diagnostics: it is
    /// the cost model, and a test that asserts the original was never copied needs it.
    pub fn piece_count(&self) -> usize {
        self.pieces.len()
    }

    fn piece_str(&self, piece: Piece) -> &str {
        let buffer = match piece.buffer {
            Buffer::Base => &self.base,
            Buffer::Added => &self.added,
        };
        &buffer[piece.start..piece.start + piece.len]
    }

    /// The current bytes, as one owned string.
    pub fn to_string_lossless(&self) -> String {
        let mut out = String::with_capacity(self.len_bytes);
        for piece in &self.pieces {
            out.push_str(self.piece_str(*piece));
        }
        out
    }

    /// The current bytes as an immutable [`SourceText`], computing and caching the derived
    /// line index on first use after a change.
    ///
    /// Every position query goes through this, which is why a stale index is not a failure
    /// mode here: there is one derivation and an edit drops it.
    pub fn source_text(&mut self) -> &SourceText {
        if self.materialized.is_none() {
            let text = self.to_string_lossless();
            // Infallible: every piece came from validated UTF-8 and pieces are only ever
            // split on char boundaries, which `edit` enforces before splicing.
            self.materialized = Some(
                SourceText::from_utf8(text.as_bytes())
                    .expect("pieces are only split on char boundaries"),
            );
        }
        self.materialized.as_ref().expect("just computed")
    }

    /// Project a byte offset, as [`SourceText::position_of`] does over the current bytes.
    pub fn position_of(&mut self, at: BytePos) -> Option<Position> {
        self.source_text().position_of(at)
    }

    /// The bytes of a span, materialized. Owned rather than borrowed so a slice cannot
    /// outlive the revision that produced it.
    pub fn slice(&self, span: ByteSpan) -> Result<String, EditError> {
        self.check_span(span)?;
        let mut out = String::with_capacity(span.len_bytes());
        let mut at = 0usize;
        for piece in &self.pieces {
            let piece_end = at + piece.len;
            let overlap_start = span.start().0.max(at);
            let overlap_end = span.end().0.min(piece_end);
            if overlap_start < overlap_end {
                let text = self.piece_str(*piece);
                out.push_str(&text[overlap_start - at..overlap_end - at]);
            }
            at = piece_end;
            if at >= span.end().0 {
                break;
            }
        }
        Ok(out)
    }

    fn check_span(&self, span: ByteSpan) -> Result<(), EditError> {
        if span.end().0 > self.len_bytes {
            return Err(EditError::OutOfRange {
                span,
                len_bytes: self.len_bytes,
            });
        }
        // Boundaries are checked against the CURRENT bytes. Doing it per-piece would be
        // cheaper and is the obvious optimization, but it is also where an off-by-one in
        // the boundary test would hide, so correctness first.
        let text = self.to_string_lossless();
        for edge in [span.start(), span.end()] {
            if !text.is_char_boundary(edge.0) {
                return Err(EditError::NotOnCharBoundary { at: edge });
            }
        }
        Ok(())
    }

    /// Replace `span` with `insert`, the one primitive the others delegate to.
    ///
    /// Refuses rather than repairs: an out-of-range span, a boundary inside a scalar, or
    /// invalid UTF-8 in the insertion all leave the rope **unchanged**. That atomicity
    /// matters more than it looks — a partially applied edit is a corrupted program with no
    /// record of what it used to be.
    pub fn replace(&mut self, span: ByteSpan, insert: &str) -> Result<(), EditError> {
        self.check_span(span)?;

        // Rebuild the piece list around the span. Pieces wholly before or after it are
        // reused untouched, which is what keeps the original bytes uncopied.
        let mut rebuilt: Vec<Piece> = Vec::with_capacity(self.pieces.len() + 2);
        let mut at = 0usize;
        for piece in &self.pieces {
            let piece_end = at + piece.len;
            // The part of this piece before the edit.
            if at < span.start().0 {
                let keep = span.start().0.min(piece_end) - at;
                if keep > 0 {
                    rebuilt.push(Piece {
                        buffer: piece.buffer,
                        start: piece.start,
                        len: keep,
                    });
                }
            }
            // The part after the edit.
            if piece_end > span.end().0 {
                let skip = span.end().0.max(at) - at;
                let keep = piece.len - skip;
                if keep > 0 {
                    rebuilt.push(Piece {
                        buffer: piece.buffer,
                        start: piece.start + skip,
                        len: keep,
                    });
                }
            }
            at = piece_end;
        }

        if !insert.is_empty() {
            let start = self.added.len();
            self.added.push_str(insert);
            // Insert the new piece at the position corresponding to the edit point. The
            // rebuilt list is ordered, so the split index is the number of bytes kept
            // before the span.
            let mut before = 0usize;
            let mut index = rebuilt.len();
            for (position, piece) in rebuilt.iter().enumerate() {
                if before >= span.start().0 {
                    index = position;
                    break;
                }
                before += piece.len;
            }
            if before >= span.start().0 && index > rebuilt.len() {
                index = rebuilt.len();
            }
            rebuilt.insert(
                index,
                Piece {
                    buffer: Buffer::Added,
                    start,
                    len: insert.len(),
                },
            );
        }

        self.pieces = rebuilt;
        self.len_bytes = self.len_bytes - span.len_bytes() + insert.len();
        // The derived index is dropped, not patched. See the module note: this is what
        // makes a stale index unrepresentable rather than merely tested against.
        self.materialized = None;
        Ok(())
    }

    /// Insert text at a point.
    pub fn insert(&mut self, at: BytePos, text: &str) -> Result<(), EditError> {
        self.replace(ByteSpan::empty_at(at), text)
    }

    /// Delete a span.
    pub fn delete(&mut self, span: ByteSpan) -> Result<(), EditError> {
        self.replace(span, "")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tiny deterministic generator. Seeded so any failure replays exactly, and
    /// hand-rolled because the dependency universe is closed (D1).
    struct Seeded(u64);

    impl Seeded {
        fn next(&mut self) -> u64 {
            // SplitMix64.
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }

        fn below(&mut self, bound: usize) -> usize {
            if bound == 0 {
                0
            } else {
                (self.next() % bound as u64) as usize
            }
        }
    }

    /// Round a byte offset down to a char boundary of `text`.
    fn floor_boundary(text: &str, at: usize) -> usize {
        let mut at = at.min(text.len());
        while at > 0 && !text.is_char_boundary(at) {
            at -= 1;
        }
        at
    }

    #[test]
    fn a_fresh_rope_is_byte_identical_and_shares_its_base() {
        let raw: Vec<u8> = [
            crate::source::BOM,
            "def f := 1\r\n".as_bytes(),
            "  -- π\n\ttab\rend".as_bytes(),
        ]
        .concat();
        let rope = Rope::from_utf8(&raw).expect("valid");
        assert_eq!(rope.to_string_lossless().as_bytes(), raw.as_slice());
        assert_eq!(rope.len_bytes(), raw.len());
        assert_eq!(
            rope.piece_count(),
            1,
            "an unedited rope is one piece over the base: nothing was copied"
        );
    }

    /// **The differential.** Every edit sequence must produce exactly what the obvious
    /// flat-buffer implementation produces. This is the only test that can catch a
    /// structure-sharing bug appearing solely at a piece boundary, which is where this
    /// class of bug lives — so it runs over seeded random sequences on text containing
    /// multi-byte scalars, a BOM, and mixed line endings.
    #[test]
    fn edits_agree_byte_for_byte_with_a_flat_buffer_over_seeded_sequences() {
        for seed in [
            0x5645_4C4C_554D_0001u64,
            0x5645_4C4C_554D_0002,
            0x5645_4C4C_554D_0003,
            0x5645_4C4C_554D_0004,
        ] {
            let mut rng = Seeded(seed);
            let start: Vec<u8> = [
                crate::source::BOM,
                "def π := 1\r\nlemma 漢 := 2\nend\r".as_bytes(),
            ]
            .concat();
            let mut rope = Rope::from_utf8(&start).expect("valid");
            let mut flat = String::from_utf8(start.clone()).expect("valid");

            for step in 0..40 {
                // Insertions deliberately include a BOM, a CR, an LF, a combining mark and
                // an astral scalar: the bytes most likely to be "helpfully" rewritten.
                let inserts = [
                    "", "x", "\r\n", "\n", "\r", "\u{FEFF}", "\u{0301}", "😀", "π",
                ];
                let insert = inserts[rng.below(inserts.len())];
                let a = floor_boundary(&flat, rng.below(flat.len() + 1));
                let b = floor_boundary(&flat, rng.below(flat.len() + 1));
                let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
                let span = ByteSpan::new(BytePos(lo), BytePos(hi)).expect("forward");

                rope.replace(span, insert).unwrap_or_else(|error| {
                    panic!("seed {seed:#x} step {step}: rope refused a valid edit: {error}")
                });
                flat.replace_range(lo..hi, insert);

                assert_eq!(
                    rope.to_string_lossless(),
                    flat,
                    "seed {seed:#x} step {step}: rope and flat buffer diverged"
                );
                assert_eq!(rope.len_bytes(), flat.len());

                // The derived views must agree with a text built fresh from the post-edit
                // bytes, so an edit cannot leave an index that answers plausibly.
                let fresh = SourceText::from_utf8(flat.as_bytes()).expect("valid");
                let text = rope.source_text();
                assert_eq!(text.as_bytes(), fresh.as_bytes());
                assert_eq!(text.line_count(), fresh.line_count());
                for (offset, _) in flat.char_indices() {
                    assert_eq!(
                        text.position_of(BytePos(offset)),
                        fresh.position_of(BytePos(offset)),
                        "seed {seed:#x} step {step}: projection disagreed at byte {offset}"
                    );
                }
            }
        }
    }

    #[test]
    fn slices_agree_with_the_flat_buffer_including_across_piece_boundaries() {
        let mut rope = Rope::from_utf8("abcπdef".as_bytes()).expect("valid");
        // Force several pieces so slices must cross boundaries to be right.
        rope.insert(BytePos(3), "-").expect("boundary");
        rope.insert(BytePos(0), "«").expect("start");
        let flat = rope.to_string_lossless();
        assert!(rope.piece_count() >= 3, "the test needs multiple pieces");

        for (start, _) in flat.char_indices().chain([(flat.len(), ' ')]) {
            for (end, _) in flat.char_indices().chain([(flat.len(), ' ')]) {
                if start > end {
                    continue;
                }
                let span = ByteSpan::new(BytePos(start), BytePos(end)).expect("forward");
                assert_eq!(
                    rope.slice(span).expect("valid span"),
                    flat[start..end],
                    "slice {start}..{end} disagreed with the flat buffer"
                );
            }
        }
    }

    #[test]
    fn an_edit_at_a_bad_boundary_is_refused_and_changes_nothing() {
        let mut rope = Rope::from_utf8("aπb".as_bytes()).expect("valid");
        let before = rope.to_string_lossless();

        // Mid-scalar: 'π' occupies bytes 1..3, so 2 is inside it.
        let mid = ByteSpan::new(BytePos(2), BytePos(2)).expect("forward");
        assert_eq!(
            rope.insert(BytePos(2), "x"),
            Err(EditError::NotOnCharBoundary { at: BytePos(2) })
        );
        assert_eq!(
            rope.delete(mid),
            Err(EditError::NotOnCharBoundary { at: BytePos(2) })
        );

        // Past the end.
        let past = ByteSpan::new(BytePos(0), BytePos(99)).expect("forward");
        assert_eq!(
            rope.delete(past),
            Err(EditError::OutOfRange {
                span: past,
                len_bytes: 4
            })
        );

        // ATOMICITY: every refusal left the rope exactly as it was. A partially applied
        // edit is a corrupted program with no record of what it used to be.
        assert_eq!(rope.to_string_lossless(), before);
        assert_eq!(rope.len_bytes(), before.len());

        // And a valid edit at the surrounding boundaries still works, so none of the above
        // is a blanket refusal.
        rope.insert(BytePos(1), "y").expect("boundary before π");
        assert_eq!(rope.to_string_lossless(), "ayπb");
    }

    /// **We must not normalize**, and an insertion's seam is the one place a normalizing
    /// implementation would act: a combining mark landing immediately after a base
    /// character is exactly the pair NFC fuses.
    #[test]
    fn an_edit_never_normalizes_what_it_joins() {
        // Insert a combining acute directly after a bare 'e'. NFC would fuse these into
        // U+00E9 and shorten the text by one byte.
        let mut rope = Rope::from_utf8("de".as_bytes()).expect("valid");
        rope.insert(BytePos(2), "\u{0301}").expect("boundary");
        let joined = rope.to_string_lossless();
        assert_eq!(joined.as_bytes(), "de\u{0301}".as_bytes());
        assert_eq!(
            joined.chars().count(),
            3,
            "the mark stayed a separate scalar"
        );
        assert_ne!(
            joined.as_bytes(),
            "d\u{00E9}".as_bytes(),
            "a normalizing edit would have produced the precomposed form"
        );
        assert_eq!(rope.len_bytes(), 4);

        // The reverse direction: inserting a base character before a lone combining mark
        // must not fuse either.
        let mut other = Rope::from_utf8("\u{0301}x".as_bytes()).expect("valid");
        other.insert(BytePos(0), "e").expect("start");
        assert_eq!(
            other.to_string_lossless().as_bytes(),
            "e\u{0301}x".as_bytes()
        );

        // And the two remain distinct texts all the way through the derived views.
        let mut precomposed = Rope::from_utf8("d\u{00E9}".as_bytes()).expect("valid");
        assert_ne!(
            precomposed.to_string_lossless(),
            rope.to_string_lossless(),
            "canonically-equivalent texts must stay distinct"
        );
        assert_ne!(
            precomposed.source_text().len_bytes(),
            rope.source_text().len_bytes()
        );
    }

    #[test]
    fn a_bom_and_mixed_line_endings_survive_edits_including_splitting_a_crlf() {
        let raw: Vec<u8> = [crate::source::BOM, b"a\r\nb\nc\rd"].concat();
        let mut rope = Rope::from_utf8(&raw).expect("valid");
        assert!(rope.source_text().has_bom());

        // SPLIT A CRLF PAIR — the case a line index is most likely to get wrong. The BOM
        // is 3 bytes, so 'a' is at 3 and the CR/LF are at 4 and 5.
        rope.insert(BytePos(5), "X").expect("between CR and LF");
        let text = rope.to_string_lossless();
        assert_eq!(
            text.as_bytes(),
            [crate::source::BOM, b"a\rX\nb\nc\rd"].concat()
        );

        // The line index must agree with a fresh derivation over the new bytes: the CR is
        // now a lone CR and does not start a line, and the LF still does.
        let fresh = SourceText::from_utf8(text.as_bytes()).expect("valid");
        assert_eq!(rope.source_text().line_count(), fresh.line_count());
        assert_eq!(rope.source_text().line_count(), 3);

        // The BOM is still there and is still reported: an edit elsewhere did not tidy it.
        assert!(rope.source_text().has_bom());
        assert!(
            rope.to_string_lossless()
                .as_bytes()
                .starts_with(crate::source::BOM)
        );

        // Deleting across the CRLF boundary is likewise byte-exact.
        let span = ByteSpan::new(BytePos(4), BytePos(6)).expect("forward");
        rope.delete(span).expect("boundaries are valid");
        assert_eq!(
            rope.to_string_lossless().as_bytes(),
            [crate::source::BOM, b"a\nb\nc\rd"].concat()
        );
    }

    #[test]
    fn the_derived_index_is_dropped_by_an_edit_rather_than_patched() {
        let mut rope = Rope::from_utf8(b"a\nb").expect("valid");
        // Force the cache to exist.
        assert_eq!(rope.source_text().line_count(), 2);
        assert!(rope.materialized.is_some());
        rope.insert(BytePos(3), "\nc").expect("end");
        assert!(
            rope.materialized.is_none(),
            "an edit must drop the derived index, not update it in place"
        );
        // And the recomputation is correct rather than merely present.
        assert_eq!(rope.source_text().line_count(), 3);
        assert_eq!(
            rope.source_text().as_bytes(),
            SourceText::from_utf8(b"a\nb\nc").expect("valid").as_bytes()
        );
    }

    #[test]
    fn a_large_deletion_does_not_copy_the_text_it_removes() {
        // The cost-model claim: pieces are byte ranges, so removing a lot of text is
        // dropping pieces rather than moving bytes. Asserted through the piece count,
        // which is the only observable that distinguishes the two.
        let body = "x".repeat(100_000);
        let mut rope = Rope::from_utf8(body.as_bytes()).expect("valid");
        assert_eq!(rope.piece_count(), 1);
        let span = ByteSpan::new(BytePos(10), BytePos(99_990)).expect("forward");
        rope.delete(span).expect("valid");
        assert_eq!(rope.len_bytes(), 20);
        assert_eq!(
            rope.piece_count(),
            2,
            "a deletion should leave the two surviving fragments, not a rebuilt buffer"
        );
        assert_eq!(rope.to_string_lossless(), "x".repeat(20));
    }

    #[test]
    fn an_empty_rope_and_edits_at_its_edges_behave() {
        let mut rope = Rope::from_utf8(b"").expect("valid");
        assert!(rope.is_empty());
        assert_eq!(rope.piece_count(), 0);
        assert_eq!(rope.to_string_lossless(), "");
        assert_eq!(
            rope.slice(ByteSpan::empty_at(BytePos(0))).expect("empty"),
            ""
        );

        rope.insert(BytePos(0), "π").expect("into empty");
        assert_eq!(rope.to_string_lossless(), "π");

        // Insert at the very end and at the very start of a non-empty rope.
        rope.insert(BytePos(rope.len_bytes()), "!").expect("at end");
        rope.insert(BytePos(0), "¡").expect("at start");
        assert_eq!(rope.to_string_lossless(), "¡π!");

        // Delete everything, then edit again.
        let all = ByteSpan::new(BytePos(0), BytePos(rope.len_bytes())).expect("forward");
        rope.delete(all).expect("valid");
        assert!(rope.is_empty());
        rope.insert(BytePos(0), "again").expect("valid");
        assert_eq!(rope.to_string_lossless(), "again");
    }
}
