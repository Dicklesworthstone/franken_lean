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

/// Update a line index in place for one replacement, **without reading the text**
/// (bead franken_lean-0sv9).
///
/// The signature is the cost proof. This function has no access to the rope's bytes, so
/// its work cannot be proportional to the file: it reads the existing index and the
/// inserted text and nothing else. A measured benchmark would show the same thing more
/// weakly — timings drift and a regression can hide inside noise — whereas a function that
/// *cannot* touch the file is proportional to the edit by construction.
///
/// The rule follows entirely from the index's definition ([`scan_line_starts`]): a start
/// `s` exists exactly when byte `s - 1` is `\n`. So for a replacement of `span` by
/// `insert`:
///
/// * starts at or before `span.start` are untouched — their producing `\n` is before the
///   edit. This is also why an edit at byte 0 cannot disturb line 0's start, BOM or not.
/// * starts in `[span.start + 1, span.end]` are dropped — their producing `\n` lay inside
///   the replaced range.
/// * every `\n` in `insert` contributes a new start.
/// * starts after `span.end` shift by `insert.len() - span.len()`.
///
/// The line-ending traps need no special cases *because* of that definition, which is the
/// argument for defining it that way. Splitting a CRLF by inserting between the `\r` and
/// the `\n` does not change which bytes are `\n`, so the start merely shifts; deleting the
/// `\n` of a CRLF removes exactly that start and leaves the `\r` as ordinary content; a
/// lone `\r` never had a start to lose. Nothing normalizes, and no terminator is invented.
///
/// Cost is O(inserted bytes + starts after the edit). Not O(1): a shift touches every
/// later start, so an edit at the top of a large file is proportional to its line count.
/// That is a real improvement on the O(file bytes) recompute it replaces — typically by
/// the average line length — but it is not the O(edit + lines touched) that a
/// tree-structured index would give, and the difference is recorded rather than glossed.
fn splice_line_starts(starts: &mut Vec<BytePos>, span: ByteSpan, insert: &str) {
    let removed = span.len_bytes();
    let inserted = insert.len();
    let keep_through = span.start().0;
    let drop_through = span.end().0;

    // Everything strictly after the replaced range shifts; everything inside it goes.
    let mut rebuilt: Vec<BytePos> = Vec::with_capacity(starts.len() + 1);
    let mut tail: Vec<BytePos> = Vec::new();
    for start in starts.iter().copied() {
        if start.0 <= keep_through {
            rebuilt.push(start);
        } else if start.0 > drop_through {
            // Signed arithmetic avoided: the shift is applied as two unsigned steps so a
            // deletion larger than the offset cannot underflow. It never can — a start
            // after the range is at least span.end, and removed <= span.end — but relying
            // on that silently is how an underflow ships in a release build.
            tail.push(BytePos(start.0 + inserted - removed));
        }
    }

    // New starts from the insertion, at their absolute offsets.
    for (offset, byte) in insert.bytes().enumerate() {
        if byte == b'\n' {
            rebuilt.push(BytePos(keep_through + offset + 1));
        }
    }
    rebuilt.extend(tail);
    *starts = rebuilt;
}

/// An editable source text that shares its original bytes.
#[derive(Debug, Clone)]
pub struct Rope {
    base: String,
    added: String,
    pieces: Vec<Piece>,
    len_bytes: usize,
    /// The line index, maintained INCREMENTALLY by every edit (bead franken_lean-0sv9).
    /// Always current, so line queries never trigger a scan and there is no "stale index"
    /// state to represent.
    line_starts: Vec<BytePos>,
    /// The full text as a [`SourceText`], for callers that want one. Dropped by every edit
    /// and rebuilt on demand; `None` means "not materialized since the last change", never
    /// "empty". Materializing is O(bytes), which is why line queries below do NOT go
    /// through it.
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
            line_starts: text.line_starts().to_vec(),
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
            // Built from the maintained index rather than rescanning, so the two can
            // never disagree by construction. `from_parts` debug-asserts equality with a
            // full scan, which turns any splice bug into a loud failure in test builds.
            self.materialized = Some(SourceText::from_parts(text, self.line_starts.clone()));
        }
        self.materialized.as_ref().expect("just computed")
    }

    /// Number of lines, from the maintained index. No text materialization.
    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }

    /// Byte offset of the start of `line`, from the maintained index.
    pub fn line_start(&self, line: usize) -> Option<BytePos> {
        self.line_starts.get(line).copied()
    }

    /// The line containing `at`, from the maintained index.
    pub fn line_of(&self, at: BytePos) -> usize {
        match self.line_starts.binary_search(&at) {
            Ok(exact) => exact,
            Err(insert) => insert.saturating_sub(1),
        }
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
        // The line index is UPDATED, not dropped — that is this bead's whole point, and
        // the update cannot read the text, so it is proportional to the edit.
        splice_line_starts(&mut self.line_starts, span, insert);
        // The full materialization is still dropped: rebuilding it is O(bytes), and only
        // callers that explicitly want a SourceText pay for it.
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
    use crate::source::scan_line_starts;

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

    /// **The differential for the incremental index** (bead franken_lean-0sv9): after every
    /// edit, the maintained index must equal a full rescan of the resulting bytes.
    ///
    /// This is the only honest proof for an incremental structure. Incremental bugs hide
    /// until a particular edit ORDER triggers them, so a handful of hand-written cases
    /// cannot establish the property — the same reason the rope itself is differentiated
    /// against a flat buffer. The insertion alphabet is weighted towards line terminators
    /// and the bytes around them, because that is where a splice rule goes wrong.
    #[test]
    fn the_incremental_line_index_equals_a_full_rescan_after_every_edit() {
        for seed in [
            0x494E_4445_5800_0001u64,
            0x494E_4445_5800_0002,
            0x494E_4445_5800_0003,
            0x494E_4445_5800_0004,
            0x494E_4445_5800_0005,
        ] {
            let mut rng = Seeded(seed);
            let start: Vec<u8> = [
                crate::source::BOM,
                "a\r\nb\nc\rd\ne".as_bytes(),
                "π\r\n漢\n".as_bytes(),
            ]
            .concat();
            let mut rope = Rope::from_utf8(&start).expect("valid");
            let mut flat = String::from_utf8(start).expect("valid");

            for step in 0..60 {
                // Terminators and their neighbours dominate on purpose.
                let inserts = [
                    "", "\n", "\r", "\r\n", "\n\r", "\n\n", "x", "π", "\u{FEFF}", "a\nb\nc",
                ];
                let insert = inserts[rng.below(inserts.len())];
                let a = floor_boundary(&flat, rng.below(flat.len() + 1));
                let b = floor_boundary(&flat, rng.below(flat.len() + 1));
                let (lo, hi) = if a <= b { (a, b) } else { (b, a) };
                let span = ByteSpan::new(BytePos(lo), BytePos(hi)).expect("forward");

                rope.replace(span, insert).unwrap_or_else(|error| {
                    panic!("seed {seed:#x} step {step}: refused a valid edit: {error}")
                });
                flat.replace_range(lo..hi, insert);

                // THE ASSERTION: the maintained index is exactly what a scan would produce.
                let expected = scan_line_starts(&flat);
                assert_eq!(
                    rope.line_starts, expected,
                    "seed {seed:#x} step {step}: incremental index diverged from a rescan \
                     (edit {lo}..{hi} -> {insert:?})"
                );

                // And the queries built on it agree, including the byte length, so an index
                // that is right cannot sit beside a length that is not.
                assert_eq!(rope.len_bytes(), flat.len());
                assert_eq!(rope.line_count(), expected.len());
                for line in 0..=expected.len() {
                    assert_eq!(rope.line_start(line), expected.get(line).copied());
                }
                // One probed offset per step: line_of over every byte every step would be
                // quadratic, and the index equality above already covers the whole file.
                if let Some((offset, _)) = flat.char_indices().nth(rng.below(flat.len().max(1))) {
                    let fresh = SourceText::from_utf8(flat.as_bytes()).expect("valid");
                    assert_eq!(
                        rope.line_of(BytePos(offset)),
                        fresh.line_of(BytePos(offset)),
                        "seed {seed:#x} step {step}: line_of disagreed at byte {offset}"
                    );
                }
            }
        }
    }

    /// The splice rule stated directly, case by case — the cases a naive newline scan gets
    /// wrong, each named so a failure says which rule broke.
    ///
    /// Note what this test does NOT pass in: the text. `splice_line_starts` cannot read it,
    /// which is the cost claim made structural — a function without access to the file
    /// cannot be proportional to it. A benchmark would say the same thing more weakly.
    #[test]
    fn the_splice_rule_handles_every_line_boundary_case() {
        let starts = |offsets: &[usize]| offsets.iter().map(|o| BytePos(*o)).collect::<Vec<_>>();
        let span = |a: usize, b: usize| ByteSpan::new(BytePos(a), BytePos(b)).expect("forward");

        // An edit wholly inside one line touches no other start.
        let mut index = starts(&[0, 4, 9]);
        splice_line_starts(&mut index, span(5, 6), "XY");
        assert_eq!(index, starts(&[0, 4, 10]), "only later starts shift");

        // Inserting a newline adds exactly one start, at the right absolute offset.
        let mut index = starts(&[0, 4]);
        splice_line_starts(&mut index, span(6, 6), "\n");
        assert_eq!(index, starts(&[0, 4, 7]));

        // Deleting a newline JOINS two lines: its start disappears.
        let mut index = starts(&[0, 4, 9]);
        splice_line_starts(&mut index, span(3, 4), "");
        assert_eq!(
            index,
            starts(&[0, 8]),
            "the start produced by the deleted \\n is gone"
        );

        // A deletion spanning SEVERAL newlines removes all of their starts.
        let mut index = starts(&[0, 3, 6, 9, 12]);
        splice_line_starts(&mut index, span(2, 10), "");
        assert_eq!(index, starts(&[0, 4]));

        // SPLITTING A CRLF: inserting between the \r and the \n does not change which bytes
        // are \n, so the start merely shifts. This is the case the bead calls out.
        let mut index = starts(&[0, 3]); // "a\r\nb" -> \n at 2, start at 3
        splice_line_starts(&mut index, span(2, 2), "X");
        assert_eq!(
            index,
            starts(&[0, 4]),
            "the \\n still starts a line, one byte later"
        );

        // Deleting the \n of a CRLF removes the start and leaves the \r as content.
        let mut index = starts(&[0, 3]);
        splice_line_starts(&mut index, span(2, 3), "");
        assert_eq!(index, starts(&[0]));

        // An edit at byte 0 never disturbs line 0's start — BOM or not.
        let mut index = starts(&[0, 5]);
        splice_line_starts(&mut index, span(0, 0), "\u{FEFF}");
        assert_eq!(index, starts(&[0, 8]), "line 0 still starts at 0");

        // Replacing the whole text with text containing terminators rebuilds from scratch.
        let mut index = starts(&[0, 3, 7]);
        splice_line_starts(&mut index, span(0, 9), "p\nq\n");
        assert_eq!(index, starts(&[0, 2, 4]));

        // An empty replacement of an empty span is a no-op.
        let mut index = starts(&[0, 4]);
        let before = index.clone();
        splice_line_starts(&mut index, span(2, 2), "");
        assert_eq!(index, before);
    }

    /// Trailing-terminator behaviour, which is where "line count" definitions usually rot.
    #[test]
    fn a_missing_or_added_final_terminator_is_described_not_normalized() {
        // No final newline: two lines, and nothing invents a third.
        let mut rope = Rope::from_utf8(b"a\nb").expect("valid");
        assert_eq!(rope.line_count(), 2);

        // Adding one at the very end adds exactly one start, and does NOT add a further
        // empty line beyond it.
        rope.insert(BytePos(3), "\n").expect("at end");
        assert_eq!(rope.line_count(), 3);
        assert_eq!(rope.line_start(2), Some(BytePos(4)));
        assert_eq!(rope.to_string_lossless(), "a\nb\n");
        assert_eq!(rope.line_starts, scan_line_starts("a\nb\n"));

        // Removing it again returns to two lines — no terminator is retained or invented.
        let span = ByteSpan::new(BytePos(3), BytePos(4)).expect("forward");
        rope.delete(span).expect("valid");
        assert_eq!(rope.line_count(), 2);
        assert_eq!(rope.to_string_lossless(), "a\nb");

        // A lone CR starts nothing, before or after an edit.
        let mut cr = Rope::from_utf8(b"a\rb").expect("valid");
        assert_eq!(cr.line_count(), 1);
        cr.insert(BytePos(3), "\rc").expect("at end");
        assert_eq!(
            cr.line_count(),
            1,
            "carriage returns are content, not terminators"
        );
        assert_eq!(cr.line_starts, scan_line_starts("a\rb\rc"));
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

    /// The two derived things an edit touches, and they are touched DIFFERENTLY — which is
    /// the change bead franken_lean-0sv9 made, so the test says which is which rather than
    /// lumping them together as "the derived index".
    #[test]
    fn an_edit_patches_the_line_index_and_drops_the_full_materialization() {
        let mut rope = Rope::from_utf8(b"a\nb").expect("valid");
        // Force the full materialization to exist.
        assert_eq!(rope.source_text().line_count(), 2);
        assert!(rope.materialized.is_some());
        rope.insert(BytePos(3), "\nc").expect("end");
        assert!(
            rope.materialized.is_none(),
            "the FULL materialization is O(bytes), so an edit must drop it rather than \
             rebuild it eagerly"
        );
        // The line index, by contrast, is maintained: current immediately, no scan.
        assert_eq!(
            rope.line_starts,
            scan_line_starts("a\nb\nc"),
            "the line index must be patched by the edit, not left stale or dropped"
        );
        assert_eq!(rope.line_count(), 3, "answered without materializing");
        assert!(
            rope.materialized.is_none(),
            "a line query must not have forced a materialization"
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
