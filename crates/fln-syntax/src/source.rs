//! Source text and `SourceInfo` — Vellum's position substrate (plan §9; bead fln-23cz).
//!
//! Anchored on the pinned Reference (`leanprover--lean4---v4.32.0`,
//! `src/lean/Init/Prelude.lean`), read rather than remembered:
//!
//! * `structure String.Pos.Raw where byteIdx : Nat` — a position is a **byte** index.
//!   Not a scalar index, not a UTF-16 offset. [`BytePos`] is that, and the scalar and
//!   UTF-16 views are *projections* computed on demand, never the stored form.
//! * `structure Substring.Raw where str, startPos, stopPos` — a slice is a pair of byte
//!   positions into a text.
//! * `SourceInfo.original (leading) (pos) (trailing) (endPos)` |
//!   `synthetic (pos) (endPos) (canonical := false)` | `none`.
//!
//! ## Lossless means byte-identical, not "semantically equal"
//!
//! The whole point of keeping `leading`/`trailing` trivia as spans is that the original
//! file can be reproduced **byte for byte** — every space, every comment, the BOM if
//! there was one, and whatever line endings the file actually had. A tree that
//! round-trips to an *equal tree* has proved much less: it has proved that its own
//! reader agrees with its own writer. So the law here is stated over bytes and asserted
//! in both directions, and [`SourceText::as_bytes`] returns exactly what was handed in.
//!
//! ## We do not normalize Unicode, ever
//!
//! Lean sees the bytes the user wrote. `é` as U+00E9 and `e` + U+0301 are different
//! programs, and an identifier normalized on the way in is a program silently rewritten.
//! That is the same false-identity failure as a lossy digest projection: two distinct
//! inputs collapsing into one internal state, after which nothing downstream can tell
//! them apart. This module therefore has no normalization step to disable — it stores
//! bytes and hands them back — and `normalization_is_never_applied` pins that by holding
//! two canonically-equivalent inputs apart at every surface this module exposes.

use std::fmt;

/// A byte offset into a source text — upstream `String.Pos.Raw`, whose only field is
/// `byteIdx`.
///
/// `usize` rather than a narrower integer because upstream's is a `Nat`: a cap would be
/// a limit we invented, and the first artifact to exceed it would be refused for a
/// reason the Reference does not have.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct BytePos(pub usize);

impl fmt::Display for BytePos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "byte {}", self.0)
    }
}

/// A half-open byte range — upstream `Substring.Raw`'s `(startPos, stopPos)` pair.
///
/// The text itself is deliberately **not** carried. Upstream's `Substring.Raw` holds its
/// `str`, which it can do cheaply because Lean strings are immutable and shared; the
/// faithful presentation of that belongs to the Mirror façade, over whatever text the
/// caller holds. Storing a copy per token here would let a span and its text disagree
/// about which text it is, which is a whole class of bug this layer simply does not have.
/// Recorded as a deliberate representation divergence rather than an oversight.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct ByteSpan {
    start: BytePos,
    end: BytePos,
}

impl ByteSpan {
    /// A span, or `None` if it runs backwards. Refusing rather than silently swapping:
    /// an inverted span is a caller bug, and normalizing it away would hide it.
    pub fn new(start: BytePos, end: BytePos) -> Option<ByteSpan> {
        (start.0 <= end.0).then_some(ByteSpan { start, end })
    }

    /// The empty span at a point — what trivia is when there is none.
    pub const fn empty_at(at: BytePos) -> ByteSpan {
        ByteSpan { start: at, end: at }
    }

    pub const fn start(self) -> BytePos {
        self.start
    }

    pub const fn end(self) -> BytePos {
        self.end
    }

    pub const fn len_bytes(self) -> usize {
        self.end.0 - self.start.0
    }

    pub const fn is_empty(self) -> bool {
        self.start.0 == self.end.0
    }
}

/// Why a source text was refused.
///
/// Decoding is total: arbitrary bytes get a typed answer, never a panic (FL-INV-07's
/// family). Invalid UTF-8 is a *rejection* — a real verdict about those bytes — and is
/// reported as such rather than being repaired, because repairing it would change the
/// program, and lossless is the one thing this module promises.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SourceError {
    /// The bytes are not valid UTF-8. `at` is the offset of the first invalid sequence.
    NotUtf8 { at: BytePos },
}

impl fmt::Display for SourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SourceError::NotUtf8 { at } => write!(f, "source is not valid UTF-8 at {at}"),
        }
    }
}

/// The UTF-8 byte-order mark, as bytes. Retained when present, never stripped.
pub const BOM: &[u8] = &[0xEF, 0xBB, 0xBF];

/// One immutable source text, holding exactly the bytes it was given.
///
/// Line starts are precomputed because every position projection needs them, and they are
/// derived from the stored text rather than tracked alongside it, so they cannot drift.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceText {
    text: String,
    /// Byte offset of the first byte of each line. Always starts with 0, so a text with
    /// no newline at all has exactly one line.
    line_starts: Vec<BytePos>,
}

impl SourceText {
    /// Take ownership of a source text, refusing invalid UTF-8 with its offset.
    ///
    /// A leading BOM is **kept**. Stripping it would be the smallest possible lossless
    /// violation and therefore the easiest one to ship by accident: byte offsets would
    /// shift by three against the file on disk, and every diagnostic span would be wrong
    /// in a way no round-trip test that reparsed its own output could detect.
    pub fn from_utf8(bytes: &[u8]) -> Result<SourceText, SourceError> {
        let text = match std::str::from_utf8(bytes) {
            Ok(text) => text.to_string(),
            Err(error) => {
                return Err(SourceError::NotUtf8 {
                    at: BytePos(error.valid_up_to()),
                });
            }
        };
        Ok(SourceText::from_string(text))
    }

    fn from_string(text: String) -> SourceText {
        let line_starts = scan_line_starts(&text);
        SourceText { text, line_starts }
    }

    /// Build from a text and a line index computed elsewhere.
    ///
    /// Exists so the rope can maintain its index incrementally (bead franken_lean-0sv9)
    /// without this module having to expose the field. Crate-private and debug-checked
    /// against a full scan, because a caller-supplied index is an invariant this type
    /// otherwise establishes for itself, and the whole value of the incremental path is
    /// that it agrees with the scan.
    pub(crate) fn from_parts(text: String, line_starts: Vec<BytePos>) -> SourceText {
        debug_assert_eq!(
            line_starts,
            scan_line_starts(&text),
            "a supplied line index must equal what a full scan produces"
        );
        SourceText { text, line_starts }
    }

    /// The line index this type would compute for itself — the reference an incremental
    /// index is differentiated against.
    pub(crate) fn line_starts(&self) -> &[BytePos] {
        &self.line_starts
    }

    /// **Exactly the bytes handed in.** The losslessness law rests on this.
    pub fn as_bytes(&self) -> &[u8] {
        self.text.as_bytes()
    }

    pub fn as_str(&self) -> &str {
        &self.text
    }

    pub fn len_bytes(&self) -> usize {
        self.text.len()
    }

    /// Whether the text begins with a UTF-8 BOM. Reported, not acted upon.
    pub fn has_bom(&self) -> bool {
        self.as_bytes().starts_with(BOM)
    }

    /// Number of lines. A text with no trailing newline still ends a line, and a text
    /// that does end with one does **not** gain an extra empty line here — the count is
    /// "how many line starts exist", which is the only definition that stays consistent
    /// under concatenation.
    pub fn line_count(&self) -> usize {
        self.line_starts.len()
    }

    /// The bytes of a span, or `None` if it is out of range or not on char boundaries.
    ///
    /// Boundary-checked rather than sliced blindly: a span landing mid-scalar is a caller
    /// bug, and `&str` indexing would turn it into a panic.
    pub fn span_str(&self, span: ByteSpan) -> Option<&str> {
        self.text.get(span.start.0..span.end.0)
    }

    /// Byte offset of the start of `line` (0-based).
    pub fn line_start(&self, line: usize) -> Option<BytePos> {
        self.line_starts.get(line).copied()
    }

    /// The line containing `at`, 0-based. Positions past the end clamp to the last line
    /// rather than failing: a caller asking about the end of the file has a real question.
    pub fn line_of(&self, at: BytePos) -> usize {
        match self.line_starts.binary_search(&at) {
            Ok(exact) => exact,
            Err(insert) => insert.saturating_sub(1),
        }
    }

    /// Project a byte offset to a line and a column in each of the three units the
    /// ecosystem actually uses (bead fln-23cz).
    ///
    /// Three units because three consumers disagree and all of them are right: the byte
    /// column is what `SourceInfo` stores and what a byte-exact artifact needs, the scalar
    /// column is what a human counting characters means, and the UTF-16 column is what the
    /// LSP wire protocol specifies. Collapsing them would put a plausible number in a
    /// protocol field that requires a specific one — silently wrong on any line containing
    /// a non-ASCII character, which for a prover means most interesting lines.
    ///
    /// Returns `None` if `at` is past the end or not on a char boundary.
    pub fn position_of(&self, at: BytePos) -> Option<Position> {
        if at.0 > self.text.len() || !self.text.is_char_boundary(at.0) {
            return None;
        }
        let line = self.line_of(at);
        let line_start = self.line_start(line)?;
        let prefix = self.text.get(line_start.0..at.0)?;
        Some(Position {
            line,
            byte_column: at.0 - line_start.0,
            scalar_column: prefix.chars().count(),
            utf16_column: prefix.chars().map(char::len_utf16).sum(),
        })
    }

    /// The inverse of [`position_of`](Self::position_of) for the scalar view.
    ///
    /// Provided because a projection asserted in one direction only is half a law: it
    /// proves the map exists, not that it is a bijection on valid inputs.
    pub fn byte_pos_of_scalar_column(&self, line: usize, scalar_column: usize) -> Option<BytePos> {
        self.column_to_byte(line, scalar_column, |_| 1)
    }

    /// The inverse for the UTF-16 view — what an editor's cursor position arrives as.
    pub fn byte_pos_of_utf16_column(&self, line: usize, utf16_column: usize) -> Option<BytePos> {
        self.column_to_byte(line, utf16_column, char::len_utf16)
    }

    fn column_to_byte(
        &self,
        line: usize,
        target: usize,
        width: impl Fn(char) -> usize,
    ) -> Option<BytePos> {
        let start = self.line_start(line)?;
        let end = self
            .line_start(line + 1)
            .unwrap_or(BytePos(self.text.len()));
        let mut consumed = 0usize;
        let mut at = start.0;
        for scalar in self.text.get(start.0..end.0)?.chars() {
            if consumed == target {
                return Some(BytePos(at));
            }
            // A column landing inside a multi-unit scalar has no byte answer; refusing is
            // the only honest response, and clamping would silently move a diagnostic.
            if consumed > target {
                return None;
            }
            consumed += width(scalar);
            at += scalar.len_utf8();
        }
        (consumed == target).then_some(BytePos(at))
    }
}

/// The authoritative definition of the line index: the offset just past every `\n`.
///
/// Deliberately keyed on `\n` alone, which is what makes the line-ending cases fall out
/// rather than needing special handling. A CRLF's `\n` starts a line and its `\r` is
/// ordinary content of the previous line; a lone `\r` starts nothing; a BOM is content of
/// line 0, which always starts at 0; and a file with no final terminator still ends a line
/// without gaining a start for a line that is not there. Nothing here rewrites a byte, so
/// the index describes the bytes that are present rather than a tidied version of them.
pub(crate) fn scan_line_starts(text: &str) -> Vec<BytePos> {
    let mut line_starts = vec![BytePos(0)];
    for (offset, byte) in text.bytes().enumerate() {
        if byte == b'\n' {
            line_starts.push(BytePos(offset + 1));
        }
    }
    line_starts
}

/// A byte offset projected into the three units of [`SourceText::position_of`].
///
/// All three are carried together on purpose: a consumer picks the one its protocol
/// requires, and no arithmetic converts between them, because no such arithmetic exists
/// for arbitrary text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Position {
    /// 0-based line.
    pub line: usize,
    /// Bytes from the line start — the unit `SourceInfo` itself stores.
    pub byte_column: usize,
    /// Unicode scalar values from the line start.
    pub scalar_column: usize,
    /// UTF-16 code units from the line start — the LSP wire unit.
    pub utf16_column: usize,
}

/// `Lean.SourceInfo` (Prelude.lean), one arm per upstream constructor.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceInfo {
    /// A token the parser read from the file, with its surrounding trivia.
    ///
    /// `leading` is inferred after parsing upstream (`Syntax.updateLeading`) because the
    /// preceding token is not well-defined during backtracking; the field is here from the
    /// start so the shape does not change when that pass exists.
    Original {
        leading: ByteSpan,
        pos: BytePos,
        trailing: ByteSpan,
        end_pos: BytePos,
    },
    /// Syntax produced by a metaprogram or by Lean itself, annotated with the span it
    /// came from. `canonical` marks syntax that should be treated as if the user wrote it
    /// for hovers and error messages; upstream defaults it to `false`.
    Synthetic {
        pos: BytePos,
        end_pos: BytePos,
        canonical: bool,
    },
    /// A synthesized token with no position information at all.
    None,
}

impl SourceInfo {
    /// `SourceInfo.getPos?` — the start position, if this info has one.
    ///
    /// `canonical_only` mirrors upstream's parameter: with it set, non-canonical synthetic
    /// syntax reports no position, which is how hovers avoid attaching to expansions the
    /// user never wrote.
    pub const fn pos(self, canonical_only: bool) -> Option<BytePos> {
        match self {
            SourceInfo::Original { pos, .. } => Some(pos),
            SourceInfo::Synthetic { pos, canonical, .. } => {
                if canonical_only && !canonical {
                    None
                } else {
                    Some(pos)
                }
            }
            SourceInfo::None => None,
        }
    }

    /// `SourceInfo.getTailPos?` — the end position, under the same canonicality rule.
    pub const fn end_pos(self, canonical_only: bool) -> Option<BytePos> {
        match self {
            SourceInfo::Original { end_pos, .. } => Some(end_pos),
            SourceInfo::Synthetic {
                end_pos, canonical, ..
            } => {
                if canonical_only && !canonical {
                    None
                } else {
                    Some(end_pos)
                }
            }
            SourceInfo::None => None,
        }
    }

    /// The span this token occupies **including** its trivia — what a lossless
    /// reassembly walks. `None` for anything not read from the file, because synthetic
    /// syntax contributes no bytes to the original text.
    pub const fn full_span(self) -> Option<ByteSpan> {
        match self {
            SourceInfo::Original {
                leading, trailing, ..
            } => Some(ByteSpan {
                start: leading.start,
                end: trailing.end,
            }),
            SourceInfo::Synthetic { .. } | SourceInfo::None => None,
        }
    }
}

/// Why a token sequence failed to account for a source text exactly.
///
/// Each arm names a distinct way losslessness breaks, because "the round trip differed"
/// tells whoever is paged nothing about which byte moved.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LosslessError {
    /// A token was not read from the file, so it contributes no bytes.
    NotOriginal { index: usize },
    /// A token's own span is not `pos..end_pos`, or its trivia does not abut it.
    Discontiguous {
        index: usize,
        expected: BytePos,
        found: BytePos,
    },
    /// The sequence does not begin at byte 0 or does not end at the last byte.
    DoesNotCover { covered: ByteSpan, text_len: usize },
    /// A span was out of range or landed inside a scalar.
    UnreadableSpan { index: usize, span: ByteSpan },
}

/// Reassemble the source text from a token sequence, returning the exact bytes.
///
/// This is the losslessness law in executable form. It walks the tokens in order and
/// requires that leading trivia, token, and trailing trivia abut exactly and that the
/// whole sequence covers `[0, len)` — so the result is not merely *equal* to the original,
/// it is built only from spans that tile it without gap or overlap. A test then asserts
/// the returned bytes are byte-identical to the input, which is the direction that
/// actually matters: a reassembly that agreed with its own reader would prove nothing.
pub fn reassemble(text: &SourceText, tokens: &[SourceInfo]) -> Result<Vec<u8>, LosslessError> {
    let mut out = Vec::with_capacity(text.len_bytes());
    let mut cursor = BytePos(0);
    for (index, token) in tokens.iter().enumerate() {
        let SourceInfo::Original {
            leading,
            pos,
            trailing,
            end_pos,
        } = *token
        else {
            return Err(LosslessError::NotOriginal { index });
        };
        // Every boundary is checked against the running cursor, so a gap or an overlap is
        // reported at the token that introduced it rather than as a final length mismatch.
        // The chain a token must satisfy to contribute a contiguous run of bytes:
        // cursor -> leading.start, leading.end == pos (trivia abuts its token), and
        // end_pos == trailing.start (the token abuts its trailing trivia). Getting this
        // list wrong is how a "lossless" reassembly quietly emits the right number of
        // bytes from the wrong places, so each equality names both sides.
        for (expected, found) in [
            (cursor, leading.start()),
            (leading.end(), pos),
            (end_pos, trailing.start()),
        ] {
            if expected != found {
                return Err(LosslessError::Discontiguous {
                    index,
                    expected,
                    found,
                });
            }
        }
        let full = ByteSpan {
            start: leading.start(),
            end: trailing.end(),
        };
        let bytes = text
            .span_str(full)
            .ok_or(LosslessError::UnreadableSpan { index, span: full })?;
        out.extend_from_slice(bytes.as_bytes());
        cursor = trailing.end();
    }
    if cursor.0 != text.len_bytes() {
        return Err(LosslessError::DoesNotCover {
            covered: ByteSpan {
                start: BytePos(0),
                end: cursor,
            },
            text_len: text.len_bytes(),
        });
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build the trivially-lossless single-token tiling of a text: one token whose
    /// trailing trivia is everything. Enough to exercise the law without a parser.
    fn whole_text_token(text: &SourceText) -> SourceInfo {
        let end = BytePos(text.len_bytes());
        SourceInfo::Original {
            leading: ByteSpan::empty_at(BytePos(0)),
            pos: BytePos(0),
            trailing: ByteSpan::empty_at(end),
            end_pos: end,
        }
    }

    /// Build a token from its four boundaries, so the abutment invariants hold by
    /// construction and a test cannot accidentally assert against a malformed token.
    fn token_at(lead_start: usize, pos: usize, end_pos: usize, trail_end: usize) -> SourceInfo {
        SourceInfo::Original {
            leading: ByteSpan::new(BytePos(lead_start), BytePos(pos)).expect("forward"),
            pos: BytePos(pos),
            trailing: ByteSpan::new(BytePos(end_pos), BytePos(trail_end)).expect("forward"),
            end_pos: BytePos(end_pos),
        }
    }

    #[test]
    fn a_source_text_hands_back_exactly_the_bytes_it_was_given() {
        // Every awkward shape at once: BOM, CRLF, bare LF, bare CR, a tab, trailing
        // whitespace, no final newline, and non-ASCII.
        let raw: Vec<u8> = [
            BOM,
            "def f := 1\r\n".as_bytes(),
            "  -- π comment\n".as_bytes(),
            "\ttab\r".as_bytes(),
            "end".as_bytes(),
        ]
        .concat();
        let text = SourceText::from_utf8(&raw).expect("valid UTF-8");
        assert_eq!(text.as_bytes(), raw.as_slice(), "bytes were not preserved");
        assert!(text.has_bom(), "the BOM must be reported, not stripped");
        assert_eq!(text.len_bytes(), raw.len());
    }

    #[test]
    fn reassembly_is_byte_identical_in_both_directions() {
        for raw in [
            b"".to_vec(),
            b"x".to_vec(),
            [BOM, b"def f := 1\r\n\r\n"].concat(),
            "π := 3\n-- \u{1F600}\r\nend\r".as_bytes().to_vec(),
        ] {
            let text = SourceText::from_utf8(&raw).expect("valid UTF-8");
            let tokens = [whole_text_token(&text)];
            let rebuilt = reassemble(&text, &tokens).expect("the tiling covers the text");
            // The direction that matters: the reassembly equals the ORIGINAL bytes, not
            // merely some re-read of our own output.
            assert_eq!(rebuilt, raw, "reassembly lost bytes");
            // And the other direction: re-taking the text from the reassembly is a fixed
            // point, so the pair is a genuine round trip rather than one lucky mapping.
            let again = SourceText::from_utf8(&rebuilt).expect("still valid");
            assert_eq!(again.as_bytes(), text.as_bytes());
            assert_eq!(again, text);
        }
    }

    #[test]
    fn a_tiling_with_a_gap_or_an_overlap_is_refused_not_papered_over() {
        let raw = b"abcdef".to_vec();
        let text = SourceText::from_utf8(&raw).expect("valid");
        // A GAP: the second token's leading trivia starts at 4 while the first ended at 3.
        let gapped = [token_at(0, 0, 3, 3), token_at(4, 4, 6, 6)];
        assert!(matches!(
            reassemble(&text, &gapped),
            Err(LosslessError::Discontiguous { index: 1, .. })
        ));

        // AN OVERLAP: the second token starts at 2, re-emitting bytes 2..3. Caught for
        // the same reason — without the cursor check this would produce plausible bytes
        // of the wrong length.
        let overlapping = [token_at(0, 0, 3, 3), token_at(2, 2, 6, 6)];
        assert!(matches!(
            reassemble(&text, &overlapping),
            Err(LosslessError::Discontiguous { index: 1, .. })
        ));

        // SHORT: a tiling that stops early is not a tiling.
        let short = [token_at(0, 0, 3, 3)];
        assert!(matches!(
            reassemble(&text, &short),
            Err(LosslessError::DoesNotCover { text_len: 6, .. })
        ));

        // And synthetic syntax contributes no bytes, so it cannot appear in one.
        assert!(matches!(
            reassemble(&text, &[SourceInfo::None]),
            Err(LosslessError::NotOriginal { index: 0 })
        ));

        // The correct tiling still passes, so none of the above is a blanket refusal.
        let exact = [token_at(0, 0, 3, 3), token_at(3, 3, 6, 6)];
        assert_eq!(reassemble(&text, &exact).expect("tiles"), raw);
    }

    /// **We must not normalize.** Two canonically-equivalent inputs are different
    /// programs, and every surface here must keep them apart (bead fln-23cz).
    #[test]
    fn normalization_is_never_applied() {
        // "é" precomposed (U+00E9, 2 bytes) vs decomposed ("e" + U+0301, 3 bytes). NFC
        // would map the second onto the first.
        let precomposed = "def \u{00E9} := 1\n".as_bytes().to_vec();
        let decomposed = "def e\u{0301} := 1\n".as_bytes().to_vec();
        assert_ne!(precomposed, decomposed, "the fixture must be byte-distinct");

        let a = SourceText::from_utf8(&precomposed).expect("valid");
        let b = SourceText::from_utf8(&decomposed).expect("valid");

        // Distinct at every surface this module exposes.
        assert_ne!(a, b);
        assert_ne!(a.as_bytes(), b.as_bytes());
        assert_ne!(a.len_bytes(), b.len_bytes());
        assert_eq!(a.as_bytes(), precomposed.as_slice());
        assert_eq!(b.as_bytes(), decomposed.as_slice());

        // And the projections disagree exactly as they should, because the two texts
        // genuinely differ in scalar and byte width while agreeing on line structure.
        let end_a = a.position_of(BytePos(a.len_bytes() - 1)).expect("in range");
        let end_b = b.position_of(BytePos(b.len_bytes() - 1)).expect("in range");
        assert_eq!(end_a.line, end_b.line);
        assert_ne!(
            (end_a.byte_column, end_a.scalar_column),
            (end_b.byte_column, end_b.scalar_column),
            "a normalizing implementation would make these agree"
        );

        // Round trip preserves each exactly, so nothing downstream can conflate them.
        for (raw, text) in [(&precomposed, &a), (&decomposed, &b)] {
            let rebuilt = reassemble(text, &[whole_text_token(text)]).expect("tiles");
            assert_eq!(&rebuilt, raw);
        }
    }

    #[test]
    fn the_three_position_projections_agree_with_their_units_and_invert() {
        // A line mixing ASCII, a 2-byte scalar, a 3-byte scalar, and a scalar outside the
        // BMP (4 bytes, TWO UTF-16 code units) — the case that separates all three units.
        let raw = "aé漢\u{1F600}b\nsecond\n".as_bytes().to_vec();
        let text = SourceText::from_utf8(&raw).expect("valid");

        // Byte offset of 'b': 1 + 2 + 3 + 4 = 10.
        let at_b = BytePos(10);
        assert_eq!(text.as_str().as_bytes()[at_b.0], b'b');
        let position = text.position_of(at_b).expect("in range");
        assert_eq!(position.line, 0);
        assert_eq!(position.byte_column, 10, "bytes from the line start");
        assert_eq!(position.scalar_column, 4, "a, é, 漢, emoji");
        assert_eq!(
            position.utf16_column, 5,
            "the emoji is a surrogate pair, so UTF-16 counts one more than scalars"
        );

        // The units are genuinely different numbers here — a test whose fixture made them
        // coincide would pass against an implementation that returned any one of them.
        assert_ne!(position.byte_column, position.scalar_column);
        assert_ne!(position.scalar_column, position.utf16_column);

        // BOTH DIRECTIONS: each column view inverts back to the same byte offset.
        assert_eq!(
            text.byte_pos_of_scalar_column(0, position.scalar_column),
            Some(at_b)
        );
        assert_eq!(
            text.byte_pos_of_utf16_column(0, position.utf16_column),
            Some(at_b)
        );

        // A column landing inside a scalar has no byte answer, and is refused rather than
        // clamped — clamping would move a diagnostic silently.
        assert_eq!(text.byte_pos_of_utf16_column(0, 4), None, "mid-surrogate");

        // Round-trip every valid boundary on the first line, so the inverse is checked as
        // a bijection rather than at one convenient point.
        for (offset, _) in text.as_str().char_indices().take_while(|(i, _)| *i <= 10) {
            let at = BytePos(offset);
            let projected = text.position_of(at).expect("boundary is in range");
            assert_eq!(
                text.byte_pos_of_scalar_column(0, projected.scalar_column),
                Some(at)
            );
            assert_eq!(
                text.byte_pos_of_utf16_column(0, projected.utf16_column),
                Some(at)
            );
        }
    }

    #[test]
    fn line_structure_survives_crlf_lone_cr_and_a_missing_final_newline() {
        // CRLF, then bare LF, then a bare CR that is NOT a line break, then no final
        // newline. Line starts follow '\n' only, and the '\r' stays inside its line.
        let raw = b"a\r\nb\nc\rd".to_vec();
        let text = SourceText::from_utf8(&raw).expect("valid");
        assert_eq!(text.line_count(), 3, "only the two '\\n' bytes start lines");
        assert_eq!(text.line_start(0), Some(BytePos(0)));
        assert_eq!(text.line_start(1), Some(BytePos(3)));
        assert_eq!(text.line_start(2), Some(BytePos(5)));
        assert_eq!(text.line_start(3), None);

        // The CR is part of line 0's content, so the byte column past it counts it.
        assert_eq!(
            text.line_of(BytePos(2)),
            0,
            "the '\\n' of a CRLF ends line 0"
        );
        assert_eq!(text.line_of(BytePos(3)), 1);
        // The lone CR does not start a line.
        assert_eq!(text.line_of(BytePos(6)), 2);
        assert_eq!(
            text.position_of(BytePos(7)).expect("in range").byte_column,
            2
        );

        // A trailing newline does not invent an extra line start beyond its own.
        let trailing = SourceText::from_utf8(b"a\n").expect("valid");
        assert_eq!(trailing.line_count(), 2);
        assert_eq!(trailing.line_start(1), Some(BytePos(2)));
    }

    #[test]
    fn invalid_input_is_a_typed_rejection_at_its_offset_and_never_a_panic() {
        // A lone continuation byte, and a truncated multi-byte sequence.
        for (raw, at) in [
            (vec![b'a', 0xFF, b'b'], 1usize),
            (
                "ok "
                    .as_bytes()
                    .iter()
                    .copied()
                    .chain([0xE6, 0xBC])
                    .collect::<Vec<u8>>(),
                3,
            ),
        ] {
            assert_eq!(
                SourceText::from_utf8(&raw),
                Err(SourceError::NotUtf8 { at: BytePos(at) }),
                "invalid UTF-8 must be refused with the offset of the first bad sequence"
            );
        }
        // Valid but adversarial input is accepted, not refused for being unusual: a NUL,
        // an unpaired-looking sequence that is legal, and a very long line.
        for raw in [
            vec![0u8],
            "\u{FEFF}\u{FEFF}".as_bytes().to_vec(),
            "x".repeat(10_000).into_bytes(),
        ] {
            let text = SourceText::from_utf8(&raw).expect("valid UTF-8 is accepted");
            assert_eq!(text.as_bytes(), raw.as_slice());
        }
        // Out-of-range and mid-scalar positions answer None rather than panicking.
        let text = SourceText::from_utf8("é".as_bytes()).expect("valid");
        assert_eq!(text.position_of(BytePos(1)), None, "mid-scalar");
        assert_eq!(text.position_of(BytePos(99)), None, "past the end");
        assert_eq!(
            text.span_str(ByteSpan::new(BytePos(0), BytePos(1)).expect("fwd")),
            None
        );
    }

    #[test]
    fn source_info_reports_positions_under_the_upstream_canonicality_rule() {
        let original = SourceInfo::Original {
            leading: ByteSpan::empty_at(BytePos(0)),
            pos: BytePos(0),
            trailing: ByteSpan::new(BytePos(3), BytePos(4)).expect("fwd"),
            end_pos: BytePos(3),
        };
        assert_eq!(original.pos(false), Some(BytePos(0)));
        assert_eq!(
            original.pos(true),
            Some(BytePos(0)),
            "original is always canonical"
        );
        assert_eq!(original.end_pos(true), Some(BytePos(3)));
        assert_eq!(
            original.full_span().map(ByteSpan::len_bytes),
            Some(4),
            "the full span spans leading through trailing"
        );

        // Synthetic: canonical_only hides a non-canonical span, which is how a hover
        // avoids attaching to an expansion the user never wrote.
        let plain = SourceInfo::Synthetic {
            pos: BytePos(7),
            end_pos: BytePos(9),
            canonical: false,
        };
        assert_eq!(plain.pos(false), Some(BytePos(7)));
        assert_eq!(plain.pos(true), None);
        assert_eq!(plain.end_pos(true), None);
        assert_eq!(
            plain.full_span(),
            None,
            "synthetic syntax contributes no bytes"
        );

        let canonical = SourceInfo::Synthetic {
            pos: BytePos(7),
            end_pos: BytePos(9),
            canonical: true,
        };
        assert_eq!(canonical.pos(true), Some(BytePos(7)));

        assert_eq!(SourceInfo::None.pos(false), None);
        assert_eq!(SourceInfo::None.full_span(), None);
    }

    #[test]
    fn an_inverted_span_is_refused_rather_than_silently_swapped() {
        assert_eq!(ByteSpan::new(BytePos(5), BytePos(3)), None);
        let forward = ByteSpan::new(BytePos(3), BytePos(5)).expect("forward");
        assert_eq!(forward.len_bytes(), 2);
        assert!(!forward.is_empty());
        assert!(ByteSpan::empty_at(BytePos(3)).is_empty());
    }
}
