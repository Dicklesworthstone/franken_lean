//! The parser's view of a source text, and the boundary that keeps it honest
//! (plan §9; bead franken_lean-tkr2).
//!
//! ## The finding this module exists for
//!
//! The Reference does **not** parse the bytes on disk. `String.crlfToLf`
//! (`Init/Data/String/Extra.lean:95`) normalizes CRLF to LF, and `Lean/Server/Utils.lean`
//! documents the server's document text as "normalized using `String.crlfToLf`, which
//! preserves logical line/column numbers". That is *why* the whitespace parser
//! (`Lean/Parser/Basic.lean:563`) can afford to reject any `\r` it meets outright with
//! "isolated carriage returns are not allowed" — after normalization a `\r` genuinely is
//! isolated, because every CRLF has already become an LF.
//!
//! So "preserve the bytes the user wrote" and "be faithful to the parser" are statements
//! about **two different texts**, and collapsing them is a bug in either direction:
//!
//! * normalize in place and the original bytes are gone — the lossless claim dies, byte
//!   offsets shift by one per CRLF against the file on disk, and every diagnostic span in
//!   a Windows-authored file is wrong;
//! * never normalize and a CRLF file fails on its first line ending, which the Reference
//!   accepts — a divergence, on the most common file shape on one major platform.
//!
//! The resolution is not to pick one. It is to keep the original **and** derive the view,
//! with a mapping between them that is asserted in both directions, so a position can
//! always be carried back to the byte the user actually wrote. Normalization becomes an
//! explicit, reversible projection instead of a silent rewrite — the same discipline as
//! the set-vs-sequence projection in fln-hash: two views of one value, neither pretending
//! to be the other.
//!
//! ## What is preserved
//!
//! Everything. [`SourceView::reconstruct_original`] returns the original bytes exactly,
//! and that is asserted against the input rather than against a re-derivation of our own
//! output. A BOM is untouched — it is not a line ending. A lone `\r` is **kept as-is**,
//! because `crlfToLf` only rewrites the two-byte sequence; the parser will reject it
//! later, which is a *parse* verdict about the file and not something this layer may
//! quietly repair. A final line with no terminator gains nothing.

use crate::source::{BytePos, SourceText};

/// A source text as the parser sees it: CRLF normalized to LF, with the map back.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceView {
    /// The normalized text — what a parser consumes.
    normalized: SourceText,
    /// View offsets at which a `\r` was removed, ascending. Each entry is the offset **in
    /// the view** of the `\n` that the removed `\r` preceded, so it is also the count of
    /// view bytes before the removal.
    removals: Vec<usize>,
    original_len: usize,
}

impl SourceView {
    /// Derive the parser's view of `original`.
    ///
    /// Only the exact two-byte sequence `\r\n` is rewritten, matching `crlfToLf`. A lone
    /// `\r` survives into the view unchanged, where the whitespace parser will refuse it —
    /// that refusal is a verdict about the file, and pre-emptively "fixing" it here would
    /// be this module changing a program.
    pub fn of(original: &SourceText) -> SourceView {
        let bytes = original.as_bytes();
        let mut text = String::with_capacity(bytes.len());
        let mut removals = Vec::new();
        let mut index = 0usize;
        while index < bytes.len() {
            if bytes[index] == b'\r' && bytes.get(index + 1) == Some(&b'\n') {
                // Drop the CR. The LF lands at the current view length, which is exactly
                // the coordinate the reverse map needs.
                removals.push(text.len());
                text.push('\n');
                index += 2;
            } else {
                // Copy one whole scalar, so the view is never split mid-character. The
                // original is valid UTF-8, so this always advances.
                let rest = &original.as_str()[index..];
                let scalar = rest.chars().next().expect("index is a char boundary");
                text.push(scalar);
                index += scalar.len_utf8();
            }
        }
        SourceView {
            normalized: SourceText::from_utf8(text.as_bytes())
                .expect("normalizing valid UTF-8 keeps it valid"),
            removals,
            original_len: bytes.len(),
        }
    }

    /// The text a parser consumes.
    pub fn normalized(&self) -> &SourceText {
        &self.normalized
    }

    /// Whether normalization actually changed anything. Reported so a caller can tell a
    /// pass-through from a rewrite without comparing lengths itself.
    pub fn normalized_anything(&self) -> bool {
        !self.removals.is_empty()
    }

    /// How many CRLF pairs were collapsed.
    pub fn removed_count(&self) -> usize {
        self.removals.len()
    }

    pub fn original_len_bytes(&self) -> usize {
        self.original_len
    }

    /// Map a view offset back to the original byte it came from.
    ///
    /// Total on `0..=view len`: every view position corresponds to an original position,
    /// because normalization only ever *removes* bytes. This is the direction diagnostics
    /// need — a span found while parsing has to name a byte in the file the user has open.
    pub fn to_original(&self, view: BytePos) -> BytePos {
        // Add one per removal at or before this view offset. The boundary is `<=`, and
        // getting it wrong is the obvious trap: at a removal point the view's `\n` IS the
        // original's `\n` — the CR is the byte that is absent from the view — so a `<`
        // here would map the LF onto the CR's offset and every diagnostic on a CRLF line
        // would point one byte early. The round-trip test caught exactly that.
        let shifted = self.removals.partition_point(|at| *at <= view.0);
        BytePos(view.0 + shifted)
    }

    /// Map an original offset forward to the view, or `None` if that byte is not in it.
    ///
    /// `None` means exactly one thing: the byte is a `\r` that normalization removed. It
    /// is not an error and it is not clamped to a neighbour — a caller asking about a byte
    /// the parser never saw deserves to be told so rather than handed the position of a
    /// different byte.
    pub fn from_original(&self, original: BytePos) -> Option<BytePos> {
        if original.0 > self.original_len {
            return None;
        }
        // The i-th removed CR sits at original offset `removals[i] + i`: its view
        // coordinate plus the i removals that preceded it. Stating it that way makes both
        // questions below one-liners instead of an accumulation whose off-by-ones have to
        // be reasoned about.
        let removed_before = self
            .removals
            .iter()
            .enumerate()
            .take_while(|(index, at)| *at + index < original.0)
            .count();
        // Is this byte itself a removed CR?
        if self
            .removals
            .get(removed_before)
            .is_some_and(|at| at + removed_before == original.0)
        {
            return None;
        }
        Some(BytePos(original.0 - removed_before))
    }

    /// Rebuild the original bytes from the view and the removal record.
    ///
    /// The losslessness law for this boundary, stated over bytes: normalization is only a
    /// projection if it is invertible, and this is the inverse. A test asserts the result
    /// equals the ORIGINAL input — not a re-normalization of our own output, which would
    /// only prove the two halves of this module agree with each other.
    pub fn reconstruct_original(&self) -> Vec<u8> {
        let view = self.normalized.as_bytes();
        let mut out = Vec::with_capacity(self.original_len);
        let mut removal = 0usize;
        for (offset, byte) in view.iter().enumerate() {
            if removal < self.removals.len() && self.removals[removal] == offset {
                out.push(b'\r');
                removal += 1;
            }
            out.push(*byte);
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::BOM;

    fn view_of(raw: &[u8]) -> (SourceText, SourceView) {
        let original = SourceText::from_utf8(raw).expect("valid UTF-8");
        let view = SourceView::of(&original);
        (original, view)
    }

    /// The corpus the bead asks for, in one input: mixed CRLF and LF, a BOM, a lone CR, a
    /// final line with no terminator, and non-ASCII either side of a line ending.
    fn awkward_corpus() -> Vec<Vec<u8>> {
        vec![
            b"".to_vec(),
            b"\r\n".to_vec(),
            b"a".to_vec(),
            [BOM, b"def f := 1\r\nlemma g := 2\n"].concat(),
            [BOM, b"a\r\nb\nc\rd\r\n"].concat(),
            "π\r\n漢\ndone\r".as_bytes().to_vec(),
            b"trailing\r\n\r\n\r\n".to_vec(),
            b"no terminator".to_vec(),
            b"\r".to_vec(),
            b"\n\r\n\n".to_vec(),
        ]
    }

    /// **Byte-identity against the ORIGINAL**, for every shape in the corpus. Asserted
    /// against the input bytes, not against a re-derivation of our own output.
    #[test]
    fn the_view_reconstructs_the_original_bytes_exactly() {
        for raw in awkward_corpus() {
            let (original, view) = view_of(&raw);
            assert_eq!(
                view.reconstruct_original(),
                raw,
                "reconstruction lost bytes for {raw:?}"
            );
            assert_eq!(view.original_len_bytes(), raw.len());
            // The view itself is a genuine normalization: no CRLF survives in it, and
            // nothing else changed.
            assert!(
                !view.normalized().as_str().contains("\r\n"),
                "the view still contains a CRLF pair"
            );
            assert_eq!(
                view.normalized().len_bytes() + view.removed_count(),
                raw.len(),
                "exactly one byte per CRLF was removed and nothing else"
            );
            // A BOM is not a line ending and must be untouched.
            assert_eq!(
                view.normalized().has_bom(),
                original.has_bom(),
                "normalization must not touch a BOM"
            );
        }
    }

    /// A lone CR is KEPT. `crlfToLf` rewrites only the two-byte sequence, and the parser's
    /// later refusal of an isolated carriage return is a verdict about the file — not
    /// something this layer may pre-emptively repair.
    #[test]
    fn a_lone_carriage_return_survives_normalization() {
        let (_, view) = view_of(b"a\rb\r\nc\r");
        assert_eq!(view.removed_count(), 1, "only the CRLF pair was collapsed");
        assert_eq!(view.normalized().as_str(), "a\rb\nc\r");
        assert_eq!(view.reconstruct_original(), b"a\rb\r\nc\r");
        // A CR at the very end, with no LF after it, is not a pair.
        let (_, tail) = view_of(b"x\r");
        assert!(!tail.normalized_anything());
        assert_eq!(tail.reconstruct_original(), b"x\r");
    }

    /// **Both directions**, at every boundary, for every corpus entry — the discipline a
    /// one-way mapping test would miss.
    #[test]
    fn the_position_map_round_trips_in_both_directions() {
        for raw in awkward_corpus() {
            let (original, view) = view_of(&raw);
            let view_text = view.normalized();

            // Forward then back is the identity on every view position, including the
            // end-of-text position.
            for offset in 0..=view_text.len_bytes() {
                if !view_text.as_str().is_char_boundary(offset) {
                    continue;
                }
                let at_original = view.to_original(BytePos(offset));
                assert!(
                    at_original.0 <= raw.len(),
                    "{raw:?}: view {offset} mapped past the original"
                );
                assert_eq!(
                    view.from_original(at_original),
                    Some(BytePos(offset)),
                    "{raw:?}: view {offset} -> original {} did not map back",
                    at_original.0
                );
            }

            // Every original byte either maps into the view or is a removed CR — and
            // nothing else is ever `None`, so the map's domain is exactly accounted for.
            let mut unmapped = 0usize;
            for offset in 0..original.len_bytes() {
                if !original.as_str().is_char_boundary(offset) {
                    continue;
                }
                match view.from_original(BytePos(offset)) {
                    Some(_) => {}
                    None => {
                        assert_eq!(
                            original.as_bytes()[offset],
                            b'\r',
                            "{raw:?}: original {offset} is unmapped but is not a CR"
                        );
                        unmapped += 1;
                    }
                }
            }
            assert_eq!(
                unmapped,
                view.removed_count(),
                "{raw:?}: unmapped originals must be exactly the removed CRs"
            );
        }
    }

    /// A diagnostic found in the view must name the byte the user wrote — which is the
    /// whole reason the map exists, so it gets a case rather than being implied.
    #[test]
    fn a_view_position_names_the_original_byte_a_user_would_see() {
        // "a\r\nbb\r\nc": the 'c' is at view offset 6 and original offset 8.
        let raw = b"a\r\nbb\r\nc";
        let (original, view) = view_of(raw);
        assert_eq!(view.normalized().as_str(), "a\nbb\nc");
        let c_in_view = view.normalized().as_str().find('c').expect("present");
        assert_eq!(c_in_view, 5);
        let c_in_original = view.to_original(BytePos(c_in_view));
        assert_eq!(c_in_original, BytePos(7));
        assert_eq!(original.as_bytes()[c_in_original.0], b'c');

        // Line/column in the VIEW is what upstream's "preserves logical line/column
        // numbers" refers to, and it must agree with the original's line structure — the
        // point of normalizing rather than stripping.
        assert_eq!(view.normalized().line_count(), original.line_count());
    }

    #[test]
    fn out_of_range_and_removed_positions_answer_none_rather_than_guessing() {
        let (_, view) = view_of(b"a\r\nb");
        assert_eq!(view.from_original(BytePos(99)), None, "past the end");
        // Byte 1 is the removed CR.
        assert_eq!(
            view.from_original(BytePos(1)),
            None,
            "a removed CR is not in the view"
        );
        // Its LF is present.
        assert_eq!(view.from_original(BytePos(2)), Some(BytePos(1)));
        assert_eq!(view.from_original(BytePos(0)), Some(BytePos(0)));
        assert_eq!(view.from_original(BytePos(3)), Some(BytePos(2)));
        // The end position maps to the end.
        assert_eq!(view.from_original(BytePos(4)), Some(BytePos(3)));
    }

    #[test]
    fn a_text_with_no_crlf_is_a_pass_through() {
        for raw in [
            b"a\nb\n".to_vec(),
            b"no endings".to_vec(),
            "π\n".as_bytes().to_vec(),
        ] {
            let (original, view) = view_of(&raw);
            assert!(!view.normalized_anything());
            assert_eq!(view.removed_count(), 0);
            assert_eq!(view.normalized().as_bytes(), original.as_bytes());
            assert_eq!(view.reconstruct_original(), raw);
            // The map is the identity.
            for offset in 0..=raw.len() {
                if original.as_str().is_char_boundary(offset) {
                    assert_eq!(view.to_original(BytePos(offset)), BytePos(offset));
                    assert_eq!(view.from_original(BytePos(offset)), Some(BytePos(offset)));
                }
            }
        }
    }
}
