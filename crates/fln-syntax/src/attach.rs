//! Trivia attachment — deciding which node owns which byte (plan §9; bead
//! franken_lean-tkr2).
//!
//! ## The rule, read off the pin rather than invented
//!
//! Losslessness usually dies here, and it dies to "close enough": trivia attached to a
//! plausible neighbour, which round-trips for most inputs and loses a byte on the awkward
//! ones. So the rule is not a judgement call. `Lean/Syntax.lean:270` is the whole of it:
//!
//! ```text
//! private def chooseNiceTrailStop (trail : Substring.Raw) : String.Pos.Raw :=
//!   (trail.posOf '\n').offsetBy trail.startPos
//! ```
//!
//! A token's **trailing** trivia runs from just past the token to *just before the first
//! newline* after it — `posOf` yields the substring's length when the character is absent,
//! so a run with no newline is taken whole. Everything from that newline onward, up to the
//! next token, is the next token's **leading** trivia (`updateLeadingAux`, which threads
//! the previous token's trailing stop as state).
//!
//! That is the intuitive rule made exact: a comment on the same line as a token belongs to
//! *that* token, and a comment on its own line belongs to the token *following* it. Both
//! halves matter — attaching the same-line comment forward, or the own-line comment
//! backward, is the classic bug, and neither is detectable by a round-trip test that only
//! reparses its own output.
//!
//! Upstream states the round-trip precondition too (`Lean/Syntax.lean:289`): the result
//! round-trips if all leading stops, atom contents and trailing starts are correct, and
//! every trailing stop lies between its trailing start and the next leading stop. That is
//! the tiling law, and [`Attachment::reconstruct`] enforces it rather than assuming it.
//!
//! ### A newline inside a block comment cuts the run — deliberately
//!
//! `posOf` scans bytes, so a `\n` inside a `/- … -/` block comment is a cut point like any
//! other, splitting that comment between one token's trailing and the next token's
//! leading. It looks wrong and it is faithful: the bytes stay contiguous so the file still
//! reconstructs exactly, and "improving" the heuristic here would be a divergence from the
//! pin in the one place the Mirror has to match. Bug-for-bug parity is the requirement,
//! and `a_newline_inside_a_block_comment_cuts_the_run_as_upstream_does` pins it.
//!
//! ## Missing tokens contribute no bytes
//!
//! A `missing` node records that something was expected and absent. The bytes do not
//! contain it — by definition — so it must occupy **zero** width in the tiling while still
//! being present in the sequence. Getting that wrong fails in one of two ways, and both are
//! silent: give it a span and the reconstruction inserts text the user never wrote; drop it
//! from the sequence and the error becomes invisible to everything downstream. [`Attached`]
//! keeps it as a positioned marker with no extent, and the tiling walks past it.

use crate::source::{BytePos, ByteSpan, SourceInfo, SourceText};

/// One entry of an attached token sequence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Attached {
    /// A token read from the source, with its trivia resolved.
    Token(SourceInfo),
    /// Something the parser expected and did not find, recorded at the offset where it was
    /// expected. Contributes no bytes.
    Missing { at: BytePos },
}

impl Attached {
    /// The bytes this entry contributes to a reconstruction — `None` for a missing token,
    /// which contributes none.
    pub fn contributed_span(self) -> Option<ByteSpan> {
        match self {
            Attached::Token(info) => info.full_span(),
            Attached::Missing { .. } => None,
        }
    }

    pub const fn is_missing(self) -> bool {
        matches!(self, Attached::Missing { .. })
    }
}

/// Why attachment refused a token sequence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AttachError {
    /// Token extents must be ascending and non-overlapping.
    NotAscending {
        index: usize,
        previous_end: BytePos,
        start: BytePos,
    },
    /// A token extent runs past the end of the text, or backwards.
    OutOfRange { index: usize, extent: ByteSpan },
    /// A token boundary falls inside a multi-byte scalar.
    NotOnCharBoundary { index: usize, at: BytePos },
    /// A missing-token marker sits outside the gap where the absent token would have gone.
    ///
    /// Its own check because it is the well-formedness question a byte walk cannot ask: a
    /// marker recording an absence somewhere other than between its neighbours describes a
    /// tree that disagrees with itself about where the parser was.
    MissingOutsideGap {
        index: usize,
        at: BytePos,
        gap: ByteSpan,
    },
}

/// A token's own extent, before trivia is attached — what a lexer produces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokenExtent {
    /// `pos..end_pos` of a real token.
    Present(ByteSpan),
    /// A token the parser expected at this offset and did not find.
    Missing(BytePos),
}

/// A fully attached sequence: every byte of the text belongs to exactly one entry, or to
/// the file's epilogue.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Attachment {
    entries: Vec<Attached>,
    /// Trivia after the last token's trailing stop.
    ///
    /// This slot exists because the rule leaves a genuine remainder: the last token's
    /// trailing stops at its first following newline, and whatever comes after that has no
    /// *next* token to become the leading trivia of. Upstream's parser consumes it without
    /// the tree attributing it, which is fine for a command-at-a-time parse and not fine
    /// for a whole-file tree that claims to reconstruct the file. Naming it is the honest
    /// alternative to silently dropping it — a file that is nothing but a comment is
    /// entirely epilogue.
    epilogue: ByteSpan,
}

impl Attachment {
    pub fn entries(&self) -> &[Attached] {
        &self.entries
    }

    pub fn epilogue(&self) -> ByteSpan {
        self.epilogue
    }

    /// Reconstruct the text this attachment covers, byte for byte.
    ///
    /// Walks the entries in order and requires each contributed span to abut the running
    /// cursor exactly, then requires the epilogue to close the file — the tiling law from
    /// slice 1, extended with the epilogue and with missing tokens contributing nothing. A
    /// gap or an overlap is a failure here rather than a length mismatch discovered later.
    pub fn reconstruct(&self, text: &SourceText) -> Option<Vec<u8>> {
        let mut out = Vec::with_capacity(text.len_bytes());
        let mut cursor = BytePos(0);
        for entry in &self.entries {
            let Some(span) = entry.contributed_span() else {
                // A missing token contributes nothing, so it constrains the byte walk in no
                // way at all. It deliberately does NOT have to sit at the cursor: the cursor
                // has been advanced by the previous token's trailing trivia, whereas a
                // marker records where a *token* was expected. Requiring them to coincide
                // conflates trivia ownership with token position — my first attempt did
                // exactly that and the missing-token test caught it. Where the marker may
                // legally sit is a well-formedness question, checked in `attach`.
                continue;
            };
            if span.start() != cursor {
                return None;
            }
            out.extend_from_slice(text.span_str(span)?.as_bytes());
            cursor = span.end();
        }
        if self.epilogue.start() != cursor {
            return None;
        }
        out.extend_from_slice(text.span_str(self.epilogue)?.as_bytes());
        if self.epilogue.end().0 != text.len_bytes() {
            return None;
        }
        Some(out)
    }
}

/// Attach trivia to a token sequence using the pin's rule.
///
/// `extents` are the tokens' own spans, ascending and non-overlapping, as a lexer emits
/// them. Everything between and around them is trivia, and every byte of it is assigned.
pub fn attach(text: &SourceText, extents: &[TokenExtent]) -> Result<Attachment, AttachError> {
    let bytes = text.as_bytes();

    // Validate first, so a later stage never has to wonder.
    let mut previous_end = BytePos(0);
    for (index, extent) in extents.iter().enumerate() {
        let span = match extent {
            TokenExtent::Present(span) => *span,
            TokenExtent::Missing(at) => ByteSpan::empty_at(*at),
        };
        if span.end().0 > text.len_bytes() {
            return Err(AttachError::OutOfRange {
                index,
                extent: span,
            });
        }
        for edge in [span.start(), span.end()] {
            if !text.as_str().is_char_boundary(edge.0) {
                return Err(AttachError::NotOnCharBoundary { index, at: edge });
            }
        }
        if span.start().0 < previous_end.0 {
            return Err(AttachError::NotAscending {
                index,
                previous_end,
                start: span.start(),
            });
        }
        if let TokenExtent::Missing(at) = extent {
            // The absent token belongs between the previous token's end and the next
            // token's start. Both ends inclusive: an absence at either boundary is
            // meaningful, and an empty gap still admits exactly one position.
            let next_start = extents[index + 1..]
                .iter()
                .find_map(|later| match later {
                    TokenExtent::Present(span) => Some(span.start()),
                    TokenExtent::Missing(_) => None,
                })
                .unwrap_or(BytePos(text.len_bytes()));
            let gap = ByteSpan::new(previous_end, next_start.max(previous_end))
                .expect("max keeps it forward");
            if at.0 < gap.start().0 || at.0 > gap.end().0 {
                return Err(AttachError::MissingOutsideGap {
                    index,
                    at: *at,
                    gap,
                });
            }
        }
        previous_end = span.end();
    }

    // `chooseNiceTrailStop`: the first newline at or after `from`, bounded by `limit`.
    // Returns `limit` when there is none, which is `posOf` yielding the run's length.
    let nice_trail_stop = |from: usize, limit: usize| -> usize {
        bytes[from..limit]
            .iter()
            .position(|byte| *byte == b'\n')
            .map_or(limit, |offset| from + offset)
    };

    let mut entries = Vec::with_capacity(extents.len());
    // The leading trivia of the next token starts where the previous token's trailing
    // stopped — upstream threads exactly this as state.
    let mut leading_start = 0usize;

    for (index, extent) in extents.iter().enumerate() {
        let span = match extent {
            TokenExtent::Present(span) => *span,
            TokenExtent::Missing(at) => {
                // A missing token takes no bytes and does not move the trivia cursor, so
                // the trivia around it belongs to the real tokens on either side. It is
                // recorded where the parser expected it.
                entries.push(Attached::Missing { at: *at });
                let _ = index;
                continue;
            }
        };
        // Trailing runs to the first newline after the token, bounded by the next token's
        // start (or end of text). Bounding matters: without it a token with no newline
        // before the next token would swallow the next token's leading trivia.
        let next_start = extents[index + 1..]
            .iter()
            .find_map(|later| match later {
                TokenExtent::Present(span) => Some(span.start().0),
                TokenExtent::Missing(_) => None,
            })
            .unwrap_or(text.len_bytes());
        let trail_stop = nice_trail_stop(span.end().0, next_start);

        entries.push(Attached::Token(SourceInfo::Original {
            leading: ByteSpan::new(BytePos(leading_start), span.start())
                .expect("validated ascending"),
            pos: span.start(),
            trailing: ByteSpan::new(span.end(), BytePos(trail_stop)).expect("trail_stop >= end"),
            end_pos: span.end(),
        }));
        leading_start = trail_stop;
    }

    Ok(Attachment {
        entries,
        epilogue: ByteSpan::new(BytePos(leading_start), BytePos(text.len_bytes()))
            .expect("leading_start <= len"),
    })
}

/// Which entries of an attachment an edit can possibly have changed.
///
/// The precision claim behind incremental reparse, at the layer that decides it. An
/// incremental reparser is only correct if it re-derives *everything* an edit touched, and
/// only useful if that set is small; this is the bound, and it is provable from the
/// attachment rule rather than estimated.
///
/// **The rule's own shape gives the bound.** Reading [`attach`], an entry's trivia depends
/// on exactly three things: its own extent, the start of the next present extent, and the
/// previous entry's trailing stop. Nothing else. So a byte change inside token *i*'s trivia
/// run can move `i`'s trailing stop, which moves `i + 1`'s leading start — and there the
/// cascade **stops**, because `i + 1`'s own trailing stop is computed from its own run,
/// which the edit did not touch.
///
/// So the bound is: the entries the edit overlaps, **plus at most one**. Never a suffix of
/// the file, and never proportional to what follows the edit — which is the whole claim. A
/// one-line edit in a large file damages one or two entries regardless of the file's size.
/// (An earlier draft of this doc claimed a flat maximum of two entries; that is only true
/// of an edit confined to a single trivia run, and the differential caught the overreach on
/// a ten-byte edit spanning three tokens.)
///
/// That is the difference between "precise" and "conservative": a reparser that
/// invalidated everything after an edit would also be sound, and would recompute the file
/// on every keystroke, which is the cost the whole substrate exists to avoid.
///
/// Returned as an inclusive index range, empty when no entry can have changed (an edit
/// falling entirely inside the epilogue). Callers must treat this as **at least** the
/// damaged set: `damaged_entries_never_under_reports` asserts containment of the entries
/// that actually differ, which is the direction that matters — missing damage leaves a
/// stale tree, while over-reporting only costs work.
pub fn damaged_entries(attachment: &Attachment, edited: ByteSpan) -> std::ops::Range<usize> {
    let mut first = None;
    let mut last = 0usize;
    for (index, entry) in attachment.entries.iter().enumerate() {
        let Some(span) = entry.contributed_span() else {
            continue;
        };
        // An entry is touched if the edit overlaps its full extent, treating an empty edit
        // (a pure insertion) at a boundary as touching the entry it lands inside or abuts.
        let overlaps = edited.start().0 <= span.end().0 && edited.end().0 >= span.start().0;
        if overlaps {
            if first.is_none() {
                first = Some(index);
            }
            last = index;
        }
    }
    match first {
        // The successor's leading start moves with its predecessor's trailing stop, so it
        // joins the damaged set even when the edit never reached its bytes.
        Some(start) => start..(last + 2).min(attachment.entries.len()),
        None => 0..0,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source::BOM;

    fn text_of(raw: &[u8]) -> SourceText {
        SourceText::from_utf8(raw).expect("valid UTF-8")
    }

    fn present(start: usize, end: usize) -> TokenExtent {
        TokenExtent::Present(ByteSpan::new(BytePos(start), BytePos(end)).expect("forward"))
    }

    /// Find every occurrence of a token literal, as a lexer would.
    fn extents_of(text: &str, tokens: &[&str]) -> Vec<TokenExtent> {
        let mut found = Vec::new();
        let mut at = 0usize;
        for token in tokens {
            let offset = text[at..].find(token).expect("token present") + at;
            found.push(present(offset, offset + token.len()));
            at = offset + token.len();
        }
        found
    }

    /// The awkward corpus, byte-exact in every case. These are the inputs that catch
    /// attachment bugs; a corpus of well-formed single-line files catches none of them.
    #[test]
    fn every_awkward_input_reconstructs_byte_for_byte() {
        let cases: Vec<(Vec<u8>, Vec<&str>)> = vec![
            // A comment between every pair of tokens.
            (
                b"a -- one\nb /- two -/ c -- three\nd".to_vec(),
                vec!["a", "b", "c", "d"],
            ),
            // A file that STARTS with a comment: all of it is the first token's leading.
            (b"-- header\ndef".to_vec(), vec!["def"]),
            // A file that is ONLY trivia: everything is epilogue, no tokens at all.
            (b"-- just a comment\n\n/- and a block -/\n".to_vec(), vec![]),
            // Mixed CRLF and LF in one file, with a BOM.
            ([BOM, b"a -- x\r\nb\nc\r\n"].concat(), vec!["a", "b", "c"]),
            // A final line with no terminator.
            (
                b"a\nb -- trailing comment, no newline".to_vec(),
                vec!["a", "b"],
            ),
            // No trivia at all, tokens abutting.
            (b"ab".to_vec(), vec!["a", "b"]),
            // Trivia only between, none at the edges.
            (b"a b".to_vec(), vec!["a", "b"]),
            // Empty file.
            (b"".to_vec(), vec![]),
            // A lone CR as trivia, which survives normalization and is bytes like any other
            // to this layer.
            (b"a\rb".to_vec(), vec!["a", "b"]),
        ];

        for (raw, tokens) in cases {
            let text = text_of(&raw);
            let extents = extents_of(text.as_str(), &tokens);
            let attachment = attach(&text, &extents).expect("valid extents");
            assert_eq!(
                attachment.reconstruct(&text).as_deref(),
                Some(raw.as_slice()),
                "reconstruction lost bytes for {raw:?}"
            );
            // Every byte belongs to exactly one entry or the epilogue — asserted by summing
            // widths, which catches a double-attribution that abutment alone would not.
            let attributed: usize = attachment
                .entries()
                .iter()
                .filter_map(|entry| entry.contributed_span())
                .map(ByteSpan::len_bytes)
                .sum::<usize>()
                + attachment.epilogue().len_bytes();
            assert_eq!(
                attributed,
                raw.len(),
                "attributed widths must sum to the file exactly for {raw:?}"
            );
        }
    }

    /// **The classic bug, in both directions.** A same-line comment belongs to the token
    /// before it; an own-line comment belongs to the token after it. Getting either
    /// backwards still round-trips, so only asserting the split itself catches it.
    #[test]
    fn a_same_line_comment_attaches_back_and_an_own_line_comment_attaches_forward() {
        //            0         1         2
        //            0123456789012345678901234
        let raw = b"a -- same line\n-- own line\nb";
        let text = text_of(raw);
        let extents = extents_of(text.as_str(), &["a", "b"]);
        let attachment = attach(&text, &extents).expect("valid");

        let Attached::Token(SourceInfo::Original {
            trailing: a_trail, ..
        }) = attachment.entries()[0]
        else {
            panic!("expected an original token");
        };
        let Attached::Token(SourceInfo::Original {
            leading: b_lead, ..
        }) = attachment.entries()[1]
        else {
            panic!("expected an original token");
        };

        // 'a' keeps the comment on its own line, stopping BEFORE the newline.
        assert_eq!(
            text.span_str(a_trail),
            Some(" -- same line"),
            "the same-line comment must be trailing trivia of the token before it"
        );
        assert_eq!(
            text.as_bytes()[a_trail.end().0],
            b'\n',
            "the cut is at the newline"
        );

        // 'b' takes the newline and the whole own-line comment as leading trivia.
        assert_eq!(
            text.span_str(b_lead),
            Some("\n-- own line\n"),
            "the own-line comment must be leading trivia of the token after it"
        );

        // And the two abut exactly, so no byte is claimed twice or dropped.
        assert_eq!(a_trail.end(), b_lead.start());
        assert_eq!(attachment.reconstruct(&text).as_deref(), Some(&raw[..]));
    }

    /// Faithful, not "nice": `posOf` scans bytes, so a newline inside a block comment is a
    /// cut point like any other and the comment is split across two tokens' trivia. The
    /// bytes stay contiguous so the file still reconstructs, and improving the heuristic
    /// here would diverge from the pin at the point the Mirror has to match.
    #[test]
    fn a_newline_inside_a_block_comment_cuts_the_run_as_upstream_does() {
        let raw = b"a /- spans\n a line -/ b";
        let text = text_of(raw);
        let extents = extents_of(text.as_str(), &["a", "b"]);
        let attachment = attach(&text, &extents).expect("valid");

        let Attached::Token(SourceInfo::Original {
            trailing: a_trail, ..
        }) = attachment.entries()[0]
        else {
            panic!("original");
        };
        // The cut lands inside the block comment, before its closing delimiter.
        assert_eq!(text.span_str(a_trail), Some(" /- spans"));
        let Attached::Token(SourceInfo::Original {
            leading: b_lead, ..
        }) = attachment.entries()[1]
        else {
            panic!("original");
        };
        assert_eq!(text.span_str(b_lead), Some("\n a line -/ "));
        // Still byte-exact, which is why the split is acceptable rather than merely odd.
        assert_eq!(attachment.reconstruct(&text).as_deref(), Some(&raw[..]));
    }

    /// A missing token records an absence and contributes no bytes — both halves, because
    /// each failure mode is silent on its own.
    #[test]
    fn a_missing_token_is_recorded_and_inserts_nothing() {
        let raw = b"a  b";
        let text = text_of(raw);
        // The parser expected something at offset 2 and did not find it.
        let extents = vec![
            present(0, 1),
            TokenExtent::Missing(BytePos(2)),
            present(3, 4),
        ];
        let attachment = attach(&text, &extents).expect("valid");

        // PRESENT IN THE TREE: the error is not invisible.
        assert_eq!(attachment.entries().len(), 3);
        assert!(attachment.entries()[1].is_missing());
        assert_eq!(
            attachment.entries()[1],
            Attached::Missing { at: BytePos(2) },
            "the absence is recorded where it was expected"
        );

        // CONTRIBUTES NOTHING: the reconstruction does not invent a token.
        assert_eq!(attachment.entries()[1].contributed_span(), None);
        assert_eq!(attachment.reconstruct(&text).as_deref(), Some(&raw[..]));

        // And the trivia around it still belongs to the real tokens, so a missing token
        // does not create an unowned byte.
        let attributed: usize = attachment
            .entries()
            .iter()
            .filter_map(|entry| entry.contributed_span())
            .map(ByteSpan::len_bytes)
            .sum::<usize>()
            + attachment.epilogue().len_bytes();
        assert_eq!(attributed, raw.len());

        // A tree that is nothing but a missing token still reconstructs the file: the
        // whole thing is epilogue, and the marker adds no bytes.
        let only_missing = attach(&text, &[TokenExtent::Missing(BytePos(0))]).expect("valid");
        assert_eq!(only_missing.reconstruct(&text).as_deref(), Some(&raw[..]));
        assert_eq!(only_missing.epilogue().len_bytes(), raw.len());

        // A marker OUTSIDE the gap between its neighbours is refused at attach time — the
        // well-formedness check a byte walk cannot perform, since a zero-width entry
        // constrains no byte.
        assert!(matches!(
            attach(
                &text,
                &[
                    present(0, 1),
                    TokenExtent::Missing(BytePos(4)),
                    present(3, 4)
                ]
            ),
            Err(AttachError::MissingOutsideGap { index: 1, .. })
        ));
    }

    /// **The differential for the damage bound**, in the shape the rope and the line index
    /// used: predict, then recompute fully, then require the prediction to contain the
    /// truth. Same harness discipline rather than a third invention.
    ///
    /// The asserted direction is containment, not equality, because the two failures are
    /// not symmetric: under-reporting leaves a stale entry in an incremental tree and is a
    /// correctness bug, while over-reporting only wastes work. So the test demands
    /// soundness and separately demands the bound be non-trivial — a prediction of "every
    /// entry" would satisfy containment and be worthless, which is exactly the vacuous pass
    /// a containment-only test invites.
    #[test]
    fn damaged_entries_never_under_reports_and_stays_tight() {
        // Several tokens with varied trivia: same-line comments, own-line comments, blank
        // lines, and a CRLF, so the trailing stops land in different places.
        let raw = b"a -- one
b
-- own
c /- blk -/ d
e";
        let text = text_of(raw);
        let tokens = ["a", "b", "c", "d", "e"];
        let extents = extents_of(text.as_str(), &tokens);
        let before = attach(&text, &extents).expect("valid");
        assert_eq!(before.entries().len(), 5);

        let mut ever_tight = false;
        for lo in 0..text.len_bytes() {
            for hi in lo..=text.len_bytes() {
                if !text.as_str().is_char_boundary(lo) || !text.as_str().is_char_boundary(hi) {
                    continue;
                }
                let edited = ByteSpan::new(BytePos(lo), BytePos(hi)).expect("forward");

                // Replace the span with the SAME number of bytes, so token extents do not
                // move and the only thing that can change is trivia attachment. That
                // isolates the property under test from the lexer's own damage, which is a
                // different question owned by a different bead.
                let mut bytes = raw.to_vec();
                for byte in &mut bytes[lo..hi] {
                    // Turn the region into newlines, the one byte the rule keys on, which
                    // is the change most likely to move a trailing stop.
                    *byte = b'\n';
                }
                let Ok(edited_text) = SourceText::from_utf8(&bytes) else {
                    continue;
                };
                let after = attach(&edited_text, &extents).expect("extents unchanged");

                // The truth: which entries actually differ.
                let actual: Vec<usize> = (0..before.entries().len())
                    .filter(|index| before.entries()[*index] != after.entries()[*index])
                    .collect();
                let predicted = damaged_entries(&before, edited);

                for index in &actual {
                    assert!(
                        predicted.contains(index),
                        "edit {lo}..{hi}: entry {index} changed but was not predicted \
                         (predicted {predicted:?}, actual {actual:?})"
                    );
                }
                // Non-trivial: the bound must not be "everything" for a small edit.
                if predicted.len() < before.entries().len() {
                    ever_tight = true;
                }
                // THE THEOREM, asserted rather than a fixed constant: the cascade adds
                // at most ONE entry beyond those the edit overlaps. A flat bound would be
                // wrong for a wide edit and would have hidden the real statement.
                let overlapped = before
                    .entries()
                    .iter()
                    .filter(|entry| {
                        entry.contributed_span().is_some_and(|span| {
                            edited.start().0 <= span.end().0 && edited.end().0 >= span.start().0
                        })
                    })
                    .count();
                assert!(
                    predicted.len() <= overlapped + 1,
                    "edit {lo}..{hi}: the bound must exceed the overlapped entries by at \
                     most one (overlapped {overlapped}, predicted {predicted:?})"
                );
            }
        }
        assert!(
            ever_tight,
            "the bound was never narrower than the whole file, so containment passed \
             vacuously"
        );
    }

    /// The cascade stops at the successor — the claim that makes the bound two entries
    /// rather than a suffix. Stated as its own case because it is the part a reader will
    /// doubt.
    #[test]
    fn moving_a_trailing_stop_changes_only_that_entry_and_its_successor() {
        //           0123456789
        let raw = b"a b
c
d";
        let text = text_of(raw);
        let extents = extents_of(text.as_str(), &["a", "b", "c", "d"]);
        let before = attach(&text, &extents).expect("valid");

        // Turn the space after 'a' into a newline: 'a' loses its trailing, 'b' gains a
        // leading newline. Nothing later can move, because 'b', 'c' and 'd' compute their
        // trailing stops from their own runs.
        let edited_bytes = b"a
b
c
d";
        let edited_text = text_of(edited_bytes);
        let after = attach(&edited_text, &extents).expect("valid");

        let differing: Vec<usize> = (0..before.entries().len())
            .filter(|index| before.entries()[*index] != after.entries()[*index])
            .collect();
        assert_eq!(
            differing,
            vec![0, 1],
            "only the entry whose trailing moved and its successor may change"
        );
        // And the prediction covers exactly that, without reaching further.
        let predicted = damaged_entries(&before, ByteSpan::new(BytePos(1), BytePos(2)).unwrap());
        for index in &differing {
            assert!(predicted.contains(index));
        }
        assert!(
            !predicted.contains(&3),
            "the bound must not extend to the end of the file"
        );
        // Both texts still reconstruct exactly, so the edit did not break the tiling.
        assert_eq!(before.reconstruct(&text).as_deref(), Some(&raw[..]));
        assert_eq!(
            after.reconstruct(&edited_text).as_deref(),
            Some(&edited_bytes[..])
        );
    }

    /// An edit entirely inside the epilogue damages no entry — the empty-range case, which
    /// a bound that always returned something non-empty would get wrong.
    #[test]
    fn an_edit_in_the_epilogue_damages_no_entry() {
        let raw = b"a
-- trailing only
";
        let text = text_of(raw);
        let extents = extents_of(text.as_str(), &["a"]);
        let attachment = attach(&text, &extents).expect("valid");
        assert!(
            attachment.epilogue().len_bytes() > 0,
            "the fixture needs a non-empty epilogue"
        );
        let in_epilogue = ByteSpan::new(
            BytePos(attachment.epilogue().start().0 + 1),
            BytePos(attachment.epilogue().end().0),
        )
        .expect("forward");
        assert_eq!(damaged_entries(&attachment, in_epilogue), 0..0);
    }

    #[test]
    fn a_reconstruction_with_a_gap_or_an_overlap_is_refused() {
        let text = text_of(b"abcdef");
        let good = attach(&text, &extents_of("abcdef", &["ab", "cd"])).expect("valid");
        assert!(good.reconstruct(&text).is_some());

        // Hand-build a broken attachment: the second token's leading starts late, leaving
        // byte 2 unowned. reconstruct must refuse rather than produce short output.
        let gapped = Attachment {
            entries: vec![
                Attached::Token(SourceInfo::Original {
                    leading: ByteSpan::empty_at(BytePos(0)),
                    pos: BytePos(0),
                    trailing: ByteSpan::empty_at(BytePos(2)),
                    end_pos: BytePos(2),
                }),
                Attached::Token(SourceInfo::Original {
                    leading: ByteSpan::empty_at(BytePos(3)),
                    pos: BytePos(3),
                    trailing: ByteSpan::empty_at(BytePos(6)),
                    end_pos: BytePos(6),
                }),
            ],
            epilogue: ByteSpan::empty_at(BytePos(6)),
        };
        assert_eq!(gapped.reconstruct(&text), None, "a gap must be refused");

        // An epilogue that does not close the file is refused too.
        let short = Attachment {
            entries: vec![Attached::Token(SourceInfo::Original {
                leading: ByteSpan::empty_at(BytePos(0)),
                pos: BytePos(0),
                trailing: ByteSpan::empty_at(BytePos(3)),
                end_pos: BytePos(3),
            })],
            epilogue: ByteSpan::empty_at(BytePos(3)),
        };
        assert_eq!(
            short.reconstruct(&text),
            None,
            "an unclosed file must be refused"
        );

        // A missing marker does NOT constrain the byte walk — it contributes nothing, so a
        // tiling that is otherwise complete reconstructs regardless of where the marker
        // sits. Its placement is checked by `attach`, not here, and asserting otherwise was
        // my own conflation of the two concerns.
        let with_marker = Attachment {
            entries: vec![Attached::Missing { at: BytePos(4) }],
            epilogue: ByteSpan::new(BytePos(0), BytePos(6)).expect("forward"),
        };
        assert_eq!(
            with_marker.reconstruct(&text).as_deref(),
            Some(&b"abcdef"[..])
        );
    }

    #[test]
    fn invalid_extents_are_refused_with_the_offending_index() {
        let text = text_of("aπb".as_bytes());
        // Descending. Boundary-valid extents on purpose, so this exercises the ascending
        // check rather than tripping the char-boundary check first.
        assert_eq!(
            attach(&text, &[present(3, 4), present(0, 1)]),
            Err(AttachError::NotAscending {
                index: 1,
                previous_end: BytePos(4),
                start: BytePos(0)
            })
        );
        // Overlapping counts as not ascending.
        assert!(matches!(
            attach(&text, &[present(0, 3), present(1, 4)]),
            Err(AttachError::NotAscending { index: 1, .. })
        ));
        // Past the end.
        assert!(matches!(
            attach(&text, &[present(0, 99)]),
            Err(AttachError::OutOfRange { index: 0, .. })
        ));
        // Mid-scalar: 'π' is bytes 1..3.
        assert_eq!(
            attach(&text, &[present(0, 2)]),
            Err(AttachError::NotOnCharBoundary {
                index: 0,
                at: BytePos(2)
            })
        );
        // The valid tokenization still works, so none of the above is a blanket refusal.
        assert!(attach(&text, &[present(0, 1), present(1, 4)]).is_ok());
    }
}
