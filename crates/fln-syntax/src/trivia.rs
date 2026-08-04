//! Trivia lexing — whitespace and comments (plan §9; bead franken_lean-81oq).
//!
//! Everything here is read off `Lean/Parser/Basic.lean` at the pin. The rules are small
//! and three of them are counter-intuitive enough that an implementation written from
//! memory gets them wrong *and still passes a byte-identity test*, which is why each is
//! cited and separately asserted.
//!
//! ## This runs on the normalized view
//!
//! The Reference parses a `crlfToLf`-normalized text, so the lexer consumes
//! [`SourceView::normalized`](crate::view::SourceView::normalized) and every position it
//! emits is a **view** position. Lossless means recoverable *through* that map, not
//! byte-equal to the raw file; carrying a view offset into a diagnostic without
//! `to_original` is the bug that shifts every span by one per CRLF.
//!
//! ## The rules, and why each is stated rather than assumed
//!
//! * **A tab is an error**, not whitespace: *"tabs are not allowed; please configure your
//!   editor to expand them"* (`Basic.lean:568`). Checked before the generic
//!   `isWhitespace` test, so it is refused rather than skipped.
//! * **An isolated carriage return is an error**: *"isolated carriage returns are not
//!   allowed"* (`Basic.lean:570`). After normalization a `\r` genuinely is isolated,
//!   which is what makes that rule affordable upstream.
//! * **`/--` and `/-!` are NOT trivia.** They are doc comments, and the whitespace parser
//!   stops at them: *"`/--` and `/-!` doc comment are actual tokens"* (`Basic.lean:583`).
//!   Only `/-` followed by something else opens a block comment. Treating a docstring as
//!   whitespace would swallow every docstring in the corpus — and the bytes stay
//!   contiguous, so a round-trip test would not notice.
//! * **Block comments nest** (`finishCommentBlock`, `Basic.lean:537`): `/-` increments the
//!   depth, `-/` decrements, and only depth 1 terminates. `/- a /- b -/ c -/` is one
//!   comment; scanning for the first `-/` ends it early and leaves ` c -/` looking like
//!   code.
//! * **An unterminated block comment is an error**, not a comment running to end of file.
//!   Every `atEnd` branch in `finishCommentBlock` calls `eoi`, which raises *"unterminated
//!   comment"*. Consuming to EOF would let one stray `/-` swallow an entire file while
//!   still reconstructing byte-exactly.
//! * **A line comment stops before its newline** (`takeUntilFn (· = '\n')`,
//!   `Basic.lean:576`). The newline is left to the whitespace scan, and that matters
//!   downstream: `chooseNiceTrailStop` cuts trailing trivia *at* the first newline, which
//!   is precisely what makes an own-line comment attach forward.

use crate::source::{BytePos, SourceText};

/// Why trivia lexing refused the input.
///
/// All three are *parse errors about the file*, not internal faults: the input is not
/// well-formed Lean, and saying so is a verdict. Each carries the offset so a diagnostic
/// can point at the byte — a view offset, to be mapped back before display.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TriviaError {
    /// `Basic.lean:568`. Upstream's message: "tabs are not allowed; please configure your
    /// editor to expand them".
    Tab { at: BytePos },
    /// `Basic.lean:570`. Upstream's message: "isolated carriage returns are not allowed".
    IsolatedCarriageReturn { at: BytePos },
    /// `finishCommentBlock`'s `eoi`. Upstream's message: "unterminated comment". `at` is
    /// where the outermost `/-` opened, which is the useful place to point.
    UnterminatedComment { opened_at: BytePos },
}

impl TriviaError {
    /// The upstream diagnostic text, so ours cannot drift from the pin's wording.
    pub const fn message(self) -> &'static str {
        match self {
            TriviaError::Tab { .. } => {
                "tabs are not allowed; please configure your editor to expand them"
            }
            TriviaError::IsolatedCarriageReturn { .. } => {
                "isolated carriage returns are not allowed"
            }
            TriviaError::UnterminatedComment { .. } => "unterminated comment",
        }
    }

    /// The same refusal with its offset moved by `delta` bytes.
    ///
    /// An exhaustive match, deliberately: a variant added later fails to compile here rather
    /// than silently keeping an offset that points into the text the user had before an edit.
    pub fn shifted(self, delta: isize) -> TriviaError {
        let moved = |at: BytePos| BytePos((at.0 as isize + delta).max(0) as usize);
        match self {
            TriviaError::Tab { at } => TriviaError::Tab { at: moved(at) },
            TriviaError::IsolatedCarriageReturn { at } => {
                TriviaError::IsolatedCarriageReturn { at: moved(at) }
            }
            TriviaError::UnterminatedComment { opened_at } => TriviaError::UnterminatedComment {
                opened_at: moved(opened_at),
            },
        }
    }

    pub const fn at(self) -> BytePos {
        match self {
            TriviaError::Tab { at } | TriviaError::IsolatedCarriageReturn { at } => at,
            TriviaError::UnterminatedComment { opened_at } => opened_at,
        }
    }
}

/// Consume trivia starting at `from`, returning the offset just past it.
///
/// Mirrors upstream's `whitespace`: it runs to the first byte that is neither whitespace
/// nor a comment, and **stops at a doc comment**, which is a token rather than trivia.
pub fn scan_trivia(text: &SourceText, from: BytePos) -> Result<BytePos, TriviaError> {
    let bytes = text.as_bytes();
    let mut at = from.0;
    loop {
        let Some(byte) = bytes.get(at).copied() else {
            return Ok(BytePos(at));
        };
        match byte {
            // Checked before the generic whitespace test, exactly as the pin orders them.
            b'\t' => return Err(TriviaError::Tab { at: BytePos(at) }),
            b'\r' => {
                return Err(TriviaError::IsolatedCarriageReturn { at: BytePos(at) });
            }
            b' ' | b'\n' | 0x0B | 0x0C => at += 1,
            b'-' if bytes.get(at + 1) == Some(&b'-') => {
                // A line comment runs to, but does not consume, the newline.
                at += 2;
                while let Some(byte) = bytes.get(at) {
                    if *byte == b'\n' {
                        break;
                    }
                    at += 1;
                }
            }
            b'/' if bytes.get(at + 1) == Some(&b'-') => {
                // Doc comments are tokens, not trivia: the scan stops here.
                if matches!(bytes.get(at + 2), Some(b'-') | Some(b'!')) {
                    return Ok(BytePos(at));
                }
                at = scan_block_comment(bytes, at)?;
            }
            _ => return Ok(BytePos(at)),
        }
    }
}

/// Consume a nesting block comment opened at `opened_at`, returning the offset past its
/// closing delimiter.
fn scan_block_comment(bytes: &[u8], opened_at: usize) -> Result<usize, TriviaError> {
    let mut at = opened_at + 2;
    let mut depth = 1usize;
    while depth > 0 {
        match (bytes.get(at), bytes.get(at + 1)) {
            (Some(b'-'), Some(b'/')) => {
                depth -= 1;
                at += 2;
            }
            (Some(b'/'), Some(b'-')) => {
                depth += 1;
                at += 2;
            }
            (Some(_), _) => at += 1,
            // Running out of input is upstream's `eoi`, an error rather than a comment
            // that happens to end at the file's end.
            (None, _) => {
                return Err(TriviaError::UnterminatedComment {
                    opened_at: BytePos(opened_at),
                });
            }
        }
    }
    Ok(at)
}

/// Whether a doc comment opens at `at` — `/--` or `/-!`, which are tokens.
pub fn opens_doc_comment(text: &SourceText, at: BytePos) -> bool {
    let bytes = text.as_bytes();
    bytes.get(at.0) == Some(&b'/')
        && bytes.get(at.0 + 1) == Some(&b'-')
        && matches!(bytes.get(at.0 + 2), Some(b'-') | Some(b'!'))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text_of(raw: &str) -> SourceText {
        SourceText::from_utf8(raw.as_bytes()).expect("valid UTF-8")
    }

    fn scan(raw: &str) -> Result<usize, TriviaError> {
        scan_trivia(&text_of(raw), BytePos(0)).map(|at| at.0)
    }

    #[test]
    fn whitespace_and_line_comments_stop_where_the_pin_stops() {
        assert_eq!(scan("   x"), Ok(3));
        assert_eq!(scan(""), Ok(0));
        assert_eq!(scan("x"), Ok(0), "no trivia at all");
        assert_eq!(scan("\n\n x"), Ok(3));

        // A line comment runs to but NOT through its newline: the scan then consumes the
        // newline as whitespace, so the end offset is past it — but the comment itself
        // stopped first, which is what lets chooseNiceTrailStop cut there.
        assert_eq!(scan("-- c\nx"), Ok(5));
        assert_eq!(scan("-- c"), Ok(4), "a line comment may end at EOF");
        // A single '-' is not a comment and not trivia.
        assert_eq!(scan("- x"), Ok(0));
    }

    /// Nesting, from `finishCommentBlock`. A scan for the first `-/` would stop early and
    /// leave the rest looking like code.
    #[test]
    fn block_comments_nest() {
        assert_eq!(scan("/- a -/x"), Ok(7));
        assert_eq!(
            scan("/- a /- b -/ c -/x"),
            Ok(17),
            "the inner -/ must not close the outer comment"
        );
        assert_eq!(scan("/- /- /- -/ -/ -/x"), Ok(17), "three deep");
        // Adjacent comments are both consumed.
        assert_eq!(scan("/-a-//-b-/x"), Ok(10));
    }

    /// Unterminated is an ERROR, not a comment that runs to EOF. Consuming to EOF would
    /// let one stray `/-` swallow a file while still reconstructing byte-exactly.
    #[test]
    fn an_unterminated_block_comment_is_an_error_not_end_of_file() {
        assert_eq!(
            scan("/- never closed"),
            Err(TriviaError::UnterminatedComment {
                opened_at: BytePos(0)
            })
        );
        // Nesting that closes too few times is still unterminated.
        assert_eq!(
            scan("/- a /- b -/"),
            Err(TriviaError::UnterminatedComment {
                opened_at: BytePos(0)
            })
        );
        // A dangling `-` at the very end does not terminate anything.
        assert_eq!(
            scan("/- a -"),
            Err(TriviaError::UnterminatedComment {
                opened_at: BytePos(0)
            })
        );
        assert_eq!(
            TriviaError::UnterminatedComment {
                opened_at: BytePos(0)
            }
            .message(),
            "unterminated comment"
        );
    }

    /// **Doc comments are tokens, not trivia.** Getting this wrong swallows every
    /// docstring in the corpus, and the bytes stay contiguous so a byte-identity test
    /// would not notice — inherited finding 2, biting in a new place.
    #[test]
    fn doc_comments_stop_the_scan_because_they_are_tokens() {
        assert_eq!(scan("/-- a doc -/"), Ok(0), "/-- is a token, so no trivia");
        assert_eq!(scan("/-! a module doc -/"), Ok(0), "/-! likewise");
        // Leading whitespace is still trivia; the scan stops AT the doc comment.
        assert_eq!(scan("  /-- doc -/"), Ok(2));
        // And an ordinary block comment is trivia, so the contrast is exact.
        assert_eq!(scan("  /- plain -/"), Ok(13));

        assert!(opens_doc_comment(&text_of("/-- x"), BytePos(0)));
        assert!(opens_doc_comment(&text_of("/-! x"), BytePos(0)));
        assert!(!opens_doc_comment(&text_of("/- x"), BytePos(0)));
        assert!(!opens_doc_comment(&text_of("/x"), BytePos(0)));
    }

    /// Tabs and isolated carriage returns are refused, with the pin's own wording.
    #[test]
    fn a_tab_and_an_isolated_carriage_return_are_parse_errors() {
        assert_eq!(scan("\tx"), Err(TriviaError::Tab { at: BytePos(0) }));
        assert_eq!(scan("  \tx"), Err(TriviaError::Tab { at: BytePos(2) }));
        assert_eq!(
            scan("\rx"),
            Err(TriviaError::IsolatedCarriageReturn { at: BytePos(0) })
        );
        // After normalization there are no CRLF pairs, so any CR reaching here is isolated
        // — which is exactly the precondition that makes the pin's rule affordable.
        assert_eq!(
            scan(" \r\n"),
            Err(TriviaError::IsolatedCarriageReturn { at: BytePos(1) }),
            "a CR surviving normalization is still refused"
        );
        assert_eq!(
            TriviaError::Tab { at: BytePos(0) }.message(),
            "tabs are not allowed; please configure your editor to expand them"
        );
        assert_eq!(
            TriviaError::IsolatedCarriageReturn { at: BytePos(0) }.message(),
            "isolated carriage returns are not allowed"
        );
        // A tab INSIDE a comment is not trivia-position whitespace, so it is fine. Same
        // for a carriage return — this caught a bad fixture of mine, so it gets a case.
        assert_eq!(scan("-- has\ta tab\nx"), Ok(13));
        assert_eq!(scan("/- has\ta tab -/x"), Ok(15));
        assert_eq!(
            scan("-- has\ra CR\nx"),
            Ok(12),
            "a CR inside a comment is content"
        );
    }

    /// The lexer runs on the VIEW, so a CRLF file has no carriage returns left to refuse —
    /// the constraint the normalization boundary exists to satisfy.
    #[test]
    fn a_crlf_file_lexes_cleanly_through_the_view() {
        // The CR must be in TRIVIA position to be refused: inside a line comment it is
        // ordinary content, which is why the scan starts after the token here.
        let original = SourceText::from_utf8(b"a\r\n  x").expect("valid");
        let view = crate::view::SourceView::of(&original);
        // Raw bytes would be refused...
        assert!(matches!(
            scan_trivia(&original, BytePos(1)),
            Err(TriviaError::IsolatedCarriageReturn { at: BytePos(1) })
        ));
        // ...and the normalized view lexes cleanly, which is the whole point.
        let end = scan_trivia(view.normalized(), BytePos(1)).expect("view has no CRLF");
        assert_eq!(view.normalized().as_bytes()[end.0], b'x');
        // The position maps back to the original byte for a diagnostic.
        let in_original = view.to_original(end);
        assert_eq!(original.as_bytes()[in_original.0], b'x');
    }
}
