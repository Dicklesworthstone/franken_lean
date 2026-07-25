//! Error recovery boundaries (plan §9; bead franken_lean-81oq).
//!
//! ## The one law
//!
//! **Recovery may only change what happens to input that was already going to fail. It may
//! never make a previously-rejected file accepted.**
//!
//! That is not a quality goal, it is a soundness property of the front end. If recovery can
//! rescue a rejection, then whether a file is legal Lean depends on which recovery
//! machinery happens to be compiled in, and the acceptance surface — the thing every
//! downstream claim rests on — stops being a property of the language.
//!
//! ## Why the design is shaped the way it is
//!
//! The law is enforced **structurally**, not by discipline. [`lex_recovering`] does not
//! contain a second lexer with looser rules; it calls the *same* [`scan_trivia`] and, when
//! that refuses, records the refusal and resumes past it. So there is exactly one place
//! that decides whether input is well-formed, and recovery is a policy about what to do
//! with a refusal it cannot influence. A recovery path with its own acceptance logic is how
//! the two drift apart, and the drift is invisible until someone diffs them.
//!
//! Concretely: [`Lexed::accepted`] is `errors.is_empty()`, and every error came from the
//! shared scanner. Recovery adds entries to that list and never removes one, so
//! `accepted` can only ever move from true to false — never the other way. The differential
//! in the tests demonstrates it over a corpus; the shape above is what makes it true.
//!
//! ## Why a differential, and not examples
//!
//! A test showing "recovery produces a tree" establishes nothing about the law: it is
//! consistent with recovery accepting garbage. The property is an equality between two
//! configurations over the *same* inputs, so the test has to run both and compare. And the
//! corpus needs passing inputs as well as failing ones, because a recovery implementation
//! that rejected everything would satisfy a failing-inputs-only corpus vacuously.
//!
//! ## Why this still steps one byte between trivia runs
//!
//! [`crate::token::lex_token`] now exists, so the obvious next move is to call it here
//! instead of stepping a byte. That would be wrong, and the reason is a fact about Lean
//! rather than a gap in this crate: **Lean's lexing is parser-driven in places, so there is
//! no total "next token" function to loop.** `Lean/Parser/Term.lean:91`:
//!
//! ```text
//! def docComment := leading_parser
//!   ppDedent $ "/--" >> ppSpace >> ... commentBody ... >> ppLine
//! ```
//!
//! `/--` is an ordinary table token, but the comment *body* is consumed by `commentBody`, a
//! dedicated parser the token table knows nothing about. String interpolation is the same
//! shape. So a `while let Ok(tok) = lex_token(..)` loop would refuse the body of every doc
//! comment in the language, and wiring it in here would trade a stated limitation for a
//! wrong answer that the acceptance differential would then dutifully certify — both
//! configurations would reject the same files, and the law would pass while the tokenizer
//! was broken. A law can only protect the property it states.
//!
//! The obligation therefore moves rather than closes: whatever drives token consumption —
//! the category parser, bead `fln-ffam` — must re-run this differential over itself
//! unchanged. The law is about acceptance, so it does not weaken when the thing between
//! boundaries gets smarter; if it starts failing there, that layer has taken acceptance
//! authority it is not allowed to have.

use crate::source::{BytePos, ByteSpan, SourceText};
use crate::trivia::{TriviaError, scan_trivia};

/// One recovered-from lexical error, with the region skipped to resume.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Recovered {
    pub error: TriviaError,
    /// The bytes skipped to get past the refusal. Recorded so the region is auditable and
    /// so a reconstruction can still account for every byte — skipped input is not lost
    /// input.
    pub skipped: ByteSpan,
}

/// The result of lexing trivia across a whole text, with or without recovery.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Lexed {
    /// Offsets where trivia ended and non-trivia began — the boundaries a tokenizer needs.
    pub boundaries: Vec<BytePos>,
    /// Every refusal encountered. Empty exactly when the input is well-formed trivia-wise.
    pub errors: Vec<Recovered>,
}

impl Lexed {
    /// Whether the input was accepted.
    ///
    /// Defined as "no errors were recorded", which is the whole of the acceptance surface.
    /// Recovery only ever appends to `errors`, so this can move from true to false and
    /// never back — the law, made a property of the type rather than a rule to remember.
    pub fn accepted(&self) -> bool {
        self.errors.is_empty()
    }
}

/// Scan trivia boundaries across `text`, stopping at the first refusal.
///
/// The no-recovery configuration, and the reference the differential compares against.
pub fn lex(text: &SourceText) -> Lexed {
    let mut boundaries = Vec::new();
    let mut at = BytePos(0);
    while at.0 < text.len_bytes() {
        match scan_trivia(text, at) {
            Ok(end) => {
                boundaries.push(end);
                // Past the trivia is a non-trivia byte; step over it so the scan advances.
                // See the module docs on why this is still one byte and not a token.
                at = BytePos(next_boundary(text, end));
            }
            Err(error) => {
                return Lexed {
                    boundaries,
                    errors: vec![Recovered {
                        error,
                        skipped: ByteSpan::empty_at(error.at()),
                    }],
                };
            }
        }
    }
    Lexed {
        boundaries,
        errors: Vec::new(),
    }
}

/// Scan trivia boundaries across `text`, recovering past refusals to keep going.
///
/// Calls the same [`scan_trivia`] as [`lex`]. When it refuses, the offending byte is
/// skipped and scanning resumes — so recovery produces *more* boundaries and *more*
/// errors, and cannot produce fewer errors than [`lex`] would have found.
pub fn lex_recovering(text: &SourceText) -> Lexed {
    let mut boundaries = Vec::new();
    let mut errors = Vec::new();
    let mut at = BytePos(0);
    while at.0 < text.len_bytes() {
        match scan_trivia(text, at) {
            Ok(end) => {
                boundaries.push(end);
                at = BytePos(next_boundary(text, end));
            }
            Err(error) => {
                // Resume past the refusal. For an unterminated comment there is nothing
                // after it, so the skip runs to end of text; for a tab or a stray carriage
                // return one byte is enough.
                let resume = match error {
                    TriviaError::Tab { at } | TriviaError::IsolatedCarriageReturn { at } => {
                        at.0 + 1
                    }
                    TriviaError::UnterminatedComment { .. } => text.len_bytes(),
                };
                let resume = resume.min(text.len_bytes());
                errors.push(Recovered {
                    error,
                    skipped: span_or_empty(error.at(), BytePos(resume)),
                });
                if resume <= at.0 {
                    // Never possible with the arms above, but a recovery loop that fails to
                    // advance is an infinite loop, so the guard is structural rather than
                    // argued.
                    break;
                }
                at = BytePos(resume);
            }
        }
    }
    Lexed { boundaries, errors }
}

/// The span from `from` to `to`, or the empty span at `from` if that runs backwards.
///
/// Deliberately total. An inverted range would be a bug in the resume arithmetic above, but
/// the reaction to it must not be a panic: this code runs on malformed input by definition,
/// and a front end that aborts while describing where a comment went wrong is worse than the
/// unterminated comment. Reporting an empty skipped region loses an audit detail and
/// nothing else — the error itself, which is what decides acceptance, is unaffected.
fn span_or_empty(from: BytePos, to: BytePos) -> ByteSpan {
    ByteSpan::new(from, to).unwrap_or(ByteSpan::empty_at(from))
}

/// Step past one non-trivia byte, on a char boundary so a scalar is never split.
fn next_boundary(text: &SourceText, from: BytePos) -> usize {
    let mut at = from.0 + 1;
    while at < text.len_bytes() && !text.as_str().is_char_boundary(at) {
        at += 1;
    }
    at.min(text.len_bytes()).max(from.0 + 1)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text_of(raw: &str) -> SourceText {
        SourceText::from_utf8(raw.as_bytes()).expect("valid UTF-8")
    }

    /// Inputs that are well-formed trivia-wise, and inputs that are not, for structurally
    /// different reasons. Both halves are required: a corpus of only-failing inputs is
    /// satisfied vacuously by an implementation that rejects everything.
    fn corpus() -> Vec<(&'static str, &'static str)> {
        vec![
            // --- should be ACCEPTED ---
            ("empty", ""),
            ("bare token", "x"),
            ("whitespace only", "   \n\n "),
            ("line comment", "-- c\nx"),
            ("block comment", "/- c -/x"),
            ("nested block", "/- a /- b -/ c -/x"),
            ("doc comment is a token", "/-- d -/x"),
            ("module doc is a token", "/-! d -/x"),
            ("comment with a tab inside", "-- has\ta tab\nx"),
            ("comment with a CR inside", "-- has\ra CR\nx"),
            ("astral scalar", "\u{1F600}x"),
            ("no final newline", "x -- end"),
            // --- should be REJECTED, each for a different reason ---
            ("tab in trivia", "x\ty"),
            ("tab at start", "\tx"),
            ("isolated CR", "x\ry"),
            ("unterminated block", "/- never closed"),
            ("unterminated nested", "/- a /- b -/"),
            ("dangling dash in block", "/- a -"),
            ("tab after a comment", "-- c\n\tx"),
            ("CR after a block comment", "/- c -/\rx"),
        ]
    }

    /// **THE LAW.** Recovery may only change what happens to input that was already going
    /// to fail; it may never make a previously-rejected file accepted.
    ///
    /// Asserted as an equality between the two configurations over the same corpus, in both
    /// directions, because both are load-bearing: recovery must not rescue a rejection, and
    /// must not break an acceptance. An example-based test — "recovery produced a tree" —
    /// is consistent with recovery accepting garbage and establishes nothing here.
    #[test]
    fn recovery_never_changes_acceptance() {
        let mut accepted = 0usize;
        let mut rejected = 0usize;
        for (label, raw) in corpus() {
            let text = text_of(raw);
            let plain = lex(&text);
            let recovered = lex_recovering(&text);
            assert_eq!(
                plain.accepted(),
                recovered.accepted(),
                "{label:?}: recovery changed acceptance ({} -> {})",
                plain.accepted(),
                recovered.accepted()
            );
            if plain.accepted() {
                accepted += 1;
                // An accepted input records no errors under either configuration, so
                // recovery cannot be quietly adding a diagnostic to clean input.
                assert!(recovered.errors.is_empty(), "{label:?}: invented an error");
            } else {
                rejected += 1;
                // A rejected input stays rejected, and recovery finds AT LEAST as many
                // problems — never fewer, which is the direction that would rescue it.
                assert!(
                    recovered.errors.len() >= plain.errors.len(),
                    "{label:?}: recovery reported fewer errors than the plain lexer"
                );
            }
        }
        // The corpus must exercise both outcomes, or the equality above is vacuous.
        assert!(
            accepted >= 10,
            "corpus needs accepted inputs, got {accepted}"
        );
        assert!(
            rejected >= 5,
            "corpus needs rejected inputs, got {rejected}"
        );
    }

    /// What recovery is FOR: it keeps going, so a file with two problems reports two rather
    /// than stopping at the first. That is the only thing it may change.
    #[test]
    fn recovery_reports_later_errors_the_plain_lexer_never_reaches() {
        let text = text_of("a\tb\tc");
        let plain = lex(&text);
        let recovered = lex_recovering(&text);

        assert_eq!(plain.errors.len(), 1, "the plain lexer stops at the first");
        assert_eq!(recovered.errors.len(), 2, "recovery reaches the second");
        assert!(!plain.accepted() && !recovered.accepted(), "still rejected");

        // Both refusals are the same kind, at the offsets a diagnostic would point at.
        assert_eq!(
            recovered.errors[0].error,
            TriviaError::Tab { at: BytePos(1) }
        );
        assert_eq!(
            recovered.errors[1].error,
            TriviaError::Tab { at: BytePos(3) }
        );
        // The skipped region is recorded, so a skipped byte is auditable rather than lost.
        assert_eq!(recovered.errors[0].skipped.len_bytes(), 1);
    }

    /// Recovery terminates. A recovery loop that fails to advance past a refusal is an
    /// infinite loop, which is a worse failure than the error it was recovering from.
    #[test]
    fn recovery_always_advances_and_terminates() {
        // Every refusal kind, including one at the very last byte where the resume point
        // clamps to end of text.
        for raw in [
            "\t",
            "\r",
            "/-",
            "\t\t\t",
            "\r\r",
            "x\t",
            "x\r",
            "/- \t -/\t",
        ] {
            let text = text_of(raw);
            let recovered = lex_recovering(&text);
            assert!(!recovered.accepted(), "{raw:?} should be rejected");
            assert!(
                !recovered.errors.is_empty(),
                "{raw:?} must record its refusals"
            );
            // Each skipped region is inside the text and non-negative by construction.
            for entry in &recovered.errors {
                assert!(entry.skipped.end().0 <= text.len_bytes());
            }
        }
    }

    /// Boundaries are only ever added by recovery, never removed — the mechanical reason
    /// `accepted` cannot move from false to true.
    #[test]
    fn recovery_only_ever_adds_to_what_the_plain_lexer_found() {
        for (label, raw) in corpus() {
            let text = text_of(raw);
            let plain = lex(&text);
            let recovered = lex_recovering(&text);
            assert!(
                recovered.boundaries.len() >= plain.boundaries.len(),
                "{label:?}: recovery lost a boundary the plain lexer had"
            );
            // On accepted input the two configurations agree exactly: recovery is inert
            // where there is nothing to recover from, so it cannot perturb a clean parse.
            if plain.accepted() {
                assert_eq!(
                    plain.boundaries, recovered.boundaries,
                    "{label:?}: recovery perturbed a clean lex"
                );
            }
        }
    }
}
