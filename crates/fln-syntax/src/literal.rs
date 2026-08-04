//! Literal lexing — numerals, strings, char literals, name literals (plan §9;
//! bead franken_lean-81oq).
//!
//! Separate from [`crate::token`] because it is a separate grammar: the token table decides
//! nothing here. [`crate::token::lex_token`] dispatches to [`lex_literal`] on the same
//! openers the pin dispatches on (`Lean/Parser/Basic.lean:1027-1046`), and this module owns
//! everything after that.
//!
//! ## The trap this module exists to get right
//!
//! `1..5` must lex as the numeral `1` followed by the token `..`, **not** as `1.` and then
//! `.5`. Upstream handles it with an explicit two-character lookahead before it will treat a
//! `.` as a decimal point (`Basic.lean:839-841`):
//!
//! ```text
//! if ∃ hj : ¬ c.atEnd j, curr = '.' && c.get' j hj = '.' then  -- stop, it is a numeral
//! ```
//!
//! Without that lookahead a range expression silently becomes a malformed float, and the
//! diagnostic lands nowhere near the cause. Asserted directly below.
//!
//! ## The other things that are easy to get wrong, all from the pin
//!
//! * **`_` is a digit separator** (`takeDigitsFn`, `Basic.lean:819-828`): `1_000` is one
//!   numeral. A `_` sets `needDigit`, so `1_` is an error rather than a numeral with a
//!   trailing underscore.
//! * **Radix prefixes require a digit**: `binNumberFn`/`octalNumberFn`/`hexNumberFn` all
//!   start with `needDigit := true`, so `0x` alone is refused, not read as `0` then `x`.
//! * **A bare trailing dot is legal** (`1.` is scientific with `hasBareDot`), but a bare dot
//!   followed by an identifier is a *specific* error reported **at the start of the
//!   numeral**, not at the identifier: "unexpected identifier after decimal point; consider
//!   parenthesizing the number". The position matters — it is what makes `1.foo` point at
//!   the thing the user has to parenthesize.
//! * **String gaps** (`stringGapFn`, `Basic.lean:633`): a `\` before a newline eats the
//!   newline and following whitespace, but **at most one newline** — a second is
//!   "unexpected additional newline in string gap".
//! * **An unterminated string is reported at its opening quote**, not at end of file, which
//!   is the only position that helps.
//!
//! ## Raw strings, and the one state nobody expects
//!
//! A raw string's delimiter is `#`-counted (`isRawStrLitStart`, `Basic.lean:736`): the closing
//! delimiter depends on how the opening one was spelled, so `r##"..."##` needs two `#` to
//! close and a lone `"#` inside it is content.
//!
//! The state machine has three states, and the third is the one that gets omitted
//! (`Basic.lean:750-809`). While counting closing `#`s, a **second `"` restarts the count at
//! zero** rather than dropping back to scanning content:
//!
//! ```text
//! closingState num closingNum:
//!   '#' -> if closingNum + 1 == num then done else keep counting
//!   '"' -> closingState num 0        -- a NEW candidate closer, not content
//!   _   -> normalState num
//! ```
//!
//! Without that restart, `r#"a""#` — a raw string whose content is `a"` — fails to close,
//! because the first `"` consumes the candidacy and the second is treated as content. The
//! test below walks `r##"a"#"##` for the same reason: it closes only on the *second* run of
//! `#`s, after an interior `"#` that looks exactly like a terminator.
//!
//! Escapes are inert in a raw string — that is the whole point of the form — so `r"\n"` is
//! four characters and not a newline, and it can never raise an escape error.

use crate::source::{BytePos, ByteSpan, SourceText};
use crate::token::{ID_BEGIN_ESCAPE, is_id_first};

/// Which literal form was lexed. These mirror the pin's `numLitKind`, `scientificLitKind`,
/// `strLitKind`, `charLitKind` and `Syntax.mkNameLit`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LiteralKind {
    /// `numLitKind` — every radix, since upstream gives hex, octal, binary and decimal the
    /// same kind. Distinguishing them here would invent a distinction the pin does not make.
    Nat,
    /// `scientificLitKind` — anything with a decimal point or an exponent.
    Scientific,
    Str,
    Char,
    Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexedLiteral {
    pub kind: LiteralKind,
    pub extent: ByteSpan,
}

/// Why literal lexing refused. Every message is the pin's, verbatim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LiteralError {
    EndOfInput {
        at: BytePos,
    },
    /// `strLitFnAux`'s `mkUnexpectedErrorAt ... startPos` — reported at the opening quote.
    UnterminatedString {
        opened_at: BytePos,
    },
    /// `quotedCharCoreFn`'s final `else`.
    InvalidEscape {
        at: BytePos,
    },
    /// `charLitFnAux`'s closing check.
    MissingEndOfCharLiteral {
        at: BytePos,
    },
    /// `stringGapFn`'s two-newline refusal.
    AdditionalNewlineInStringGap {
        at: BytePos,
    },
    /// `parseOptExp`'s `e`-with-no-digits refusal.
    MissingExponentDigits {
        at: BytePos,
    },
    /// `parseOptExp`'s bare-dot-then-identifier refusal, reported at the numeral's start.
    IdentifierAfterDecimalPoint {
        at: BytePos,
    },
    /// `takeDigitsFn`'s refusal. `expecting` is the pin's own label for the radix, which is
    /// what a diagnostic shows the user.
    ExpectedDigit {
        at: BytePos,
        expecting: &'static str,
    },
    /// `nameLitAux`'s refusal.
    InvalidNameLiteral {
        at: BytePos,
    },
    /// An unterminated `«` inside a name literal, propagated from the identifier scan.
    UnterminatedIdentifierEscape {
        at: BytePos,
    },
    /// `rawStrLitFnAux`'s `errorUnterminated` — reported at the opening `r`, like the
    /// ordinary string's refusal and for the same reason.
    UnterminatedRawString {
        opened_at: BytePos,
    },
}

impl LiteralError {
    pub fn message(&self) -> &'static str {
        match self {
            LiteralError::EndOfInput { .. } => "unexpected end of input",
            LiteralError::UnterminatedString { .. } => "unterminated string literal",
            LiteralError::InvalidEscape { .. } => "invalid escape sequence",
            LiteralError::MissingEndOfCharLiteral { .. } => "missing end of character literal",
            LiteralError::AdditionalNewlineInStringGap { .. } => {
                "unexpected additional newline in string gap"
            }
            LiteralError::MissingExponentDigits { .. } => {
                "missing exponent digits in scientific literal"
            }
            LiteralError::IdentifierAfterDecimalPoint { .. } => {
                "unexpected identifier after decimal point; consider parenthesizing the number"
            }
            LiteralError::ExpectedDigit { .. } => "unexpected character",
            LiteralError::InvalidNameLiteral { .. } => "invalid Name literal",
            LiteralError::UnterminatedIdentifierEscape { .. } => "unterminated identifier escape",
            LiteralError::UnterminatedRawString { .. } => "unterminated raw string literal",
        }
    }

    /// The same refusal with its offset moved by `delta` bytes.
    ///
    /// Exhaustive on purpose. An incremental re-lex reuses refusals from after an edit, and
    /// this is where a reused diagnostic acquires its new position; a variant that forgot to
    /// move would underline the wrong character, which is the kind of wrongness a user sees
    /// and a test does not — unless the test is a differential, which is how the omission was
    /// caught in the first place.
    pub fn shifted(&self, delta: isize) -> LiteralError {
        let moved = |at: BytePos| BytePos((at.0 as isize + delta).max(0) as usize);
        match self {
            LiteralError::EndOfInput { at } => LiteralError::EndOfInput { at: moved(*at) },
            LiteralError::UnterminatedString { opened_at } => LiteralError::UnterminatedString {
                opened_at: moved(*opened_at),
            },
            LiteralError::InvalidEscape { at } => LiteralError::InvalidEscape { at: moved(*at) },
            LiteralError::MissingEndOfCharLiteral { at } => {
                LiteralError::MissingEndOfCharLiteral { at: moved(*at) }
            }
            LiteralError::AdditionalNewlineInStringGap { at } => {
                LiteralError::AdditionalNewlineInStringGap { at: moved(*at) }
            }
            LiteralError::MissingExponentDigits { at } => {
                LiteralError::MissingExponentDigits { at: moved(*at) }
            }
            LiteralError::IdentifierAfterDecimalPoint { at } => {
                LiteralError::IdentifierAfterDecimalPoint { at: moved(*at) }
            }
            LiteralError::ExpectedDigit { at, expecting } => LiteralError::ExpectedDigit {
                at: moved(*at),
                expecting,
            },
            LiteralError::InvalidNameLiteral { at } => {
                LiteralError::InvalidNameLiteral { at: moved(*at) }
            }
            LiteralError::UnterminatedIdentifierEscape { at } => {
                LiteralError::UnterminatedIdentifierEscape { at: moved(*at) }
            }
            LiteralError::UnterminatedRawString { opened_at } => {
                LiteralError::UnterminatedRawString {
                    opened_at: moved(*opened_at),
                }
            }
        }
    }

    pub fn at(&self) -> BytePos {
        match self {
            LiteralError::EndOfInput { at }
            | LiteralError::InvalidEscape { at }
            | LiteralError::MissingEndOfCharLiteral { at }
            | LiteralError::AdditionalNewlineInStringGap { at }
            | LiteralError::MissingExponentDigits { at }
            | LiteralError::IdentifierAfterDecimalPoint { at }
            | LiteralError::ExpectedDigit { at, .. }
            | LiteralError::InvalidNameLiteral { at }
            | LiteralError::UnterminatedIdentifierEscape { at } => *at,
            LiteralError::UnterminatedString { opened_at }
            | LiteralError::UnterminatedRawString { opened_at } => *opened_at,
        }
    }
}

/// Whether a literal starts at `from`, and if so which opener — the pin's dispatch order
/// from `tokenFnAux`, which this mirrors so the two cannot fall out of step.
///
/// `''` is deliberately *not* a char-literal opener (`curr == '\'' && c.getNext i != '\''`),
/// which is why the second condition is a lookahead rather than a bare character test.
pub fn starts_literal(text: &SourceText, from: BytePos) -> bool {
    let s = text.as_str();
    let Some(first) = s[from.0..].chars().next() else {
        return false;
    };
    let next = s[from.0..].chars().nth(1);
    first == '"'
        || (first == '\'' && next != Some('\''))
        || first.is_ascii_digit()
        || (first == '`' && next.is_some_and(|c| is_id_first(c) || c == ID_BEGIN_ESCAPE))
        || (first == 'r' && is_raw_string_start(s, from.0 + 1))
}

/// `isRawStrLitStart` (`Basic.lean:736`): after the `r`, zero or more `#` then a `"`.
fn is_raw_string_start(s: &str, at: usize) -> bool {
    let rest = s.as_bytes().get(at..).unwrap_or(&[]);
    let hashes = rest.iter().take_while(|b| **b == b'#').count();
    rest.get(hashes) == Some(&b'"')
}

/// Lex a literal at `from`. Call only where [`starts_literal`] holds.
pub fn lex_literal(text: &SourceText, from: BytePos) -> Result<LexedLiteral, LiteralError> {
    let s = text.as_str();
    let Some(first) = s[from.0..].chars().next() else {
        return Err(LiteralError::EndOfInput { at: from });
    };
    if first == 'r' {
        // Reached only when `starts_literal` saw a raw-string opener.
        return lex_raw_string(s, from);
    }
    match first {
        '"' => lex_string(s, from),
        '\'' => lex_char(s, from),
        '`' => lex_name(s, from),
        _ => lex_number(s, from),
    }
}

// ---------------------------------------------------------------------------------------
// Numerals
// ---------------------------------------------------------------------------------------

/// `numberFnAux` (`Basic.lean:900`).
fn lex_number(s: &str, from: BytePos) -> Result<LexedLiteral, LiteralError> {
    let bytes = s.as_bytes();
    if bytes[from.0] == b'0' {
        let after = from.0 + 1;
        match bytes.get(after) {
            Some(b'b' | b'B') => {
                let stop = take_digits(
                    s,
                    after + 1,
                    |c| c == b'0' || c == b'1',
                    "binary number",
                    true,
                )?;
                return Ok(nat(from, stop));
            }
            Some(b'o' | b'O') => {
                let stop = take_digits(
                    s,
                    after + 1,
                    |c| c.is_ascii_digit() && c <= b'7',
                    "octal number",
                    true,
                )?;
                return Ok(nat(from, stop));
            }
            Some(b'x' | b'X') => {
                let stop = take_digits(
                    s,
                    after + 1,
                    |c| c.is_ascii_hexdigit(),
                    "hexadecimal number",
                    true,
                )?;
                return Ok(nat(from, stop));
            }
            _ => {}
        }
    }
    // Decimal. The first digit is already known to be one, so no digit is *needed* here;
    // `takeDigitsFn` is entered with `needDigit := false`.
    let at = take_digits(
        s,
        from.0 + 1,
        |c| c.is_ascii_digit(),
        "decimal number",
        false,
    )?;
    lex_after_decimal_digits(s, from, at)
}

/// `decimalNumberFn`'s tail (`Basic.lean:831-848`) — where the `..` lookahead lives.
fn lex_after_decimal_digits(
    s: &str,
    from: BytePos,
    at: usize,
) -> Result<LexedLiteral, LiteralError> {
    let bytes = s.as_bytes();
    let Some(&c) = bytes.get(at) else {
        return Ok(nat(from, at));
    };
    // THE LOOKAHEAD: `1..5` is the numeral `1` and then the token `..`. Without this, a
    // range expression becomes a malformed float and the diagnostic lands far from the cause.
    if c == b'.' && bytes.get(at + 1) == Some(&b'.') {
        return Ok(nat(from, at));
    }
    if c == b'.' || c == b'e' || c == b'E' {
        return lex_scientific(s, from, at);
    }
    Ok(nat(from, at))
}

/// `parseScientific` = `parseOptDot` then `parseOptExp` (`Basic.lean:849-882`).
fn lex_scientific(s: &str, from: BytePos, at: usize) -> Result<LexedLiteral, LiteralError> {
    let bytes = s.as_bytes();
    let mut at = at;
    let mut bare_dot = false;
    if bytes.get(at) == Some(&b'.') {
        at += 1;
        if bytes.get(at).is_some_and(u8::is_ascii_digit) {
            at = take_digits(s, at, |c| c.is_ascii_digit(), "decimal number", false)?;
        } else {
            // `1.` — legal on its own. What may not follow it is an identifier.
            bare_dot = true;
        }
    }
    match bytes.get(at) {
        Some(b'e' | b'E') => {
            at += 1;
            if matches!(bytes.get(at), Some(b'-' | b'+')) {
                at += 1;
            }
            if bytes.get(at).is_some_and(u8::is_ascii_digit) {
                at = take_digits(s, at, |c| c.is_ascii_digit(), "decimal number", false)?;
            } else {
                return Err(LiteralError::MissingExponentDigits { at: BytePos(at) });
            }
        }
        Some(_) if bare_dot => {
            let next = s[at..].chars().next().unwrap_or('\0');
            if is_id_first(next) || next == ID_BEGIN_ESCAPE {
                // Reported at the START of the numeral, which is the span the user has to
                // parenthesize — `(1).foo`. Pointing at `foo` would describe the symptom.
                return Err(LiteralError::IdentifierAfterDecimalPoint { at: from });
            }
        }
        _ => {}
    }
    Ok(LexedLiteral {
        kind: LiteralKind::Scientific,
        extent: span(from, BytePos(at)),
    })
}

/// `takeDigitsFn` (`Basic.lean:815-828`).
///
/// One function with `need_digit` threaded through it, as upstream has it — not a strict and
/// a lenient variant. The only difference between call sites is the *initial* value: a radix
/// prefix demands a digit, a decimal numeral has already seen one. A `_` sets the demand
/// again wherever it appears, which is why `1_` is an error in the decimal path too even
/// though that path starts out lenient.
fn take_digits(
    s: &str,
    from: usize,
    is_digit: impl Fn(u8) -> bool,
    expecting: &'static str,
    need_digit: bool,
) -> Result<usize, LiteralError> {
    let bytes = s.as_bytes();
    let mut at = from;
    let mut need_digit = need_digit;
    loop {
        match bytes.get(at) {
            None => {
                return if need_digit {
                    Err(LiteralError::ExpectedDigit {
                        at: BytePos(at),
                        expecting,
                    })
                } else {
                    Ok(at)
                };
            }
            Some(&b'_') => {
                need_digit = true;
                at += 1;
            }
            Some(&c) if is_digit(c) => {
                need_digit = false;
                at += 1;
            }
            Some(_) => {
                return if need_digit {
                    Err(LiteralError::ExpectedDigit {
                        at: BytePos(at),
                        expecting,
                    })
                } else {
                    Ok(at)
                };
            }
        }
    }
}

fn nat(from: BytePos, stop: usize) -> LexedLiteral {
    LexedLiteral {
        kind: LiteralKind::Nat,
        extent: span(from, BytePos(stop)),
    }
}

// ---------------------------------------------------------------------------------------
// Strings and char literals
// ---------------------------------------------------------------------------------------

/// `strLitFnAux` (`Basic.lean:719`). `from` is the opening quote.
fn lex_string(s: &str, from: BytePos) -> Result<LexedLiteral, LiteralError> {
    let mut at = from.0 + 1;
    loop {
        let Some(c) = s[at..].chars().next() else {
            return Err(LiteralError::UnterminatedString { opened_at: from });
        };
        match c {
            '"' => {
                return Ok(LexedLiteral {
                    kind: LiteralKind::Str,
                    extent: span(from, BytePos(at + 1)),
                });
            }
            '\\' => at = quoted_char(s, at + 1, true)?,
            _ => at += c.len_utf8(),
        }
    }
}

/// `charLitFnAux` (`Basic.lean:704`). `from` is the opening quote.
fn lex_char(s: &str, from: BytePos) -> Result<LexedLiteral, LiteralError> {
    let mut at = from.0 + 1;
    let Some(c) = s[at..].chars().next() else {
        return Err(LiteralError::EndOfInput { at: BytePos(at) });
    };
    if c == '\\' {
        at = quoted_char(s, at + 1, false)?;
    } else {
        at += c.len_utf8();
    }
    // Exactly one character, then the close. `'ab'` is an error, not a two-char literal.
    match s[at..].chars().next() {
        Some('\'') => Ok(LexedLiteral {
            kind: LiteralKind::Char,
            extent: span(from, BytePos(at + 1)),
        }),
        _ => Err(LiteralError::MissingEndOfCharLiteral { at: BytePos(at) }),
    }
}

/// `quotedCharCoreFn` (`Basic.lean:655-671`). `at` is just past the backslash; returns the
/// offset just past the escape.
fn quoted_char(s: &str, at: usize, in_string: bool) -> Result<usize, LiteralError> {
    let Some(c) = s[at..].chars().next() else {
        return Err(LiteralError::EndOfInput { at: BytePos(at) });
    };
    // `isQuotableCharDefault`: exactly these six, and no others. `\0` and `\a` are not Lean
    // escapes even though most languages have them.
    if matches!(c, '\\' | '"' | '\'' | 'r' | 'n' | 't') {
        return Ok(at + 1);
    }
    if c == 'x' {
        return hex_digits(s, at + 1, 2);
    }
    if c == 'u' {
        return hex_digits(s, at + 1, 4);
    }
    if in_string && c == '\n' {
        return string_gap(s, at + 1);
    }
    Err(LiteralError::InvalidEscape { at: BytePos(at) })
}

fn hex_digits(s: &str, at: usize, count: usize) -> Result<usize, LiteralError> {
    let bytes = s.as_bytes();
    for offset in 0..count {
        match bytes.get(at + offset) {
            Some(c) if c.is_ascii_hexdigit() => {}
            // Upstream reaches `hexDigitFn`, whose refusal is about the escape being wrong.
            _ => {
                return Err(LiteralError::InvalidEscape {
                    at: BytePos(at + offset),
                });
            }
        }
    }
    Ok(at + count)
}

/// `stringGapFn` (`Basic.lean:633`): whitespace after the escaped newline, with **at most
/// one** newline. The cap is upstream's, on the grounds that more than one is visually
/// confusing — a readability rule enforced by the lexer, so ours has to enforce it too.
fn string_gap(s: &str, at: usize) -> Result<usize, LiteralError> {
    let mut at = at;
    let mut seen_newline = true; // the escaped newline itself
    while let Some(c) = s[at..].chars().next() {
        if c == '\n' {
            if seen_newline {
                return Err(LiteralError::AdditionalNewlineInStringGap { at: BytePos(at) });
            }
            seen_newline = true;
            at += 1;
        } else if c.is_whitespace() {
            at += c.len_utf8();
        } else {
            break;
        }
    }
    Ok(at)
}

// ---------------------------------------------------------------------------------------
// Raw strings
// ---------------------------------------------------------------------------------------

/// `rawStrLitFnAux` (`Basic.lean:750`). `from` is the opening `r`.
///
/// Byte-stepping rather than scalar-stepping: every character this machine branches on
/// (`"`, `#`) is ASCII, and a UTF-8 continuation byte can never equal an ASCII byte, so the
/// two agree on every input. Recorded because it is a deliberate divergence from the pin's
/// `c.next'`, not an oversight about multi-byte content.
fn lex_raw_string(s: &str, from: BytePos) -> Result<LexedLiteral, LiteralError> {
    let bytes = s.as_bytes();
    let unterminated = LiteralError::UnterminatedRawString { opened_at: from };

    // `initState`: count the `#`s after the `r`, then require the opening quote.
    let mut at = from.0 + 1;
    let mut hashes = 0usize;
    while bytes.get(at) == Some(&b'#') {
        hashes += 1;
        at += 1;
    }
    if bytes.get(at) != Some(&b'"') {
        // Upstream calls this state unreachable given `isRawStrLitStart`. Refusing rather
        // than asserting keeps `lex_raw_string` total even if a caller skips that check.
        return Err(unterminated);
    }
    at += 1;

    // `normalState`, with `closingState` inlined as the inner loop.
    loop {
        match bytes.get(at) {
            None => return Err(unterminated),
            Some(&b'"') => {
                at += 1;
                if hashes == 0 {
                    return Ok(str_literal(from, at));
                }
                let mut closing = 0usize;
                loop {
                    match bytes.get(at) {
                        None => return Err(unterminated),
                        Some(&b'#') => {
                            at += 1;
                            closing += 1;
                            if closing == hashes {
                                return Ok(str_literal(from, at));
                            }
                        }
                        // THE RESTART: this quote is a new candidate closer, not content.
                        Some(&b'"') => {
                            at += 1;
                            closing = 0;
                        }
                        Some(_) => {
                            at += 1;
                            break;
                        }
                    }
                }
            }
            Some(_) => at += 1,
        }
    }
}

/// A raw string and an ordinary string share `strLitKind` upstream, so they share a kind
/// here. Giving raw strings their own kind would invent a distinction the pin does not make.
fn str_literal(from: BytePos, stop: usize) -> LexedLiteral {
    LexedLiteral {
        kind: LiteralKind::Str,
        extent: span(from, BytePos(stop)),
    }
}

// ---------------------------------------------------------------------------------------
// Name literals
// ---------------------------------------------------------------------------------------

/// `nameLitAux` (`Basic.lean:1015`): a backtick then an identifier. The identifier scan is
/// [`crate::token`]'s, deliberately — a name literal's name has to be the same name an
/// identifier would be, and a second scanner is a second thing to drift.
fn lex_name(s: &str, from: BytePos) -> Result<LexedLiteral, LiteralError> {
    match crate::token::scan_ident_extent(s, BytePos(from.0 + 1)) {
        Ok(Some(stop)) => Ok(LexedLiteral {
            kind: LiteralKind::Name,
            extent: span(from, stop),
        }),
        Ok(None) => Err(LiteralError::InvalidNameLiteral { at: from }),
        // The escape refusal is passed through with its own offset rather than flattened
        // into "invalid Name literal": upstream propagates identFnAux's error too, and the
        // unterminated `«` is the actionable fact.
        Err(error) => Err(LiteralError::UnterminatedIdentifierEscape { at: error.at() }),
    }
}

fn span(start: BytePos, end: BytePos) -> ByteSpan {
    ByteSpan::new(start, end).unwrap_or(ByteSpan::empty_at(start))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text_of(raw: &str) -> SourceText {
        SourceText::from_utf8(raw.as_bytes()).expect("valid UTF-8")
    }

    /// A classification string, for the same reason [`crate::token`]'s tests use one: the
    /// interesting failures are misclassifications, and a diff shows both sides.
    fn lex(raw: &str) -> String {
        let text = text_of(raw);
        match lex_literal(&text, BytePos(0)) {
            Ok(lexed) => format!("{:?} {}", lexed.kind, lexed.extent.len_bytes()),
            Err(error) => format!("error {error:?}"),
        }
    }

    /// **The `1..5` trap.** A numeral followed by the range token must not eat the first dot.
    /// This is the single highest-value assertion in the module: get it wrong and every range
    /// expression in the corpus becomes a malformed float, diagnosed nowhere near the cause.
    #[test]
    fn a_numeral_before_a_range_token_stops_at_the_first_dot() {
        assert_eq!(lex("1..5"), "Nat 1", "`1..5` is `1` then `..`");
        assert_eq!(lex("10..20"), "Nat 2");
        assert_eq!(lex("0..1"), "Nat 1");
        // One dot still makes it scientific, which is what makes the lookahead necessary
        // rather than a blanket "a dot never follows a numeral".
        assert_eq!(lex("1.5"), "Scientific 3");
        assert_eq!(lex("1."), "Scientific 2");
    }

    /// Radix prefixes, and the digit each one requires.
    #[test]
    fn every_radix_needs_at_least_one_digit_after_its_prefix() {
        assert_eq!(lex("0b1010"), "Nat 6");
        assert_eq!(lex("0B1010"), "Nat 6");
        assert_eq!(lex("0o17"), "Nat 4");
        assert_eq!(lex("0x1F"), "Nat 4");
        assert_eq!(lex("0X1f"), "Nat 4");

        // A prefix with nothing after it is refused, NOT read as `0` followed by `x`.
        assert_eq!(
            lex("0x"),
            format!(
                "error {:?}",
                LiteralError::ExpectedDigit {
                    at: BytePos(2),
                    expecting: "hexadecimal number"
                }
            )
        );
        assert!(lex("0b").starts_with("error"), "0b alone");
        assert!(lex("0o").starts_with("error"), "0o alone");
        // And a digit outside the radix is refused at the offending byte.
        assert!(lex("0b2").starts_with("error"), "2 is not binary");
        assert!(lex("0o8").starts_with("error"), "8 is not octal");
        assert!(lex("0xg").starts_with("error"), "g is not hex");
        // `0` on its own is a numeral, not a broken prefix.
        assert_eq!(lex("0"), "Nat 1");
        assert_eq!(
            lex("0777"),
            "Nat 4",
            "a leading zero is not an octal prefix"
        );
    }

    /// `_` is a digit separator, and it demands a digit after it.
    #[test]
    fn underscore_separates_digits_but_may_not_trail() {
        assert_eq!(lex("1_000"), "Nat 5");
        assert_eq!(lex("1_000_000"), "Nat 9");
        assert_eq!(lex("0xdead_beef"), "Nat 11");
        // A `_` sets the digit requirement wherever it appears, so a trailing one is an
        // error in EVERY path — including decimal, which started out lenient. One function
        // with `need_digit` threaded, as the pin has it, is what makes that fall out.
        assert!(lex("1_").starts_with("error"), "trailing _ in a decimal");
        assert!(lex("0x1_").starts_with("error"), "trailing _ after hex");
        assert!(lex("1_a").starts_with("error"), "_ then a non-digit");
    }

    /// Scientific forms, including the exponent that has no digits.
    #[test]
    fn exponents_are_lexed_and_an_empty_one_is_refused() {
        assert_eq!(lex("1e10"), "Scientific 4");
        assert_eq!(lex("1E10"), "Scientific 4");
        assert_eq!(lex("1e+10"), "Scientific 5");
        assert_eq!(lex("1e-10"), "Scientific 5");
        assert_eq!(lex("1.5e-10"), "Scientific 7");
        assert_eq!(
            lex("1e"),
            format!(
                "error {:?}",
                LiteralError::MissingExponentDigits { at: BytePos(2) }
            )
        );
        assert!(lex("1e+").starts_with("error"), "sign but no digits");
    }

    /// A bare decimal point followed by an identifier is a specific refusal, and it is
    /// reported at the START of the numeral — the span the user has to parenthesize. A
    /// diagnostic pointing at `foo` would describe the symptom instead of the fix.
    #[test]
    fn a_bare_dot_before_an_identifier_is_refused_at_the_numerals_start() {
        assert_eq!(
            lex("1.foo"),
            format!(
                "error {:?}",
                LiteralError::IdentifierAfterDecimalPoint { at: BytePos(0) }
            )
        );
        assert_eq!(
            LiteralError::IdentifierAfterDecimalPoint { at: BytePos(0) }.message(),
            "unexpected identifier after decimal point; consider parenthesizing the number"
        );
        // But a bare dot before something that cannot start an identifier is fine.
        assert_eq!(lex("1.)"), "Scientific 2");
        assert_eq!(lex("1. "), "Scientific 2");
    }

    /// Strings, escapes, and the exact set of quotable characters.
    #[test]
    fn strings_accept_the_pins_escapes_and_no_others() {
        assert_eq!(lex(r#""abc""#), "Str 5");
        assert_eq!(lex(r#""""#), "Str 2", "the empty string");
        assert_eq!(lex(r#""a\nb""#), "Str 6");
        assert_eq!(lex(r#""\\""#), "Str 4");
        assert_eq!(
            lex(r#""\"""#),
            "Str 4",
            "an escaped quote does not close it"
        );
        assert_eq!(lex(r#""\x41""#), "Str 6");
        assert_eq!(lex(r#""\u0041""#), "Str 8");
        // Escapes most languages have and Lean does not.
        assert!(
            lex(r#""\0""#).starts_with("error"),
            r"\0 is not a Lean escape"
        );
        assert!(
            lex(r#""\a""#).starts_with("error"),
            r"\a is not a Lean escape"
        );
        // A short hex escape is refused rather than accepted as one digit.
        assert!(lex(r#""\x4""#).starts_with("error"), "one hex digit");
        assert!(lex(r#""\u041""#).starts_with("error"), "three hex digits");
        // Multi-byte content is measured in bytes.
        assert_eq!(lex("\"αβ\""), "Str 6");
    }

    /// An unterminated string is reported at its OPENING QUOTE. End-of-file is where the
    /// scan noticed; the opening quote is the only position that helps.
    #[test]
    fn an_unterminated_string_points_at_its_opening_quote() {
        assert_eq!(
            lex(r#""abc"#),
            format!(
                "error {:?}",
                LiteralError::UnterminatedString {
                    opened_at: BytePos(0)
                }
            )
        );
        // A trailing backslash does not close it either.
        assert!(lex(r#""abc\"#).starts_with("error"));
    }

    /// String gaps: `\` before a newline eats the newline and the following indentation, but
    /// at most one newline.
    #[test]
    fn a_string_gap_eats_one_newline_and_the_indentation_after_it() {
        assert_eq!(
            lex("\"a\\\n   b\""),
            "Str 9",
            "gap eats the newline and spaces"
        );
        assert_eq!(
            lex("\"a\\\n\n b\""),
            format!(
                "error {:?}",
                LiteralError::AdditionalNewlineInStringGap { at: BytePos(4) }
            ),
            "a second newline in one gap is refused"
        );
        // A raw newline with no backslash is just content, not a gap and not an error.
        assert_eq!(lex("\"a\nb\""), "Str 5");
    }

    /// Char literals hold exactly one character.
    #[test]
    fn a_char_literal_holds_exactly_one_character() {
        assert_eq!(lex("'a'"), "Char 3");
        assert_eq!(lex(r"'\n'"), "Char 4");
        assert_eq!(lex(r"'\''"), "Char 4");
        assert_eq!(lex(r"'\\'"), "Char 4");
        assert_eq!(lex("'α'"), "Char 4", "a multi-byte scalar is one character");
        assert_eq!(
            lex("'ab'"),
            format!(
                "error {:?}",
                LiteralError::MissingEndOfCharLiteral { at: BytePos(2) }
            ),
            "two characters is an error, not a two-char literal"
        );
        assert!(lex("'a").starts_with("error"), "unterminated");
    }

    /// `''` is not a char-literal opener at all — the dispatch looks ahead. Without the
    /// lookahead, `''` would be lexed as an empty char literal, which does not exist.
    #[test]
    fn two_quotes_are_not_a_char_literal() {
        let text = text_of("''");
        assert!(
            !starts_literal(&text, BytePos(0)),
            "`''` must fall through to the token table"
        );
        let text = text_of("'a'");
        assert!(starts_literal(&text, BytePos(0)), "`'a'` is a char literal");
    }

    /// Name literals reuse the identifier scanner, so a name literal's name is exactly the
    /// name the same text would be as an identifier.
    #[test]
    fn a_name_literal_is_a_backtick_and_an_identifier() {
        assert_eq!(lex("`foo"), "Name 4");
        assert_eq!(lex("`Nat.succ"), "Name 9");
        assert_eq!(lex("`«odd one»"), "Name 12");
        // A backtick with no identifier after it is not a name literal opener, so the
        // dispatch never calls us — asserted at the dispatch, where the decision is.
        let text = text_of("`1");
        assert!(!starts_literal(&text, BytePos(0)), "`1 is not a name lit");
        let text = text_of("`");
        assert!(!starts_literal(&text, BytePos(0)), "a bare backtick");
    }

    /// Raw strings: the `#` count decides the closer, so an interior `"` or `"#` is content.
    #[test]
    fn a_raw_strings_closer_is_spelled_the_way_its_opener_was() {
        assert_eq!(lex(r##"r"a""##), "Str 4");
        assert_eq!(lex(r##"r#"a"#"##), "Str 6");
        assert_eq!(lex(r###"r##"a"##"###), "Str 8");
        // An interior `#` is content when no quote precedes it.
        assert_eq!(lex(r##"r#"a#"#"##), "Str 7");
    }

    /// **The state nobody implements.** While counting closing `#`s, a second `"` restarts
    /// the count — it is a new candidate closer, not content. Without the restart, a raw
    /// string whose content ends in a quote never closes.
    #[test]
    fn a_quote_while_counting_closing_hashes_restarts_the_count() {
        // Content is `a"`. The first `"` opens a candidacy, the second replaces it, the `#`
        // completes it.
        assert_eq!(lex(r##"r#"a""#"##), "Str 7");
        // Content is `a"#`, which contains a complete-looking terminator for a ONE-hash raw
        // string. Only the second run of `#`s closes this two-hash one.
        assert_eq!(lex(r###"r##"a"#"##"###), "Str 10");
    }

    /// Escapes are inert in a raw string. That is the form's entire purpose, so a raw string
    /// can never raise an escape error, and `r"\n"` is two characters of content.
    #[test]
    fn escapes_are_inert_inside_a_raw_string() {
        assert_eq!(lex(r##"r"\n""##), "Str 5");
        assert_eq!(
            lex(r##"r"\""##),
            "Str 4",
            "a backslash does not escape the closer"
        );
        // The same bytes in an ORDINARY string do process the escape, which is the contrast
        // that makes the claim mean something.
        assert_eq!(lex(r#""\n""#), "Str 4");
        assert!(
            lex(r#""\q""#).starts_with("error"),
            "an ordinary string refuses an unknown escape"
        );
        assert_eq!(
            lex(r##"r"\q""##),
            "Str 5",
            "a raw string has no opinion about \\q"
        );
    }

    /// An unterminated raw string is reported at its opening `r` — the same choice the
    /// ordinary string makes, for the same reason.
    #[test]
    fn an_unterminated_raw_string_points_at_its_opening_r() {
        assert_eq!(
            lex(r##"r"a"##),
            format!(
                "error {:?}",
                LiteralError::UnterminatedRawString {
                    opened_at: BytePos(0)
                }
            )
        );
        // Closed with too few `#`s is unterminated, not closed.
        assert!(
            lex(r##"r##"a"#"##).starts_with("error"),
            "one # closes nothing"
        );
        assert!(
            lex(r##"r#"a""##).starts_with("error"),
            "quote without its #"
        );
        assert_eq!(
            LiteralError::UnterminatedRawString {
                opened_at: BytePos(0)
            }
            .message(),
            "unterminated raw string literal"
        );
    }

    /// `r` is only an opener when a raw string actually starts there.
    #[test]
    fn a_plain_r_identifier_is_not_a_raw_string_opener() {
        for raw in ["rfl", "rw", "r", "rec"] {
            let text = text_of(raw);
            assert!(
                !starts_literal(&text, BytePos(0)),
                "{raw:?} is an identifier"
            );
        }
        for raw in [r##"r"a""##, r##"r#"a"#"##, r###"r##"a"##"###] {
            let text = text_of(raw);
            assert!(
                starts_literal(&text, BytePos(0)),
                "{raw:?} is a raw-string opener"
            );
        }
    }
}
