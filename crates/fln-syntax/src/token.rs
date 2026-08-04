//! The token table, maximal munch, and identifier/keyword classification (plan §9;
//! bead franken_lean-81oq).
//!
//! ## What the pin actually does, and why it is not the obvious thing
//!
//! Upstream has **no fixed keyword list**. `Lean.Parser.TokenTable` is a `Trie Token` built
//! from whatever symbols the currently-imported syntax declares, so `theorem` is a keyword
//! only because something put the string `theorem` in the table. A lexer with a hard-coded
//! keyword set could never be extended by a user `notation`, which is a language feature,
//! not an edge case. So the table is a parameter here too.
//!
//! Tokenizing an identifier-or-keyword is one pass, not two, and this is the part that
//! surprises people (`Lean/Parser/Basic.lean:1027-1046`, `959-1011`):
//!
//! 1. Ask the trie for the **longest token that is a prefix of the input here**
//!    (`Trie.matchPrefix`, `Lean/Data/Trie.lean:170`). That answer is an `Option`; it is
//!    kept aside, not acted on.
//! 2. Independently lex an identifier from the same position (`identFnAux`) — dot-separated
//!    parts, each either bare or `«escaped»`.
//! 3. Decide between them with `isToken` (`Basic.lean:934-940`):
//!
//!    ```text
//!    tk.utf8ByteSize ≥ idStartPos.byteDistance idStopPos   →  it is a SYMBOL
//!    ```
//!
//! The comparison is **`≥`, not `>`**, and that single character is the whole keyword rule.
//! Equality is the *common* case: `theorem` lexes as a 7-byte identifier and matches a
//! 7-byte token, and `≥` is what makes it the keyword. Written `>`, every keyword in the
//! language would silently become an identifier — the language would still parse a huge
//! amount of code, wrongly. Tested directly, both directions, below.
//!
//! The other half of the same rule is what stops the naive fix: `int` must not lex as the
//! keyword `in` followed by `t`. The identifier scan reaches 3 bytes, the trie only reaches
//! 2, `2 ≥ 3` is false, so it is one identifier. A tokenizer that consulted the trie *first*
//! and committed to its match would split it — the classic longest-match-against-the-wrong-
//! alphabet bug. Consulting the trie first is precisely what upstream does not do.
//!
//! ## Why the symbol's extent comes from the table and not from the scan
//!
//! When `isToken` says symbol, upstream calls `mkTokenAndFixPos`, which sets the position to
//! `startPos + tk` — the *token's* length, discarding wherever the identifier scan got to.
//! The "FixPos" in that name is load-bearing: the scan is a probe, and its reach must not
//! leak into the token's extent.
//!
//! ## Scope of this slice
//!
//! Identifiers, escaped identifiers, dotted names, and table symbols with maximal munch.
//! **Not** numerals, string/char/name/raw-string literals — those are a separate body of
//! work (escape grammars, radix prefixes, float forms) and get their own slice rather than
//! being half-done here. [`lex_token`] refuses a literal opener with a typed
//! [`TokenError::LiteralNotYetLexed`] instead of guessing, so the gap is visible in types
//! rather than mistaken for a symbol.
//!
//! `forbiddenTk?` is deliberately absent: it is a property of a parser context (a `notation`
//! forbidding its own leading token to stop left recursion), not of the lexer, and modelling
//! it here would put parser state in the wrong layer.

use crate::literal::{self, LiteralError, LiteralKind};
use crate::source::{BytePos, ByteSpan, SourceText};
use fln_core::name::Name;
use std::{collections::BTreeMap, fmt, mem};

/// A token string in the table — upstream `Lean.Parser.Token = String`.
pub type Token = String;

/// A trie of token strings, keyed by **bytes**.
///
/// Bytes rather than chars because `Trie.matchPrefix` walks `getUTF8Byte` and compares raw
/// bytes; a char-keyed trie would agree on every token anyone writes but would be a
/// different function, and the difference would only show up on input that splits a scalar.
/// Matching the pin's alphabet is cheaper than arguing that the difference is unreachable.
#[derive(Default)]
pub struct TokenTable {
    root: TrieNode,
}

#[derive(Default)]
struct TrieNode {
    /// The token ending here, if this path spells one.
    value: Option<Token>,
    children: BTreeMap<u8, TrieNode>,
}

/// An explicit trie worklist.
///
/// Token strings are user-extensible grammar state, so trie depth is input-controlled. Keeping
/// the traversal state here, on the heap, prevents every caller that walks the table from
/// turning one token byte into one host-stack frame (bead `franken_lean-36di`).
struct TrieNodes<'a> {
    pending: Vec<&'a TrieNode>,
}

impl<'a> TrieNodes<'a> {
    fn new(root: &'a TrieNode) -> TrieNodes<'a> {
        TrieNodes {
            pending: vec![root],
        }
    }
}

impl<'a> Iterator for TrieNodes<'a> {
    type Item = &'a TrieNode;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.pending.pop()?;
        // Push in reverse byte order so the LIFO walk itself remains canonical. The order is
        // not needed by `max_token_len`, but it keeps Clone and Debug deterministic too.
        self.pending.extend(node.children.values().rev());
        Some(node)
    }
}

impl Clone for TokenTable {
    fn clone(&self) -> TokenTable {
        let mut cloned = TokenTable::new();
        for node in TrieNodes::new(&self.root) {
            if let Some(token) = node.value.as_deref() {
                cloned.insert(token);
            }
        }
        cloned
    }
}

impl PartialEq for TokenTable {
    fn eq(&self, other: &TokenTable) -> bool {
        let mut pending = vec![(&self.root, &other.root)];
        while let Some((left, right)) = pending.pop() {
            if left.value != right.value || left.children.len() != right.children.len() {
                return false;
            }
            for ((left_byte, left_child), (right_byte, right_child)) in
                left.children.iter().zip(&right.children).rev()
            {
                if left_byte != right_byte {
                    return false;
                }
                pending.push((left_child, right_child));
            }
        }
        true
    }
}

impl Eq for TokenTable {}

impl fmt::Debug for TokenTable {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let tokens: Vec<&str> = TrieNodes::new(&self.root)
            .filter_map(|node| node.value.as_deref())
            .collect();
        formatter
            .debug_struct("TokenTable")
            .field("tokens", &tokens)
            .finish()
    }
}

impl Drop for TokenTable {
    fn drop(&mut self) {
        // The compiler-generated drop glue would recurse through one `TrieNode` per byte.
        // Drain every child edge before its node is dropped, leaving only shallow, childless
        // values for ordinary drop glue. Allocation failure remains outside this API's claim.
        let mut pending = Vec::new();
        pending.extend(mem::take(&mut self.root.children).into_values());
        while let Some(mut node) = pending.pop() {
            pending.extend(mem::take(&mut node.children).into_values());
        }
    }
}

impl TokenTable {
    pub fn new() -> TokenTable {
        TokenTable::default()
    }

    /// Build a table from token strings. Later duplicates are harmless — a token is its own
    /// value, so inserting `"fun"` twice cannot mean two different things.
    pub fn from_tokens<I, S>(tokens: I) -> TokenTable
    where
        I: IntoIterator<Item = S>,
        S: AsRef<str>,
    {
        let mut table = TokenTable::new();
        for token in tokens {
            table.insert(token.as_ref());
        }
        table
    }

    /// Insert one token. The empty string is ignored: a zero-length token would match
    /// everywhere and make `isToken`'s length comparison meaningless.
    pub fn insert(&mut self, token: &str) {
        if token.is_empty() {
            return;
        }
        let mut node = &mut self.root;
        for byte in token.as_bytes() {
            node = node.children.entry(*byte).or_default();
        }
        node.value = Some(token.to_string());
    }

    /// The longest token in the table that is a prefix of `text` starting at `from`.
    ///
    /// Upstream `Trie.matchPrefix`: walk as far as the input allows, carrying the last value
    /// seen. Longest match, not first match — `<=>` must win over `<=` over `<`.
    pub fn match_prefix(&self, text: &SourceText, from: BytePos) -> Option<&str> {
        let bytes = text.as_bytes();
        let mut node = &self.root;
        let mut best: Option<&str> = node.value.as_deref();
        let mut at = from.0;
        while at < bytes.len() {
            match node.children.get(&bytes[at]) {
                Some(next) => {
                    node = next;
                    at += 1;
                    if let Some(value) = node.value.as_deref() {
                        best = Some(value);
                    }
                }
                None => break,
            }
        }
        best
    }

    /// The longest token in the table, in bytes.
    ///
    /// This is the lexer's *lookahead bound* for table matching: `match_prefix` walks the trie
    /// as far as it has children, which can be further than the token it finally returns —
    /// with `<`, `<=` and `<==>` in the table, matching at `<==x` reads four bytes and emits
    /// one. An incremental re-lex has to back up by at least this much or an edit inside the
    /// walked-but-not-emitted region can silently change a decision it never revisits.
    /// [`crate::run`] consumes it for exactly that.
    pub fn max_token_len(&self) -> usize {
        TrieNodes::new(&self.root)
            .filter_map(|node| node.value.as_deref())
            .map(str::len)
            .max()
            .unwrap_or(0)
    }

    pub fn contains(&self, token: &str) -> bool {
        let mut node = &self.root;
        for byte in token.as_bytes() {
            match node.children.get(byte) {
                Some(next) => node = next,
                None => return false,
            }
        }
        node.value.is_some()
    }
}

/// What a lexed token is.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    /// A table token — upstream's atom. Keywords are this: a keyword is exactly "a symbol
    /// that also happens to be spellable as an identifier", which is why there is no
    /// separate `Keyword` variant. Inventing one would imply a distinction the pin does not
    /// make, and something downstream would eventually branch on it.
    Symbol(Token),
    /// An identifier, with the structural `Name` its parts spell.
    Ident(Name),
    /// A literal. The form is [`crate::literal`]'s business; the table decides nothing here.
    Literal(LiteralKind),
}

/// One lexed token: what it is and the bytes it occupies (view coordinates).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexedToken {
    pub kind: TokenKind,
    pub extent: ByteSpan,
}

/// Why token lexing refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenError {
    /// Nothing here: at end of input. Upstream `mkEOIError`.
    EndOfInput { at: BytePos },
    /// The bytes here start neither an identifier nor any token in the table. Upstream
    /// `mkTokenAndFixPos`'s `mkErrorAt "token"`.
    NotAToken { at: BytePos },
    /// A `«` with no `»`. Upstream's message, verbatim.
    UnterminatedIdentifierEscape { at: BytePos },
    /// A literal opener was found but the literal is malformed. Wrapped rather than
    /// flattened: a literal's refusals are about the literal's own grammar, and collapsing
    /// them into "not a token" would throw away the position and the message the user needs.
    Literal(LiteralError),
}

impl TokenError {
    /// Upstream's diagnostic text where upstream has one, so ours cannot drift.
    pub fn message(&self) -> &'static str {
        match self {
            TokenError::EndOfInput { .. } => "unexpected end of input",
            TokenError::NotAToken { .. } => "token",
            TokenError::UnterminatedIdentifierEscape { .. } => "unterminated identifier escape",
            TokenError::Literal(error) => error.message(),
        }
    }

    /// The same refusal with its offset moved by `delta` bytes, literal refusals included.
    ///
    /// The nested literal error delegates rather than being flattened here — that is what
    /// makes the delegation exhaustive on both levels. An earlier version of this reasoned
    /// that a reused literal refusal was unreachable and left it unshifted; the incremental
    /// property disagreed, with a char-literal refusal pointing seven bytes past its own
    /// token. The lesson is not that the argument was careless, it is that an argument is not
    /// a substitute for the differential.
    pub fn shifted(&self, delta: isize) -> TokenError {
        let moved = |at: BytePos| BytePos((at.0 as isize + delta).max(0) as usize);
        match self {
            TokenError::EndOfInput { at } => TokenError::EndOfInput { at: moved(*at) },
            TokenError::NotAToken { at } => TokenError::NotAToken { at: moved(*at) },
            TokenError::UnterminatedIdentifierEscape { at } => {
                TokenError::UnterminatedIdentifierEscape { at: moved(*at) }
            }
            TokenError::Literal(error) => TokenError::Literal(error.shifted(delta)),
        }
    }

    pub fn at(&self) -> BytePos {
        match self {
            TokenError::EndOfInput { at }
            | TokenError::NotAToken { at }
            | TokenError::UnterminatedIdentifierEscape { at } => *at,
            TokenError::Literal(error) => error.at(),
        }
    }
}

/// `«` — upstream `idBeginEscape`.
pub const ID_BEGIN_ESCAPE: char = '«';
/// `»` — upstream `idEndEscape`.
pub const ID_END_ESCAPE: char = '»';

/// Upstream `isIdFirst` (`Init/Meta/Defs.lean:120`): ASCII alpha, `_`, or letter-like.
///
/// `Char.isAlpha` upstream is **ASCII only** (`isUpper || isLower`, each a range check on
/// `A-Z`/`a-z`), so every non-ASCII identifier character arrives through `is_letter_like` —
/// not through Rust's `char::is_alphabetic`, which accepts vastly more. Using the Rust
/// predicate here would accept identifiers the Reference rejects, which is a silent
/// widening of the accepted language.
pub fn is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c == '_' || is_letter_like(c)
}

/// Upstream `isIdRest` (`Init/Meta/Defs.lean:133`).
///
/// Note `!` and `?` and `'`: `foo!`, `foo?` and `h'` are each **one identifier**, not an
/// identifier followed by a symbol. This is where a from-scratch lexer usually diverges,
/// because `!` and `?` look like operators everywhere else.
pub fn is_id_rest(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || c == '_'
        || c == '\''
        || c == '!'
        || c == '?'
        || is_letter_like(c)
        || is_subscript_alnum(c)
}

/// Upstream `isLetterLike` (`Init/Meta/Defs.lean:101`), ranges transcribed exactly.
///
/// The exclusions are the interesting part and are not decorative: lower-case lambda
/// (U+03BB) is excluded because `λ` is a *token*, and upper-case Pi (U+03A0) and Sigma
/// (U+03A3) are excluded for the same reason. Include them and `λ x => x` lexes as one
/// identifier named `λ` and nothing works.
pub fn is_letter_like(c: char) -> bool {
    let v = c as u32;
    (0x3b1..=0x3c9).contains(&v) && v != 0x3bb // lower Greek, but not λ
        || (0x391..=0x3A9).contains(&v) && v != 0x3A0 && v != 0x3A3 // upper Greek, but not Π Σ
        || (0x3ca..=0x3fb).contains(&v) // Coptic
        || (0x1f00..=0x1ffe).contains(&v) // polytonic Greek
        || (0x2100..=0x214f).contains(&v) // letter-like block
        || (0x1d49c..=0x1d59f).contains(&v) // script / double-struck / fraktur
        || (0x00c0..=0x00ff).contains(&v) && v != 0x00d7 && v != 0x00f7 // Latin-1, but not × ÷
        || (0x0100..=0x017f).contains(&v) // Latin Extended-A
}

/// Upstream `isSubScriptAlnum` (`Init/Meta/Defs.lean:114`).
pub fn is_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

/// Lex one token at `from`, which must already be past any trivia.
///
/// Follows `tokenFnAux` → `identFnAux` → `mkIdResult` → `isToken`, in that order, because
/// the order *is* the specification: the trie is consulted first but decided last.
pub fn lex_token(
    text: &SourceText,
    table: &TokenTable,
    from: BytePos,
) -> Result<LexedToken, TokenError> {
    let s = text.as_str();
    if from.0 >= s.len() {
        return Err(TokenError::EndOfInput { at: from });
    }
    // Literal openers first, in the pin's own order (`tokenFnAux`). The table is not
    // consulted for them at all: a `"` is a string opener whatever the table says about `"`.
    if literal::starts_literal(text, from) {
        return literal::lex_literal(text, from)
            .map(|lexed| LexedToken {
                kind: TokenKind::Literal(lexed.kind),
                extent: lexed.extent,
            })
            .map_err(TokenError::Literal);
    }

    // Step 1: the trie's longest match, kept aside and NOT acted on yet.
    let tk = table.match_prefix(text, from).map(str::to_string);

    // Step 2: the identifier scan, independent of the trie.
    let scanned = scan_ident(s, from)?;

    // Step 3: `isToken` decides — `≥`, not `>`, see the module docs. A scan that found
    // nothing contributes length 0, so a table match always wins there, which is exactly
    // `mkTokenAndFixPos` on a non-identifier character.
    let scanned_len = scanned.as_ref().map_or(0, |id| id.stop.0 - from.0);
    match (tk.filter(|token| token.len() >= scanned_len), scanned) {
        (Some(token), _) => {
            // `mkTokenAndFixPos`: the extent is the TOKEN's length, not the scan's reach.
            let stop = BytePos(from.0 + token.len());
            Ok(LexedToken {
                kind: TokenKind::Symbol(token),
                extent: span(from, stop),
            })
        }
        (None, Some(id)) => Ok(LexedToken {
            kind: TokenKind::Ident(id.name),
            extent: span(from, id.stop),
        }),
        // Neither an identifier nor a table token: upstream `mkErrorAt "token"`.
        (None, None) => Err(TokenError::NotAToken { at: from }),
    }
}

/// The extent of an identifier starting at `from`, or `Ok(None)` if none does.
///
/// Exposed for [`crate::literal`]'s name literals: `` `foo `` has to spell exactly the name
/// that `foo` would spell as an identifier, and a second scanner is a second thing to drift.
pub fn scan_ident_extent(s: &str, from: BytePos) -> Result<Option<BytePos>, TokenError> {
    Ok(scan_ident(s, from)?.map(|id| id.stop))
}

/// An identifier scan's result: the name its parts spell, and where it stopped.
struct ScannedIdent {
    name: Name,
    stop: BytePos,
}

/// Upstream `identFnAux`: dot-separated parts, each bare or `«escaped»`.
///
/// `Ok(None)` means "no identifier starts here" — a symbol position, which is not an error
/// on its own because the trie may well have a token for it.
fn scan_ident(s: &str, from: BytePos) -> Result<Option<ScannedIdent>, TokenError> {
    let mut name = Name::anonymous();
    let mut at = from.0;
    let mut any = false;
    loop {
        if at >= s.len() {
            break;
        }
        let c = char_at(s, at);
        if c == ID_BEGIN_ESCAPE {
            let part_start = at + c.len_utf8();
            let Some(end_off) = s[part_start..].find(ID_END_ESCAPE) else {
                return Err(TokenError::UnterminatedIdentifierEscape {
                    at: BytePos(part_start),
                });
            };
            let part_stop = part_start + end_off;
            name = Name::str(name, &s[part_start..part_stop]);
            at = part_stop + ID_END_ESCAPE.len_utf8();
            any = true;
        } else if is_id_first(c) {
            let part_start = at;
            at += c.len_utf8();
            while at < s.len() {
                let c = char_at(s, at);
                if is_id_rest(c) {
                    at += c.len_utf8();
                } else {
                    break;
                }
            }
            name = Name::str(name, &s[part_start..at]);
            any = true;
        } else {
            break;
        }
        // Upstream `isIdCont`: a `.` continues the name only when what FOLLOWS it could
        // begin a part. That is why `foo.1` is the identifier `foo` and then `.` — the
        // projection syntax depends on this exact lookahead.
        if !is_id_cont(s, at) {
            break;
        }
        at += 1; // the '.'
    }
    if any {
        Ok(Some(ScannedIdent {
            name,
            stop: BytePos(at),
        }))
    } else {
        Ok(None)
    }
}

/// Upstream `isIdCont` (`Basic.lean:921`).
fn is_id_cont(s: &str, at: usize) -> bool {
    if at >= s.len() || s.as_bytes()[at] != b'.' {
        return false;
    }
    match char_after(s, at) {
        Some(c) => is_id_first(c) || c == ID_BEGIN_ESCAPE,
        None => false,
    }
}

/// The char starting at `at`, which must be a char boundary inside `s`.
///
/// Total by construction: every caller reaches `at` by stepping whole scalars from a
/// boundary, and a `SourceText` is valid UTF-8 by its own constructor. `'\0'` on a
/// malformed offset is not a silent repair of the input — it cannot describe any real byte
/// here — and it keeps a lexer bug from becoming a panic on user source.
fn char_at(s: &str, at: usize) -> char {
    s[at..].chars().next().unwrap_or('\0')
}

fn char_after(s: &str, at: usize) -> Option<char> {
    s[at..].chars().nth(1)
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

    /// A table shaped like a real one: keywords that are identifier-spellable, symbols that
    /// are not, and three tokens sharing a prefix so maximal munch has something to do.
    fn table() -> TokenTable {
        TokenTable::from_tokens([
            "theorem", "def", "fun", "in", "at", "Type", "λ", "→", "<", "<=", "<=>", ".", "..",
            "(", ")",
        ])
    }

    fn lex(raw: &str) -> Result<LexedToken, TokenError> {
        let text = text_of(raw);
        lex_token(&text, &table(), BytePos(0))
    }

    /// A one-line classification of what the lexer made of `raw`.
    ///
    /// Deliberately a value rather than a `match` with a failing arm: the interesting
    /// failures here are *misclassifications*, and comparing strings shows both what was
    /// expected and what actually happened, in the assertion, instead of a panic inside a
    /// helper. It also lets one helper cover symbols, identifiers and refusals uniformly.
    fn classify(raw: &str) -> String {
        classify_with(&table(), raw)
    }

    fn classify_with(table: &TokenTable, raw: &str) -> String {
        match lex_token(&text_of(raw), table, BytePos(0)) {
            Ok(LexedToken {
                kind: TokenKind::Ident(name),
                ..
            }) => format!("ident {}", name.to_display_string()),
            Ok(LexedToken {
                kind: TokenKind::Symbol(token),
                ..
            }) => format!("symbol {token}"),
            Ok(LexedToken {
                kind: TokenKind::Literal(kind),
                ..
            }) => format!("literal {kind:?}"),
            Err(error) => format!("error {error:?}"),
        }
    }

    /// How many bytes the token occupies, or `None` if it did not lex.
    fn extent_bytes(raw: &str) -> Option<usize> {
        lex(raw).ok().map(|lexed| lexed.extent.len_bytes())
    }

    /// **The keyword rule, both directions.** `isToken` compares with `≥`, and each
    /// direction of that comparison is a different bug when it is wrong.
    ///
    /// Written `>`: every exact keyword becomes an identifier (first block below).
    /// Consulting the trie first and committing: every keyword-prefixed identifier gets
    /// split (second block). Both are silent — the language still parses a great deal of
    /// code, incorrectly — which is why both are asserted rather than one.
    #[test]
    fn a_keyword_is_a_symbol_but_a_keyword_prefix_is_not() {
        // Exact match: identifier scan length == token length, and `≥` makes it a symbol.
        assert_eq!(classify("theorem"), "symbol theorem");
        assert_eq!(classify("def"), "symbol def");
        assert_eq!(classify("in"), "symbol in");
        assert_eq!(classify("Type"), "symbol Type");

        // Keyword followed by more identifier: the scan outruns the trie, so it is ONE
        // identifier. `int` is not `in` + `t`.
        assert_eq!(classify("int"), "ident int");
        assert_eq!(classify("theorems"), "ident theorems");
        assert_eq!(classify("defn"), "ident defn");
        assert_eq!(classify("atom"), "ident atom");
        assert_eq!(classify("Types"), "ident Types");

        // And the extent of a symbol comes from the TABLE, not from how far the identifier
        // probe reached — `mkTokenAndFixPos`.
        assert_eq!(extent_bytes("theorem"), Some("theorem".len()));
    }

    /// Maximal munch over the table, which is the only place the trie decides anything.
    #[test]
    fn the_table_matches_the_longest_token_not_the_first() {
        assert_eq!(classify("<=>"), "symbol <=>");
        assert_eq!(classify("<=x"), "symbol <=");
        assert_eq!(classify("<x"), "symbol <");
        assert_eq!(classify(".."), "symbol ..");
        assert_eq!(classify(".x"), "symbol .");
        // A multi-byte symbol's extent is in bytes, not chars.
        assert_eq!(extent_bytes("→"), Some(3));
    }

    /// The identifier alphabet, transcribed from the pin rather than guessed. Each of these
    /// is a case a from-scratch lexer typically gets wrong in the same direction: treating
    /// the trailing character as an operator.
    #[test]
    fn bang_question_and_prime_are_identifier_characters() {
        assert_eq!(classify("foo!"), "ident foo!");
        assert_eq!(classify("foo?"), "ident foo?");
        assert_eq!(classify("h'"), "ident h'");
        assert_eq!(classify("h₁"), "ident h₁"); // subscript is id-rest
        assert_eq!(classify("_x"), "ident _x");
        assert_eq!(classify("α"), "ident α"); // letter-like: lower Greek
    }

    /// The letter-like exclusions. λ, Π and Σ are excluded from the identifier alphabet on
    /// purpose: they are tokens. If they were identifier characters, `λ x => x` would lex as
    /// a single identifier and the language would not work at all.
    #[test]
    fn lambda_pi_and_sigma_are_not_identifier_characters() {
        assert!(!is_letter_like('λ'), "λ must not be letter-like");
        assert!(!is_letter_like('Π'), "Π must not be letter-like");
        assert!(!is_letter_like('Σ'), "Σ must not be letter-like");
        // Their neighbours in the same ranges ARE, so the exclusion is surgical and the
        // ranges themselves are not simply missing.
        assert!(is_letter_like('κ') && is_letter_like('μ'), "λ's neighbours");
        assert!(is_letter_like('Ο') && is_letter_like('Ρ'), "Π's neighbours");
        // And λ is a symbol here because the table says so, not because the lexer knows it.
        assert_eq!(classify("λ"), "symbol λ");

        // × and ÷ sit inside the Latin-1 range and are excluded for the same reason.
        assert!(!is_letter_like('×') && !is_letter_like('÷'));
        assert!(is_letter_like('Ø') && is_letter_like('é'));
    }

    /// Dotted names, and the lookahead that makes `foo.1` work.
    #[test]
    fn a_dot_continues_a_name_only_when_what_follows_could_start_a_part() {
        assert_eq!(classify("Nat.succ.foo"), "ident Nat.succ.foo");

        // `foo.1`: the `.` is NOT part of the name, because `1` cannot begin a part. The
        // identifier stops at 3 bytes and the `.` is the next token's problem.
        assert_eq!(classify("foo.1"), "ident foo");
        assert_eq!(extent_bytes("foo.1"), Some(3));

        // A trailing dot at end of input likewise does not continue.
        assert_eq!(classify("foo."), "ident foo");
        assert_eq!(extent_bytes("foo."), Some(3));
    }

    /// Escaped identifiers: the guillemets are delimiters, not part of the component, and
    /// an escape can hold characters the bare alphabet forbids — which is what it is for.
    #[test]
    fn escaped_identifiers_carry_their_contents_verbatim() {
        assert_eq!(classify("«hello world»"), "ident hello world");
        assert_eq!(classify("«a.b»"), "ident a.b");
        assert_eq!(classify("«theorem»"), "ident theorem");
        // Mixed parts, and the extent covers the guillemets even though the name does not.
        assert_eq!(classify("Nat.«odd one»"), "ident Nat.odd one");
        assert_eq!(
            extent_bytes("Nat.«odd one»"),
            Some("Nat.«odd one»".len()),
            "the extent covers the guillemets the name omits"
        );
    }

    /// `«theorem»` is an identifier even though `theorem` is a keyword — that is the entire
    /// purpose of the escape. Asserted next to the bare form so the pair reads as the
    /// contrast it is.
    #[test]
    fn an_escape_defeats_the_keyword_rule() {
        assert_eq!(classify("theorem"), "symbol theorem");
        assert_eq!(classify("«theorem»"), "ident theorem");
    }

    /// Refusals are typed and total: nothing here panics, and nothing here quietly
    /// classifies input it does not understand.
    #[test]
    fn refusals_are_typed_and_name_their_offset() {
        assert_eq!(
            lex(""),
            Err(TokenError::EndOfInput { at: BytePos(0) }),
            "end of input"
        );
        assert_eq!(
            lex("«unterminated"),
            Err(TokenError::UnterminatedIdentifierEscape { at: BytePos(2) }),
            "the offset is the start of the part, as upstream reports it"
        );
        assert_eq!(
            TokenError::UnterminatedIdentifierEscape { at: BytePos(0) }.message(),
            "unterminated identifier escape",
            "the pin's wording"
        );
        // A byte that is neither an identifier start nor in the table.
        assert_eq!(lex("#"), Err(TokenError::NotAToken { at: BytePos(0) }));
        // Literals reach the literal grammar rather than the table, and their refusals keep
        // their own message and position.
        assert_eq!(classify("\"abc\""), "literal Str");
        assert_eq!(classify("42"), "literal Nat");
        assert_eq!(classify("'a'"), "literal Char");
        assert_eq!(classify("`foo"), "literal Name");
        assert_eq!(classify("1.5"), "literal Scientific");
        assert!(
            matches!(lex("\"abc"), Err(TokenError::Literal(_))),
            "an unterminated string is a literal refusal, not a token refusal"
        );
    }

    /// An empty table is a real configuration (no imports yet), and every identifier must
    /// still lex — the identifier alphabet does not come from the table.
    #[test]
    fn with_an_empty_table_identifiers_still_lex_and_symbols_do_not() {
        let empty = TokenTable::new();
        assert_eq!(
            classify_with(&empty, "theorem"),
            "ident theorem",
            "without a table, `theorem` is just a name"
        );
        // And a symbol with nothing to match it is refused rather than invented.
        let text = text_of("→");
        assert_eq!(
            lex_token(&text, &empty, BytePos(0)),
            Err(TokenError::NotAToken { at: BytePos(0) })
        );
    }

    /// The table itself: insertion, membership, and the empty-token guard. A zero-length
    /// token would match at every position and make `isToken`'s comparison vacuous.
    #[test]
    fn the_table_refuses_an_empty_token() {
        let mut t = TokenTable::new();
        t.insert("");
        assert!(!t.contains(""), "an empty token would match everywhere");
        let text = text_of("x");
        assert_eq!(t.match_prefix(&text, BytePos(0)), None);

        t.insert("fun");
        assert!(t.contains("fun"));
        assert!(!t.contains("fu"), "a prefix of a token is not a token");
        assert!(!t.contains("funny"));
    }

    /// Lexing starts wherever it is told, not only at zero, and multi-byte scalars before
    /// the start offset must not shift anything.
    #[test]
    fn lexing_is_positional_and_survives_multibyte_prefixes() {
        let text = text_of("α → theorem");
        let table = table();
        // `α` is 2 bytes, `→` is 3.
        let arrow = lex_token(&text, &table, BytePos(3)).expect("lexes");
        assert_eq!(arrow.kind, TokenKind::Symbol("→".to_string()));
        assert_eq!(arrow.extent.start(), BytePos(3));
        assert_eq!(arrow.extent.end(), BytePos(6));

        let kw = lex_token(&text, &table, BytePos(7)).expect("lexes");
        assert_eq!(kw.kind, TokenKind::Symbol("theorem".to_string()));
        assert_eq!(kw.extent.end(), BytePos(14));
    }
}
