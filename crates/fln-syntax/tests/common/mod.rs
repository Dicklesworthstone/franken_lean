//! Shared fixtures for the lexer property suites (bead franken_lean-81oq).
//!
//! Deterministic by construction. There is no external property-testing crate here and there
//! never will be — the dependency universe is closed (D1) — so randomness is a seeded
//! splitmix64 and every failure is replayable from the seed printed in the assertion. That is
//! not a limitation to work around: a fuzz failure nobody can reproduce is a rumour.

#![forbid(unsafe_code)]
#![allow(dead_code)] // each suite uses a different subset

use fln_syntax::source::{BytePos, ByteSpan, SourceText};
use fln_syntax::token::TokenTable;

/// splitmix64. Chosen because it is eight lines, has no state beyond a `u64`, and passes the
/// statistical bar for choosing test inputs — which is the only bar that applies here.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed)
    }

    pub fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    /// A value in `0..n`, or 0 when `n` is 0.
    pub fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            0
        } else {
            (self.next_u64() % n as u64) as usize
        }
    }

    pub fn pick<'a, T>(&mut self, items: &'a [T]) -> &'a T {
        &items[self.below(items.len())]
    }
}

/// A table shaped like a real one, and deliberately containing tokens that share prefixes so
/// the trie's lookahead runs past what it emits — `<`, `<=`, `<==>` is the shape that breaks a
/// naive incremental restart rule.
pub fn table() -> TokenTable {
    TokenTable::from_tokens([
        "def", "theorem", "fun", "in", "at", "Type", "λ", "→", ":=", "=>", "(", ")", "{", "}", "[",
        "]", ",", ";", ".", "..", "<", "<=", "<==>", "+", "-", "*", "/", "/--", "/-!",
    ])
}

/// Fragments a generator can paste in. Weighted toward the bytes where lexing decisions live
/// rather than toward plausible-looking Lean, because a generator that mostly produces valid
/// programs mostly tests the easy path.
pub const FRAGMENTS: &[&str] = &[
    "",
    " ",
    "\n",
    "\t",
    "\r",
    "\r\n",
    "-",
    "--",
    "/-",
    "-/",
    "/--",
    "/-!",
    "\"",
    "\\",
    "'",
    "`",
    "#",
    "r",
    "r#",
    "r#\"",
    "«",
    "»",
    "0",
    "1",
    "9",
    ".",
    "..",
    "_",
    "e",
    "x",
    "b",
    "o",
    "<",
    "=",
    ">",
    "λ",
    "α",
    "→",
    "😀",
    "def ",
    "theorem ",
    "fun x => x",
    "in",
    "int",
    "1..5",
    "0x1F",
    "1_000",
    "1e-3",
    "\"a\\nb\"",
    "'c'",
    "`Nat.succ",
    "r#\"a\"#",
    "«odd»",
    "-- c\n",
    "/- a /- b -/ -/",
    "/-- d -/",
    "foo!",
    "h'",
    "x₁",
];

/// Realistic base texts for edit sequences, including ones that are already ill-formed —
/// incremental lexing has to agree with a full re-lex on broken input too, and broken input is
/// what an editor spends most of its time holding.
pub const BASES: &[&str] = &[
    "def f := fun x => x + 1\ntheorem t : f 1 = 2 := rfl\n",
    "-- a leading comment\ndef g := 0x1F\n/- block\n   comment -/\ndef h := \"text\"\n",
    "def a := 1..5\ndef b := 1.5e-3\ndef c := `Nat.succ\ndef d := r#\"raw \"quoted\" raw\"#\n",
    "def «odd name» := λ x => x\ndef unicode := α → β\ndef bang := foo!\n",
    "def broken := \"unterminated\ndef after := 1\n",
    "/- unterminated block comment\ndef never := 0\n",
    "def tabbed :=\tvalue\ndef next := 1\n",
    "x",
    "",
];

/// A byte offset in `text` at or before `at` that sits on a char boundary.
pub fn boundary_at_or_before(text: &SourceText, at: usize) -> usize {
    let s = text.as_str();
    let mut at = at.min(s.len());
    while at > 0 && !s.is_char_boundary(at) {
        at -= 1;
    }
    at
}

/// A random span of `text`, on char boundaries.
pub fn random_span(rng: &mut Rng, text: &SourceText) -> ByteSpan {
    let len = text.len_bytes();
    let a = boundary_at_or_before(text, rng.below(len + 1));
    let b = boundary_at_or_before(text, a + rng.below(len - a + 1));
    ByteSpan::new(BytePos(a), BytePos(b)).expect("a <= b by construction")
}

/// A random insertion built from one to three fragments.
pub fn random_insert(rng: &mut Rng) -> String {
    let count = 1 + rng.below(3);
    let mut out = String::new();
    for _ in 0..count {
        out.push_str(rng.pick(FRAGMENTS));
    }
    out
}

pub fn text_of(raw: &str) -> SourceText {
    SourceText::from_utf8(raw.as_bytes()).expect("fixture is valid UTF-8")
}
