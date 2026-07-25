//! Shared fixtures for the parser property suites (bead fln-ffam).
//!
//! The seeded-generator shape is reused from `fln-syntax`'s lexer suites rather than reinvented:
//! same splitmix64, same "print the seed in every assertion" discipline. D1 closes the dependency
//! universe, so there is no property-testing crate to reach for and there never will be — and the
//! constraint is the right one anyway, because a fuzz failure nobody can reproduce is a rumour.

#![forbid(unsafe_code)]
#![allow(dead_code)] // each suite uses a different subset

use fln_syntax::source::SourceText;
use fln_syntax::token::TokenTable;

/// splitmix64, identical to the lexer suites'.
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

/// A table with the tokens the generator emits, plus prefix-sharing ones so the trie has work.
pub fn table() -> TokenTable {
    TokenTable::from_tokens([
        "def", "theorem", "fun", "=>", ":=", "+", "-", "*", "^", "=", "<", "<=", "(", ")", "{",
        "}", ",", ";", "λ", "→", "/--", "/-!",
    ])
}

/// Fragments weighted toward the places construction and attachment can go wrong: line endings of
/// every kind, comments, literals, unicode, and the trivia boundaries that decide ownership.
pub const FRAGMENTS: &[&str] = &[
    "def ",
    "theorem ",
    "fun x => x",
    " := ",
    " + ",
    " * ",
    " ^ ",
    " = ",
    "( ",
    " )",
    "x",
    "y",
    "Nat.succ",
    "«odd name»",
    "foo!",
    "h'",
    "x₁",
    "0",
    "1",
    "42",
    "0x1F",
    "1_000",
    "1.5e-3",
    "\"str\"",
    "'c'",
    "`n",
    "r#\"raw\"#",
    " ",
    "  ",
    "\n",
    "\r\n",
    "\t",
    "-- c\n",
    "-- c\r\n",
    "/- b -/",
    "/- a /- n -/ -/",
    "/-- d -/",
    "α",
    "→",
    "λ",
    "😀",
    "",
];

/// A generated source text, and the raw string it came from.
pub fn generate(rng: &mut Rng) -> String {
    let pieces = 1 + rng.below(14);
    let mut out = String::new();
    for _ in 0..pieces {
        out.push_str(rng.pick(FRAGMENTS));
    }
    out
}

pub fn text_of(raw: &str) -> Option<SourceText> {
    SourceText::from_utf8(raw.as_bytes()).ok()
}
