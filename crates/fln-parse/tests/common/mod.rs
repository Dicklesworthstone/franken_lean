//! Shared fixtures for the parser property suites (bead fln-ffam).
//!
//! The seeded-generator shape is reused from `fln-syntax`'s lexer suites rather than reinvented:
//! same splitmix64, same "print the seed in every assertion" discipline. D1 closes the dependency
//! universe, so there is no property-testing crate to reach for and there never will be — and the
//! constraint is the right one anyway, because a fuzz failure nobody can reproduce is a rumour.

#![forbid(unsafe_code)]
#![cfg(test)]
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

/// The complete member tree equals its standalone parse in group coordinates.
/// The caller supplies the known normalized prefix length independently of the
/// mutual parser. Keep every position, trivia span and raw identifier range.
pub fn assert_member_in_group(
    member: &fln_syntax::tree::Syntax,
    standalone: &[u8],
    normalized_offset: usize,
) {
    use fln_syntax::source::SourceInfo;
    use fln_syntax::tree::Syntax;

    fn coordinates(info: SourceInfo) -> (u8, bool, Vec<usize>) {
        match info {
            SourceInfo::None => (0, false, vec![]),
            SourceInfo::Original {
                leading,
                pos,
                trailing,
                end_pos,
            } => (
                1,
                false,
                vec![
                    leading.start().0,
                    leading.end().0,
                    pos.0,
                    trailing.start().0,
                    trailing.end().0,
                    end_pos.0,
                ],
            ),
            SourceInfo::Synthetic {
                pos,
                end_pos,
                canonical,
            } => (2, canonical, vec![pos.0, end_pos.0]),
        }
    }

    let parsed = fln_parse::parse_definition(standalone).unwrap();
    let mut pending = vec![(member, parsed.syntax())];
    while let Some((actual, expected)) = pending.pop() {
        let (actual_kind, actual_canonical, actual_positions) = coordinates(actual.info());
        let (expected_kind, expected_canonical, expected_positions) = coordinates(expected.info());
        assert_eq!(
            (actual_kind, actual_canonical),
            (expected_kind, expected_canonical)
        );
        assert_eq!(actual_positions.len(), expected_positions.len());
        for (actual, expected) in actual_positions.iter().zip(expected_positions) {
            assert_eq!(*actual, expected + normalized_offset);
        }
        match (actual, expected) {
            (Syntax::Missing, Syntax::Missing) => {}
            (
                Syntax::Node {
                    kind: a, args: aa, ..
                },
                Syntax::Node {
                    kind: b, args: ba, ..
                },
            ) => {
                assert_eq!(a, b);
                assert_eq!(aa.len(), ba.len());
                pending.extend(aa.iter().zip(ba));
            }
            (Syntax::Atom { val: a, .. }, Syntax::Atom { val: b, .. }) => assert_eq!(a, b),
            (
                Syntax::Ident {
                    raw_val: ar,
                    val: a,
                    preresolved: ap,
                    ..
                },
                Syntax::Ident {
                    raw_val: br,
                    val: b,
                    preresolved: bp,
                    ..
                },
            ) => {
                assert_eq!((a, ap), (b, bp));
                assert_eq!(ar.start().0, br.start().0 + normalized_offset);
                assert_eq!(ar.end().0, br.end().0 + normalized_offset);
            }
            _ => panic!("member and standalone syntax shapes differ: {actual:?} / {expected:?}"),
        }
    }
}
