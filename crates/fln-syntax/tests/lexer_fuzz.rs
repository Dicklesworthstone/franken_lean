//! `lexer_fuzz` — invariants that must hold for *every* input, checked over a large seeded
//! corpus (bead franken_lean-81oq).
//!
//! ## What a fuzz suite is for here
//!
//! Not "does the lexer produce the right tokens" — that is the unit and pin-fidelity suites'
//! job, and a fuzzer has no oracle for it. This suite checks the properties that must hold
//! whatever the bytes are, and each one corresponds to a way the lexer could take down
//! something downstream:
//!
//! * **Totality.** Every input gets a typed answer. A panic here is an FL-INV-07 violation:
//!   malformed source must not panic (doctrine §8), because a panic is an invariant failure
//!   and never a user diagnostic. The harness turns any panic into a failure, so totality is
//!   checked simply by running.
//! * **Progress.** No token has zero width. A zero-width token makes every driving loop spin
//!   forever, so this is the difference between a diagnostic and a hung editor.
//! * **Extents inside the text, on scalar boundaries.** A span that splits a scalar makes
//!   every `&text[span]` downstream panic — which converts a lexer bug into a crash in
//!   whatever slices it.
//! * **Diagnostic offsets inside the text.** A diagnostic pointing past the end crashes the
//!   renderer, not the lexer.
//! * **Coverage.** Every byte belongs to exactly one event, in order, with no hole and no
//!   overlap. Incremental re-lexing realigns on event starts, so a hole is not cosmetic — it
//!   is what makes the incremental path unsound.
//! * **The recovery law**, over thousands of inputs rather than the twenty hand-written ones
//!   the differential in `crate::recover` uses.
//! * **Invalid UTF-8 is a typed rejection**, never a panic and never a repair.
//!
//! Randomness is a seeded splitmix64 (see `common`), because the dependency universe is closed
//! (D1) — and because a fuzz failure nobody can reproduce is a rumour. Every assertion prints
//! the seed and the input.

#![forbid(unsafe_code)]

mod common;

use common::{FRAGMENTS, Rng, table};
use fln_syntax::recover::{lex, lex_recovering};
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::SourceText;
use fln_syntax::token::TokenTable;

/// Build an input by pasting together fragments chosen from the lexically interesting set.
fn generate(rng: &mut Rng) -> String {
    let pieces = 1 + rng.below(12);
    let mut out = String::new();
    for _ in 0..pieces {
        out.push_str(rng.pick(FRAGMENTS));
    }
    out
}

/// Every structural violation in one run, as messages — empty when the run is well formed.
///
/// Returned rather than asserted so the checker itself can be tested against deliberately
/// corrupted runs. A fuzz suite whose checker is never shown to reject anything is indisputably
/// green and possibly vacuous, which is the failure mode this whole bead keeps running into in
/// new places.
fn violations(run: &fln_syntax::run::LexRun, text: &SourceText) -> Vec<String> {
    let mut found = Vec::new();
    let end = text.len_bytes();
    let mut at = 0usize;
    for (index, event) in run.events.iter().enumerate() {
        let extent = event.extent();
        if extent.start().0 != at {
            found.push(format!(
                "event {index} starts at {} but the previous ended at {at}",
                extent.start().0
            ));
        }
        if extent.end().0 < extent.start().0 {
            found.push(format!("event {index} runs backwards"));
        }
        if extent.end().0 > end {
            found.push(format!(
                "event {index} ends at {} past the text end {end}",
                extent.end().0
            ));
        }
        // Scalar boundaries: a span that splits a scalar panics whatever slices it.
        if !text.as_str().is_char_boundary(extent.start().0.min(end))
            || !text.as_str().is_char_boundary(extent.end().0.min(end))
        {
            found.push(format!("event {index} is not on scalar boundaries"));
        }
        // Progress: a zero-width token spins any driver forever.
        if let Event::Token(token) = event
            && token.extent.len_bytes() == 0
        {
            found.push(format!("zero-width token at {}", token.extent.start().0));
        }
        at = extent.end().0;
    }
    if at != end {
        found.push(format!("run covered {at} of {end} bytes"));
    }
    for (message, offset) in run.diagnostics() {
        if offset.0 > end {
            found.push(format!(
                "diagnostic {message:?} points at {} past the end {end}",
                offset.0
            ));
        }
        if message.is_empty() {
            found.push("an empty diagnostic message".to_string());
        }
    }
    found
}

/// Every invariant that must hold for one input.
fn check_invariants(table: &TokenTable, raw: &str, context: &str) {
    let text = SourceText::from_utf8(raw.as_bytes()).expect("generated inputs are valid UTF-8");
    let run = lex_run(&text, table);

    let found = violations(&run, &text);
    assert!(
        found.is_empty(),
        "{context}: {} structural violation(s)\n  input={raw:?}\n  {}",
        found.len(),
        found.join("\n  ")
    );

    // The recovery law, on this input: recovery may not change acceptance in either
    // direction. The same property the hand-written differential establishes, here over
    // arbitrary bytes.
    assert_eq!(
        lex(&text).accepted(),
        lex_recovering(&text).accepted(),
        "{context}: recovery changed acceptance\n  input={raw:?}"
    );
}

/// The main sweep. Every invariant, over a large generated corpus.
#[test]
fn every_invariant_holds_over_a_generated_corpus() {
    let table = table();
    let mut inputs = 0usize;
    for seed in 0..20_000u64 {
        let mut rng = Rng::new(seed);
        let raw = generate(&mut rng);
        check_invariants(&table, &raw, &format!("seed={seed}"));
        inputs += 1;
    }
    assert!(inputs >= 20_000, "only {inputs} inputs were generated");
}

/// The same invariants with an **empty** table, which is a real configuration — a file lexed
/// before any syntax is imported. Symbols become refusals, so this exercises the recovery and
/// coverage paths far more heavily than the populated table does.
#[test]
fn every_invariant_holds_with_no_tokens_declared() {
    let empty = TokenTable::new();
    for seed in 0..5_000u64 {
        let mut rng = Rng::new(seed ^ 0xDEAD_BEEF);
        let raw = generate(&mut rng);
        check_invariants(&empty, &raw, &format!("empty-table seed={seed}"));
    }
}

/// Long single-character runs: the shapes that find quadratic behaviour and off-by-one
/// boundary handling, and that a fragment-paste generator produces only by accident.
#[test]
fn long_uniform_runs_are_lexed_without_incident() {
    let table = table();
    for unit in [
        "#", "\"", "'", "«", "»", "\\", "-", "/", ".", "0", "x", "_", "\t", "\r", "\n", "r", "😀",
        "λ",
    ] {
        for count in [1usize, 2, 3, 7, 64, 500] {
            let raw = unit.repeat(count);
            check_invariants(&table, &raw, &format!("{unit:?} x{count}"));
        }
    }
}

/// Arbitrary **bytes**, not arbitrary text: invalid UTF-8 must be a typed rejection.
///
/// This is the one boundary where the lexer is not even reached, and it is worth fuzzing
/// separately because the failure mode is different in kind — a panic in decoding is reached
/// by every caller that reads a file, before any lexing decision exists to be wrong. The
/// contract is also that it must not *repair*: a decoder that replaced bad bytes with U+FFFD
/// would silently change the program, and lossless is the one thing the source layer promises.
#[test]
fn arbitrary_bytes_get_a_typed_answer_and_are_never_repaired() {
    let mut rejected = 0usize;
    let mut accepted = 0usize;
    for seed in 0..20_000u64 {
        let mut rng = Rng::new(seed.wrapping_mul(0x2545_F491_4F6C_DD1D));
        let len = rng.below(24);
        let bytes: Vec<u8> = (0..len).map(|_| (rng.next_u64() & 0xFF) as u8).collect();
        match SourceText::from_utf8(&bytes) {
            Ok(text) => {
                accepted += 1;
                // Valid UTF-8 after all: it must round-trip byte-exactly, unrepaired.
                assert_eq!(
                    text.as_bytes(),
                    bytes.as_slice(),
                    "seed={seed}: decoding altered the bytes"
                );
                let run = lex_run(&text, &table());
                let covered = run.events.last().map_or(0, |event| event.extent().end().0);
                assert_eq!(
                    covered,
                    text.len_bytes(),
                    "seed={seed}: incomplete coverage"
                );
            }
            Err(error) => {
                rejected += 1;
                // The refusal names the first bad offset, and it is inside the input.
                let fln_syntax::source::SourceError::NotUtf8 { at } = error;
                assert!(
                    at.0 <= bytes.len(),
                    "seed={seed}: refusal points at {} past the input length {}",
                    at.0,
                    bytes.len()
                );
            }
        }
    }
    // Both outcomes must occur, or one of the two paths above is never exercised — the same
    // anti-vacuity discipline the recovery corpus needs.
    assert!(accepted > 0, "no generated byte string was valid UTF-8");
    assert!(rejected > 0, "no generated byte string was invalid UTF-8");
}

/// **The checker can fail.** Each corrupted run below violates exactly one invariant, and the
/// checker must catch each — otherwise the twenty-five thousand inputs above prove nothing.
#[test]
fn the_invariant_checker_rejects_a_corrupted_run() {
    use fln_syntax::run::LexRun;
    use fln_syntax::source::{BytePos, ByteSpan};
    use fln_syntax::token::{LexedToken, TokenKind};

    let text = SourceText::from_utf8("ab".as_bytes()).expect("valid");
    let span = |a: usize, b: usize| ByteSpan::new(BytePos(a), BytePos(b)).expect("forward span");
    let token = |a: usize, b: usize| {
        Event::Token(LexedToken {
            kind: TokenKind::Symbol("x".to_string()),
            extent: span(a, b),
        })
    };

    // A well-formed run, to show the checker accepts something — a rejector that rejects
    // everything would pass every case below and be useless.
    let good = LexRun {
        events: vec![Event::Trivia(span(0, 0)), token(0, 2)],
    };
    assert!(
        violations(&good, &text).is_empty(),
        "the checker must accept a well-formed run: {:?}",
        violations(&good, &text)
    );

    // A hole: nothing covers byte 0.
    let hole = LexRun {
        events: vec![Event::Trivia(span(1, 1)), token(1, 2)],
    };
    assert!(
        !violations(&hole, &text).is_empty(),
        "a hole in the coverage must be caught"
    );

    // An overlap: two events claim byte 1.
    let overlap = LexRun {
        events: vec![Event::Trivia(span(0, 0)), token(0, 2), token(1, 2)],
    };
    assert!(
        !violations(&overlap, &text).is_empty(),
        "an overlap must be caught"
    );

    // A zero-width token: the shape that spins a driver forever.
    let zero = LexRun {
        events: vec![Event::Trivia(span(0, 0)), token(0, 0), token(0, 2)],
    };
    assert!(
        violations(&zero, &text)
            .iter()
            .any(|message| message.contains("zero-width")),
        "a zero-width token must be caught by name"
    );

    // Past the end.
    let over = LexRun {
        events: vec![Event::Trivia(span(0, 0)), token(0, 9)],
    };
    assert!(
        !violations(&over, &text).is_empty(),
        "an extent past the end must be caught"
    );

    // Short: the run stops before the text does.
    let short = LexRun {
        events: vec![Event::Trivia(span(0, 0)), token(0, 1)],
    };
    assert!(
        violations(&short, &text)
            .iter()
            .any(|message| message.contains("covered")),
        "a run that stops short must be caught"
    );

    // A span that splits a multi-byte scalar.
    let astral = SourceText::from_utf8("\u{1F600}".as_bytes()).expect("valid");
    let split = LexRun {
        events: vec![Event::Trivia(span(0, 0)), token(0, 2), token(2, 4)],
    };
    assert!(
        violations(&split, &astral)
            .iter()
            .any(|message| message.contains("scalar boundaries")),
        "a span splitting a scalar must be caught by name"
    );
}
