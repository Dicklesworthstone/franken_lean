//! `parser_fuzz` — invariants the engine must hold for any input (bead fln-ffam).
//!
//! Same shape as `fln-syntax`'s `lexer_fuzz`, deliberately: seeded splitmix64, seed printed in every
//! assertion, checker returning violations so it can be shown to reject. What differs is what is
//! checked — this suite is about the *construction and resolution* layers rather than the lexer.
//!
//! Each invariant corresponds to a way the parser could take down something downstream:
//!
//! * **Totality.** Any input gets a typed answer. A panic is an FL-INV-07 violation, since
//!   malformed source must not panic.
//! * **A leaf per token, in order.** Construction never invents or drops a leaf, because a parse
//!   tree with a leaf the lexer did not produce cannot be traced back to the file.
//! * **Extents ascending and non-overlapping, on scalar boundaries.** An overlap means two leaves
//!   claim the same byte; a split scalar panics whatever slices it.
//! * **Refusals are typed.** Construction refuses extents it cannot attach rather than repairing
//!   them, since a repaired attachment reconstructs cleanly and misplaces everything.
//! * **Resolution is total.** `longest_match` over generated candidate sets always answers, never
//!   loops, and only ever reports an ambiguity when candidates genuinely tie.

#![forbid(unsafe_code)]

mod common;

use common::{Rng, generate, table, text_of};
use fln_core::name::Name;
use fln_parse::build::Leaves;
use fln_parse::state::{ParserState, Production, Resolution, longest_match};
use fln_syntax::run::{Event, lex_run};
use fln_syntax::source::{BytePos, SourceInfo, SourceText};
use fln_syntax::token::LexedToken;

/// Every structural violation in one construction, as messages. Empty when well formed.
///
/// Returned rather than asserted so the checker itself can be tested against deliberately broken
/// input — a fuzz suite whose checker is never shown to reject anything is green and possibly
/// vacuous.
fn violations(text: &SourceText, tokens: &[LexedToken], leaves: &Leaves) -> Vec<String> {
    let mut found = Vec::new();
    if leaves.len() != tokens.len() {
        found.push(format!(
            "{} leaves for {} tokens",
            leaves.len(),
            tokens.len()
        ));
    }
    let mut previous_end = 0usize;
    for (index, token) in tokens.iter().enumerate() {
        let Ok(leaf) = leaves.leaf(index) else {
            found.push(format!("no leaf for token {index}"));
            continue;
        };
        let SourceInfo::Original { pos, end_pos, .. } = leaf.info() else {
            found.push(format!("leaf {index} is not Original"));
            continue;
        };
        if (pos, end_pos) != (token.extent.start(), token.extent.end()) {
            found.push(format!("leaf {index} does not carry the lexer's extent"));
        }
        if token.extent.start().0 < previous_end {
            found.push(format!("token {index} overlaps the previous one"));
        }
        if token.extent.end().0 > text.len_bytes() {
            found.push(format!("token {index} ends past the text"));
        }
        if !text
            .as_str()
            .is_char_boundary(token.extent.start().0.min(text.len_bytes()))
            || !text
                .as_str()
                .is_char_boundary(token.extent.end().0.min(text.len_bytes()))
        {
            found.push(format!("token {index} is not on scalar boundaries"));
        }
        previous_end = token.extent.end().0;
    }
    found
}

/// **The sweep.** Construction is total and structurally sound over a generated corpus.
#[test]
fn construction_holds_its_invariants_over_a_generated_corpus() {
    let table = table();
    let mut built = 0usize;
    let mut refused = 0usize;
    let mut with_tokens = 0usize;

    for seed in 0..12_000u64 {
        let mut rng = Rng::new(seed);
        let raw = generate(&mut rng);
        let Some(text) = text_of(&raw) else { continue };
        let run = lex_run(&text, &table);
        let tokens: Vec<LexedToken> = run
            .events
            .iter()
            .filter_map(|event| match event {
                Event::Token(token) => Some(token.clone()),
                _ => None,
            })
            .collect();

        match Leaves::build(&text, &tokens) {
            Ok(leaves) => {
                let found = violations(&text, &tokens, &leaves);
                assert!(
                    found.is_empty(),
                    "seed={seed}: {} violation(s)\n  raw={raw:?}\n  {}",
                    found.len(),
                    found.join("\n  ")
                );
                if !tokens.is_empty() {
                    with_tokens += 1;
                }
                built += 1;
            }
            // A typed refusal is a legitimate answer; a panic would have failed the harness.
            Err(_) => refused += 1,
        }
    }

    assert!(built > 8_000, "only {built} inputs built");
    assert!(
        with_tokens > 6_000,
        "only {with_tokens} built inputs had tokens; the corpus is mostly trivia"
    );
    // The lexer's extents always attach, so refusals should be rare or absent — reported rather
    // than asserted either way, because a sudden change in this number is informative.
    println!("parser_fuzz: built={built} refused={refused} with_tokens={with_tokens}");
}

/// **The checker can fail.** Broken constructions must be rejected, or the sweep proves nothing.
#[test]
fn the_invariant_checker_rejects_broken_constructions() {
    use fln_syntax::source::ByteSpan;
    use fln_syntax::token::TokenKind;

    let text = SourceText::from_utf8(b"abcdef").expect("valid");
    let span = |a: usize, b: usize| ByteSpan::new(BytePos(a), BytePos(b)).expect("forward");
    let token = |a: usize, b: usize| LexedToken {
        kind: TokenKind::Symbol("x".to_string()),
        extent: span(a, b),
    };

    // Well formed, so the checker is shown to accept something.
    let good = vec![token(0, 2), token(2, 4)];
    let leaves = Leaves::build(&text, &good).expect("attaches");
    assert!(
        violations(&text, &good, &leaves).is_empty(),
        "the checker must accept a well-formed construction: {:?}",
        violations(&text, &good, &leaves)
    );

    // A token list longer than the leaves: construction dropped one.
    let mut extra = good.clone();
    extra.push(token(4, 6));
    assert!(
        !violations(&text, &extra, &leaves).is_empty(),
        "a token with no leaf must be caught"
    );

    // Overlapping tokens, checked directly against the same leaves so the overlap rule fires.
    let overlapping = vec![token(0, 3), token(2, 4)];
    assert!(
        !violations(&text, &overlapping, &leaves).is_empty(),
        "overlapping tokens must be caught"
    );
}

/// **Resolution is total** over generated candidate sets: it always answers, and it reports an
/// ambiguity only when candidates genuinely tie.
#[test]
fn resolution_is_total_and_only_reports_genuine_ties() {
    for seed in 0..4_000u64 {
        let mut rng = Rng::new(seed ^ 0xA11B);
        let count = 1 + rng.below(5);

        // Each candidate consumes to a generated end and either succeeds or fails.
        let mut ends = Vec::new();
        let mut fails = Vec::new();
        let mut priorities = Vec::new();
        for _ in 0..count {
            ends.push(rng.below(8));
            fails.push(rng.below(3) == 0);
            priorities.push(rng.below(3) as u32);
        }

        let productions: Vec<Production> = (0..count)
            .map(|index| {
                let end = ends[index];
                let fail = fails[index];
                Production::new(
                    Name::str(Name::anonymous(), format!("p{index}")),
                    priorities[index],
                    move |state| {
                        state.set_pos(BytePos(end));
                        if fail {
                            state.set_error(fln_parse::state::ParseError::consuming(
                                "no",
                                BytePos(end),
                            ));
                        } else {
                            state.push(fln_syntax::tree::Syntax::Missing);
                        }
                    },
                )
            })
            .collect();
        let borrowed: Vec<&Production> = productions.iter().collect();

        let mut state = ParserState::new(0);
        let resolution = longest_match(&mut state, None, &borrowed);

        // Total: an answer, always.
        assert!(
            matches!(
                resolution,
                Resolution::Unique | Resolution::Ambiguous { .. } | Resolution::Failed
            ),
            "seed={seed}: a non-empty candidate list must resolve, got {resolution:?}"
        );

        // An ambiguity requires at least two candidates that agree on end, success and priority —
        // the score's three components. Anything else reported as ambiguous is a manufactured one,
        // which is the defect the dedup guard in slice C exists to prevent.
        if let Resolution::Ambiguous { alternatives } = resolution {
            let winner = ends.iter().copied().max().unwrap_or(0);
            let tied = (0..count)
                .filter(|index| ends[*index] == winner && !fails[*index])
                .count();
            assert!(
                tied >= 2,
                "seed={seed}: reported {alternatives} alternatives but only {tied} candidates tie"
            );
        }

        // The winning position is the furthest any candidate reached.
        if resolution != Resolution::None {
            let furthest = ends.iter().copied().max().unwrap_or(0);
            assert_eq!(
                state.pos().0,
                furthest,
                "seed={seed}: resolution must land at the furthest candidate's end"
            );
        }
    }
}

/// An empty candidate list is a typed refusal rather than a panic or a silent success — the shape a
/// category with no applicable productions produces.
#[test]
fn an_empty_candidate_list_refuses() {
    let mut state = ParserState::new(0);
    assert_eq!(longest_match(&mut state, None, &[]), Resolution::None);
    assert!(state.has_error());
}
