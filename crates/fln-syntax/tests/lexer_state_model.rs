//! `lexer_state_model` — the driver's state machine, stated as a model and checked against the
//! runs it produces (bead franken_lean-81oq).
//!
//! ## The model
//!
//! The driver is a two-state loop, and writing it down is the point of this suite — the shape
//! is what every other lexer property leans on:
//!
//! ```text
//! AtHead:                        -- the loop head; trivia is scanned here
//!   scan trivia
//!     Ok(stop)  -> emit Trivia(at..stop)
//!                  if stop == end then Done
//!                  else lex a token at stop:
//!                       Ok(token)  -> emit Token(token) ; AtHead at token end
//!                       Err(error) -> emit Refused      ; AtHead past the refusal
//!     Err(error) -> emit Refused(at..resume)            ; AtHead at resume
//! ```
//!
//! Three consequences follow, and each is asserted below rather than assumed:
//!
//! 1. **Every `Token` is immediately preceded by a `Trivia`.** The driver cannot emit a token
//!    without having scanned trivia first, even when that trivia is empty.
//! 2. **The resumable points are exactly the `Trivia` starts.** Lexing from one reproduces the
//!    tail of the run exactly, because the driver reads only forward.
//! 3. **A `Refused` from the trivia arm has no preceding `Trivia`** in its own iteration — it
//!    replaces it. This asymmetry is real and is why "the events alternate" would be a wrong
//!    model.
//!
//! ## Why the model earns its place
//!
//! Consequence 2 is the theorem the incremental re-lex rests on, and consequence 1 is the fact
//! that made three of its five defects. They were discovered *through* the incremental
//! differential, which is an expensive way to learn a property of a two-state loop. Stating the
//! model directly means the next person changing the driver breaks a test that names the law,
//! rather than a property suite three layers away that reports a mysterious duplicated event.

#![forbid(unsafe_code)]

mod common;

use common::{BASES, FRAGMENTS, Rng, table, text_of};
use fln_syntax::run::{Event, LexRun, lex_run, lex_run_from};
use fln_syntax::source::BytePos;
use fln_syntax::token::TokenTable;

/// The corpus: realistic bases plus generated inputs weighted toward lexical decision points.
fn corpus() -> Vec<String> {
    let mut inputs: Vec<String> = BASES.iter().map(|base| (*base).to_string()).collect();
    for seed in 0..600u64 {
        let mut rng = Rng::new(seed ^ 0x1D0D_1D0D);
        let pieces = 1 + rng.below(10);
        let mut out = String::new();
        for _ in 0..pieces {
            out.push_str(rng.pick(FRAGMENTS));
        }
        inputs.push(out);
    }
    inputs
}

/// The model's states, as a value, so conformance is a comparison rather than a story.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Model {
    /// At the loop head: the next event must be a `Trivia`, or a `Refused` from the trivia arm.
    AtHead,
    /// Trivia has just been emitted: the next event, if any, is a `Token` or a `Refused`.
    AfterTrivia,
}

/// Walk a run against the model, returning every violation.
fn conformance_violations(run: &LexRun) -> Vec<String> {
    let mut state = Model::AtHead;
    let mut found = Vec::new();
    for (index, event) in run.events.iter().enumerate() {
        match (state, event) {
            (Model::AtHead, Event::Trivia(_)) => state = Model::AfterTrivia,
            // The trivia arm's refusal replaces the trivia event for that iteration.
            (Model::AtHead, Event::Refused { .. }) => state = Model::AtHead,
            (Model::AfterTrivia, Event::Token(_) | Event::Refused { .. }) => state = Model::AtHead,
            (Model::AfterTrivia, Event::Trivia(_)) => {
                found.push(format!(
                    "event {index}: two Trivia events in a row — the driver cannot do that, so \
                     either a splice duplicated one or the loop head moved"
                ));
                state = Model::AfterTrivia;
            }
            (Model::AtHead, Event::Token(_)) => {
                found.push(format!(
                    "event {index}: a Token with no Trivia before it — every token is preceded \
                     by a trivia scan, even an empty one"
                ));
                state = Model::AtHead;
            }
        }
    }
    found
}

/// **Consequence 1.** Every run conforms to the model, and every `Token` has a `Trivia` before
/// it.
#[test]
fn every_run_conforms_to_the_two_state_model() {
    let table = table();
    let mut tokens_seen = 0usize;
    let mut trivia_refusals = 0usize;
    for raw in corpus() {
        let text = text_of(&raw);
        let run = lex_run(&text, &table);
        let found = conformance_violations(&run);
        assert!(
            found.is_empty(),
            "input {raw:?} violates the model:\n  {}",
            found.join("\n  ")
        );
        for (index, event) in run.events.iter().enumerate() {
            if matches!(event, Event::Token(_)) {
                tokens_seen += 1;
                assert!(
                    index > 0 && matches!(run.events[index - 1], Event::Trivia(_)),
                    "input {raw:?}: token at event {index} is not preceded by trivia"
                );
            }
        }
        trivia_refusals += run
            .events
            .iter()
            .enumerate()
            .filter(|(index, event)| {
                matches!(event, Event::Refused { .. })
                    && (*index == 0 || !matches!(run.events[index - 1], Event::Trivia(_)))
            })
            .count();
    }
    // Anti-vacuity: both interesting shapes must actually occur in the corpus, or the model
    // walk above has nothing to conform to.
    assert!(tokens_seen > 500, "only {tokens_seen} tokens in the corpus");
    assert!(
        trivia_refusals > 0,
        "no trivia-arm refusal in the corpus, so the asymmetric transition is untested"
    );
}

/// **The model can fail.** Each corrupted run below breaks exactly one model rule.
#[test]
fn the_model_rejects_runs_the_driver_could_not_have_produced() {
    use fln_syntax::source::ByteSpan;
    use fln_syntax::token::{LexedToken, TokenKind};

    let span = |a: usize, b: usize| ByteSpan::new(BytePos(a), BytePos(b)).expect("forward");
    let token = |a: usize, b: usize| {
        Event::Token(LexedToken {
            kind: TokenKind::Symbol("x".to_string()),
            extent: span(a, b),
        })
    };

    // Conforming, so the checker is shown to accept something.
    let good = LexRun {
        events: vec![Event::Trivia(span(0, 0)), token(0, 1)],
    };
    assert!(conformance_violations(&good).is_empty(), "must accept");

    // A token with no trivia before it — what a bad splice produces.
    let bare = LexRun {
        events: vec![token(0, 1)],
    };
    assert!(
        conformance_violations(&bare)
            .iter()
            .any(|message| message.contains("no Trivia before it")),
        "a bare token must be rejected by name"
    );

    // Two trivia in a row — what restarting at a token's offset produced before it was fixed.
    let doubled = LexRun {
        events: vec![
            Event::Trivia(span(0, 0)),
            Event::Trivia(span(0, 0)),
            token(0, 1),
        ],
    };
    assert!(
        conformance_violations(&doubled)
            .iter()
            .any(|message| message.contains("two Trivia events in a row")),
        "a doubled trivia event must be rejected by name"
    );
}

/// **Consequence 2, the theorem the incremental re-lex rests on.** Lexing from any resumable
/// point reproduces the tail of the run exactly.
///
/// Checked at *every* trivia start of every input, not a sampled few, because the incremental
/// path may pick any of them.
#[test]
fn lexing_from_any_resumable_point_reproduces_the_tail() {
    let table = table();
    let mut resumptions = 0usize;
    for raw in corpus() {
        let text = text_of(&raw);
        let run = lex_run(&text, &table);
        for (index, event) in run.events.iter().enumerate() {
            if !matches!(event, Event::Trivia(_)) {
                continue;
            }
            let resumed = lex_run_from(&text, &table, event.start());
            assert_eq!(
                resumed.events,
                run.events[index..],
                "input {raw:?}: resuming at event {index} (offset {}) did not reproduce the tail",
                event.start().0
            );
            resumptions += 1;
        }
    }
    assert!(
        resumptions > 1_000,
        "only {resumptions} resumptions were checked"
    );
}

/// **The other direction, so the restriction is a constraint and not a convention.** Resuming at
/// a non-resumable offset does *not* generally reproduce the tail.
///
/// If it did, `relex_incremental` would not need to constrain its restart to trivia events at
/// all, and the fix for that defect would have been unnecessary. Asserting the negative is what
/// distinguishes "we chose trivia starts" from "we had to".
#[test]
fn resuming_at_a_token_offset_does_not_reproduce_the_tail() {
    let table = table();
    let mut disagreements = 0usize;
    let mut checked = 0usize;

    for raw in corpus() {
        let text = text_of(&raw);
        let run = lex_run(&text, &table);
        for (index, event) in run.events.iter().enumerate() {
            // A token whose preceding trivia is NON-empty: resuming at the token's own offset
            // skips that trivia, so the tail must differ.
            let Event::Token(_) = event else { continue };
            let Some(Event::Trivia(before)) = run.events.get(index.wrapping_sub(1)) else {
                continue;
            };
            if before.is_empty() {
                // With empty preceding trivia the offsets coincide, and resuming there emits an
                // equivalent empty trivia — so those cases legitimately agree and prove nothing.
                continue;
            }
            checked += 1;
            let resumed = lex_run_from(&text, &table, event.start());
            if resumed.events != run.events[index..] {
                disagreements += 1;
            }
        }
    }

    assert!(
        checked > 100,
        "only {checked} token-offset resumptions were available to check"
    );
    assert_eq!(
        disagreements,
        checked,
        "resuming at a token offset agreed with the tail {} of {checked} times; if it always \
         agreed, constraining the restart to trivia events would be unnecessary",
        checked - disagreements
    );
}

/// A run is total and contiguous from any resumable point, not just from zero — the coverage
/// law, restated for resumption, because the incremental path splices from these offsets.
#[test]
fn a_resumed_run_covers_the_rest_of_the_text_contiguously() {
    let table = table();
    for raw in corpus() {
        let text = text_of(&raw);
        let run = lex_run(&text, &table);
        for event in run.events.iter().filter(|e| matches!(e, Event::Trivia(_))) {
            let from = event.start();
            let resumed = lex_run_from(&text, &table, from);
            let mut at = from.0;
            for resumed_event in &resumed.events {
                assert_eq!(
                    resumed_event.extent().start().0,
                    at,
                    "input {raw:?}: resumed run from {} has a gap at {at}",
                    from.0
                );
                at = resumed_event.extent().end().0;
            }
            assert_eq!(
                at,
                text.len_bytes(),
                "input {raw:?}: resumed run from {} stopped at {at}",
                from.0
            );
        }
    }
}

/// Resuming past the end is total and yields an empty run, since the driver's loop condition is
/// the first thing it checks. Worth asserting because an off-by-one in a caller's restart
/// arithmetic lands here, and an empty run is a much better outcome than a panic.
#[test]
fn resuming_at_or_past_the_end_yields_an_empty_run() {
    let table = table();
    for raw in ["", "x", "def f := 1", "/- open"] {
        let text = text_of(raw);
        for offset in [
            text.len_bytes(),
            text.len_bytes() + 1,
            text.len_bytes() + 99,
        ] {
            let resumed = lex_run_from(&text, &table, BytePos(offset));
            assert!(
                resumed.events.is_empty(),
                "input {raw:?} resumed at {offset} produced {} events",
                resumed.events.len()
            );
            assert!(resumed.accepted(), "an empty run has no refusals");
        }
    }
}

/// The empty table is a valid configuration and the model must hold for it too — it turns most
/// symbols into refusals, which exercises the trivia-arm and token-arm refusal transitions far
/// more than a populated table does.
#[test]
fn the_model_holds_with_no_tokens_declared() {
    let empty = TokenTable::new();
    let mut refusals = 0usize;
    for raw in corpus() {
        let text = text_of(&raw);
        let run = lex_run(&text, &empty);
        let found = conformance_violations(&run);
        assert!(
            found.is_empty(),
            "input {raw:?} with an empty table violates the model:\n  {}",
            found.join("\n  ")
        );
        refusals += run.diagnostics().len();
    }
    assert!(
        refusals > 200,
        "only {refusals} refusals with an empty table — expected many more"
    );
}
