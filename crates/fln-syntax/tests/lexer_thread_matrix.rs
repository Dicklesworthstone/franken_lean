//! `lexer_thread_matrix` — FL-INV-01 for the lexer: **identical**, not merely equivalent,
//! results at {1, 8, 32} threads (bead franken_lean-81oq).
//!
//! ## What "identical" is required to mean
//!
//! Determinism is a contract (doctrine §6, FL-INV-01): the same input closure must give the
//! same environment, the same diagnostics and the same artifacts at any thread count. For the
//! lexer that means three things must match the single-threaded run exactly, and each is
//! asserted separately because each could drift on its own:
//!
//! 1. **The token stream** — every event, in order, with its extent and its kind, including the
//!    `Name` inside an identifier and the `LiteralKind` of a literal.
//! 2. **The diagnostics** — every refusal's message *and* offset, in order. Not the count. A
//!    lexer that reported the same number of errors at different positions would satisfy a
//!    count check and be non-deterministic in exactly the way a user notices.
//! 3. **The trivia attachment** — the whole `Attachment`, entry by entry, plus its epilogue.
//!    Attachment is where losslessness lives, and it is computed from the token stream, so a
//!    stream that matched while attachment did not would mean the attachment step itself had
//!    become order-dependent.
//!
//! ## Why this is a real test and not a formality
//!
//! The lexer is a pure function today, so one might argue the matrix cannot fail. Two answers.
//!
//! First, that is a claim about the current implementation and this suite is what keeps it
//! true: the moment anyone adds a token cache, a memo table, an interner, or a shared
//! `TokenTable` behind a lock — all of which upstream has, in the shape of `ParserState`'s
//! token cache — the assumption is gone, and the failure would otherwise surface as a
//! flaky test in something far away. Upstream caches tokens *by design*
//! (`updateTokenCache`, `Lean/Parser/Basic.lean:1048`), so a faithful implementation is
//! heading toward exactly the structure this guards.
//!
//! Second, the `Name` in an identifier event is `Arc`-backed and hashed at construction. A
//! hash that mixed in an address, or an interner that assigned ids in completion order, would
//! produce equal-looking names with different identities. Comparing whole events is what
//! catches that; comparing rendered text would not.
//!
//! The work is deliberately partitioned so that the *same* input is lexed on different threads
//! in different interleavings, and results are collected into indexed slots rather than in
//! completion order — collecting in completion order would produce a permutation and prove
//! nothing about the lexer.

#![forbid(unsafe_code)]

mod common;

use common::{BASES, FRAGMENTS, Rng, table, text_of};
use fln_syntax::attach::{TokenExtent, attach};
use fln_syntax::run::{LexRun, lex_run};
use fln_syntax::token::TokenTable;
use std::thread;

const THREAD_COUNTS: [usize; 3] = [1, 8, 32];

/// The corpus: the realistic bases plus generated inputs, so the matrix covers both
/// well-formed files and the broken ones an editor actually holds.
fn corpus() -> Vec<String> {
    let mut inputs: Vec<String> = BASES.iter().map(|base| (*base).to_string()).collect();
    for seed in 0..240u64 {
        let mut rng = Rng::new(seed ^ 0x5151_5151);
        let pieces = 1 + rng.below(10);
        let mut out = String::new();
        for _ in 0..pieces {
            out.push_str(rng.pick(FRAGMENTS));
        }
        inputs.push(out);
    }
    inputs
}

/// Everything one input produces, in one comparable value.
///
/// Bundled deliberately: comparing the three properties as one value means a future addition
/// to the lexer's output cannot be silently left out of the determinism claim.
#[derive(Debug, PartialEq, Eq)]
struct Observed {
    run: LexRun,
    diagnostics: Vec<(&'static str, fln_syntax::source::BytePos)>,
    attachment: Option<fln_syntax::attach::Attachment>,
}

fn observe(table: &TokenTable, raw: &str) -> Observed {
    let text = text_of(raw);
    let run = lex_run(&text, table);
    let extents: Vec<TokenExtent> = run
        .token_extents()
        .into_iter()
        .map(TokenExtent::Present)
        .collect();
    Observed {
        diagnostics: run.diagnostics(),
        attachment: attach(&text, &extents).ok(),
        run,
    }
}

/// Lex every input at `threads` threads, collecting into indexed slots.
fn observe_all(table: &TokenTable, inputs: &[String], threads: usize) -> Vec<Observed> {
    if threads == 1 {
        return inputs.iter().map(|raw| observe(table, raw)).collect();
    }
    let mut slots: Vec<Option<Observed>> = (0..inputs.len()).map(|_| None).collect();
    thread::scope(|scope| {
        // Interleave rather than block-partition: with a stride, adjacent inputs land on
        // different threads, so neighbouring work overlaps in time. Block partitioning would
        // let each thread run a contiguous, effectively sequential stretch.
        let mut handles = Vec::new();
        for offset in 0..threads {
            handles.push(scope.spawn(move || {
                let table = table;
                let mut produced = Vec::new();
                let mut index = offset;
                while index < inputs.len() {
                    produced.push((index, observe(table, &inputs[index])));
                    index += threads;
                }
                produced
            }));
        }
        for handle in handles {
            for (index, observed) in handle.join().expect("a lexing thread panicked") {
                slots[index] = Some(observed);
            }
        }
    });
    // Every slot must have been filled: with a stride partition, an off-by-one in the striding
    // would silently leave inputs unlexed and the comparison would then run over fewer inputs
    // than the corpus has. Asserting the count first says so directly.
    let filled = slots.iter().filter(|slot| slot.is_some()).count();
    assert_eq!(
        filled,
        inputs.len(),
        "{threads} threads lexed {filled} of {} inputs",
        inputs.len()
    );
    slots.into_iter().flatten().collect()
}

/// **FL-INV-01 for the lexer.** Token stream, diagnostics and trivia attachment are identical
/// at 1, 8 and 32 threads.
#[test]
fn the_lexer_is_identical_at_one_eight_and_thirty_two_threads() {
    let table = table();
    let inputs = corpus();
    assert!(inputs.len() > 200, "corpus is too small to be meaningful");

    let baseline = observe_all(&table, &inputs, 1);

    for threads in THREAD_COUNTS {
        let observed = observe_all(&table, &inputs, threads);
        assert_eq!(
            observed.len(),
            baseline.len(),
            "{threads} threads produced {} results for {} inputs",
            observed.len(),
            baseline.len()
        );
        for (index, (got, want)) in observed.iter().zip(baseline.iter()).enumerate() {
            // Compared as one value, then narrowed for the message — so a mismatch in any of
            // the three properties fails, and the report says which.
            if got != want {
                assert_eq!(
                    got.run, want.run,
                    "{threads} threads: token stream differs on input {index}: {:?}",
                    inputs[index]
                );
                assert_eq!(
                    got.diagnostics, want.diagnostics,
                    "{threads} threads: DIAGNOSTICS differ on input {index}: {:?}",
                    inputs[index]
                );
                assert_eq!(
                    got.attachment, want.attachment,
                    "{threads} threads: trivia ATTACHMENT differs on input {index}: {:?}",
                    inputs[index]
                );
                unreachable!("the bundle differed but no field did — Observed lost a field");
            }
        }
    }
}

/// The same input lexed concurrently by many threads at once — contention on one input rather
/// than one input per thread.
///
/// This is the shape that would expose shared mutable state inside the lexer or the table: the
/// partitioned test above gives each thread its own inputs, so a per-input cache would still
/// look deterministic there.
#[test]
fn the_same_input_lexed_concurrently_is_identical_every_time() {
    let table = table();
    // The input carries every construct that could plausibly acquire a cache: a keyword, a
    // dotted identifier, an escaped identifier, all three literal families, a nested block
    // comment, and two refusals.
    let raw =
        "def Nat.succ «odd one» := 0x1F + 1.5e-3 \"s\" 'c' `n r#\"r\"# /- a /- b -/ -/ \t\u{0d}x";
    let baseline = observe(&table, raw);

    for threads in THREAD_COUNTS {
        let results: Vec<Observed> = thread::scope(|scope| {
            let handles: Vec<_> = (0..threads)
                .map(|_| scope.spawn(|| observe(&table, raw)))
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("a lexing thread panicked"))
                .collect()
        });
        for (worker, observed) in results.iter().enumerate() {
            assert_eq!(
                *observed, baseline,
                "{threads} threads, worker {worker}: differs from the single-threaded result"
            );
        }
    }
}

/// Determinism is not the same as "the run is empty". If the fixture produced no tokens and no
/// diagnostics, the matrix above would pass on vacuum — the same trap the recovery corpus and
/// the incremental damage bound each had to close in their own way.
#[test]
fn the_matrix_fixture_actually_produces_tokens_diagnostics_and_attachment() {
    let table = table();
    let inputs = corpus();
    let observed = observe_all(&table, &inputs, 1);

    let tokens: usize = observed.iter().map(|o| o.run.token_extents().len()).sum();
    let diagnostics: usize = observed.iter().map(|o| o.diagnostics.len()).sum();
    let attached = observed.iter().filter(|o| o.attachment.is_some()).count();
    let accepted = observed.iter().filter(|o| o.run.accepted()).count();

    assert!(tokens > 500, "only {tokens} tokens across the corpus");
    assert!(
        diagnostics > 50,
        "only {diagnostics} diagnostics — the corpus barely exercises refusals"
    );
    assert!(
        attached > 100,
        "only {attached} inputs produced an attachment"
    );
    // And both acceptance outcomes are present, so the matrix is not comparing only failures.
    assert!(accepted > 0, "no input in the corpus was accepted");
    assert!(
        accepted < observed.len(),
        "every input was accepted; the corpus needs refusals too"
    );

    // The single-threaded observation is itself stable across repeats — if it were not, the
    // comparisons above would be measuring noise rather than thread behaviour.
    let again = observe_all(&table, &inputs, 1);
    assert_eq!(observed, again, "the single-threaded run is not repeatable");
}

/// **The matrix's comparison must be sensitive to positions, not just counts.**
///
/// FL-INV-01 asks for *identical* diagnostics, and "identical" is a stronger claim than "the
/// same number of them". A lexer that reported one tab error per run but at a different offset
/// depending on scheduling would satisfy a count check while being non-deterministic in exactly
/// the way a user sees — the underline lands on a different character.
///
/// This is that assertion's plant: perturb one diagnostic *offset*, leaving the message and the
/// count untouched, and confirm the comparison rejects it. Without this, nothing establishes
/// that the matrix above compares more than shapes.
#[test]
fn a_diagnostic_at_a_different_offset_is_not_identical() {
    use fln_syntax::source::BytePos;

    let table = table();
    let raw = "a\tb\tc";
    let baseline = observe(&table, raw);
    assert_eq!(
        baseline.diagnostics.len(),
        2,
        "the fixture must produce more than one diagnostic to be worth perturbing"
    );

    // Same messages, same count, one offset moved by a single byte.
    let mut perturbed: Vec<(&'static str, BytePos)> = baseline.diagnostics.clone();
    let (message, at) = perturbed[1];
    perturbed[1] = (message, BytePos(at.0 + 1));

    assert_eq!(
        perturbed.len(),
        baseline.diagnostics.len(),
        "the perturbation must not change the count, or this proves nothing"
    );
    assert_eq!(
        perturbed.iter().map(|(m, _)| *m).collect::<Vec<_>>(),
        baseline
            .diagnostics
            .iter()
            .map(|(m, _)| *m)
            .collect::<Vec<_>>(),
        "the perturbation must not change the messages either"
    );
    assert_ne!(
        perturbed, baseline.diagnostics,
        "a moved diagnostic offset must compare as DIFFERENT — otherwise the thread matrix \
         would accept position drift"
    );

    // And the same for the bundle, so the field is actually reached by the matrix's comparison.
    let moved = Observed {
        run: baseline.run.clone(),
        diagnostics: perturbed,
        attachment: baseline.attachment.clone(),
    };
    assert_ne!(
        moved, baseline,
        "Observed must distinguish runs that differ only in a diagnostic offset"
    );
}

/// The same plant for the token stream: a token whose extent moved by one byte must compare as
/// different, even though the kind and the count are unchanged.
#[test]
fn a_token_at_a_different_extent_is_not_identical() {
    use fln_syntax::run::Event;
    use fln_syntax::source::{BytePos, ByteSpan};

    let table = table();
    let baseline = observe(&table, "def f := 1");
    let mut shifted = baseline.run.clone();
    let moved = shifted
        .events
        .iter_mut()
        .find_map(|event| match event {
            Event::Token(token) => {
                let start = token.extent.start();
                token.extent =
                    ByteSpan::new(start, BytePos(token.extent.end().0 + 1)).expect("wider span");
                Some(())
            }
            _ => None,
        })
        .is_some();
    assert!(moved, "the fixture must contain a token to perturb");
    assert_eq!(
        shifted.events.len(),
        baseline.run.events.len(),
        "the perturbation must not change the event count"
    );
    assert_ne!(
        shifted, baseline.run,
        "a token whose extent moved must compare as DIFFERENT"
    );
}
