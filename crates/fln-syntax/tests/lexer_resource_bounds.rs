//! `lexer_resource_bounds` — a budget refusal is inconclusive, never rejected, and never
//! changes an answer (bead franken_lean-81oq; FL-INV-07).
//!
//! ## The law
//!
//! Resource exhaustion yields a typed `Inconclusive` outcome, never rendered as, cached as, or
//! promoted to acceptance *or* rejection (doctrine §8, FL-INV-07). For the lexer that means a
//! file too big to lex is not a file with an error in it. If a budget refusal reached the
//! diagnostic stream, a user would be told their correct source is malformed — the exact
//! confusion the two-axis outcome model exists to prevent.
//!
//! ## Two directions, again
//!
//! * A budget that is **not** exceeded must be **invisible**: the run is byte-for-byte the one
//!   the unbounded lexer produces. A budget is a stopping condition, not a lexing rule, and one
//!   that changed a token stream would make lexing depend on a caller's allowance.
//! * A budget that **is** exceeded must actually stop. Without this, the first assertion is
//!   satisfied by a budget that never triggers, which is a very comfortable way to have no
//!   bound at all.
//!
//! ## Why two units and not one
//!
//! `InputBytes` and `ProducedNodes` answer different questions — "is this file too big to
//! consider" versus "did lexing it materialize more structure than I allowed" — so a caller
//! raising one is making a different decision from a caller raising the other. That is why
//! `StructuralUnit` distinguishes them (bead franken_lean-vui8), and this suite is where the
//! distinction is held to: each unit is asserted to be reported for its own cause, and *not* for
//! the other's.

#![forbid(unsafe_code)]

mod common;

use common::{BASES, FRAGMENTS, Rng, table, text_of};
use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_syntax::run::{LexBudget, lex_run, lex_run_bounded};

/// The run inside a completed outcome, or `None` if the outcome was not a completion.
///
/// Returning an `Option` rather than matching with a failing arm so the assertions read as value
/// comparisons: a budget that unexpectedly refused shows up as `None` against `Some(run)`, which
/// says what happened, instead of a panic inside a helper.
fn completed(outcome: Outcome<fln_syntax::run::LexRun>) -> Option<fln_syntax::run::LexRun> {
    match outcome {
        Outcome::Complete(run) => Some(run),
        _ => None,
    }
}

/// The usage inside an inconclusive outcome, or `None` if the outcome was not a resource stop.
fn usage(outcome: &Outcome<fln_syntax::run::LexRun>) -> Option<&fln_core::outcome::ResourceUsage> {
    match outcome {
        Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => Some(usage),
            _ => None,
        },
        _ => None,
    }
}

/// **Direction one: a budget that is not exceeded is invisible.**
///
/// Byte-for-byte against the unbounded run, over the whole corpus — including the ill-formed
/// inputs, because a budget must not change what a refusal says either.
#[test]
fn a_generous_budget_produces_exactly_the_unbounded_run() {
    let table = table();
    let mut checked = 0usize;
    for base in BASES {
        let text = text_of(base);
        let unbounded = lex_run(&text, &table);
        let bounded = completed(lex_run_bounded(&text, &table, LexBudget::generous()));
        assert_eq!(
            bounded,
            Some(unbounded),
            "a generous budget must complete and produce the unbounded run for {base:?}"
        );
        checked += 1;
    }
    for seed in 0..2_000u64 {
        let mut rng = Rng::new(seed ^ 0xB0_0B);
        let pieces = 1 + rng.below(10);
        let mut raw = String::new();
        for _ in 0..pieces {
            raw.push_str(rng.pick(FRAGMENTS));
        }
        let text = text_of(&raw);
        let unbounded = lex_run(&text, &table);
        let bounded = completed(lex_run_bounded(&text, &table, LexBudget::generous()));
        assert_eq!(
            bounded,
            Some(unbounded),
            "seed={seed}: a generous budget must complete and produce the unbounded run for {raw:?}"
        );
        checked += 1;
    }
    assert!(checked > 2_000, "only {checked} inputs compared");
}

/// **Direction two: a tight budget actually stops**, and reports the unit that caused it.
#[test]
fn an_exceeded_input_budget_is_inconclusive_and_names_input_bytes() {
    let table = table();
    let text = text_of("def f := 1\n");
    let budget = LexBudget {
        max_input_bytes: 4,
        max_events: 1_000,
    };
    let outcome = lex_run_bounded(&text, &table, budget);

    let usage = usage(&outcome).expect("an exceeded input budget is a resource stop");
    assert_eq!(
        usage.reason,
        ResourceReason::StructuralBudget {
            unit: StructuralUnit::InputBytes
        },
        "an input-size stop must name InputBytes, not ProducedNodes — the caller's next \
         decision depends on which one it was"
    );
    assert_eq!(usage.allowed, 4);
    assert_eq!(usage.observed, text.len_bytes() as u64);
    assert!(
        usage.is_genuine_exhaustion(),
        "observed must exceed allowed, or the stop is misreported"
    );
}

/// The event budget, reported as `ProducedNodes` — a different unit for a different question.
#[test]
fn an_exceeded_event_budget_is_inconclusive_and_names_produced_nodes() {
    let table = table();
    let text = text_of("def f := fun x => x + 1\ntheorem t := rfl\n");
    let full = lex_run(&text, &table);
    assert!(full.events.len() > 6, "the fixture needs enough events");

    let budget = LexBudget {
        max_input_bytes: 1_000_000,
        max_events: 3,
    };
    let outcome = lex_run_bounded(&text, &table, budget);

    let usage = usage(&outcome).expect("an exceeded event budget is a resource stop");
    assert_eq!(
        usage.reason,
        ResourceReason::StructuralBudget {
            unit: StructuralUnit::ProducedNodes
        },
        "an event-count stop must name ProducedNodes, not InputBytes"
    );
    assert_eq!(usage.allowed, 3);
    assert!(
        usage.observed > usage.allowed,
        "observed {} must exceed allowed {}",
        usage.observed,
        usage.allowed
    );
    assert!(usage.is_genuine_exhaustion());
}

/// **The refusal is not a rejection.** A budget stop is neither `Complete` nor a diagnostic, and
/// the input it refused is a *well-formed* file — so nothing about the stop may suggest the file
/// was bad.
#[test]
fn a_budget_stop_is_never_an_acceptance_or_a_rejection() {
    let table = table();
    // Deliberately impeccable input: if a budget stop leaked into the diagnostic stream, this is
    // the case where a user would be told a correct file has an error in it.
    let text = text_of("def f := 1\n");
    let unbounded = lex_run(&text, &table);
    assert!(
        unbounded.accepted(),
        "the fixture must be accepted when lexed without a budget"
    );
    assert!(
        unbounded.diagnostics().is_empty(),
        "the fixture must produce no diagnostics without a budget"
    );

    for budget in [
        LexBudget {
            max_input_bytes: 2,
            max_events: 1_000,
        },
        LexBudget {
            max_input_bytes: 1_000,
            max_events: 1,
        },
    ] {
        let outcome = lex_run_bounded(&text, &table, budget);

        // Not an acceptance.
        assert!(
            !matches!(outcome, Outcome::Complete(_)),
            "{budget:?}: a stop must not be Complete"
        );
        // Not an internal fault either: declining is not a bug.
        assert!(
            !matches!(outcome, Outcome::InternalFault(_)),
            "{budget:?}: declining to finish is not an internal fault"
        );
        // And a resource stop specifically, not a cancellation — cause and outcome stay apart.
        let usage = usage(&outcome).expect("a resource stop");
        assert_ne!(
            usage.reason,
            ResourceReason::Cancelled,
            "{budget:?}: a budget overrun is not a cancellation"
        );
        assert!(usage.is_genuine_exhaustion(), "{budget:?}");
    }
}

/// A budget stop carries **no diagnostics**, because there is nothing wrong with the file.
///
/// Stated as a pair: the same text lexed without a budget produces no diagnostics at all, so
/// nothing the stop declined to finish was a real problem. That pairing is what makes the claim
/// meaningful — on an already-broken file, "the stop reported no diagnostics" would be
/// indistinguishable from "the diagnostics had not been reached yet".
#[test]
fn a_budget_stop_says_nothing_about_a_clean_file() {
    let table = table();
    let text = text_of("def a := 1\ndef b := 2\ndef c := 3\n");

    let clean = lex_run(&text, &table);
    assert!(clean.accepted(), "the fixture must lex cleanly unbounded");
    assert!(
        clean.diagnostics().is_empty(),
        "the fixture must have no diagnostics unbounded"
    );

    let stopped = lex_run_bounded(
        &text,
        &table,
        LexBudget {
            max_input_bytes: 1_000,
            max_events: 4,
        },
    );
    assert!(
        matches!(stopped, Outcome::Inconclusive(_)),
        "expected a stop, got {stopped:?}"
    );

    assert!(
        usage(&stopped).is_some(),
        "a resource stop, not a rejection"
    );

    // NONPUBLICATION, directly: `Inconclusive::diagnostic` is the user-visible projection, and a
    // budget stop on a clean file must leave it empty. This is the field a renderer reads, so
    // asserting it is `None` is the assertion that the user is never shown an error here — much
    // stronger than inferring it from the outcome's shape.
    let published = match &stopped {
        Outcome::Inconclusive(inconclusive) => inconclusive.diagnostic.clone(),
        _ => None,
    };
    assert!(
        published.is_none(),
        "a budget stop on a clean file published a diagnostic: {published:?}"
    );
}

/// A budget of zero stops immediately rather than looping or completing vacuously.
#[test]
fn a_zero_budget_stops_at_once() {
    let table = table();
    let text = text_of("x");
    for budget in [
        LexBudget {
            max_input_bytes: 0,
            max_events: 0,
        },
        LexBudget {
            max_input_bytes: 0,
            max_events: 1_000,
        },
        LexBudget {
            max_input_bytes: 1_000,
            max_events: 0,
        },
    ] {
        let outcome = lex_run_bounded(&text, &table, budget);
        assert!(
            usage(&outcome).is_some(),
            "{budget:?} must stop on a one-byte input"
        );
    }
    // The empty text is the one case a zero budget completes: there is no work to refuse, and
    // refusing anyway would make "lex nothing" fail.
    let empty = text_of("");
    assert_eq!(
        completed(lex_run_bounded(
            &empty,
            &table,
            LexBudget {
                max_input_bytes: 0,
                max_events: 0,
            }
        )),
        Some(lex_run(&empty, &table)),
        "lexing nothing under a zero budget must complete: there is no work to refuse"
    );
}

/// The exact boundary: a budget equal to what the input needs completes; one below it stops.
///
/// Off-by-one here is the difference between a bound that is honoured and a bound that is
/// approximately honoured, and only one of those is a contract.
#[test]
fn the_budget_boundary_is_exact() {
    let table = table();
    let text = text_of("def f := 1\n");
    let needed = lex_run(&text, &table).events.len() as u64;
    let bytes = text.len_bytes() as u64;

    // Exactly enough: completes, and equals the unbounded run.
    assert_eq!(
        completed(lex_run_bounded(
            &text,
            &table,
            LexBudget {
                max_input_bytes: bytes,
                max_events: needed,
            }
        )),
        Some(lex_run(&text, &table)),
        "an exactly-sufficient budget must complete with the unbounded run"
    );

    // One event short: stops.
    assert!(
        usage(&lex_run_bounded(
            &text,
            &table,
            LexBudget {
                max_input_bytes: bytes,
                max_events: needed - 1,
            }
        ))
        .is_some(),
        "one event short of what the input needs must stop"
    );

    // One byte short: stops, and names the other unit.
    let stop = lex_run_bounded(
        &text,
        &table,
        LexBudget {
            max_input_bytes: bytes - 1,
            max_events: needed,
        },
    );
    assert_eq!(
        usage(&stop).expect("a stop").reason,
        ResourceReason::StructuralBudget {
            unit: StructuralUnit::InputBytes
        }
    );
}
