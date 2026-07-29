//! `grammar_effect_totality` — every registration effect answers, and a budget refusal is
//! inconclusive rather than a rejection (bead fln-okfb; FL-INV-07).
//!
//! ## Totality
//!
//! Every operation on the registry returns a typed answer for every input. Registration runs on
//! user input — a `syntax` command names a category the user typed — so a malformed request is a
//! diagnostic, never a panic. A panic here would be an invariant failure reported as a user error,
//! which is exactly what FL-INV-07 forbids.
//!
//! ## The budget law, on the LexBudget precedent
//!
//! Same shape as `fln_syntax::run::LexBudget` (bead franken_lean-81oq) and the same two directions,
//! because the first is vacuous alone:
//!
//! * A budget that is **not** exceeded is **invisible** — the resulting grammar root is identical to
//!   the unbounded one. A budget is a stopping condition, not a registration rule.
//! * A budget that **is** exceeded actually stops, and stops **atomically**: the grammar is
//!   untouched, so a caller can retry with a larger allowance rather than inspect wreckage.
//!
//! A grammar too large to hold is not a malformed grammar. Saying so would tell a user their correct
//! file has an error in it.

#![forbid(unsafe_code)]

use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::name::Name;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_parse::category::LeadingIdentBehavior;
use fln_parse::registry::{GrammarEpoch, RegisterError, Registry, RegistryBudget, Request};
use fln_parse::state::Production;

fn name(text: &str) -> Name {
    Name::str(Name::anonymous(), text)
}

fn production(label: &str) -> Production {
    Production::new(name(label), 0, |_state| {})
}

fn request(index: u64, token: &str, kind: &str, category: &Name) -> Request {
    Request {
        key: (index, kind.to_string()),
        category: category.clone(),
        token: name(token),
        production: production(kind),
        scoped: false,
    }
}

fn term_registry() -> (Registry, Name) {
    let mut registry = Registry::new();
    let term = name("term");
    registry
        .declare_category(term.clone(), LeadingIdentBehavior::Default)
        .expect("declares");
    (registry, term)
}

fn usage(
    outcome: &Outcome<Result<GrammarEpoch, RegisterError>>,
) -> Option<&fln_core::outcome::ResourceUsage> {
    match outcome {
        Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => Some(usage),
            _ => None,
        },
        _ => None,
    }
}

/// **Totality.** Every effect answers for every input, including the malformed ones.
#[test]
fn every_effect_answers_for_every_input() {
    let (mut registry, term) = term_registry();

    // Unknown category, empty token, an absurdly long token, unicode, and a duplicate category —
    // each gets a typed answer.
    assert!(
        registry
            .add_leading(&name("nope"), name("t"), production("p"), false)
            .is_err()
    );
    assert!(
        registry
            .add_leading(&term, name(""), production("p"), false)
            .is_ok(),
        "an empty token is a legal key"
    );
    assert!(
        registry
            .add_leading(&term, name(&"x".repeat(4096)), production("p"), false)
            .is_ok()
    );
    assert!(
        registry
            .add_leading(&term, name("😀→λ"), production("p"), false)
            .is_ok()
    );
    assert!(
        registry
            .declare_category(term.clone(), LeadingIdentBehavior::Both)
            .is_err()
    );
    assert!(registry.pop_scope().is_err(), "no scope is open");

    // Lookups at absurd epochs answer rather than panicking.
    for epoch in [GrammarEpoch(0), GrammarEpoch(u64::MAX)] {
        let _ = registry.kinds_at(&term, &name("x"), epoch);
        let _ = registry.grammar_root(epoch);
        let _ = registry.view_at(&term, epoch);
    }
    // And for a category that does not exist.
    assert!(registry.view_at(&name("nope"), registry.epoch()).is_none());
    assert!(
        registry
            .kinds_at(&name("nope"), &name("x"), registry.epoch())
            .is_empty()
    );
}

/// **Direction one: a generous budget is invisible.** The grammar root matches the unbounded one.
#[test]
fn a_generous_budget_produces_exactly_the_unbounded_grammar() {
    let requests = |term: &Name| {
        (0..40u64)
            .map(|index| request(index, "tok", &format!("k{index}"), term))
            .collect::<Vec<_>>()
    };

    let (mut unbounded, term) = term_registry();
    unbounded.apply_batch(requests(&term)).expect("applies");
    let expected = unbounded.grammar_root(unbounded.epoch());

    let (mut bounded, term) = term_registry();
    let outcome = bounded.apply_batch_bounded(requests(&term), RegistryBudget::generous());
    assert!(
        matches!(outcome, Outcome::Complete(Ok(_))),
        "a generous budget must complete: {outcome:?}"
    );
    assert_eq!(
        bounded.grammar_root(bounded.epoch()),
        expected,
        "a budget that is not exceeded must not change the grammar"
    );
}

/// **Direction two: an exceeded budget stops, and stops ATOMICALLY.**
#[test]
fn an_exceeded_budget_is_inconclusive_and_leaves_the_grammar_untouched() {
    let (mut registry, term) = term_registry();
    registry
        .add_leading(&term, name("existing"), production("existing"), false)
        .expect("registers");
    let before = registry.grammar_root(registry.epoch());
    let before_epoch = registry.epoch();

    let budget = RegistryBudget {
        max_categories: 4096,
        max_productions: 3,
    };
    let requests: Vec<Request> = (0..10u64)
        .map(|index| request(index, "tok", &format!("k{index}"), &term))
        .collect();
    let outcome = registry.apply_batch_bounded(requests, budget);

    let usage = usage(&outcome).expect("an exceeded budget is a resource stop");
    assert_eq!(
        usage.reason,
        ResourceReason::StructuralBudget {
            unit: StructuralUnit::ProducedNodes
        }
    );
    assert!(
        usage.is_genuine_exhaustion(),
        "observed must exceed allowed"
    );

    // ATOMICITY: nothing was applied, so a caller can retry with a larger allowance.
    assert_eq!(
        registry.grammar_root(registry.epoch()),
        before,
        "a refused batch must leave the grammar untouched"
    );
    assert_eq!(
        registry.epoch(),
        before_epoch,
        "and must not advance the epoch"
    );
}

/// **A budget stop is not a rejection, and publishes no diagnostic.**
///
/// The requests are impeccable — they would all register cleanly under a larger budget — so if a
/// budget refusal reached the diagnostic stream this is where a user would be told their correct
/// file has an error in it.
#[test]
fn a_budget_stop_publishes_no_diagnostic() {
    let (mut registry, term) = term_registry();
    let requests: Vec<Request> = (0..10u64)
        .map(|index| request(index, "tok", &format!("k{index}"), &term))
        .collect();

    // The same requests succeed under a generous budget, so nothing about them is wrong.
    let (mut control, control_term) = term_registry();
    let control_requests: Vec<Request> = (0..10u64)
        .map(|index| request(index, "tok", &format!("k{index}"), &control_term))
        .collect();
    assert!(matches!(
        control.apply_batch_bounded(control_requests, RegistryBudget::generous()),
        Outcome::Complete(Ok(_))
    ));

    let outcome = registry.apply_batch_bounded(
        requests,
        RegistryBudget {
            max_categories: 4096,
            max_productions: 2,
        },
    );

    assert!(
        !matches!(outcome, Outcome::Complete(_)),
        "not an acceptance"
    );
    assert!(
        !matches!(outcome, Outcome::InternalFault(_)),
        "declining to finish is not an internal fault"
    );
    let published = match &outcome {
        Outcome::Inconclusive(inconclusive) => inconclusive.diagnostic.clone(),
        _ => None,
    };
    assert!(
        published.is_none(),
        "a budget stop on a clean batch published a diagnostic: {published:?}"
    );
    assert_ne!(
        usage(&outcome).expect("a stop").reason,
        ResourceReason::Cancelled,
        "a budget overrun is not a cancellation — cause and outcome stay apart"
    );
}

/// The category budget is a different unit from the production budget, reported as its own.
#[test]
fn the_two_budget_units_are_reported_separately() {
    let mut registry = Registry::new();
    for index in 0..5 {
        registry
            .declare_category(name(&format!("c{index}")), LeadingIdentBehavior::Default)
            .expect("declares");
    }
    let outcome = registry.apply_batch_bounded(
        Vec::new(),
        RegistryBudget {
            max_categories: 2,
            max_productions: 1_000,
        },
    );
    let usage = usage(&outcome).expect("a stop");
    assert_eq!(
        usage.allowed, 2,
        "the category allowance, not the production one"
    );
    assert_eq!(usage.observed, 5);
}

/// A zero budget on an empty batch completes: there is no work to refuse, and refusing anyway would
/// make "register nothing" fail.
#[test]
fn a_zero_budget_on_an_empty_batch_completes() {
    let (mut registry, _) = term_registry();
    let outcome = registry.apply_batch_bounded(
        Vec::new(),
        RegistryBudget {
            max_categories: 4096,
            max_productions: 0,
        },
    );
    assert!(
        matches!(outcome, Outcome::Complete(Ok(_))),
        "an empty batch under a zero production budget has nothing to refuse: {outcome:?}"
    );
}

/// The exact boundary: a budget equal to what the batch needs completes; one below it stops.
#[test]
fn the_budget_boundary_is_exact() {
    let build = || {
        let (registry, term) = term_registry();
        let requests: Vec<Request> = (0..4u64)
            .map(|index| request(index, "tok", &format!("k{index}"), &term))
            .collect();
        (registry, requests)
    };

    let (mut registry, requests) = build();
    let needed = requests.len() as u64;
    assert!(matches!(
        registry.apply_batch_bounded(
            requests,
            RegistryBudget {
                max_categories: 4096,
                max_productions: needed
            }
        ),
        Outcome::Complete(Ok(_))
    ));

    let (mut registry, requests) = build();
    assert!(
        usage(&registry.apply_batch_bounded(
            requests,
            RegistryBudget {
                max_categories: 4096,
                max_productions: needed - 1
            }
        ))
        .is_some(),
        "one below what the batch needs must stop"
    );
}
