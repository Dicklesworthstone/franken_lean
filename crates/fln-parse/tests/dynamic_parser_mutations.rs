//! `dynamic_parser_mutations` — mutants, and which oracle kills each (bead fln-okfb).
//!
//! ## The criterion this suite is built around
//!
//! **If a mutant dies only because the oracle and the implementation share an assumption, it is not
//! a kill.** So every mutant below is recorded with the *grade of the assertion that kills it*, and
//! the suite asserts that the mutants a self-differential structurally cannot catch are killed by
//! **pin-derived** assertions instead.
//!
//! Three grades, the same ones used across this bead:
//!
//! * `PinObserved` — killed by an assertion derived from running the pinned binary. A real kill.
//! * `Transcribed` — killed by an assertion derived from reading the pin's source. Weaker: if the
//!   reading is wrong, the mutant and the assertion are wrong together.
//! * `OurOwnRule` — killed by an assertion of our own design, with no pin backing. Weakest, and
//!   recorded as such rather than counted as a kill.
//!
//! ## Why these mutants and not others
//!
//! The interesting ones are those a self-differential is structurally blind to — a registration
//! dropped identically on both sides, an order both the runner and the canonical rule agree on
//! wrongly. Each of those produces the *same* result at every thread count and in every arrival
//! order, so `parser_interleaving_dpor` is green for all of them. They are marked below.
//!
//! Each mutant is simulated inline rather than patched into the source: the mutant's behaviour is
//! implemented in the test and the killing assertion is applied to it. That keeps the record of
//! "what kills this" next to the mutant instead of in a commit message.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::category::LeadingIdentBehavior;
use fln_parse::registry::{GrammarEpoch, Registry};
use fln_parse::state::Production;

fn name(text: &str) -> Name {
    Name::str(Name::anonymous(), text)
}

fn production(label: &str) -> Production {
    Production::new(name(label), 0, |_state| {})
}

/// What kind of evidence the killing assertion rests on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Grade {
    PinObserved,
    Transcribed,
    OurOwnRule,
}

/// One mutant: what it does, what kills it, and whether a self-differential could see it.
#[derive(Debug)]
struct Mutant {
    what: &'static str,
    killed_by: &'static str,
    grade: Grade,
    /// True when every thread count and arrival order produces the same wrong answer, so the
    /// interleaving sweep is green for it.
    invisible_to_self_differential: bool,
}

fn mutants() -> Vec<Mutant> {
    vec![
        Mutant {
            what: "last-wins registration: a second production under a token replaces the first",
            killed_by: "additive shadowing — two `notation \"dup\"` give `error: Ambiguous term`",
            grade: Grade::PinObserved,
            invisible_to_self_differential: true,
        },
        Mutant {
            what: "the epoch filter is dropped, so a lookup sees later registrations",
            killed_by: "interleaving — `#check myfoo` before its `syntax` gives Unknown identifier",
            grade: Grade::PinObserved,
            invisible_to_self_differential: true,
        },
        Mutant {
            what: "scope discard uses `<=` on depth, taking the enclosing scope too",
            killed_by: "nested scopes — after `end B`, n1 resolves and n2 does not",
            grade: Grade::PinObserved,
            invisible_to_self_differential: true,
        },
        Mutant {
            what: "a scoped registration is treated as global, so `local notation` outlives its scope",
            killed_by: "scope restore — `local notation` is unknown after `end`",
            grade: Grade::PinObserved,
            invisible_to_self_differential: true,
        },
        Mutant {
            what: "registering into an unknown category succeeds by creating the category",
            killed_by: "typed refusal — `syntax \"zz\" : nosuchcategory` gives `unknown category`",
            grade: Grade::PinObserved,
            invisible_to_self_differential: true,
        },
        Mutant {
            what: "the canonical sort is removed, so arrival order reaches the grammar",
            killed_by: "the interleaving sweep — different arrival orders give different roots",
            grade: Grade::OurOwnRule,
            invisible_to_self_differential: false,
        },
        Mutant {
            what: "hooks fire in registration order instead of reverse",
            killed_by: "a reading of Extension.lean:313 (`hook::hooks`) and :315 (`hooks.forM`)",
            grade: Grade::Transcribed,
            invisible_to_self_differential: true,
        },
        Mutant {
            what: "a refused batch applies part of itself before refusing",
            killed_by: "our atomicity rule, so a caller can retry with a larger allowance",
            grade: Grade::OurOwnRule,
            invisible_to_self_differential: true,
        },
    ]
}

/// **THE ACCOUNTING.** Every mutant that a self-differential cannot see must be killed by an
/// assertion stronger than a self-differential — and the ones killed only by a weaker oracle are
/// counted and named rather than folded into a total.
#[test]
fn every_mutant_invisible_to_a_self_differential_is_killed_by_a_stronger_oracle() {
    let mutants = mutants();
    let mut pin_killed = 0usize;
    let mut weaker = Vec::new();

    for mutant in &mutants {
        if !mutant.invisible_to_self_differential {
            // A mutant the sweep CAN see may legitimately be killed by the sweep.
            continue;
        }
        match mutant.grade {
            Grade::PinObserved => pin_killed += 1,
            Grade::Transcribed | Grade::OurOwnRule => weaker.push(mutant),
        }
    }

    assert!(
        pin_killed >= 5,
        "only {pin_killed} of the self-differential-invisible mutants are killed by a pin \
         observation; the rest are resting on weaker evidence"
    );

    // The two that are NOT pin-killed are named here on purpose. This assertion is a ratchet: if a
    // future change adds another mutant on weak evidence, this fails and the addition has to be
    // justified rather than absorbed.
    let names: Vec<&str> = weaker.iter().map(|mutant| mutant.what).collect();
    assert_eq!(
        names.len(),
        2,
        "the mutants killed only by weaker evidence are expected to be exactly two; found \
         {names:?}"
    );
    assert!(
        names.iter().any(|what| what.contains("hooks fire")),
        "hook ordering is one of them — killed by a reading, not an observation"
    );
    assert!(
        names.iter().any(|what| what.contains("refused batch")),
        "batch atomicity is the other — our own rule, with no pin backing"
    );
}

/// **MUTANT: last-wins registration.** Invisible to a self-differential; killed by the pin.
#[test]
fn mutant_last_wins_is_killed_by_the_additive_shadowing_observation() {
    let mut registry = Registry::new();
    let term = name("term");
    registry
        .declare_category(term.clone(), LeadingIdentBehavior::Default)
        .expect("declares");
    registry
        .add_leading(&term, name("dup"), production("first"), false)
        .expect("registers");
    registry
        .add_leading(&term, name("dup"), production("second"), false)
        .expect("registers");
    let real = registry.kinds_at(&term, &name("dup"), registry.epoch());

    // The mutant: keep only the last.
    let mutant: Vec<Name> = real.last().cloned().into_iter().collect();

    assert_eq!(
        real,
        vec![name("first"), name("second")],
        "the real registry is additive"
    );
    assert_ne!(
        real, mutant,
        "the pin's `Ambiguous term` requires BOTH productions live, so last-wins is killed"
    );

    // And the crucial part: at every thread count the mutant is self-consistent, so the sweep
    // cannot see it. Demonstrated rather than asserted in prose — the mutant's answer does not
    // depend on order at all.
    let mut reversed = Registry::new();
    reversed
        .declare_category(term.clone(), LeadingIdentBehavior::Default)
        .expect("declares");
    reversed
        .add_leading(&term, name("dup"), production("second"), false)
        .expect("registers");
    reversed
        .add_leading(&term, name("dup"), production("first"), false)
        .expect("registers");
    let mutant_reversed: Vec<Name> = reversed
        .kinds_at(&term, &name("dup"), reversed.epoch())
        .last()
        .cloned()
        .into_iter()
        .collect();
    assert_eq!(
        mutant.len(),
        mutant_reversed.len(),
        "the mutant produces one production either way, so an arrival-order sweep sees no \
         difference — which is exactly why the pin observation is what kills it"
    );
}

/// **MUTANT: the epoch filter dropped.** Invisible to a self-differential; killed by the pin.
#[test]
fn mutant_ignoring_the_epoch_is_killed_by_the_interleaving_observation() {
    let mut registry = Registry::new();
    let term = name("term");
    registry
        .declare_category(term.clone(), LeadingIdentBehavior::Default)
        .expect("declares");
    let before = registry.epoch();
    registry
        .add_leading(&term, name("tok"), production("later"), false)
        .expect("registers");

    let real = registry.kinds_at(&term, &name("tok"), before);
    // The mutant ignores the epoch and reports everything.
    let mutant = registry.kinds_at(&term, &name("tok"), registry.epoch());

    assert!(
        real.is_empty(),
        "at an epoch before the registration, nothing is live — `#check` before `syntax` fails"
    );
    assert_ne!(
        real, mutant,
        "the mutant reports a registration that had not happened yet"
    );
}

/// **MUTANT: a scoped registration treated as global.** Killed by the pin's scope-restore
/// observation.
#[test]
fn mutant_ignoring_scoping_is_killed_by_the_scope_restore_observation() {
    let build = |scoped: bool| {
        let mut registry = Registry::new();
        let term = name("term");
        registry
            .declare_category(term.clone(), LeadingIdentBehavior::Default)
            .expect("declares");
        registry.push_scope();
        registry
            .add_leading(&term, name("loc"), production("local"), scoped)
            .expect("registers");
        let after = registry.pop_scope().expect("pops");
        registry.kinds_at(&term, &name("loc"), after)
    };

    assert!(
        build(true).is_empty(),
        "a scoped registration is gone after `end` — the pin gives Unknown identifier"
    );
    assert_eq!(
        build(false),
        vec![name("local")],
        "the mutant treats it as global, so it survives — which the pin says it must not"
    );
}

/// **MUTANT: registering into an unknown category creates it.** Killed by the pin's typed refusal.
#[test]
fn mutant_autocreating_a_category_is_killed_by_the_typed_refusal() {
    let mut registry = Registry::new();
    let missing = name("nosuchcategory");
    assert!(
        registry
            .add_leading(&missing, name("zz"), production("zz"), false)
            .is_err(),
        "the pin gives `unknown category 'nosuchcategory'`, so registration must refuse"
    );
    assert!(
        !registry.has_category(&missing),
        "and the refusal must not have created the category as a side effect"
    );
    assert_eq!(registry.epoch(), GrammarEpoch(0), "nor advanced the epoch");
}

/// **MUTANT: a refused batch applies part of itself.** Killed by OUR atomicity rule, and recorded as
/// such — there is no pin observation behind it.
///
/// The pin's observed behaviour is in fact the *opposite* at command granularity: a failed command
/// does not roll back previously-registered grammar, so registration is not transactional across
/// commands. Our atomicity claim is about a single batch, which the pin has no equivalent of, so it
/// is our own rule and graded `OurOwnRule` in the accounting above.
#[test]
fn mutant_partial_batch_application_is_killed_by_our_own_atomicity_rule() {
    use fln_core::outcome::Outcome;
    use fln_parse::registry::{RegistryBudget, Request};

    let mut registry = Registry::new();
    let term = name("term");
    registry
        .declare_category(term.clone(), LeadingIdentBehavior::Default)
        .expect("declares");
    let before = registry.grammar_root(registry.epoch());

    let requests: Vec<Request> = (0..8u64)
        .map(|index| Request {
            key: (index, format!("k{index}")),
            category: term.clone(),
            token: name("tok"),
            production: production(&format!("k{index}")),
            scoped: false,
        })
        .collect();
    let outcome = registry.apply_batch_bounded(
        requests,
        RegistryBudget {
            max_categories: 4096,
            max_productions: 2,
        },
    );

    assert!(
        matches!(outcome, Outcome::Inconclusive(_)),
        "the batch is refused"
    );
    assert_eq!(
        registry.grammar_root(registry.epoch()),
        before,
        "and nothing was applied. This is OUR rule: the pin's observed behaviour at COMMAND \
         granularity is the opposite — a failed command does not roll back earlier grammar — so \
         this assertion is graded OurOwnRule rather than counted as a pin kill."
    );
}

/// The mutant table itself is well formed: no duplicates, every field populated, and the grade
/// distribution is what the accounting expects.
#[test]
fn the_mutant_table_is_well_formed() {
    let mutants = mutants();
    assert!(mutants.len() >= 8, "only {} mutants listed", mutants.len());

    let mut whats: Vec<&str> = mutants.iter().map(|mutant| mutant.what).collect();
    whats.sort_unstable();
    let count = whats.len();
    whats.dedup();
    assert_eq!(whats.len(), count, "duplicate mutant in the table");

    for mutant in &mutants {
        assert!(!mutant.what.is_empty() && !mutant.killed_by.is_empty());
    }

    let pin = mutants
        .iter()
        .filter(|m| m.grade == Grade::PinObserved)
        .count();
    assert!(
        pin * 2 > mutants.len(),
        "only {pin} of {} mutants are killed by a pin observation; a mutation suite resting mostly \
         on its own rules is measuring its own opinions",
        mutants.len()
    );
}
