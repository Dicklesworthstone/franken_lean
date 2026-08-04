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
use fln_hash::domain::Digest;
use fln_parse::category::LeadingIdentBehavior;
use fln_parse::registry::{
    GrammarComponent, GrammarEpoch, GrammarIdentity, GrammarTransition, InvalidationReason,
    MemoAdvanceBudget, MemoAdvanceCheckpoint, MemoKey, MemoLookup, ParseDependencies, ParseMemo,
    ParseProduct, ParserEffect, ParserPosition, RegisterError, Registry, RegistryBudget, Request,
};
use fln_parse::state::{ParserDescriptor, Production};
use fln_syntax::source::BytePos;

fn name(text: &str) -> Name {
    Name::str(Name::anonymous(), text)
}

fn production(label: &str) -> Production {
    Production::new(name(label), 0, |_state| {})
}

fn stable_production(label: &str) -> Production {
    let kind = name(label);
    Production::described(
        kind.clone(),
        0,
        ParserDescriptor::stable(kind, 1, b"grammar-effect-totality".to_vec()),
        |_state| {},
    )
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
    let foreign = GrammarEpoch::from_parts(u64::MAX, Digest([0xa5; 32]));
    for epoch in [registry.epoch(), foreign] {
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

/// Every state-changing surface emits a typed effect, while an unknown surface is explicitly
/// opaque and establishes the suffix barrier.
#[test]
fn every_effect_variant_is_emitted_or_conservatively_opaque() {
    let (mut registry, term) = term_registry();

    registry
        .add_leading_at(
            BytePos(2),
            &term,
            name("tok"),
            stable_production("kind"),
            false,
        )
        .expect("adds syntax");
    assert!(registry.last_transition().is_some_and(|transition| {
        transition
            .effects
            .iter()
            .any(|effect| matches!(effect, ParserEffect::AddsSyntax { .. }))
            && transition
                .effects
                .iter()
                .any(|effect| matches!(effect, ParserEffect::AddsToken { .. }))
            && !transition.has_opaque_effect()
    }));

    registry.register_token_parser_at(
        BytePos(3),
        name("literal"),
        ParserDescriptor::stable(name("literal-parser"), 1, b"decimal".to_vec()),
    );
    assert!(registry.last_transition().is_some_and(|transition| {
        transition
            .effects
            .iter()
            .any(|effect| matches!(effect, ParserEffect::AddsToken { .. }))
    }));

    registry
        .set_precedence_at(BytePos(4), &term, name("kind"), 65)
        .expect("changes precedence");
    assert!(registry.last_transition().is_some_and(|transition| {
        transition
            .effects
            .iter()
            .any(|effect| matches!(effect, ParserEffect::ChangesPrecedence { .. }))
    }));

    registry.push_scope_at(BytePos(5));
    assert!(registry.last_transition().is_some_and(|transition| {
        transition
            .effects
            .iter()
            .any(|effect| matches!(effect, ParserEffect::OpensScope { .. }))
    }));
    registry.pop_scope_at(BytePos(6)).expect("closes scope");
    assert!(registry.last_transition().is_some_and(|transition| {
        transition
            .effects
            .iter()
            .any(|effect| matches!(effect, ParserEffect::ClosesScope { .. }))
    }));

    registry.register_macro_at(
        BytePos(7),
        name("macro"),
        ParserDescriptor::stable(name("macro"), 1, b"expander".to_vec()),
    );
    assert!(registry.last_transition().is_some_and(|transition| {
        transition
            .effects
            .iter()
            .any(|effect| matches!(effect, ParserEffect::RegistersMacro { .. }))
    }));

    registry.set_option_at(BytePos(8), name("parser.option"), "on");
    assert!(registry.last_transition().is_some_and(|transition| {
        transition
            .effects
            .iter()
            .any(|effect| matches!(effect, ParserEffect::ChangesOption { .. }))
    }));

    let imported = term_registry().0;
    registry.import_grammar_at(BytePos(9), name("Imported"), imported.identity());
    assert!(registry.last_transition().is_some_and(|transition| {
        transition
            .effects
            .iter()
            .any(|effect| matches!(effect, ParserEffect::ImportsGrammar { .. }))
    }));

    registry
        .remove_syntax_at(
            BytePos(10),
            &term,
            &name("tok"),
            &name("kind"),
            ParserPosition::Leading,
        )
        .expect("removes syntax");
    assert!(registry.last_transition().is_some_and(|transition| {
        transition
            .effects
            .iter()
            .any(|effect| matches!(effect, ParserEffect::RemovesSyntax { .. }))
    }));

    let before_refusal = registry.epoch();
    assert!(matches!(
        registry.remove_syntax_at(
            BytePos(11),
            &term,
            &name("missing"),
            &name("kind"),
            ParserPosition::Leading,
        ),
        Err(RegisterError::ProductionNotFound { .. })
    ));
    assert_eq!(
        registry.epoch(),
        before_refusal,
        "a malformed removal is failure-atomic"
    );

    registry.set_unknown_option_at(BytePos(12), name("future.option"), "unknown");
    assert!(
        registry
            .last_transition()
            .is_some_and(|transition| transition.has_opaque_effect())
    );
    assert_eq!(registry.opaque_suffix_barrier(), Some(BytePos(12)));
    assert!(!registry.distributed_parse_allowed_at(BytePos(12)));
}

fn assert_exact_component_invalidation(
    mut registry: Registry,
    key_category: &Name,
    affected: GrammarComponent,
    unaffected: GrammarComponent,
    mutate: impl FnOnce(&mut Registry),
) {
    let before = registry.identity().clone();
    let affected_key = MemoKey {
        position: BytePos(20),
        category: key_category.clone(),
        precedence: 0,
        epoch: before.epoch(),
    };
    let unaffected_key = MemoKey {
        position: BytePos(30),
        category: key_category.clone(),
        precedence: 0,
        epoch: before.epoch(),
    };
    let mut memo = ParseMemo::new();
    memo.insert(
        affected_key.clone(),
        &before,
        ParseProduct::new(
            before.epoch(),
            ParseDependencies::from_components([affected.clone()]),
            "affected",
        ),
    )
    .expect("the affected fixture is epoch-consistent");
    memo.insert(
        unaffected_key.clone(),
        &before,
        ParseProduct::new(
            before.epoch(),
            ParseDependencies::from_components([unaffected]),
            "unaffected",
        ),
    )
    .expect("the control fixture is epoch-consistent");

    mutate(&mut registry);
    let transition = registry
        .last_transition()
        .expect("a matrix mutation publishes one transition")
        .clone();
    let after = registry.identity().clone();
    let report = memo
        .advance(
            &transition,
            &before,
            &after,
            MemoAdvanceBudget::generous(),
            None,
        )
        .into_complete()
        .expect("the matrix advance completes")
        .expect("the live identities match the transition");

    assert_eq!(report.scanned, 2);
    assert_eq!(report.invalidated, 1);
    assert_eq!(report.promoted, 1);
    assert_eq!(report.prefix_reused, 0);
    assert_eq!(
        report.reasons,
        vec![(affected_key.clone(), InvalidationReason::Changed(affected))]
    );

    let mut affected_after = affected_key;
    affected_after.epoch = after.epoch();
    assert!(matches!(
        memo.lookup(&affected_after, &after),
        Ok(MemoLookup::Miss | MemoLookup::CollisionMiss)
    ));

    let mut unaffected_after = unaffected_key;
    unaffected_after.epoch = after.epoch();
    let control = memo
        .lookup(&unaffected_after, &after)
        .expect("the promoted control lookup is well formed");
    let MemoLookup::Hit(control) = control else {
        panic!("an unrelated dependency must be promoted");
    };
    assert_eq!(control.value(), &"unaffected");
    assert_eq!(control.epoch(), after.epoch());
}

/// Every typed registry surface invalidates its exact dependency and promotes a close near-miss.
///
/// This is deliberately a real mutation matrix: the effect producer, dependency intersection,
/// report reason, and published memo keys are checked as one seam.
#[test]
fn every_typed_effect_has_an_exact_memo_invalidation_witness() {
    let category = name("term");
    let other_category = name("command");
    assert_exact_component_invalidation(
        Registry::new(),
        &category,
        GrammarComponent::Category(category.clone()),
        GrammarComponent::Category(other_category),
        |registry| {
            registry
                .declare_category_at(BytePos(10), category.clone(), LeadingIdentBehavior::Default)
                .expect("declares the affected category");
        },
    );

    let (registry, term) = term_registry();
    let syntax_token = name("syntax-token");
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Syntax {
            category: term.clone(),
            token: syntax_token.clone(),
            position: ParserPosition::Leading,
        },
        GrammarComponent::Syntax {
            category: term.clone(),
            token: syntax_token.clone(),
            position: ParserPosition::Trailing,
        },
        |registry| {
            registry
                .add_leading_at(
                    BytePos(10),
                    &term,
                    syntax_token,
                    stable_production("syntax-kind"),
                    false,
                )
                .expect("adds the affected leading syntax");
        },
    );

    let (registry, term) = term_registry();
    let token = name("literal");
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Token(token.clone()),
        GrammarComponent::Token(name("other-literal")),
        |registry| {
            registry.register_token_parser_at(
                BytePos(10),
                token,
                ParserDescriptor::stable(name("literal-parser"), 1, b"decimal-literal".to_vec()),
            );
        },
    );

    let (registry, term) = term_registry();
    let parser = name("infix-parser");
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Precedence {
            category: term.clone(),
            parser: parser.clone(),
        },
        GrammarComponent::Precedence {
            category: term.clone(),
            parser: name("other-parser"),
        },
        |registry| {
            registry
                .set_precedence_at(BytePos(10), &term, parser, 65)
                .expect("sets the affected precedence");
        },
    );

    let (registry, term) = term_registry();
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Scope,
        GrammarComponent::Option(name("scope-control")),
        |registry| {
            registry.push_scope_at(BytePos(10));
        },
    );

    let (mut registry, term) = term_registry();
    registry.push_scope_at(BytePos(0));
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Scope,
        GrammarComponent::Option(name("close-scope-control")),
        |registry| {
            registry
                .pop_scope_at(BytePos(10))
                .expect("closes the affected scope");
        },
    );

    let (registry, term) = term_registry();
    let macro_name = name("term-macro");
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Macro(macro_name.clone()),
        GrammarComponent::Macro(name("other-macro")),
        |registry| {
            registry.register_macro_at(
                BytePos(10),
                macro_name,
                ParserDescriptor::stable(name("macro-expander"), 1, b"expander".to_vec()),
            );
        },
    );

    let (registry, term) = term_registry();
    let option = name("parser.option");
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Option(option.clone()),
        GrammarComponent::Option(name("other.option")),
        |registry| {
            registry.set_option_at(BytePos(10), option, "on");
        },
    );

    let (registry, term) = term_registry();
    let imported = term_registry().0.identity().clone();
    let module = name("Imported");
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Import(module.clone()),
        GrammarComponent::Import(name("OtherImported")),
        |registry| {
            registry.import_grammar_at(BytePos(10), module, &imported);
        },
    );

    let (mut registry, term) = term_registry();
    let removable_token = name("removable");
    let removable_kind = name("removable-kind");
    registry
        .add_leading_at(
            BytePos(0),
            &term,
            removable_token.clone(),
            stable_production("removable-kind"),
            false,
        )
        .expect("seeds syntax for exact removal");
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Syntax {
            category: term.clone(),
            token: removable_token.clone(),
            position: ParserPosition::Leading,
        },
        GrammarComponent::Syntax {
            category: term.clone(),
            token: removable_token.clone(),
            position: ParserPosition::Trailing,
        },
        |registry| {
            registry
                .remove_syntax_at(
                    BytePos(10),
                    &term,
                    &removable_token,
                    &removable_kind,
                    ParserPosition::Leading,
                )
                .expect("removes the exact affected syntax");
        },
    );

    let (mut registry, term) = term_registry();
    let shadowed_token = name("shadowed");
    registry
        .add_leading_at(
            BytePos(0),
            &term,
            shadowed_token.clone(),
            stable_production("older-kind"),
            false,
        )
        .expect("seeds the shadowed syntax");
    assert_exact_component_invalidation(
        registry,
        &term,
        GrammarComponent::Syntax {
            category: term.clone(),
            token: shadowed_token.clone(),
            position: ParserPosition::Leading,
        },
        GrammarComponent::Syntax {
            category: term.clone(),
            token: shadowed_token.clone(),
            position: ParserPosition::Trailing,
        },
        |registry| {
            registry
                .add_leading_at(
                    BytePos(10),
                    &term,
                    shadowed_token,
                    stable_production("newer-kind"),
                    false,
                )
                .expect("adds the shadowing syntax");
        },
    );
}

/// An opaque effect ignores dependency precision for the suffix, while preserving the historical
/// prefix under the exact epoch that recognized it.
#[test]
fn opaque_effect_invalidates_every_suffix_dependency_and_preserves_the_prefix() {
    let (mut registry, term) = term_registry();
    let before = registry.identity().clone();
    let old_keys = [BytePos(5), BytePos(20), BytePos(30)].map(|position| MemoKey {
        position,
        category: term.clone(),
        precedence: 0,
        epoch: before.epoch(),
    });
    let dependencies = [
        GrammarComponent::Syntax {
            category: term.clone(),
            token: name("prefix"),
            position: ParserPosition::Leading,
        },
        GrammarComponent::Option(name("suffix.option")),
        GrammarComponent::Macro(name("suffix.macro")),
    ];
    let mut memo = ParseMemo::new();
    for ((key, component), value) in old_keys
        .iter()
        .zip(dependencies)
        .zip(["prefix", "option", "macro"])
    {
        memo.insert(
            key.clone(),
            &before,
            ParseProduct::new(
                before.epoch(),
                ParseDependencies::from_components([component]),
                value,
            ),
        )
        .expect("the opaque fixture is epoch-consistent");
    }

    registry.apply_opaque_effect_at(BytePos(10), name("unknown-parser-callback"));
    let transition = registry
        .last_transition()
        .expect("the opaque mutation publishes a transition")
        .clone();
    let after = registry.identity().clone();
    let report = memo
        .advance(
            &transition,
            &before,
            &after,
            MemoAdvanceBudget::generous(),
            None,
        )
        .into_complete()
        .expect("the opaque advance completes")
        .expect("the live identities match the transition");

    assert_eq!(report.scanned, 3);
    assert_eq!(report.prefix_reused, 1);
    assert_eq!(report.invalidated, 2);
    assert_eq!(report.promoted, 0);
    assert_eq!(
        report.reasons,
        old_keys[1..]
            .iter()
            .cloned()
            .map(|key| (key, InvalidationReason::OpaqueSuffixBarrier))
            .collect::<Vec<_>>()
    );
    assert!(matches!(
        memo.lookup(&old_keys[0], &before),
        Ok(MemoLookup::Hit(_))
    ));
    for old_key in &old_keys {
        let mut after_key = old_key.clone();
        after_key.epoch = after.epoch();
        assert!(!matches!(
            memo.lookup(&after_key, &after),
            Ok(MemoLookup::Hit(_))
        ));
    }
}

fn memo_transition_fixture() -> (
    ParseMemo<&'static str>,
    GrammarTransition,
    GrammarIdentity,
    GrammarIdentity,
    [MemoKey; 2],
) {
    let (mut registry, term) = term_registry();
    let before_identity = registry.identity().clone();
    let old_keys = [BytePos(20), BytePos(30)].map(|position| MemoKey {
        position,
        category: term.clone(),
        precedence: 0,
        epoch: before_identity.epoch(),
    });
    let dependencies = ParseDependencies::from_components([GrammarComponent::Syntax {
        category: term.clone(),
        token: name("unrelated"),
        position: ParserPosition::Leading,
    }]);
    let mut memo = ParseMemo::new();
    for (key, value) in old_keys.iter().zip(["first", "second"]) {
        memo.insert(
            key.clone(),
            &before_identity,
            ParseProduct::new(before_identity.epoch(), dependencies.clone(), value),
        )
        .expect("fixture memo insert");
    }

    registry
        .add_leading_at(
            BytePos(10),
            &term,
            name("changed"),
            stable_production("changed-kind"),
            false,
        )
        .expect("fixture transition");
    let transition = registry
        .last_transition()
        .expect("syntax registration emits a transition")
        .clone();
    let after_identity = registry.identity().clone();
    (memo, transition, before_identity, after_identity, old_keys)
}

fn assert_memo_was_not_advanced(
    memo: &ParseMemo<&'static str>,
    before: &GrammarIdentity,
    after: &GrammarIdentity,
    old_keys: &[MemoKey; 2],
) {
    assert_eq!(memo.len(), old_keys.len());
    for old_key in old_keys {
        assert!(matches!(
            memo.lookup(old_key, before),
            Ok(MemoLookup::Hit(_))
        ));
        let mut after_key = old_key.clone();
        after_key.epoch = after.epoch();
        assert!(
            !matches!(memo.lookup(&after_key, after), Ok(MemoLookup::Hit(_))),
            "a non-answer must publish no promoted key"
        );
    }
}

/// Memo scanning has an exact resource boundary, reports genuine exhaustion, and can be retried
/// without repairing partial publication.
#[test]
fn memo_advance_budget_is_exact_atomic_and_retryable() {
    let (mut memo, transition, before, after, old_keys) = memo_transition_fixture();
    let outcome = memo.advance(
        &transition,
        &before,
        &after,
        MemoAdvanceBudget { max_entries: 1 },
        None,
    );
    let Outcome::Inconclusive(inconclusive) = outcome else {
        panic!("one entry below the exact scan boundary must be inconclusive");
    };
    let InconclusiveCause::ResourceExhausted { usage } = inconclusive.cause else {
        panic!("the memo budget stop must be resource exhaustion");
    };
    assert_eq!(
        usage.reason,
        ResourceReason::StructuralBudget {
            unit: StructuralUnit::ProducedNodes
        }
    );
    assert_eq!(usage.allowed, 1);
    assert_eq!(usage.observed, 2);
    assert_memo_was_not_advanced(&memo, &before, &after, &old_keys);

    let report = memo
        .advance(
            &transition,
            &before,
            &after,
            MemoAdvanceBudget { max_entries: 2 },
            None,
        )
        .into_complete()
        .expect("the exact boundary is authoritative")
        .expect("the transition identities match");
    assert_eq!(report.scanned, 2);
    assert_eq!(report.promoted, 2);
    assert_eq!(report.invalidated, 0);
    assert_eq!(report.prefix_reused, 0);
}

/// Cancellation after partial scanning leaves the memo byte-for-byte authoritative at the old
/// epoch, then a clean retry publishes the complete plan.
#[test]
fn memo_advance_mid_scan_cancellation_is_atomic_and_retryable() {
    let (mut memo, transition, before, after, old_keys) = memo_transition_fixture();
    let cancel = |checkpoint| {
        matches!(
            checkpoint,
            MemoAdvanceCheckpoint::BeforeEntry { scanned: 1 }
        )
    };
    let outcome = memo.advance(
        &transition,
        &before,
        &after,
        MemoAdvanceBudget::generous(),
        Some(&cancel),
    );
    let Outcome::Inconclusive(inconclusive) = outcome else {
        panic!("the sampled cancellation must be inconclusive");
    };
    assert!(matches!(
        inconclusive.cause,
        InconclusiveCause::Cancelled { .. }
    ));
    assert!(inconclusive.diagnostic.is_none());
    assert_memo_was_not_advanced(&memo, &before, &after, &old_keys);

    let report = memo
        .advance(
            &transition,
            &before,
            &after,
            MemoAdvanceBudget::generous(),
            None,
        )
        .into_complete()
        .expect("the uncancelled retry is authoritative")
        .expect("the transition identities match");
    assert_eq!(report.promoted, 2);
}

/// A final cancellation sample guards publication even when the complete promotion plan already
/// exists.
#[test]
fn memo_advance_prepublication_cancellation_leaks_no_product() {
    let (mut memo, transition, before, after, old_keys) = memo_transition_fixture();
    let cancel = |checkpoint| {
        matches!(
            checkpoint,
            MemoAdvanceCheckpoint::BeforePublication { scanned: 2 }
        )
    };
    let outcome = memo.advance(
        &transition,
        &before,
        &after,
        MemoAdvanceBudget::generous(),
        Some(&cancel),
    );
    let Outcome::Inconclusive(inconclusive) = outcome else {
        panic!("the final cancellation sample must be inconclusive");
    };
    assert!(matches!(
        inconclusive.cause,
        InconclusiveCause::Cancelled { .. }
    ));
    assert_memo_was_not_advanced(&memo, &before, &after, &old_keys);
}
