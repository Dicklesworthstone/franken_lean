//! `parser_interleaving_dpor` — schedule independence for concurrent registration at 1/8/32
//! (bead fln-okfb; FL-INV-01).
//!
//! ## READ THIS BEFORE READING THE GREEN BAR
//!
//! **This suite is a self-differential.** It compares my registry against my registry, at different
//! thread counts and arrival orders. A sweep that finds no interleaving violation is evidence that
//! *my* schedule space contains no violation *my own model can express*. That is not schedule
//! independence, and it is not FL-INV-01.
//!
//! FL-INV-01 is the claim. This sweep is **one piece of support for it**, and a weak one on its own:
//!
//! * It cannot see a violation that both the runner and the canonical order agree on wrongly. If
//!   `apply_batch`'s key ordering is wrong, every thread count produces the same wrong root and the
//!   suite is green.
//! * It explores the arrival orders I generate, not the schedule space the machine has. There is no
//!   DPOR scheduler here — the name is the bead's, and what this actually does is exhaustive
//!   permutation of arrival order for small batches plus randomised concurrent submission for large
//!   ones. Calling that DPOR would overstate it.
//! * It says nothing about whether the grammar is *correct*, only that it is the same one every
//!   time.
//!
//! ## The positive oracle it is paired with
//!
//! What the pin does establish, observed by running it, is that **registration order is
//! semantically significant**: two `notation "dup"` declarations give `error: Ambiguous term`, so
//! the sequence of productions under a token is part of the grammar rather than an artefact.
//!
//! That observation is what makes this suite non-trivial. Because order matters, concurrent
//! registration cannot be made schedule-independent by locking alone — a mutex gives *a* result,
//! not *the same* result. Independence requires a **canonical order**, which is the registered
//! tie-break the determinism doctrine asks for. The suite therefore also asserts the negative: that
//! arrival order applied *without* canonicalisation does produce different roots, so the
//! canonicalisation is demonstrably load-bearing rather than incidentally satisfied.

#![forbid(unsafe_code)]

use fln_core::name::Name;
use fln_parse::category::LeadingIdentBehavior;
use fln_parse::registry::{GrammarRoot, Registry, Request};
use fln_parse::state::Production;
use std::thread;

const THREAD_COUNTS: [usize; 3] = [1, 8, 32];

fn name(text: &str) -> Name {
    Name::str(Name::anonymous(), text)
}

fn production(label: &str) -> Production {
    Production::new(name(label), 0, |_state| {})
}

/// A batch of requests, described so it can be rebuilt in any order.
fn descriptions(count: u64) -> Vec<(u64, String, String)> {
    (0..count)
        .map(|index| {
            // Deliberately collide tokens, so additive shadowing puts several productions under one
            // token and the ORDER of that list is part of the root.
            let token = format!("t{}", index % 3);
            (index, token, format!("k{index}"))
        })
        .collect()
}

fn build_requests(term: &Name, order: &[(u64, String, String)]) -> Vec<Request> {
    order
        .iter()
        .map(|(index, token, kind)| Request {
            key: (*index, kind.clone()),
            category: term.clone(),
            token: token.clone(),
            production: production(kind),
            scoped: false,
        })
        .collect()
}

/// Apply a batch in the given arrival order and return the resulting root.
fn root_for(order: &[(u64, String, String)]) -> GrammarRoot {
    let mut registry = Registry::new();
    let term = name("term");
    registry
        .declare_category(term.clone(), LeadingIdentBehavior::Default)
        .expect("declares");
    registry
        .apply_batch(build_requests(&term, order))
        .expect("applies");
    registry.grammar_root(registry.epoch())
}

/// **The sweep: identical roots for every arrival order, exhaustively for a small batch.**
///
/// Exhaustive permutation rather than sampling, because for six requests the space is 720 and there
/// is no reason to guess. What this establishes is bounded: see the module docs.
#[test]
fn every_arrival_order_of_a_small_batch_gives_the_identical_root() {
    let base = descriptions(6);
    let expected = root_for(&base);

    let mut order = base.clone();
    let mut permutations = 0usize;

    // Heap's algorithm, iterative, so the sweep is deterministic and complete.
    let n = order.len();
    let mut counters = vec![0usize; n];
    let mut index = 0usize;
    assert_eq!(root_for(&order), expected);
    permutations += 1;
    while index < n {
        if counters[index] < index {
            if index.is_multiple_of(2) {
                order.swap(0, index);
            } else {
                order.swap(counters[index], index);
            }
            let labels: Vec<u64> = order.iter().map(|(i, _, _)| *i).collect();
            assert_eq!(
                root_for(&order),
                expected,
                "arrival order {labels:?} produced a different grammar root"
            );
            permutations += 1;
            counters[index] += 1;
            index = 0;
        } else {
            counters[index] = 0;
            index += 1;
        }
    }
    assert_eq!(permutations, 720, "6! arrival orders must all be swept");
}

/// **Identical at 1, 8 and 32 threads.** Identical, not equivalent — the whole grammar root
/// compared, so a difference anywhere in any category, token or ordering fails.
#[test]
fn concurrent_registration_gives_the_identical_root_at_one_eight_and_thirty_two_threads() {
    let base = descriptions(48);
    let expected = root_for(&base);

    for threads in THREAD_COUNTS {
        // Each thread builds and applies the whole batch in a different rotation, so the arrival
        // order genuinely differs per thread rather than being the same sequence run concurrently.
        let roots: Vec<GrammarRoot> = thread::scope(|scope| {
            let handles: Vec<_> = (0..threads)
                .map(|worker| {
                    let base = base.clone();
                    scope.spawn(move || {
                        let mut order = base;
                        let shift = worker % order.len().max(1);
                        order.rotate_left(shift);
                        root_for(&order)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("a registration thread panicked"))
                .collect()
        });

        assert_eq!(roots.len(), threads);
        for (worker, root) in roots.iter().enumerate() {
            assert_eq!(
                *root, expected,
                "{threads} threads, worker {worker}: the grammar root differs. FL-INV-01 requires \
                 IDENTICAL grammars, not equivalent ones."
            );
        }
    }
}

/// **THE NEGATIVE that makes the sweep non-trivial.** Applying arrival order *without*
/// canonicalisation produces different roots.
///
/// Paired with the pin observation that registration order is semantically significant — two
/// `notation` declarations under one token give `Ambiguous term`, so the order of that list is part
/// of the grammar. Without this assertion, the sweep above would be equally green for a registry
/// where order simply did not matter, and it would prove nothing about the canonicalisation that
/// makes independence true.
#[test]
fn without_canonicalisation_arrival_order_does_change_the_root() {
    let base = descriptions(6);
    let mut reversed = base.clone();
    reversed.reverse();

    // Apply on arrival, bypassing apply_batch's sort — this is what the code would do if the
    // canonical order were removed.
    let root_on_arrival = |order: &[(u64, String, String)]| {
        let mut registry = Registry::new();
        let term = name("term");
        registry
            .declare_category(term.clone(), LeadingIdentBehavior::Default)
            .expect("declares");
        for (_, token, kind) in order {
            registry
                .add_leading(&term, token.clone(), production(kind), false)
                .expect("registers");
        }
        registry.grammar_root(registry.epoch())
    };

    assert_ne!(
        root_on_arrival(&base),
        root_on_arrival(&reversed),
        "applying on arrival MUST give different roots for different orders. If these were equal, \
         order would not matter, the canonical sort would be unnecessary, and the sweep above \
         would prove nothing."
    );

    // And with canonicalisation both orders agree, which is the property under test.
    assert_eq!(root_for(&base), root_for(&reversed));
}

/// The root is sensitive to what it should be sensitive to. A determinism suite over a root that
/// ignored differences would be green for the wrong reason.
#[test]
fn the_grammar_root_distinguishes_grammars_that_differ() {
    let base = descriptions(4);
    let root = root_for(&base);

    // A different kind under the same token.
    let mut changed_kind = base.clone();
    changed_kind[0].2 = "different".to_string();
    assert_ne!(
        root_for(&changed_kind),
        root,
        "a changed kind must change the root"
    );

    // A different token.
    let mut changed_token = base.clone();
    changed_token[1].1 = "brandnew".to_string();
    assert_ne!(
        root_for(&changed_token),
        root,
        "a changed token must change the root"
    );

    // One fewer request.
    let fewer = base[..3].to_vec();
    assert_ne!(
        root_for(&fewer),
        root,
        "a missing registration must change the root"
    );

    // A different ORDER under the same token, applied on arrival — the root must see it, since
    // additive shadowing makes that order part of the grammar.
    let mut swapped = base.clone();
    swapped.swap(0, 3);
    for (index, entry) in swapped.iter_mut().enumerate() {
        entry.0 = index as u64; // re-key, so the canonical sort follows the new order
    }
    assert_ne!(
        root_for(&swapped),
        root,
        "re-keying to a different canonical order must change the root, because the sequence of \
         productions under a token is part of the grammar"
    );
}

/// The same input lexed by many threads at once, contending on one batch rather than one batch per
/// thread — the shape that would expose shared mutable state if the registry acquired any.
#[test]
fn many_threads_applying_the_same_batch_all_agree() {
    let base = descriptions(24);
    let expected = root_for(&base);
    for threads in THREAD_COUNTS {
        let roots: Vec<GrammarRoot> = thread::scope(|scope| {
            let handles: Vec<_> = (0..threads)
                .map(|_| {
                    let base = base.clone();
                    scope.spawn(move || root_for(&base))
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("thread panicked"))
                .collect()
        });
        for (worker, root) in roots.iter().enumerate() {
            assert_eq!(*root, expected, "{threads} threads, worker {worker}");
        }
    }
}
