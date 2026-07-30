//! The checked-declaration capability contract (bead `fln-yswb`; D6, FL-INV-02,
//! FL-INV-06).
//!
//! # What is under test
//!
//! `fln_kernel::check` returns a verdict whose `Accepted` arm carried only a
//! `Consumption`, while `fln_env::Environment::plan_add_decl` accepts a raw
//! `ConstantInfo`. Nothing connected them, so **checking declaration A and
//! publishing declaration B was representable**. An invariant that is merely
//! tested against is audited; this bead is about making it enforced.
//!
//! # Most of this contract is not testable at run time, and that is the point
//!
//! The strongest properties here are compile-time: they are the programs that
//! do NOT compile. A run-time test can only observe that a forged capability
//! was rejected — it cannot observe that forging one is inexpressible. So the
//! refusals are recorded as commented programs beside the test that exercises
//! the legitimate path, and `the_capability_has_no_public_constructor_surface`
//! pins the API shape those refusals depend on.
//!
//! Each entry names the mutant it corresponds to from the bead's list.

#![forbid(unsafe_code)]

use std::cell::Cell;

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, OpaqueVal,
    ReducibilityHints,
};
use fln_env::environment::{
    DeclarationBudget, DeclarationCommitted, Environment, preflight_declaration,
};
use fln_env::modules::CancellationProbe;
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Admitted, Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, convene};
use fln_kernel::verdict::Budget;

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn sort1() -> Expr {
    Expr::sort(Level::one())
}

fn axiom(name: &str, type_: Expr) -> Declaration {
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        is_unsafe: false,
    })
}

struct TripAfter {
    remaining: Cell<usize>,
    samples: Cell<usize>,
}

impl TripAfter {
    fn new(remaining: usize) -> Self {
        Self {
            remaining: Cell::new(remaining),
            samples: Cell::new(0),
        }
    }
}

impl CancellationProbe for TripAfter {
    fn is_cancelled(&self) -> bool {
        self.samples.set(self.samples.get() + 1);
        let remaining = self.remaining.get();
        if remaining == 0 {
            true
        } else {
            self.remaining.set(remaining - 1);
            false
        }
    }
}

fn accepted<'e>(
    env: &'e Environment,
    decl: Declaration,
) -> fln_kernel::capability::CheckedDecl<'e> {
    match admit(env, decl, Budget::DEFAULT) {
        // Through the council, because there is no other way (bead `fln-glml`).
        // `Admitted::Accepted` carries a `Reviewable`, which has no `publish`
        // and no route to a `CheckedDecl` outside `fln-kernel`; the empty
        // council is the honest answer for these fixtures and now has to be
        // SPELLED rather than skipped.
        Outcome::Complete(admitted) => match convene(&Council::nobody_was_asked(), admitted) {
            CouncilOutcome::Agreed(checked) => checked,
            CouncilOutcome::KernelRejected { class, .. } => {
                panic!("expected an accepted admission, got rejected {class:?}")
            }
            CouncilOutcome::Halted(halt) => {
                panic!(
                    "an empty council cannot object, yet it halted: {}",
                    halt.summary()
                )
            }
        },
        Outcome::Inconclusive(_) => panic!("expected an accepted admission, got inconclusive"),
        Outcome::InternalFault(fault) => panic!("admission faulted: {fault:?}"),
    }
}

// ---------------------------------------------------------------------------
// The legitimate path still works
// ---------------------------------------------------------------------------

#[test]
fn an_accepted_declaration_publishes_through_its_capability() {
    // Without this the refusals below could all be passing because nothing
    // works at all, which is the cheapest way to make a capability look sound.
    let env = Environment::new();
    let cap = accepted(&env, axiom("A", sort1()));
    assert!(cap.name().is_some());
    assert!(
        cap.consumption().steps_used > 0,
        "a real check was performed"
    );
    match cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
            // The new environment really did gain the constant.
            assert!(p.environment.find(&n("A")).is_some());
        }
        other => panic!("a legitimate publication did not commit: {other:?}"),
    }
    // And the base is untouched: publication returns a NEW environment rather
    // than mutating the one that was checked against.
    assert!(env.find(&n("A")).is_none(), "the base was mutated in place");
}

#[test]
fn an_accepted_opaque_publishes_as_the_exact_opaque_that_was_checked() {
    let env = Environment::new();
    let opaque = Declaration::Opaque(OpaqueVal {
        base: ConstantVal {
            name: n("Sealed"),
            level_params: vec![],
            type_: sort1(),
        },
        value: Expr::sort(Level::zero()),
        is_unsafe: false,
        all: vec![n("Sealed")],
    });
    let cap = accepted(&env, opaque);
    assert_eq!(cap.name(), Some(&n("Sealed")));
    match cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
            assert!(
                matches!(
                    p.environment.find(&n("Sealed")),
                    Some(ConstantInfo::Opaque(value))
                        if value.value == Expr::sort(Level::zero())
                ),
                "the checked opaque must retain its opaque kind and exact body"
            );
        }
        other => panic!("an accepted opaque did not publish: {other:?}"),
    }
    assert!(
        env.find(&n("Sealed")).is_none(),
        "opaque publication mutated its checked base"
    );
}

// ---------------------------------------------------------------------------
// MUTANT: check A, publish B
// ---------------------------------------------------------------------------

#[test]
fn the_capability_carries_the_declaration_that_was_checked() {
    // `publish` takes no declaration parameter, so there is nothing to
    // substitute. This test pins the consequence: what lands is what was
    // checked, by name.
    let env = Environment::new();
    let cap = accepted(&env, axiom("Checked", sort1()));
    assert_eq!(cap.name(), Some(&n("Checked")));
    match cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
            assert!(p.environment.find(&n("Checked")).is_some());
            assert!(
                p.environment.find(&n("Substituted")).is_none(),
                "a declaration nobody checked reached the environment"
            );
        }
        other => panic!("unexpected: {other:?}"),
    }

    // MUTANT `check-A-publish-B`, refused at compile time. There is no
    // signature that accepts a second declaration:
    //
    //   cap.publish(axiom("Substituted", sort1()), ..)   // too many arguments
    //
    // and the field holding the checked declaration is private, so it cannot be
    // overwritten either:
    //
    //   cap.decl = axiom("Substituted", sort1());        // field `decl` is private
}

// ---------------------------------------------------------------------------
// MUTANT: forged capability
// ---------------------------------------------------------------------------

#[test]
fn the_capability_has_no_public_constructor_surface() {
    // MUTANT `forged capability`, refused at compile time. Every field is
    // private and one has a private TYPE (`Seal`) that no other crate can name,
    // so none of these compiles from outside `fln-kernel`:
    //
    //   CheckedDecl { base: &env, decl, consumption, _seal: Seal }
    //       // error: fields `base`, `decl`, `consumption`, `_seal` are private
    //       // error: cannot find type `Seal` in this scope
    //
    //   CheckedDecl::default()      // no Default impl
    //   CheckedDecl::from(decl)     // no From impl
    //
    // This test pins the shape those refusals rest on: the ONLY way to obtain
    // one is `admit`, and it is reachable.
    let env = Environment::new();
    let cap = accepted(&env, axiom("Only", sort1()));
    let _ = cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    );
}

// ---------------------------------------------------------------------------
// MUTANTS: rejection, inconclusive, internal fault cannot inhabit it
// ---------------------------------------------------------------------------

#[test]
fn a_rejected_declaration_yields_no_capability() {
    // `Prop`-typed value where a sort is required: a real rejection.
    let env = Environment::new();
    let bad = Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n("Bad"),
            level_params: vec![],
            // A bound variable with no binder is not a type.
            type_: Expr::bvar(0).expect("a loose bvar is representable"),
        },
        is_unsafe: false,
    });
    match admit(&env, bad, Budget::DEFAULT) {
        Outcome::Complete(Admitted::Rejected { .. }) => {}
        Outcome::Complete(Admitted::Accepted(_)) => {
            panic!("a rejected declaration minted a publication capability")
        }
        // A non-answer is equally acceptable here; what must NOT happen is a
        // capability.
        Outcome::Inconclusive(_) | Outcome::InternalFault(_) => {}
    }
    // MUTANT `InternalFault`: the `Admitted` enum has no arm carrying a
    // capability alongside a fault, and `admit` propagates
    // Inconclusive/InternalFault unchanged. There is no expression that turns
    // either into a `CheckedDecl`:
    //
    //   let cap: CheckedDecl = Outcome::InternalFault(f).into();  // no From impl
}

/// PLANTED VIOLATION — publishing without naming a council does not compile
/// (bead `fln-glml`).
///
/// This one is a compile-fail rather than a runtime test, and that is the
/// point rather than a shortcut: a funnel enforced by the type system has no
/// runtime behaviour to assert. There is no value of the bypassing program for
/// a test to inspect, because the program does not exist.
///
/// What the bead found, and what this pins shut: `admit` used to hand back the
/// `CheckedDecl` itself, so publishing without convening was a matter of simply
/// not calling `convene` — and the one production publisher in the tree,
/// `fln_verdict::reflection`, did exactly that. Nothing misbehaved, because an
/// empty council agrees vacuously; the defect was that "policy decided nobody
/// was asked" and "nobody thought to ask" were the same program.
///
/// Each of the following is refused by the compiler today. The first two were
/// the actual bypass; the rest are the obvious ways around it.
///
/// ```text
/// let Outcome::Complete(Admitted::Accepted(r)) = admit(&env, decl, budget);
/// r.publish(..);              // error: no method `publish` on `Reviewable`
/// let checked: CheckedDecl = r.into_checked();   // error: `into_checked` is
///                                                // private to fln-kernel
/// let checked: CheckedDecl = *r;                 // error: cannot dereference
/// let checked = CheckedDecl { .. };              // error: fields are private
/// ```
///
/// The empty council remains legal and remains vacuous. What it no longer is,
/// is omissible: `Council::nobody_was_asked()` has to be written down, which is
/// what makes a later audit of publication sites a `rg` rather than a reading.
///
/// The runtime half of the same property — that convening with objections
/// yields no capability at all — is `tests/consensus_seat.rs`, which is where
/// the seat's own behaviour is exercised.
#[test]
fn publishing_without_naming_a_council_is_not_expressible() {
    // The positive half, so this test is not purely a comment: the legitimate
    // route works and is the ONLY route. `accepted()` above goes through
    // `convene`, because there is no other way to obtain the value it returns.
    let env = Environment::new();
    let cap = accepted(&env, axiom("Funnelled", sort1()));
    match cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::Committed(DeclarationCommitted::Published(p))) => {
            // The NEW environment gained it. `env` is untouched — publication
            // returns a fresh environment rather than mutating the base, which
            // is what keeps a capability from being replayed against a base
            // that moved under it.
            assert!(p.environment.find(&n("Funnelled")).is_some());
            assert!(env.find(&n("Funnelled")).is_none());
        }
        other => panic!("the only route to publication did not commit: {other:?}"),
    }
}

#[test]
fn an_exhausted_budget_yields_no_capability() {
    // MUTANT `exhaustion`. A budget too small to complete the check must
    // produce a non-answer, never a capability — FL-INV-07 says resource
    // exhaustion is never promoted to acceptance, and here it additionally
    // cannot be promoted to a publication right.
    let env = Environment::new();
    let starved = Budget::DEFAULT.narrowed(0, Budget::DEFAULT.depth);
    if let Outcome::Complete(Admitted::Accepted(_)) =
        admit(&env, axiom("Starved", sort1()), starved)
    {
        panic!("an exhausted check minted a publication capability");
    }
}

// ---------------------------------------------------------------------------
// MUTANTS: replay, stale base, substitution of the base
// ---------------------------------------------------------------------------

#[test]
fn publication_consumes_the_capability_exactly_once() {
    let env = Environment::new();
    let cap = accepted(&env, axiom("Once", sort1()));
    let _first = cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    );

    // MUTANT `replay`, refused at compile time. `publish` takes `self` by value
    // and `CheckedDecl` is deliberately neither `Clone` nor `Copy`:
    //
    //   let second = cap.publish(..);   // error: use of moved value `cap`
    //   let copy = cap.clone();         // error: no method named `clone`
    //
    // A second publication from one check is a use-after-move, not a run-time
    // check that could be forgotten.
}

#[test]
fn the_base_environment_cannot_be_substituted_or_moved() {
    // MUTANT `stale base`. `publish` takes NO environment parameter — it
    // publishes into the base it borrowed — so there is no argument to get
    // wrong:
    //
    //   cap.publish(&other_env, ..);    // too many arguments
    //
    // and the borrow prevents the base being moved or mutated while the
    // capability is alive:
    //
    //   let cap = accepted(&env, decl);
    //   drop(env);                      // error: cannot move out of `env`
    //   cap.publish(..);                //        because it is borrowed
    //
    // This test pins the observable half: two capabilities against two
    // different bases publish into their own bases and do not cross.
    let env_a = Environment::new();
    let env_b = Environment::new();
    let cap_a = accepted(&env_a, axiom("InA", sort1()));
    let cap_b = accepted(&env_b, axiom("InB", sort1()));
    let a = cap_a.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    );
    let b = cap_b.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    );
    match (a, b) {
        (
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(pa))),
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(pb))),
        ) => {
            assert!(pa.environment.find(&n("InA")).is_some());
            assert!(pa.environment.find(&n("InB")).is_none());
            assert!(pb.environment.find(&n("InB")).is_some());
            assert!(pb.environment.find(&n("InA")).is_none());
        }
        other => panic!("unexpected: {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Blocks publish as one failure-atomic capability transition
// ---------------------------------------------------------------------------

#[test]
fn an_accepted_mutual_block_publishes_every_member_and_only_the_final_environment() {
    let env = Environment::new();
    let names = vec![n("mutualA"), n("mutualB")];
    let member = |name: &str| DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: sort1(),
        },
        value: Expr::sort(Level::zero()),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Partial,
        all: names.clone(),
    };
    let a = member("mutualA");
    let b = member("mutualB");
    let cap = accepted(&env, Declaration::Mutual(vec![a.clone(), b.clone()]));
    assert_eq!(cap.name(), None, "a block has no single publication name");

    match cap.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::BlockCommitted(publication)) => {
            assert_eq!(publication.names, names);
            assert_eq!(
                publication.environment.find(&n("mutualA")),
                Some(&ConstantInfo::Defn(a))
            );
            assert_eq!(
                publication.environment.find(&n("mutualB")),
                Some(&ConstantInfo::Defn(b))
            );
        }
        other => panic!("an accepted mutual block did not publish atomically: {other:?}"),
    }
    assert!(
        env.find(&n("mutualA")).is_none() && env.find(&n("mutualB")).is_none(),
        "block publication must leave the checked base untouched"
    );
}

#[test]
fn a_one_member_mutual_declaration_remains_a_block_publication() {
    let env = Environment::new();
    let only = DefinitionVal {
        base: ConstantVal {
            name: n("onlyMutualMember"),
            level_params: vec![],
            type_: sort1(),
        },
        value: Expr::sort(Level::zero()),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Partial,
        all: vec![n("onlyMutualMember")],
    };
    let cap = accepted(&env, Declaration::Mutual(vec![only]));
    match cap.publish(
        DeclarationBudget::UNBOUNDED,
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::BlockCommitted(publication)) => {
            assert_eq!(publication.names, vec![n("onlyMutualMember")]);
            assert!(
                publication
                    .environment
                    .find(&n("onlyMutualMember"))
                    .is_some()
            );
        }
        other => panic!("a one-member mutual declaration lost block atomicity: {other:?}"),
    }
}

#[test]
fn a_late_block_admission_stop_exposes_no_prefix_and_a_clean_retry_recovers() {
    let env = Environment::new();
    let first_name = n("a");
    let second_name = n("secondMemberWhoseLongNameMakesItsCanonicalRowLarger");
    let names = vec![first_name.clone(), second_name.clone()];
    let member = |name: &str| DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: sort1(),
        },
        value: Expr::sort(Level::zero()),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Partial,
        all: names.clone(),
    };
    let first = member("a");
    let second = member("secondMemberWhoseLongNameMakesItsCanonicalRowLarger");
    let first_info = ConstantInfo::Defn(first.clone());
    let second_info = ConstantInfo::Defn(second.clone());
    let Outcome::Complete(first_usage) =
        preflight_declaration(&first_info, DeclarationBudget::UNBOUNDED, None)
    else {
        panic!("the first fixture must have a measurable declaration row");
    };
    let Outcome::Complete(second_usage) =
        preflight_declaration(&second_info, DeclarationBudget::UNBOUNDED, None)
    else {
        panic!("the second fixture must have a measurable declaration row");
    };
    assert!(
        second_usage.canonical_bytes > first_usage.canonical_bytes,
        "the stop fixture must pass one member before the larger second member"
    );
    let stops_on_second = DeclarationBudget {
        max_canonical_bytes: first_usage.canonical_bytes,
        ..DeclarationBudget::UNBOUNDED
    };
    let cap = accepted(
        &env,
        Declaration::Mutual(vec![first.clone(), second.clone()]),
    );
    assert!(matches!(
        cap.publish(stops_on_second, CollisionBudget::default(), None,),
        Outcome::Inconclusive(_)
    ));
    assert!(
        env.find(&first_name).is_none() && env.find(&second_name).is_none(),
        "a stop after staging the first member must expose no accepted prefix"
    );

    let retry = accepted(&env, Declaration::Mutual(vec![first, second]));
    match retry.publish(
        DeclarationBudget::UNBOUNDED,
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(Published::BlockCommitted(publication)) => {
            assert_eq!(publication.names, names);
            assert!(
                publication
                    .names
                    .iter()
                    .all(|name| publication.environment.find(name).is_some())
            );
        }
        other => panic!("an unbounded clean retry did not publish the whole block: {other:?}"),
    }
}

#[test]
fn cancellation_after_one_staged_member_exposes_no_prefix() {
    let env = Environment::new();
    let first_name = n("cancelA");
    let second_name = n("cancelB");
    let names = vec![first_name.clone(), second_name.clone()];
    let member = |name: &str| DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: sort1(),
        },
        value: Expr::sort(Level::zero()),
        hints: ReducibilityHints::Regular(1),
        safety: DefinitionSafety::Partial,
        all: names.clone(),
    };
    let cap = accepted(
        &env,
        Declaration::Mutual(vec![member("cancelA"), member("cancelB")]),
    );
    // One definition samples before its type, before its body, and before its
    // staged publication. The fourth sample is therefore inside member two.
    let cancellation = TripAfter::new(3);
    assert!(matches!(
        cap.publish(
            DeclarationBudget::UNBOUNDED,
            CollisionBudget::default(),
            Some(&cancellation),
        ),
        Outcome::Inconclusive(_)
    ));
    assert_eq!(
        cancellation.samples.get(),
        4,
        "the fixture must stop after one complete staged member"
    );
    assert!(
        env.find(&first_name).is_none() && env.find(&second_name).is_none(),
        "cancellation during member two must expose no member-one prefix"
    );
}
