//! The consensus seat, exercised with ZERO in-repo engines (bead `fln-uc44`).
//!
//! There is no second engine and no NbE in this workspace, and this file does
//! not pretend otherwise. It does not need one: every property the seat must
//! have is a property of the *mechanism*, and a planted seat verdict exercises
//! the mechanism exactly as a real witness would — because a real witness's
//! verdict is also just data it states.
//!
//! The negative tests are the load-bearing ones. A consensus mechanism that has
//! only ever been tested with agreeing seats has not been tested at all, and
//! the specific failure this file exists to catch is a seat that turns out to
//! be theatre: one whose disagreement is recorded and then ignored, or whose
//! agreement can be forged into a publication right.

#![forbid(unsafe_code)]

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::Outcome;
use fln_env::constants::{AxiomVal, ConstantVal};
use fln_env::environment::{DeclarationBudget, Environment};
use fln_env::pmap::CollisionBudget;
use fln_kernel::Declaration;
use fln_kernel::capability::{Admitted, Published, admit};
use fln_kernel::council::{Council, CouncilOutcome, Seat, SeatVerdict, convene};
use fln_kernel::verdict::Budget;

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn sort1() -> Expr {
    Expr::sort(Level::one())
}

/// `A : Sort 1` — a declaration the kernel accepts.
fn good_axiom(name: &str) -> Declaration {
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: sort1(),
        },
        is_unsafe: false,
    })
}

/// An axiom whose "type" is a bound variable — the kernel rejects this (KR-100:
/// kernel terms must be closed).
fn bad_axiom(name: &str) -> Declaration {
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::bvar(0).expect("bvar 0 packs"),
        },
        is_unsafe: false,
    })
}

fn admitted<'e>(env: &'e Environment, decl: Declaration) -> Admitted<'e> {
    // `Admitted` is deliberately not `Debug` — it carries the capability — so
    // the failure arms are named rather than formatted.
    match admit(env, decl, Budget::DEFAULT) {
        Outcome::Complete(a) => a,
        Outcome::Inconclusive(_) => panic!("admission was inconclusive; these fixtures are tiny"),
        Outcome::InternalFault(fault) => panic!("admission faulted: {fault:?}"),
    }
}

fn publish(checked: fln_kernel::capability::CheckedDecl<'_>) -> Published {
    match checked.publish(
        DeclarationBudget::default(),
        CollisionBudget::default(),
        None,
    ) {
        Outcome::Complete(published) => published,
        other => panic!("expected a completed publication, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// The negative half — the tests that decide whether the seat is real
// ---------------------------------------------------------------------------

/// A FORGED seat cannot publish.
///
/// A seat verdict is ordinary data, so a hostile or buggy caller can state
/// `Agrees` about anything at all. This proves that stating it grants nothing:
/// over a declaration the KERNEL rejects, a unanimously agreeing council still
/// produces no capability and publishes nothing.
///
/// The stronger half of this property is not expressible as a runtime test and
/// is enforced by the type system instead: there is no path from `SeatVerdict`
/// to `CheckedDecl`. `CheckedDecl` has a private field of a private type, no
/// constructor, no `Default`, no `From`, and no deserialisation, so the
/// following does not compile outside `fln-kernel`:
///
/// ```text
/// let forged = CheckedDecl { .. };            // error: fields are private
/// let forged: CheckedDecl = seat_verdict.into();  // error: no such impl
/// ```
#[test]
fn a_forged_seat_agreeing_about_a_rejected_declaration_publishes_nothing() {
    let env = Environment::new();
    let council = Council::of(vec![
        Seat::new("forged-a", SeatVerdict::Agrees),
        Seat::new("forged-b", SeatVerdict::Agrees),
    ]);

    match convene(&council, admitted(&env, bad_axiom("Forged"))) {
        CouncilOutcome::KernelRejected { .. } => {}
        CouncilOutcome::Agreed(_) => {
            panic!("forged agreement manufactured a publication right for a rejected declaration")
        }
        CouncilOutcome::Halted(halt) => {
            panic!(
                "expected the kernel's own rejection, got a council halt: {}",
                halt.summary()
            )
        }
    }
    assert!(
        env.find(&n("Forged")).is_none(),
        "nothing may be published when the kernel rejects, however many seats agree"
    );
}

/// A ONE-SEAT DISAGREEMENT halts, and is not outvoted.
///
/// Three seats agree and one dissents. If anything in the council counted, the
/// majority would carry. Nothing counts.
#[test]
fn one_dissenting_seat_halts_publication_and_is_never_outvoted() {
    let env = Environment::new();
    let council = Council::of(vec![
        Seat::new("engine-k1", SeatVerdict::Agrees),
        Seat::new("engine-k2", SeatVerdict::Agrees),
        Seat::new("fln-checker", SeatVerdict::Agrees),
        Seat::new(
            "leanchecker",
            SeatVerdict::Disagrees {
                detail: "foreign witness rejects at KR-303".into(),
            },
        ),
    ]);

    let halt = match convene(&council, admitted(&env, good_axiom("Contested"))) {
        CouncilOutcome::Halted(halt) => halt,
        CouncilOutcome::Agreed(_) => {
            panic!("three agreeing seats outvoted a dissenter; the seat is a vote, not a veto")
        }
        CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
    };

    // The halt must not be readable as the kernel having rejected.
    assert!(
        halt.kernel_accepted,
        "the kernel accepted; only a seat objected"
    );
    assert_eq!(halt.objections.len(), 1);
    assert_eq!(halt.objections[0].id.as_str(), "leanchecker");
    assert!(
        halt.summary().contains("foreign witness rejects at KR-303"),
        "the dissent's reason must survive onto the halt: {}",
        halt.summary()
    );
    assert!(
        env.find(&n("Contested")).is_none(),
        "a halted declaration must not reach the environment"
    );
}

/// AN ABSENT SEAT halts. A witness that did not run has not agreed.
///
/// This is the decay path that matters in practice: a lane that is skipped,
/// times out, or errors, and whose silence is read as assent. FL-INV-07 says a
/// non-answer is not an answer, and the council must not be the one place that
/// forgets it.
#[test]
fn an_absent_or_errored_seat_halts_rather_than_abstaining_into_a_pass() {
    let env = Environment::new();
    for reason in [
        "witness binary not present at the pin",
        "cancelled",
        "timed out after 30s",
        "lane skipped",
    ] {
        let council = Council::of(vec![
            Seat::new("engine-k1", SeatVerdict::Agrees),
            Seat::new(
                "leanchecker",
                SeatVerdict::NoAnswer {
                    reason: reason.into(),
                },
            ),
        ]);
        match convene(&council, admitted(&env, good_axiom("Silent"))) {
            CouncilOutcome::Halted(halt) => {
                assert_eq!(halt.objections.len(), 1, "reason={reason}");
                assert!(halt.summary().contains(reason), "{}", halt.summary());
            }
            CouncilOutcome::Agreed(_) => {
                panic!("a seat that did not answer was read as agreement (reason={reason})")
            }
            CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
        }
        assert!(env.find(&n("Silent")).is_none());
    }
}

/// EVERY objection is retained, in the order the seats were supplied, with its
/// reason intact. A halt that reports only the first objection, or that reorders
/// them, makes a multi-seat disagreement harder to investigate than a
/// single-seat one — and an uninvestigable disagreement is the one most likely
/// to be dismissed as noise.
///
/// The order is the supplied order and nothing else: no sorting by a
/// schedule-dependent key, no set iteration (FL-INV-01).
#[test]
fn every_objection_is_retained_in_order_with_its_reason() {
    let env = Environment::new();
    let council = Council::of(vec![
        Seat::new(
            "first-objector",
            SeatVerdict::Disagrees {
                detail: "rejects at KR-303".into(),
            },
        ),
        Seat::new("agreeing-seat", SeatVerdict::Agrees),
        Seat::new(
            "second-objector",
            SeatVerdict::NoAnswer {
                reason: "timed out".into(),
            },
        ),
    ]);

    let halt = match convene(&council, admitted(&env, good_axiom("Multi"))) {
        CouncilOutcome::Halted(halt) => halt,
        CouncilOutcome::Agreed(_) => panic!("two objections were ignored"),
        CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
    };

    assert_eq!(
        halt.objections.len(),
        2,
        "the agreeing seat is not an objection"
    );
    assert_eq!(halt.objections[0].id.as_str(), "first-objector");
    assert_eq!(halt.objections[1].id.as_str(), "second-objector");
    let summary = halt.summary();
    assert!(summary.contains("rejects at KR-303"), "{summary}");
    assert!(summary.contains("timed out"), "{summary}");
    assert!(env.find(&n("Multi")).is_none());
}

// ---------------------------------------------------------------------------
// The positive half — the mechanism must still let correct work through
// ---------------------------------------------------------------------------

/// Unanimous agreement publishes. A veto that blocks everything is as useless
/// as one that blocks nothing.
#[test]
fn a_unanimous_council_publishes() {
    let env = Environment::new();
    let council = Council::of(vec![
        Seat::new("engine-k1", SeatVerdict::Agrees),
        Seat::new("leanchecker", SeatVerdict::Agrees),
    ]);

    let checked = match convene(&council, admitted(&env, good_axiom("Agreed"))) {
        CouncilOutcome::Agreed(checked) => checked,
        CouncilOutcome::Halted(halt) => panic!("unanimous council halted: {}", halt.summary()),
        CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
    };
    assert!(matches!(publish(checked), Published::Committed(_)));
}

/// An empty council is the "nobody was asked" state and agrees vacuously. It is
/// spelled by name so a call site with no policy yet says so, rather than
/// looking like it consulted someone.
#[test]
fn an_empty_council_is_named_rather_than_defaulted() {
    let env = Environment::new();
    let checked = match convene(
        &Council::nobody_was_asked(),
        admitted(&env, good_axiom("Unwitnessed")),
    ) {
        CouncilOutcome::Agreed(checked) => checked,
        CouncilOutcome::Halted(halt) => panic!("empty council halted: {}", halt.summary()),
        CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
    };
    assert!(matches!(publish(checked), Published::Committed(_)));
}

/// The council is not consulted about a rejection, even when every seat
/// disagrees with the kernel. Asking seats to ratify a rejection would invite
/// the reading that enough agreement could overturn one.
#[test]
fn seats_cannot_overturn_a_kernel_rejection() {
    let env = Environment::new();
    let council = Council::of(vec![
        Seat::new("a", SeatVerdict::Agrees),
        Seat::new("b", SeatVerdict::Agrees),
        Seat::new("c", SeatVerdict::Agrees),
    ]);
    match convene(&council, admitted(&env, bad_axiom("Overruled"))) {
        CouncilOutcome::KernelRejected { .. } => {}
        other => panic!(
            "a kernel rejection must survive unanimous seat agreement, got {}",
            match other {
                CouncilOutcome::Agreed(_) => "Agreed",
                CouncilOutcome::Halted(_) => "Halted",
                CouncilOutcome::KernelRejected { .. } => unreachable!(),
            }
        ),
    }
    assert!(env.find(&n("Overruled")).is_none());
}
