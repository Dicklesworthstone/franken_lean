//! The consensus seat, exercised with ZERO in-repo engines (beads `fln-uc44`
//! and `franken_lean-4o3n`).
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
//!
//! The second half of the file is the budget-parity boundary. Its planted
//! violations are the ones that matter *before* a second engine exists, because
//! the pressure on this seat will not arrive as a forged agreement — it will
//! arrive as a flood of resource halts and a competent argument that they are
//! noise. See `tests/budget_parity.rs` for the bound-level half.

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
use fln_kernel::council::{
    Council, CouncilOutcome, Incomparability, ObjectionKind, Seat, SeatBounds, SeatOrigin,
    SeatVerdict, convene,
};
use fln_kernel::verdict::{
    Bound, Budget, ComparabilityDefect, EngineId, ExecConfig, Profile, StackMeasurement,
};

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
// Seat bound fixtures
// ---------------------------------------------------------------------------

/// A second engine that has done the work bead `franken_lean-4o3n` requires: it
/// measured its OWN frames in the configuration it actually runs in. This is
/// what a seat's bounds look like when they can be compared with the kernel's.
fn measured_here(engine: &'static str) -> SeatBounds {
    SeatBounds::Derived(Budget::derive(
        StackMeasurement::measured(
            EngineId::named(engine),
            ExecConfig::current(),
            1_500,
            StackMeasurement::K1_ENTRY_RESERVE_BYTES,
            StackMeasurement::K1_SAFETY_FACTOR,
        ),
        ExecConfig::current(),
        16 * 1024 * 1024,
        Budget::DEFAULT_STEPS,
    ))
}

/// A second engine whose ceiling was derived in the profile this build is NOT.
/// Its `depth` is a number of the same kind as the kernel's and a resource of a
/// different kind — the 9.3x gap measured in `franken_lean-kxbj`.
fn measured_in_the_other_profile(engine: &'static str) -> SeatBounds {
    let elsewhere = ExecConfig::of(
        match Profile::current() {
            Profile::Dev => Profile::Release,
            Profile::Release => Profile::Dev,
        },
        ExecConfig::current().arch,
        ExecConfig::current().os,
    );
    SeatBounds::Derived(Budget::derive(
        StackMeasurement::measured(
            EngineId::named(engine),
            elsewhere,
            1_500,
            StackMeasurement::K1_ENTRY_RESERVE_BYTES,
            StackMeasurement::K1_SAFETY_FACTOR,
        ),
        elsewhere,
        16 * 1024 * 1024,
        Budget::DEFAULT_STEPS,
    ))
}

/// An external process with no bound this process derived.
fn unmeasured_subprocess() -> SeatBounds {
    SeatBounds::not_established("subprocess witness; wall clock only")
}

fn synthetic_seat(id: &'static str, bounds: SeatBounds, verdict: SeatVerdict) -> Seat {
    Seat::new(id, SeatOrigin::SyntheticFixture, bounds, verdict)
}

fn engine_seat(id: &'static str, bounds: SeatBounds, verdict: SeatVerdict) -> Seat {
    Seat::new(id, SeatOrigin::FrankenLeanEngine, bounds, verdict)
}

fn independent_seat(id: &'static str, bounds: SeatBounds, verdict: SeatVerdict) -> Seat {
    Seat::new(id, SeatOrigin::IndependentImplementation, bounds, verdict)
}

fn reference_oracle_seat(id: &'static str, bounds: SeatBounds, verdict: SeatVerdict) -> Seat {
    Seat::new(id, SeatOrigin::ReferenceKernelOracle, bounds, verdict)
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
        synthetic_seat("forged-a", unmeasured_subprocess(), SeatVerdict::Agrees),
        synthetic_seat("forged-b", unmeasured_subprocess(), SeatVerdict::Agrees),
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
        engine_seat("engine-k2", measured_here("test/k2"), SeatVerdict::Agrees),
        engine_seat("engine-k3", measured_here("test/k3"), SeatVerdict::Agrees),
        independent_seat("fln-checker", unmeasured_subprocess(), SeatVerdict::Agrees),
        reference_oracle_seat(
            "leanchecker",
            unmeasured_subprocess(),
            SeatVerdict::Disagrees {
                detail: "Reference kernel oracle rejects at KR-303".into(),
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
    assert_eq!(halt.objections[0].origin, SeatOrigin::ReferenceKernelOracle);
    assert!(
        halt.summary()
            .contains("Reference kernel oracle rejects at KR-303"),
        "the dissent's reason must survive onto the halt: {}",
        halt.summary()
    );
    assert!(
        halt.summary()
            .contains("leanchecker[reference_kernel_oracle]"),
        "the halt summary must retain the origin classification: {}",
        halt.summary()
    );
    assert!(
        !halt.is_purely_resource(),
        "a disagreement is evidence about the declaration and must never be classed as noise"
    );
    assert!(
        env.find(&n("Contested")).is_none(),
        "a halted declaration must not reach the environment"
    );
}

/// Running the Reference kernel in a second process is a second execution, not
/// a second semantic implementation.
///
/// The planted defect this catches is collapsing both origins into one
/// "external witness" bucket and then counting `leanchecker` as independent.
#[test]
fn reference_kernel_reexecution_does_not_count_as_an_independent_implementation() {
    let council = Council::of(vec![
        reference_oracle_seat("leanchecker", unmeasured_subprocess(), SeatVerdict::Agrees),
        independent_seat("fln-checker", unmeasured_subprocess(), SeatVerdict::Agrees),
    ]);

    assert!(council.has_reference_kernel_oracle());
    assert!(council.has_independent_implementation());
    assert!(
        !council.seats()[0].origin.is_independent_implementation(),
        "ReferenceKernelOracle must never supply independent corroboration"
    );
    assert!(
        council.seats()[1].origin.is_independent_implementation(),
        "the independent checker control keeps the test discriminating"
    );

    let reference_only = Council::of(vec![reference_oracle_seat(
        "leanchecker",
        unmeasured_subprocess(),
        SeatVerdict::Agrees,
    )]);
    assert!(reference_only.has_reference_kernel_oracle());
    assert!(
        !reference_only.has_independent_implementation(),
        "a Reference-only council has zero independent implementations"
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
            engine_seat("engine-k2", measured_here("test/k2"), SeatVerdict::Agrees),
            reference_oracle_seat(
                "leanchecker",
                unmeasured_subprocess(),
                SeatVerdict::NoAnswer {
                    reason: reason.into(),
                },
            ),
        ]);
        match convene(&council, admitted(&env, good_axiom("Silent"))) {
            CouncilOutcome::Halted(halt) => {
                assert_eq!(halt.objections.len(), 1, "reason={reason}");
                assert!(halt.summary().contains(reason), "{}", halt.summary());
                assert_eq!(halt.classify()[0].1, ObjectionKind::Silence);
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
        synthetic_seat(
            "first-objector",
            unmeasured_subprocess(),
            SeatVerdict::Disagrees {
                detail: "rejects at KR-303".into(),
            },
        ),
        synthetic_seat(
            "agreeing-seat",
            unmeasured_subprocess(),
            SeatVerdict::Agrees,
        ),
        synthetic_seat(
            "second-objector",
            unmeasured_subprocess(),
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
// Budget parity — the planted violations that need no second engine
// ---------------------------------------------------------------------------

/// A BUDGET-INDUCED STOP IS NEVER SILENTLY EQUATED WITH AGREEMENT.
///
/// The failure this prevents, stated plainly: a second engine under a bound
/// asymmetric to the kernel's cannot finish some declarations, every one of
/// those becomes a halt, and someone proposes reading the engine's inconclusive
/// as assent because the halts are noise. The halt below stays a halt, publishes
/// nothing, and — this is the part that survives the argument — is *typed* as a
/// resource stop rather than as a disagreement, so the noise can be reported
/// honestly instead of laundered.
#[test]
fn a_budget_induced_stop_halts_and_is_typed_as_exhaustion_not_agreement() {
    let env = Environment::new();
    for bound in [
        Bound::Depth,
        Bound::Steps,
        Bound::Other("wall clock".into()),
    ] {
        let council = Council::of(vec![
            engine_seat("engine-k2", measured_here("test/k2"), SeatVerdict::Agrees),
            engine_seat(
                "engine-k3",
                measured_here("test/k3"),
                SeatVerdict::Exhausted {
                    bound: bound.clone(),
                },
            ),
        ]);

        let halt = match convene(&council, admitted(&env, good_axiom("Starved"))) {
            CouncilOutcome::Halted(halt) => halt,
            CouncilOutcome::Agreed(_) => {
                panic!("a seat that ran out of {bound:?} was read as agreement")
            }
            CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
        };

        let classified = halt.classify();
        assert_eq!(classified.len(), 1);
        assert_eq!(
            classified[0].1,
            ObjectionKind::Exhaustion {
                bound: bound.clone()
            },
            "a comparable resource stop must be typed as exhaustion, and never as a \
             disagreement: {}",
            halt.summary()
        );
        assert!(
            halt.is_purely_resource(),
            "nothing here is evidence about the declaration, and saying so is the honest \
             half of the concession"
        );
        assert!(
            env.find(&n("Starved")).is_none(),
            "being purely a resource stop is legible, not waivable: it still halts"
        );
    }
}

/// A STOP UNDER AN INCOMPARABLE BOUND IS A TYPED REFUSAL, NOT A DISAGREEMENT
/// AND NOT NOISE.
///
/// The seat below ran out under a ceiling derived in a configuration this build
/// is not. Its `depth` number is of exactly the same kind as the kernel's and
/// its resource is not — the measured 9.3x gap. Nothing may be concluded from
/// the difference: not that the engines disagree, and not that the stop is a
/// spurious artifact. Both readings are claims about a comparison that did not
/// happen, and the second is the one that will be argued for.
#[test]
fn a_stop_under_an_incomparable_bound_is_refused_rather_than_read() {
    let env = Environment::new();
    let council = Council::of(vec![engine_seat(
        "engine-k2",
        measured_in_the_other_profile("test/k2"),
        SeatVerdict::Exhausted {
            bound: Bound::Depth,
        },
    )]);

    let halt = match convene(&council, admitted(&env, good_axiom("Incomparable"))) {
        CouncilOutcome::Halted(halt) => halt,
        CouncilOutcome::Agreed(_) => panic!("an incomparable stop was read as agreement"),
        CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
    };

    match &halt.classify()[0].1 {
        ObjectionKind::ExhaustionNotComparable { bound, why } => {
            assert_eq!(*bound, Bound::Depth);
            assert!(
                matches!(
                    why,
                    Incomparability::Defect(
                        ComparabilityDefect::RunsInDifferentConfigurations { .. }
                    ) | Incomparability::Defect(ComparabilityDefect::NotMeasuredWhereItRuns { .. })
                ),
                "the refusal must name the configuration mismatch: {}",
                why.describe()
            );
        }
        other => panic!(
            "a stop under an incomparable bound was classified as {other:?}; the whole \
             failure mode is that an unreadable stop gets read"
        ),
    }
    assert!(
        halt.summary().contains("not comparable"),
        "the record must say the comparison did not happen: {}",
        halt.summary()
    );
    assert!(env.find(&n("Incomparable")).is_none());
}

/// A SEAT WITH NO ESTABLISHED BOUND CANNOT HAVE ITS STOP READ EITHER — and the
/// distinction is honest about *us*, not about the witness.
///
/// A subprocess witness with only a wall clock has no bound this process
/// derived. That is a statement about what we know. It costs the witness
/// nothing when it completes (see the positive tests: such a seat agrees and
/// publishes); it costs only the ability to read its resource stop against the
/// kernel's.
#[test]
fn a_seat_that_declared_no_bound_cannot_have_its_stop_compared() {
    let env = Environment::new();
    let council = Council::of(vec![reference_oracle_seat(
        "leanchecker",
        unmeasured_subprocess(),
        SeatVerdict::Exhausted {
            bound: Bound::Other("30s wall clock".into()),
        },
    )]);

    let halt = match convene(&council, admitted(&env, good_axiom("Unbounded"))) {
        CouncilOutcome::Halted(halt) => halt,
        CouncilOutcome::Agreed(_) => panic!("an unreadable stop was read as agreement"),
        CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
    };
    assert!(matches!(
        &halt.classify()[0].1,
        ObjectionKind::ExhaustionNotComparable {
            why: Incomparability::NoBoundEstablished { .. },
            ..
        }
    ));
    assert!(env.find(&n("Unbounded")).is_none());
}

/// A SEAT CALIBRATED FOR THE KERNEL'S OWN ENGINE CANNOT CORROBORATE IT.
///
/// Two bounds calibrated for one engine agree with themselves. A seat holding
/// K1's own budget is K1 nodding at K1, and its stop says nothing about a second
/// opinion — so the classification refuses rather than certifying the pair as
/// comparable.
#[test]
fn a_seat_holding_the_kernels_own_bound_is_not_an_independent_witness() {
    let env = Environment::new();
    let council = Council::of(vec![engine_seat(
        "k1-again",
        SeatBounds::Derived(Budget::DEFAULT),
        SeatVerdict::Exhausted {
            bound: Bound::Depth,
        },
    )]);

    let halt = match convene(&council, admitted(&env, good_axiom("SelfWitness"))) {
        CouncilOutcome::Halted(halt) => halt,
        CouncilOutcome::Agreed(_) => panic!("self-corroboration was read as agreement"),
        CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
    };
    assert!(matches!(
        &halt.classify()[0].1,
        ObjectionKind::ExhaustionNotComparable {
            why: Incomparability::Defect(ComparabilityDefect::SameEngine { .. }),
            ..
        }
    ));
}

/// The halt records what the seats were compared AGAINST. A record that omits
/// the kernel's own bound cannot be re-read later, and every judgement about a
/// seat's stop is a judgement relative to it.
#[test]
fn the_halt_records_the_kernels_own_bound() {
    let env = Environment::new();
    let council = Council::of(vec![engine_seat(
        "engine-k2",
        measured_here("test/k2"),
        SeatVerdict::Exhausted {
            bound: Bound::Steps,
        },
    )]);
    let halt = match convene(&council, admitted(&env, good_axiom("Recorded"))) {
        CouncilOutcome::Halted(halt) => halt,
        other => panic!(
            "expected a halt, got {}",
            match other {
                CouncilOutcome::Agreed(_) => "Agreed",
                CouncilOutcome::KernelRejected { .. } => "KernelRejected",
                CouncilOutcome::Halted(_) => unreachable!(),
            }
        ),
    };
    assert_eq!(halt.kernel_budget, Budget::DEFAULT);
    assert_eq!(halt.kernel_budget.engine(), EngineId::K1);
}

// ---------------------------------------------------------------------------
// The positive half — the mechanism must still let correct work through
// ---------------------------------------------------------------------------

/// Unanimous agreement publishes. A veto that blocks everything is as useless
/// as one that blocks nothing.
///
/// Note the seats: one with a derived bound, one Reference-kernel oracle with
/// none.
/// A completed check is a completed check under any bound — a budget can stop a
/// check but cannot make one finish falsely — so requiring comparability in
/// order to *agree* would have locked out the only real witnesses we have.
#[test]
fn a_unanimous_council_publishes() {
    let env = Environment::new();
    let council = Council::of(vec![
        engine_seat("engine-k2", measured_here("test/k2"), SeatVerdict::Agrees),
        reference_oracle_seat("leanchecker", unmeasured_subprocess(), SeatVerdict::Agrees),
    ]);

    let checked = match convene(&council, admitted(&env, good_axiom("Agreed"))) {
        CouncilOutcome::Agreed(checked) => checked,
        CouncilOutcome::Halted(halt) => panic!("unanimous council halted: {}", halt.summary()),
        CouncilOutcome::KernelRejected { .. } => panic!("the kernel accepts this declaration"),
    };
    assert!(matches!(publish(checked), Published::Committed(_)));
}

/// Even a seat whose bound is incomparable with the kernel's may AGREE, and
/// that agreement publishes. Comparability is required to read a resource stop,
/// not to accept a completed answer — conflating the two would turn an honest
/// boundary into a wall.
#[test]
fn an_incomparable_bound_does_not_prevent_a_completed_agreement() {
    let env = Environment::new();
    let council = Council::of(vec![engine_seat(
        "engine-k2",
        measured_in_the_other_profile("test/k2"),
        SeatVerdict::Agrees,
    )]);
    let checked = match convene(&council, admitted(&env, good_axiom("StillPublishes"))) {
        CouncilOutcome::Agreed(checked) => checked,
        CouncilOutcome::Halted(halt) => panic!("a completed agreement halted: {}", halt.summary()),
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
        synthetic_seat("a", unmeasured_subprocess(), SeatVerdict::Agrees),
        synthetic_seat("b", unmeasured_subprocess(), SeatVerdict::Agrees),
        synthetic_seat("c", unmeasured_subprocess(), SeatVerdict::Agrees),
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
