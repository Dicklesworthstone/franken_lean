//! Fuel and budget parity: engines must agree on a **measured quantity**, never
//! on a configured number (bead `franken_lean-4o3n`).
//!
//! # Why this file exists before there is a second engine
//!
//! Because it can. That is the whole test, and it is the general rule this bead
//! also records:
//!
//! * A **constraint** says "this may never happen". It is falsifiable by a
//!   planted violation today, costs nothing to enforce while nothing violates
//!   it, and must precede the code it governs — afterwards there is working
//!   code and a deadline, and the constraint becomes negotiable.
//! * A **description** says "this is what happened". It can only be validated
//!   against real instances, so inventing it early shapes it to imagined
//!   failure modes.
//!
//! Fuel parity passes that test: two incomparably-derived budgets can be
//! planted and refused right now, with no engine. (The structured
//! first-divergence *record* fails it and is deliberately deferred.)
//!
//! # The failure this prevents
//!
//! `franken_lean-kxbj` measured this kernel's marginal native stack at 5,935
//! bytes per unit of depth in `dev` and 640 in `release` — the same code, the
//! same target, the same `depth = 4096`, a 9.3x gap in what the number costs.
//! So two engines both reporting "depth 4096" have agreed about a LABEL. The
//! tests below plant exactly that: bounds whose numbers are identical and whose
//! resources are not, and prove they are refused rather than certified.

#![forbid(unsafe_code)]

use fln_core::expr::Expr;
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_env::constants::{AxiomVal, ConstantVal};
use fln_env::environment::Environment;
use fln_kernel::capability::{Admitted, admit};
use fln_kernel::verdict::{
    Budget, Comparability, ComparabilityDefect, EngineId, ExecConfig, Grade, Profile,
    StackMeasurement, Verdict,
};
use fln_kernel::{Declaration, check};

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn good_axiom(name: &str) -> Declaration {
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_: Expr::sort(Level::one()),
        },
        is_unsafe: false,
    })
}

/// The profile this build was NOT compiled under. Every "derived for another
/// configuration" fixture is expressed against this rather than against a
/// hard-coded `Release`, so the file plants a real mismatch whether it is run
/// by `cargo test` or `cargo test --release`.
fn the_other_profile() -> Profile {
    match Profile::current() {
        Profile::Dev => Profile::Release,
        Profile::Release => Profile::Dev,
    }
}

fn other_config() -> ExecConfig {
    ExecConfig::of(
        the_other_profile(),
        ExecConfig::current().arch,
        ExecConfig::current().os,
    )
}

/// A second engine that has done the work this bead requires: it measured its
/// OWN frames, in the configuration it actually runs in.
fn honest_second_engine(bytes_per_depth: usize) -> StackMeasurement {
    StackMeasurement::measured(
        EngineId::named("test/k2"),
        ExecConfig::current(),
        bytes_per_depth,
        StackMeasurement::K1_ENTRY_RESERVE_BYTES,
        StackMeasurement::K1_SAFETY_FACTOR,
    )
}

// ---------------------------------------------------------------------------
// PLANTED VIOLATION 1 — identical numbers, incomparable resources
// ---------------------------------------------------------------------------

/// TWO BOUNDS DERIVED IN DIFFERENT CONFIGURATIONS REFUSE TO BE COMPARED, EVEN
/// WHEN THEIR NUMBERS ARE IDENTICAL.
///
/// This is the bead's headline case and the sharpest form of it: both budgets
/// below carry `depth == 4096`. A comparison that looked at the number would
/// find perfect agreement. There is none — one of them was derived from a cost
/// measured in a configuration it does not run in, and 4096 buys 9.3x more
/// stack there.
#[test]
fn two_bounds_with_the_same_depth_number_and_different_configurations_are_refused() {
    let depth = Budget::DEFAULT_DEPTH;

    // K1, here, measured here: the honest bound.
    let here = StackMeasurement::k1_here();
    let mine = Budget::derive(
        here,
        ExecConfig::current(),
        here.stack_bytes_for_depth(depth),
        Budget::DEFAULT_STEPS,
    );

    // A second engine whose measurement was taken in the OTHER profile, and
    // whose stack was chosen so the derived ceiling lands on the same number.
    let theirs_measurement = StackMeasurement::measured(
        EngineId::named("test/k2"),
        other_config(),
        here.bytes_per_depth(),
        StackMeasurement::K1_ENTRY_RESERVE_BYTES,
        StackMeasurement::K1_SAFETY_FACTOR,
    );
    let theirs = Budget::derive(
        theirs_measurement,
        other_config(),
        theirs_measurement.stack_bytes_for_depth(depth),
        Budget::DEFAULT_STEPS,
    );

    assert_eq!(
        mine.depth, theirs.depth,
        "the fixture is only a fixture if the two NUMBERS agree"
    );

    let comparability = Comparability::establish(&mine, &theirs);
    assert!(
        !comparability.is_established(),
        "two bounds derived in different configurations were certified comparable on the \
         strength of an identical depth number — that is the vacuity this bead exists for"
    );
    assert!(
        matches!(
            comparability.defect(),
            Some(ComparabilityDefect::NotMeasuredWhereItRuns { .. })
                | Some(ComparabilityDefect::RunsInDifferentConfigurations { .. })
        ),
        "the refusal must name a configuration defect, got {:?}",
        comparability.defect()
    );
}

/// The same refusal when both sides measured themselves honestly but run in
/// different configurations. Nothing is wrong with either bound; they are
/// simply not statements about the same resource.
#[test]
fn honest_bounds_in_different_configurations_are_still_not_comparable() {
    let here = StackMeasurement::k1_here();
    let mine = Budget::derive(
        here,
        ExecConfig::current(),
        Budget::MIN_STACK_BYTES,
        Budget::DEFAULT_STEPS,
    );

    let theirs_measurement = StackMeasurement::measured(
        EngineId::named("test/k2"),
        other_config(),
        1_000,
        StackMeasurement::K1_ENTRY_RESERVE_BYTES,
        StackMeasurement::K1_SAFETY_FACTOR,
    );
    let theirs = Budget::derive(
        theirs_measurement,
        other_config(),
        16 * 1024 * 1024,
        Budget::DEFAULT_STEPS,
    );

    assert_eq!(theirs.calibration().grade(), Grade::Measured);
    assert!(matches!(
        Comparability::establish(&mine, &theirs).defect(),
        Some(ComparabilityDefect::RunsInDifferentConfigurations { .. })
    ));
}

/// COMPARABILITY IS REACHABLE. A constraint that refuses everything is as
/// useless as one that refuses nothing: two engines that each measured
/// themselves where they run, in the same configuration, ARE comparable.
#[test]
fn two_honestly_measured_engines_in_the_same_configuration_are_comparable() {
    let mine = Budget::DEFAULT;
    let theirs = Budget::derive(
        honest_second_engine(2_000),
        ExecConfig::current(),
        32 * 1024 * 1024,
        Budget::DEFAULT_STEPS,
    );
    assert_eq!(
        Comparability::establish(&mine, &theirs),
        Comparability::Established,
        "two engines each measured where they run must be comparable, or the boundary is a wall"
    );
}

/// AN ENGINE CANNOT CORROBORATE ITSELF. Two bounds calibrated for the same
/// engine agree with themselves; certifying that as parity is the rubber stamp
/// in its purest form.
#[test]
fn an_engine_cannot_be_established_comparable_with_itself() {
    let a = Budget::DEFAULT;
    let b = Budget::for_stack_bytes(Budget::MIN_STACK_BYTES);
    assert!(matches!(
        Comparability::establish(&a, &b).defect(),
        Some(ComparabilityDefect::SameEngine { .. })
    ));
}

/// AN EXTRAPOLATED BOUND RUNS BUT IS NEVER COMPARABLE.
///
/// This is the deliberate asymmetry. The safety factor exists to carry a
/// measurement to a target we have not measured, so refusing to *run* there
/// would make the kernel unusable on every unmeasured platform. What the factor
/// cannot do is make "safe by a factor we chose" into "measured", so the bound
/// is honestly ungradeable for comparison — and the council says so rather than
/// certifying parity on an unmeasured target.
#[test]
fn an_extrapolated_bound_is_usable_and_never_comparable() {
    let elsewhere = StackMeasurement::measured(
        EngineId::named("test/k2"),
        ExecConfig::of(Profile::current(), "some-unmeasured-arch", "linux"),
        900,
        StackMeasurement::K1_ENTRY_RESERVE_BYTES,
        StackMeasurement::K1_SAFETY_FACTOR,
    );
    let theirs = Budget::derive(
        elsewhere,
        ExecConfig::current(),
        16 * 1024 * 1024,
        Budget::DEFAULT_STEPS,
    );
    assert_eq!(theirs.calibration().grade(), Grade::Extrapolated);
    assert!(matches!(
        Comparability::establish(&Budget::DEFAULT, &theirs).defect(),
        Some(ComparabilityDefect::NotMeasuredWhereItRuns { .. })
    ));
}

// ---------------------------------------------------------------------------
// PLANTED VIOLATION 2 — the kernel refuses a bound that is not about it
// ---------------------------------------------------------------------------

/// THE KERNEL REFUSES A BUDGET DERIVED FROM ANOTHER ENGINE'S MEASUREMENT.
///
/// A ceiling derived from someone else's frames is a number. Running the
/// kernel's descent under it is either unsafe or artificially shallow, and
/// artificially shallow is a non-answer generator — which is how a consensus
/// seat drowns in halts it did not earn.
///
/// The refusal is typed and it happens BEFORE the first descent: a native stack
/// overflow aborts the process uncatchably, so there is no point after the
/// descent at which FL-INV-07 could still type it.
#[test]
fn the_kernel_refuses_a_budget_calibrated_for_another_engine() {
    let env = Environment::new();
    let foreign = Budget::derive(
        honest_second_engine(640),
        ExecConfig::current(),
        Budget::MIN_STACK_BYTES,
        Budget::DEFAULT_STEPS,
    );

    match check(&env, &good_axiom("Foreign"), foreign) {
        Outcome::Inconclusive(inconclusive) => {
            assert!(
                matches!(
                    inconclusive.cause,
                    InconclusiveCause::AuthorityIncomplete { .. }
                ),
                "a bound the kernel cannot establish authority over is an authority \
                 non-answer, got {:?}",
                inconclusive.cause
            );
        }
        Outcome::Complete(verdict) => panic!(
            "the kernel ran under a ceiling derived from another engine's frames and \
             produced {}",
            match verdict {
                Verdict::Accepted { .. } => "an ACCEPTANCE",
                Verdict::Rejected { .. } => "a rejection",
            }
        ),
        Outcome::InternalFault(fault) => {
            panic!("a caller-supplied budget must not be reported as our fault: {fault:?}")
        }
    }
}

/// The same refusal mints no capability. FL-INV-07 says an inconclusive is
/// never promoted to acceptance or rejection; here it is additionally never
/// promoted to a publication right.
#[test]
fn a_budget_calibrated_for_another_engine_mints_no_capability() {
    let env = Environment::new();
    let foreign = Budget::derive(
        honest_second_engine(640),
        ExecConfig::current(),
        Budget::MIN_STACK_BYTES,
        Budget::DEFAULT_STEPS,
    );
    if let Outcome::Complete(Admitted::Accepted(_)) = admit(&env, good_axiom("Foreign2"), foreign) {
        panic!("an uncalibrated budget minted a publication capability");
    }
    assert!(env.find(&n("Foreign2")).is_none());
}

/// THE KERNEL REFUSES A BUDGET DERIVED FOR ANOTHER CONFIGURATION.
///
/// This is the 9.3x case aimed at the kernel itself: K1's own measurement, K1's
/// own engine id, and a ceiling derived for a build this process is not. In
/// `dev` that ceiling is nine times above the floor, and the failure mode is a
/// process abort rather than a typed answer.
#[test]
fn the_kernel_refuses_a_budget_calibrated_for_another_configuration() {
    let env = Environment::new();
    let elsewhere = Budget::derive(
        StackMeasurement::k1_here(),
        other_config(),
        Budget::MIN_STACK_BYTES,
        Budget::DEFAULT_STEPS,
    );
    assert!(
        matches!(
            check(&env, &good_axiom("Elsewhere"), elsewhere),
            Outcome::Inconclusive(_)
        ),
        "a budget derived for a configuration this process is not running in must be \
         refused before the descent, not audited after it"
    );
}

/// The refusal is not a blanket one: the budgets callers actually use are
/// accepted, and this must keep being true or the constraint is a wall.
#[test]
fn the_calibrated_budgets_callers_actually_use_are_accepted() {
    let env = Environment::new();
    for budget in [
        Budget::DEFAULT,
        Budget::for_stack_bytes(Budget::MIN_STACK_BYTES),
        Budget::for_stack_bytes(2 * 1024 * 1024),
        Budget::DEFAULT.narrowed(1_000, 64),
    ] {
        assert!(
            budget.objection_to_governing(EngineId::K1).is_none(),
            "a budget derived here for K1 must be usable here: {}",
            budget.calibration().describe()
        );
        assert!(
            matches!(
                check(&env, &good_axiom("Ok"), budget),
                Outcome::Complete(Verdict::Accepted { .. })
            ),
            "calibrated budget was refused: {}",
            budget.calibration().describe()
        );
    }
}

// ---------------------------------------------------------------------------
// The derivation discipline itself
// ---------------------------------------------------------------------------

/// EVERY BUDGET CARRIES ITS PROVENANCE, AND THERE IS NO WAY TO MAKE ONE
/// WITHOUT IT.
///
/// The runtime half is below. The stronger half is enforced by the type system
/// and is not expressible as a runtime test: `Budget`'s calibration field is
/// private, so outside `fln-kernel` neither
///
/// ```text
/// let forged = Budget { steps: 1, depth: 4096, .. };   // error: private field
/// let forged = Budget { steps: 1, ..Budget::DEFAULT }; // error: private field
/// ```
///
/// compiles. A bound can only come from [`Budget::derive`] — which requires a
/// [`StackMeasurement`] naming an engine and a configuration — or from
/// [`Budget::narrowed`], which keeps the one it was given.
#[test]
fn every_budget_carries_the_measurement_it_came_from() {
    let default = Budget::DEFAULT.calibration();
    assert_eq!(default.engine(), EngineId::K1);
    assert_eq!(default.measurement().engine(), EngineId::K1);
    assert_eq!(default.running_in(), ExecConfig::current());
    assert!(default.stack_bytes() >= Budget::stack_bytes_for_depth(Budget::DEFAULT_DEPTH));

    let described = default.describe();
    for expected in ["engine=", "measured_in=", "running_in=", "bytes_per_depth="] {
        assert!(
            described.contains(expected),
            "provenance must be legible in a record: {described}"
        );
    }
}

/// The default's stack requirement is DERIVED from the measurement, not chosen.
/// If someone raises `DEFAULT_DEPTH` without re-deriving the floor, the const
/// assertions in `verdict.rs` refuse to compile; this is the runtime statement
/// of the same pairing, kept here because it is the property a reader checks.
#[test]
fn the_stack_floor_is_derived_from_the_measurement_rather_than_chosen() {
    assert!(Budget::stack_bytes_for_depth(Budget::DEFAULT_DEPTH) <= Budget::MIN_STACK_BYTES);
    assert!(Budget::depth_for_stack_bytes(Budget::MIN_STACK_BYTES) >= Budget::DEFAULT_DEPTH);
    assert_eq!(
        Budget::MEASURED_STACK_BYTES_PER_DEPTH,
        StackMeasurement::k1_here().bytes_per_depth(),
        "the shipped constant and the current profile's measurement are one fact"
    );

    // Rust's default spawned-thread stack, the pairing bead franken_lean-kxbj
    // aborted on. The derivation must yield a strictly shallower ceiling there.
    let spawned = Budget::for_stack_bytes(2 * 1024 * 1024);
    assert!(
        spawned.depth < Budget::DEFAULT_DEPTH,
        "a 2 MiB stack must not be handed the default ceiling"
    );
    assert!(spawned.depth >= 1, "a ceiling of zero would bound nothing");
}
