//! Depth-budget / native-stack calibration (bead `franken_lean-kxbj`).
//!
//! `Budget::depth` is the only thing standing between a legitimately deep
//! Corpus term and a native stack overflow, and a stack overflow is the one
//! failure FL-INV-07 cannot absorb after the fact: it aborts the process
//! uncatchably, so no typed `Inconclusive` can ever be produced. The guarantee
//! therefore has to come from the ceiling being provably below the floor.
//!
//! This file is the measurement that makes that provable rather than assumed.
//! It is black-box: it never inspects a stack pointer and never models a frame
//! layout. It runs the kernel's own public authority on a thread of *known*
//! stack size, at a known `Budget::depth`, in a subprocess, and asks the only
//! question that matters — did the process survive and return a typed answer?
//! Bisecting the largest surviving depth at two different stack sizes yields
//! the marginal bytes-of-stack-per-unit-of-depth directly, with the fixed entry
//! overhead solved out rather than guessed at.
//!
//! Layout:
//!   * `probe_child`   — the subprocess entry point (inert without its env var).
//!   * `calibrate_*`   — `#[ignore]`d measurement runs; these produce the number.
//!   * the remaining tests — always-on guards that keep the shipped constants
//!     honest, including the planted witness that reproduces the former abort
//!     inside a contained subprocess.

#![forbid(unsafe_code)]

use std::process::Command;

use fln_core::diag::ResourceReason;
use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_env::constants::{
    AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};

// ---------------------------------------------------------------------------
// Probe shapes
// ---------------------------------------------------------------------------

/// The residual recursive descents that thread `depth`. Consecutive
/// application, lambda, Pi, let, recursor-major, and matching binder-defeq
/// spines have explicit worklists now, so they are covered by shallow-depth
/// regressions rather than pretending to remain native-stack calibration
/// shapes. Each shape here is built so that reaching depth `d` costs `O(d)`
/// work, not `O(d^2)`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Shape {
    /// Converted: checking-mode KR-106 now types a right-nested argument tree
    /// on a heap stack. Kept so the former abort pairing can prove it answers
    /// typed rather than dying. Not a residual native-stack shape.
    AppInfer,
    /// `infer_proj` down a projection nest (KR-112): each scrutinee is itself
    /// a projection, so `infer_core_mode` still re-enters per layer.
    ProjInfer,
}

impl Shape {
    const ALL: [Shape; 1] = [Shape::ProjInfer];

    fn as_str(self) -> &'static str {
        match self {
            Shape::AppInfer => "app_infer",
            Shape::ProjInfer => "proj_infer",
        }
    }

    fn parse(s: &str) -> Option<Shape> {
        match s {
            "app_infer" => Some(Shape::AppInfer),
            "proj_infer" => Some(Shape::ProjInfer),
            _ => None,
        }
    }
}

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn sort1() -> Expr {
    Expr::sort(Level::one())
}

fn axiom_decl(name: &str, type_: Expr) -> Declaration {
    Declaration::Axiom(AxiomVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        is_unsafe: false,
    })
}

fn defn_decl(name: &str, type_: Expr, value: Expr) -> Declaration {
    Declaration::Defn(DefinitionVal {
        base: ConstantVal {
            name: n(name),
            level_params: vec![],
            type_,
        },
        value,
        hints: ReducibilityHints::Opaque,
        safety: DefinitionSafety::Safe,
        all: vec![n(name)],
    })
}

fn add(env: &Environment, decl: &Declaration) -> Environment {
    let info = match decl.clone() {
        Declaration::Axiom(v) => ConstantInfo::Axiom(v),
        Declaration::Defn(v) => ConstantInfo::Defn(v),
        _ => unreachable!("probe environments hold only axioms and definitions"),
    };
    env.add_decl(info).expect("probe environment extends")
}

/// What a probe run submits to the kernel's public authority.
enum Probe {
    Decl(Environment, Declaration),
}

impl Probe {
    fn run(&self, budget: Budget) -> Outcome<Verdict> {
        match self {
            Probe::Decl(env, decl) => check(env, decl, budget),
        }
    }
}

/// Builds a term guaranteed to force the descent past `levels` units of depth.
fn build_probe(shape: Shape, levels: u32) -> Probe {
    match shape {
        Shape::AppInfer => {
            // `T : Sort 1`, `f : T -> T`, `a : T`; term `f (f (... (f a)))`.
            // Checking-mode infer now walks this on the heap; the shape remains
            // so the former abort pairing can prove it answers typed.
            let env = Environment::new();
            let env = add(&env, &axiom_decl("T", sort1()));
            let t = Expr::const_(n("T"), vec![]);
            let env = add(
                &env,
                &axiom_decl(
                    "f",
                    Expr::forall_e(n("_"), t.clone(), t.clone(), BinderInfo::Default),
                ),
            );
            let env = add(&env, &axiom_decl("a", t.clone()));
            let f = Expr::const_(n("f"), vec![]);
            let mut e = Expr::const_(n("a"), vec![]);
            for _ in 0..levels {
                e = Expr::app(f.clone(), e);
            }
            Probe::Decl(env, defn_decl("Probe", t, e))
        }
        Shape::ProjInfer => {
            // `T : Sort 1`, `a : T`; term `a.1.1...`. The nest is ill-typed
            // (T is not a structure) but `infer_proj` infers the scrutinee
            // before that rejection, so the descent still reaches the ceiling.
            let env = Environment::new();
            let env = add(&env, &axiom_decl("T", sort1()));
            let t = Expr::const_(n("T"), vec![]);
            let env = add(&env, &axiom_decl("a", t.clone()));
            let mut e = Expr::const_(n("a"), vec![]);
            let structure = n("S");
            for _ in 0..levels {
                e = Expr::proj(structure.clone(), 0, e);
            }
            Probe::Decl(env, defn_decl("Probe", t, e))
        }
    }
}

// ---------------------------------------------------------------------------
// Outcome classification
// ---------------------------------------------------------------------------

/// The single line a probe child prints. `DEPTH_EXHAUSTED` is the only result
/// that makes a probe *valid*: it proves the descent actually reached the
/// depth ceiling rather than finishing early or running out of steps.
const RESULT_DEPTH_EXHAUSTED: &str = "DEPTH_EXHAUSTED";

fn classify(outcome: &Outcome<Verdict>) -> String {
    match outcome {
        Outcome::Inconclusive(inconclusive) => match &inconclusive.cause {
            InconclusiveCause::ResourceExhausted { usage } => match usage.reason {
                ResourceReason::RecursionDepth { .. } => RESULT_DEPTH_EXHAUSTED.to_string(),
                ResourceReason::ExecutionSteps => "STEPS_EXHAUSTED".to_string(),
                _ => "OTHER_RESOURCE".to_string(),
            },
            _ => "OTHER_INCONCLUSIVE".to_string(),
        },
        Outcome::Complete(Verdict::Accepted { .. }) => "ACCEPTED".to_string(),
        Outcome::Complete(Verdict::Rejected { class, .. }) => {
            format!("REJECTED:{}", class.as_str())
        }
        Outcome::InternalFault(fault) => format!("FAULT:{fault:?}"),
    }
}

// ---------------------------------------------------------------------------
// Subprocess protocol
// ---------------------------------------------------------------------------

const ENV_SHAPE: &str = "FLN_KXBJ_PROBE_SHAPE";
const ENV_DEPTH: &str = "FLN_KXBJ_PROBE_DEPTH";
const ENV_STACK: &str = "FLN_KXBJ_PROBE_STACK";
const CHILD_TEST: &str = "probe_child";

/// The probe subprocess. Inert (and instant) in an ordinary `cargo test` run:
/// without `FLN_KXBJ_PROBE_SHAPE` it returns immediately.
///
/// With the env set it spawns a worker of exactly the requested stack size,
/// submits a term deeper than the requested `Budget::depth`, prints one result
/// line, and exits 0. If the native stack cannot hold that descent the runtime
/// aborts this process — which is the whole point: the parent reads the
/// non-zero exit status as "this (stack, depth) pair does not fit".
#[test]
fn probe_child() {
    let Ok(shape) = std::env::var(ENV_SHAPE) else {
        return;
    };
    let shape = Shape::parse(&shape).expect("probe shape is one of the registered names");
    let depth: u32 = std::env::var(ENV_DEPTH)
        .expect("probe depth")
        .parse()
        .expect("probe depth parses");
    let stack: usize = std::env::var(ENV_STACK)
        .expect("probe stack")
        .parse()
        .expect("probe stack parses");

    let worker = std::thread::Builder::new()
        .name(format!("kxbj-probe-{}", shape.as_str()))
        .stack_size(stack)
        .spawn(move || {
            // Deeper than the ceiling, so the ceiling — not the term — ends
            // the descent, and `max_depth` is pinned to `depth` exactly.
            let probe = build_probe(shape, depth.saturating_add(16));
            // Stated, not derived: this IS the instrument that decides what a
            // derivation may claim, so it must be able to ask for a depth the
            // current constants call unsafe. `stack` is the claim the
            // experiment is about to test (bead `franken_lean-4o3n`).
            let budget = Budget::stated_for_measurement(u64::MAX, depth, stack);
            classify(&probe.run(budget))
        })
        .expect("probe worker spawns");
    let result = worker.join().expect("probe worker does not panic");
    println!("PROBE_RESULT {result}");
    // Bypass libtest teardown: the parent reads exit status, and a normal
    // return would let a later harness step change it.
    std::io::Write::flush(&mut std::io::stdout()).expect("probe stdout flushes");
    std::process::exit(0);
}

/// What one `(shape, stack, depth)` subprocess run reported.
#[derive(Debug, PartialEq, Eq)]
enum ProbeOutcome {
    /// Survived the native stack and hit the depth ceiling: a valid data point.
    DepthExhausted,
    /// Survived, but the descent never reached the ceiling — the probe term is
    /// not forcing what we think it forces. Never treated as a fit.
    SurvivedOther(String),
    /// The process died. On this target that is the stack overflow.
    Died(String),
}

impl ProbeOutcome {
    fn fits(&self) -> bool {
        matches!(self, ProbeOutcome::DepthExhausted)
    }
}

fn run_probe(shape: Shape, stack_bytes: usize, depth: u32) -> ProbeOutcome {
    let exe = std::env::current_exe().expect("probe re-invokes this test binary");
    let output = Command::new(exe)
        .args([CHILD_TEST, "--exact", "--nocapture", "--test-threads=1"])
        .env(ENV_SHAPE, shape.as_str())
        .env(ENV_DEPTH, depth.to_string())
        .env(ENV_STACK, stack_bytes.to_string())
        .output()
        .expect("probe subprocess launches");
    if !output.status.success() {
        let err = String::from_utf8_lossy(&output.stderr);
        let tail = err.lines().rev().take(3).collect::<Vec<_>>().join(" | ");
        return ProbeOutcome::Died(format!("status={:?} stderr={tail}", output.status));
    }
    // libtest prints `test probe_child ... ` without a trailing newline before
    // the child's own output lands, so the marker is mid-line, not at column 0.
    let stdout = String::from_utf8_lossy(&output.stdout);
    let line = stdout
        .split_once("PROBE_RESULT ")
        .map(|(_, rest)| rest.lines().next().unwrap_or("").trim().to_string())
        .unwrap_or_else(|| "MISSING".to_string());
    if line == RESULT_DEPTH_EXHAUSTED {
        ProbeOutcome::DepthExhausted
    } else {
        ProbeOutcome::SurvivedOther(line)
    }
}

/// Largest `Budget::depth` that survives `stack_bytes` for this shape.
///
/// Requires `lo` to fit and searches up to `hi`. Returns `None` if even `lo`
/// does not fit (the calibration is then badly wrong and the caller says so).
fn max_surviving_depth(shape: Shape, stack_bytes: usize, lo: u32, hi: u32) -> Option<u32> {
    if !run_probe(shape, stack_bytes, lo).fits() {
        return None;
    }
    let (mut lo, mut hi) = (lo, hi);
    // Invariant: `lo` fits, `hi + 1` does not (or `hi` is the search cap).
    if run_probe(shape, stack_bytes, hi).fits() {
        return Some(hi);
    }
    while hi - lo > 1 {
        let mid = lo + (hi - lo) / 2;
        if run_probe(shape, stack_bytes, mid).fits() {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    Some(lo)
}

// ---------------------------------------------------------------------------
// The measurement (ignored: hundreds of subprocess spawns)
// ---------------------------------------------------------------------------

const CALIBRATION_STACK_SMALL: usize = 1024 * 1024;
const CALIBRATION_STACK_LARGE: usize = 4 * 1024 * 1024;
const CALIBRATION_SEARCH_CAP: u32 = 32_768;

/// Measures marginal stack bytes per unit of `Budget::depth`, per shape.
///
/// Two stack sizes, not one: a single `(stack, depth)` pair conflates the
/// fixed entry overhead with the per-level cost, and dividing by it would
/// understate the slope. With two points the intercept solves out —
/// `bytes_per_depth = (S_large - S_small) / (D_large - D_small)` — and the
/// residual intercept is reported so a nonsensical fit is visible rather than
/// silently averaged away.
#[test]
#[ignore = "calibration: spawns hundreds of subprocesses; run explicitly"]
fn calibrate_stack_bytes_per_depth() {
    let mut worst = 0f64;
    let mut worst_shape = None;
    println!(
        "shape                small_stack  small_depth  large_stack  large_depth  bytes/depth  intercept"
    );
    for shape in Shape::ALL {
        let small = max_surviving_depth(shape, CALIBRATION_STACK_SMALL, 8, CALIBRATION_SEARCH_CAP)
            .unwrap_or_else(|| panic!("{shape:?} cannot reach depth 8 in 1 MiB"));
        let large = max_surviving_depth(shape, CALIBRATION_STACK_LARGE, 8, CALIBRATION_SEARCH_CAP)
            .unwrap_or_else(|| panic!("{shape:?} cannot reach depth 8 in 4 MiB"));
        assert!(
            large > small,
            "{shape:?}: a larger stack must admit a deeper descent (small={small}, large={large})"
        );
        let bytes_per_depth =
            (CALIBRATION_STACK_LARGE - CALIBRATION_STACK_SMALL) as f64 / f64::from(large - small);
        let intercept = CALIBRATION_STACK_SMALL as f64 - bytes_per_depth * f64::from(small);
        println!(
            "{:<20} {:>11} {:>12} {:>12} {:>12} {:>12.1} {:>10.0}",
            shape.as_str(),
            CALIBRATION_STACK_SMALL,
            small,
            CALIBRATION_STACK_LARGE,
            large,
            bytes_per_depth,
            intercept
        );
        if bytes_per_depth > worst {
            worst = bytes_per_depth;
            worst_shape = Some(shape);
        }
    }
    println!(
        "WORST {} {worst:.1} bytes/depth",
        worst_shape.expect("at least one shape").as_str()
    );
    println!(
        "SHIPPED Budget::MEASURED_STACK_BYTES_PER_DEPTH = {}",
        Budget::MEASURED_STACK_BYTES_PER_DEPTH
    );
}

// ---------------------------------------------------------------------------
// Always-on guards
// ---------------------------------------------------------------------------

/// The shipped constants must be internally consistent. `DEFAULT_DEPTH` is the
/// single policy choice; `MIN_STACK_BYTES` is what it costs. The kernel already
/// asserts the ceiling-below-floor relation at compile time — these are the
/// properties of the derivation itself, which a `const` assert at one point
/// cannot cover.
#[test]
fn the_stack_derivation_is_sound_at_and_around_the_shipped_point() {
    assert_eq!(Budget::DEFAULT.depth, Budget::DEFAULT_DEPTH);
    assert_eq!(Budget::DEFAULT.steps, Budget::DEFAULT_STEPS);
    assert!(
        Budget::stack_bytes_for_depth(Budget::DEFAULT_DEPTH) <= Budget::MIN_STACK_BYTES,
        "DEFAULT needs {} bytes of stack but only requires {}",
        Budget::stack_bytes_for_depth(Budget::DEFAULT_DEPTH),
        Budget::MIN_STACK_BYTES
    );

    // Never hand out a zero ceiling: a caller with no usable stack must still
    // get a typed depth non-answer on the first descent rather than an abort.
    assert_eq!(Budget::depth_for_stack_bytes(0), 1);
    assert_eq!(Budget::depth_for_stack_bytes(1), 1);

    // Monotone, and the two directions are mutual inverses up to the flooring.
    let mut previous = 0;
    for mib in [1usize, 2, 4, 8, 16, 32, 64, 128] {
        let stack = mib * 1024 * 1024;
        let depth = Budget::depth_for_stack_bytes(stack);
        assert!(depth > previous, "depth must grow with stack at {mib} MiB");
        previous = depth;
        assert!(
            Budget::stack_bytes_for_depth(depth) <= stack,
            "{mib} MiB: derived depth {depth} must fit back inside the stack it came from"
        );
        assert!(
            Budget::stack_bytes_for_depth(depth + 1) > stack,
            "{mib} MiB: derived depth {depth} must be the LARGEST that fits, not merely one that does"
        );
    }
}

/// The planted witness, positive half: on a thread carrying exactly the
/// documented minimum stack, a term deeper than `Budget::DEFAULT.depth`
/// returns a typed FL-INV-07 `Inconclusive` and the worker returns cleanly.
///
/// Every residual recursive shape, because the guarantee is over every path
/// still represented by `Budget::depth`, not only the measured worst one.
#[test]
fn default_budget_is_survivable_on_the_documented_minimum_stack() {
    for shape in Shape::ALL {
        let worker = std::thread::Builder::new()
            .name(format!("kxbj-witness-{}", shape.as_str()))
            .stack_size(Budget::MIN_STACK_BYTES)
            .spawn(move || {
                let probe = build_probe(shape, Budget::DEFAULT.depth.saturating_add(16));
                classify(&probe.run(Budget::DEFAULT))
            })
            .expect("witness worker spawns");
        let result = worker.join().expect("witness worker does not panic");
        assert_eq!(
            result,
            RESULT_DEPTH_EXHAUSTED,
            "{shape:?}: exhaustion at Budget::DEFAULT on a {}-byte stack must be a typed \
             depth non-answer",
            Budget::MIN_STACK_BYTES
        );
    }
}

/// The same guarantee for the configuration that actually aborted: Rust's
/// default *spawned-thread* stack, which is what a caller gets when they do
/// nothing at all. `for_stack_bytes` is the API that makes this safe, and this
/// proves it does.
#[test]
fn derived_budget_is_survivable_on_rusts_default_spawned_thread_stack() {
    const RUST_DEFAULT_SPAWNED_STACK: usize = 2 * 1024 * 1024;
    let budget = Budget::for_stack_bytes(RUST_DEFAULT_SPAWNED_STACK);
    for shape in Shape::ALL {
        let worker = std::thread::Builder::new()
            .name(format!("kxbj-2mib-{}", shape.as_str()))
            .stack_size(RUST_DEFAULT_SPAWNED_STACK)
            .spawn(move || {
                let probe = build_probe(shape, budget.depth.saturating_add(16));
                classify(&probe.run(budget))
            })
            .expect("witness worker spawns");
        let result = worker.join().expect("witness worker does not panic");
        assert_eq!(
            result, RESULT_DEPTH_EXHAUSTED,
            "{shape:?}: a budget derived for a 2 MiB stack must exhaust typed on a 2 MiB stack"
        );
    }
}

/// The planted witness, negative half — the reproduction.
///
/// This is the bead's original defect, contained: `Budget::DEFAULT` on Rust's
/// 2 MiB spawned-thread stack is exactly the pairing that killed the Tribunal
/// on `Init.GrindInstances.Ring.SInt`. It must still kill a *subprocess*, and
/// the same run under `for_stack_bytes(2 MiB)` must not. If this ever stops
/// dying, the hazard has moved and the calibration above is measuring the
/// wrong thing — a silently-passing calibration is worse than none.
#[test]
fn undersized_stack_still_aborts_and_the_derived_budget_prevents_it() {
    const RUST_DEFAULT_SPAWNED_STACK: usize = 2 * 1024 * 1024;
    assert!(
        Budget::DEFAULT.depth > Budget::depth_for_stack_bytes(RUST_DEFAULT_SPAWNED_STACK),
        "this witness is only meaningful while DEFAULT assumes more stack than 2 MiB"
    );
    let shape = Shape::WITNESS;

    let uncalibrated = run_probe(shape, RUST_DEFAULT_SPAWNED_STACK, Budget::DEFAULT.depth);
    assert!(
        matches!(uncalibrated, ProbeOutcome::Died(_)),
        "the uncalibrated pairing (Budget::DEFAULT on a 2 MiB stack) must still abort — \
         that is the defect this bead exists to bound; got {uncalibrated:?}"
    );

    let calibrated = run_probe(
        shape,
        RUST_DEFAULT_SPAWNED_STACK,
        Budget::depth_for_stack_bytes(RUST_DEFAULT_SPAWNED_STACK),
    );
    assert_eq!(
        calibrated,
        ProbeOutcome::DepthExhausted,
        "the derived pairing must survive and answer typed"
    );
}

/// The former AppInfer abort pairing must now answer typed. If this starts
/// dying again, the heap trampoline has regressed onto the native stack.
#[test]
fn former_app_infer_abort_pairing_now_answers_typed() {
    const RUST_DEFAULT_SPAWNED_STACK: usize = 2 * 1024 * 1024;
    let outcome = run_probe(
        Shape::AppInfer,
        RUST_DEFAULT_SPAWNED_STACK,
        Budget::DEFAULT.depth,
    );
    assert!(
        matches!(outcome, ProbeOutcome::DepthExhausted),
        "right-nested checking-mode infer is a heap walk; Budget::DEFAULT on a 2 MiB \
         stack must hit the depth ceiling, not abort. got {outcome:?}"
    );
}

impl Shape {
    /// The shape used by the reproduction witness and by the tripwire's planted
    /// violations: the WORST per-level descent in
    /// `calibrate_stack_bytes_per_depth`'s table, i.e. the one that overflows
    /// first.
    ///
    /// Re-measured after the explicit telescope/worklist conversion:
    /// matching binder-defeq (KR-302) and right-nested application infer
    /// (KR-106) are heap walks, so they no longer belong in a native-stack
    /// witness. Retaining a converted shape would make "survived without
    /// reaching the ceiling" look like a calibration failure. `ProjInfer`
    /// is the residual worst case (`infer_proj` still recurses on the
    /// scrutinee).
    const WITNESS: Shape = Shape::ProjInfer;
}

// ---------------------------------------------------------------------------
// The tripwire: the shipped calibration cannot go stale silently (bead
// `fln-kx3y`)
// ---------------------------------------------------------------------------
//
// WHY THE GUARDS ABOVE DO NOT COVER THIS. They prove SURVIVAL AT THE SHIPPED
// PAIRING — `Budget::DEFAULT` returns a typed non-answer on a 64 MiB thread,
// `for_stack_bytes(2 MiB)` does the same on 2 MiB. That is a different claim
// from "the shipped number still describes this descent". They pass unchanged
// while the true per-level cost drifts upward, because `STACK_SAFETY_FACTOR`
// is 2 and `MIN_STACK_BYTES` was rounded up on top of that: there is roughly
// 3x of headroom in which `MEASURED_STACK_BYTES_PER_DEPTH` can be fiction and
// every test still passes. And when the headroom finally runs out the guard
// does not fail — it aborts the test binary uncatchably.
//
// THE DRIFT IS NOT HYPOTHETICAL. Two observations on 2026-07-25, both recorded
// on `franken_lean-kxbj`'s judgement row: the same instrument read 5,935.3
// bytes/depth on the development host and 6,553.6 on an RCH remote worker at
// the identical (profile, arch, os); and widening `Budget` for
// `franken_lean-4o3n` cost two of the then-four shapes one level of ceiling. Neither
// was caught by anything. Both were caught because a human re-ran an
// `#[ignore]`d test on a hunch.
//
// SO THE SAFETY FACTOR IS TURNED FROM A SILENT ABSORBER OF DRIFT INTO A MARGIN
// WITH A TRIPWIRE IN IT, which is what a margin is supposed to be. The bands
// below sit strictly inside the factor, so this fires while the margin is
// still intact rather than after it has been spent.

/// Stack the tripwire probes against.
///
/// Large on purpose. The tripwire predicts a depth from the shipped constants
/// using [`Budget::STACK_ENTRY_RESERVE_BYTES`] in place of the measured
/// intercept, and that substitution is only harmless while the fixed cost is a
/// small part of the total. At 4 MiB the reserve overstates the measured
/// intercept by about 38 KiB — under 1% of the prediction, an order of
/// magnitude inside the narrowest band. At 1 MiB the same substitution is a 4%
/// error and would eat into it.
const TRIPWIRE_STACK_BYTES: usize = 4 * 1024 * 1024;

/// How far the true per-level cost may exceed the shipped constant before the
/// tripwire fires.
///
/// This is the UNSAFE direction: an understated constant makes
/// [`Budget::MIN_STACK_BYTES`] promise less stack than the descent needs, which
/// is bead `franken_lean-kxbj`'s defect returning. 25% is chosen against two
/// measured facts rather than picked: it is 2.4x the largest host-to-host
/// spread yet observed (10.4%), so ordinary machine variation cannot redden the
/// tree, and it is half of [`Budget::STACK_SAFETY_FACTOR`], so it fires with
/// the whole margin still unspent.
const TRIPWIRE_TOLERANCE_HIGH: f64 = 0.25;

/// How far the true per-level cost may fall BELOW the shipped constant.
///
/// Deliberately looser, because the two directions have different consequences.
/// An overstated constant is not merely wasteful: it shrinks
/// [`Budget::depth_for_stack_bytes`] for every caller, so a legitimate deep
/// term becomes a typed non-answer that nobody can distinguish from a real one
/// — and under `franken_lean-4o3n` a manufactured non-answer is exactly what
/// erodes a consensus seat. It is still not a SAFETY failure, so it is given
/// room that the unsafe direction is not.
const TRIPWIRE_TOLERANCE_LOW: f64 = 0.33;

/// Depth used by the entry-reserve probe. The per-level allowance is placed at
/// the tripwire's accepted low edge, preventing an intentionally conservative
/// slope claim from silently donating its accumulated slack to a false entry
/// reserve. Sixteen levels also keep the requested stack above the platform
/// thread minimum, so a planted low reserve remains observable.
const TRIPWIRE_RESERVE_PROBE_DEPTH: u32 = 16;

/// What the two bracket probes and the reserve probe said about one shape.
#[derive(Debug)]
struct ShapeObservation {
    shape: Shape,
    /// Survived the depth that only fits while this shape's cost is within
    /// [`TRIPWIRE_TOLERANCE_HIGH`] of the claim.
    within_high_bound: bool,
    /// Survived the depth that only fits once this shape's cost has fallen
    /// [`TRIPWIRE_TOLERANCE_LOW`] below the claim.
    below_low_bound: bool,
    /// The claimed entry reserve plus a few levels held a descent of those
    /// levels.
    reserve_covers_entry: bool,
    high_probe_depth: u32,
    low_probe_depth: u32,
    reserve_probe_stack: usize,
}

/// Ask one shape the three questions, against a CLAIMED calibration.
///
/// The claim is a parameter, not a constant read, and that is the whole design:
/// a tripwire that could only ever be handed the shipped numbers could not be
/// shown to discriminate, and a check that cannot fail is a rubber stamp. The
/// planted violations below hand it deliberately wrong claims and require it to
/// refuse each one.
///
/// Note what this does NOT do: it never re-derives the constant and compares
/// the result to itself, which would be the same number twice and would prove
/// nothing. It brackets — it asks the real descent questions whose answers are
/// only all correct when the claim is true.
fn observe_shape(
    shape: Shape,
    claimed_bytes_per_depth: usize,
    claimed_entry_reserve: usize,
) -> ShapeObservation {
    let usable = TRIPWIRE_STACK_BYTES.saturating_sub(claimed_entry_reserve);
    let claimed = claimed_bytes_per_depth.max(1) as f64;

    let depth_at = |cost_per_level: f64| -> u32 {
        ((usable as f64) / cost_per_level)
            .floor()
            .clamp(1.0, f64::from(u32::MAX)) as u32
    };
    let high_probe_depth = depth_at(claimed * (1.0 + TRIPWIRE_TOLERANCE_HIGH));
    let low_probe_depth = depth_at(claimed * (1.0 - TRIPWIRE_TOLERANCE_LOW)).saturating_add(1);
    let reserve_level_bytes = (claimed * (1.0 - TRIPWIRE_TOLERANCE_LOW)).ceil().max(1.0) as usize;
    let reserve_probe_stack =
        claimed_entry_reserve + (TRIPWIRE_RESERVE_PROBE_DEPTH as usize) * reserve_level_bytes;

    ShapeObservation {
        shape,
        within_high_bound: run_probe(shape, TRIPWIRE_STACK_BYTES, high_probe_depth).fits(),
        below_low_bound: run_probe(shape, TRIPWIRE_STACK_BYTES, low_probe_depth).fits(),
        reserve_covers_entry: run_probe(shape, reserve_probe_stack, TRIPWIRE_RESERVE_PROBE_DEPTH)
            .fits(),
        high_probe_depth,
        low_probe_depth,
        reserve_probe_stack,
    }
}

/// Every way a claimed calibration can be refused, over the whole shape set.
///
/// THE TWO DIRECTIONS ARE NOT QUANTIFIED THE SAME WAY, and getting that wrong
/// is how this check would have become a flake generator. The constant is the
/// MAXIMUM over the registered residual descents, so:
///
/// * ABOVE the claim is a property of ANY shape. One descent costing more than
///   the constant says is enough to make `MIN_STACK_BYTES` promise too little,
///   whatever the other three do.
/// * BELOW the claim is a property of ALL shapes AT ONCE. A single cheap
///   descent is not evidence the constant is overstated — the constant is not
///   describing that shape. A cheaper residual descent sitting below the
///   shipped maximum is expected; quantifying the low bound per shape would
///   put a permanent tripwire next to a value that is correct, and the first
///   person to see it fire would have widened the band rather than read it.
fn calibration_refusals(
    claimed_bytes_per_depth: usize,
    claimed_entry_reserve: usize,
) -> Vec<String> {
    let observations: Vec<ShapeObservation> = Shape::ALL
        .into_iter()
        .map(|shape| observe_shape(shape, claimed_bytes_per_depth, claimed_entry_reserve))
        .collect();
    let mut refusals = Vec::new();

    for o in &observations {
        if !o.within_high_bound {
            refusals.push(format!(
                "{:?}: a descent to depth {} did not survive {TRIPWIRE_STACK_BYTES} bytes of \
                 stack, so this shape's per-level cost is more than {:.0}% ABOVE the claimed \
                 {claimed_bytes_per_depth} bytes/depth. MIN_STACK_BYTES now promises less \
                 stack than the descent needs — this is the direction that aborts processes. \
                 Re-run `calibrate_stack_bytes_per_depth` and move \
                 Budget::MEASURED_STACK_BYTES_PER_DEPTH up",
                o.shape,
                o.high_probe_depth,
                TRIPWIRE_TOLERANCE_HIGH * 100.0
            ));
        }
        if !o.reserve_covers_entry {
            refusals.push(format!(
                "{:?}: a stack of {} bytes — the claimed entry reserve of \
                 {claimed_entry_reserve} plus {TRIPWIRE_RESERVE_PROBE_DEPTH} levels at the \
                 accepted low-edge slope — could not hold {TRIPWIRE_RESERVE_PROBE_DEPTH} \
                 levels, so the fixed entry cost has outgrown \
                 Budget::STACK_ENTRY_RESERVE_BYTES and depth_for_stack_bytes over-promises \
                 depth to every caller",
                o.shape, o.reserve_probe_stack
            ));
        }
    }

    if observations.iter().all(|o| o.below_low_bound) {
        refusals.push(format!(
            "every shape survived its low-bound probe (depths {:?}), so the WORST per-level \
             cost is more than {:.0}% BELOW the claimed {claimed_bytes_per_depth} bytes/depth. \
             Not a safety failure and refused anyway: every caller is being handed a \
             shallower ceiling than its stack supports, which manufactures typed non-answers \
             that nobody can tell from real ones. Re-run `calibrate_stack_bytes_per_depth` \
             and move the constant down",
            observations
                .iter()
                .map(|o| o.low_probe_depth)
                .collect::<Vec<_>>(),
            TRIPWIRE_TOLERANCE_LOW * 100.0
        ));
    }

    refusals
}

/// THE TRIPWIRE. The shipped calibration still describes the descent — every
/// shape, both directions, plus the entry reserve.
///
/// Every shape rather than the measured-worst one, because
/// `MEASURED_STACK_BYTES_PER_DEPTH` is the MAXIMUM over the registered descents: a
/// drift that moved a different shape above the shipped figure would be exactly
/// as unsafe and would be invisible to a single-shape check. Six subprocess
/// probes, no bisection.
#[test]
fn the_shipped_calibration_still_describes_the_descent() {
    let refusals = calibration_refusals(
        Budget::MEASURED_STACK_BYTES_PER_DEPTH,
        Budget::STACK_ENTRY_RESERVE_BYTES,
    );
    assert!(
        refusals.is_empty(),
        "the shipped stack calibration no longer describes the kernel:\n  {}",
        refusals.join("\n  ")
    );
}

/// PLANTED VIOLATION — an understated constant is refused. The unsafe
/// direction: half the true cost is what a stale constant looks like after the
/// descent has grown, and it is the shape of `franken_lean-kxbj`'s original
/// defect.
#[test]
fn a_calibration_that_understates_the_cost_is_refused() {
    let claim = Budget::MEASURED_STACK_BYTES_PER_DEPTH / 2;
    let refusals = calibration_refusals(claim, Budget::STACK_ENTRY_RESERVE_BYTES);
    assert!(
        refusals.iter().any(|r| r.contains("ABOVE the claimed")),
        "a constant claiming half the true per-level cost must be refused in the unsafe \
         direction; a tripwire that accepts it is not watching the direction that aborts \
         processes. Got: {refusals:?}"
    );
}

/// PLANTED VIOLATION — an overstated constant is refused. Not a safety failure,
/// and refused anyway: it shrinks every derived ceiling and manufactures the
/// typed non-answers that erode a consensus seat.
#[test]
fn a_calibration_that_overstates_the_cost_is_refused() {
    let claim = Budget::MEASURED_STACK_BYTES_PER_DEPTH * 3;
    let refusals = calibration_refusals(claim, Budget::STACK_ENTRY_RESERVE_BYTES);
    assert!(
        refusals.iter().any(|r| r.contains("BELOW the claimed")),
        "a constant claiming three times the true cost must be refused; every shape is then \
         below it, which is what the all-shapes quantifier is for. Got: {refusals:?}"
    );
}

/// PLANTED VIOLATION — an entry reserve below the true fixed cost is refused.
/// The slope and the intercept drift independently, and on 2026-07-25 it was
/// the intercept that moved while the slope held exactly.
#[test]
fn an_entry_reserve_below_the_fixed_cost_is_refused() {
    let refusals = calibration_refusals(Budget::MEASURED_STACK_BYTES_PER_DEPTH, 8 * 1024);
    assert!(
        refusals.iter().any(|r| r.contains("entry reserve")),
        "an entry reserve of 8 KiB is far below the measured fixed cost and must be refused. \
         Got: {refusals:?}"
    );
}
