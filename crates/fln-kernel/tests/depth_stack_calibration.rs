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
use fln_kernel::{Declaration, check, check_def_eq};

// ---------------------------------------------------------------------------
// Probe shapes
// ---------------------------------------------------------------------------

/// The distinct mutually-recursive descents that thread `depth`. Each shape is
/// built so that reaching depth `d` costs `O(d)` work, not `O(d^2)`: every
/// binder is non-dependent, so `open_binder`/`instantiate` prune on the loose
/// bvar flag and contribute no work per level. That keeps a bisection over
/// depth cheap enough to run to 32k.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Shape {
    /// `infer`/`infer_core` down a `forall` telescope (KR-108).
    ForallInfer,
    /// `infer`/`infer_core` down a `lam` telescope (KR-107) — `ensure_sort_of`,
    /// `open_binder` and `abstract_fvar` all live on this frame.
    LamInfer,
    /// `infer_core` down a right-nested application spine (KR-106): the
    /// widest `infer_core` arm, carrying `whnf`, `is_def_eq` and `instantiate`
    /// calls in the same frame.
    AppInfer,
    /// `is_def_eq` → `quick_def_eq_rules` → `is_def_eq` binder congruence
    /// (KR-302). Two kernel frames per unit of depth.
    DefEqBinder,
}

impl Shape {
    const ALL: [Shape; 4] = [
        Shape::ForallInfer,
        Shape::LamInfer,
        Shape::AppInfer,
        Shape::DefEqBinder,
    ];

    fn as_str(self) -> &'static str {
        match self {
            Shape::ForallInfer => "forall_infer",
            Shape::LamInfer => "lam_infer",
            Shape::AppInfer => "app_infer",
            Shape::DefEqBinder => "defeq_binder",
        }
    }

    fn parse(s: &str) -> Option<Shape> {
        Shape::ALL.into_iter().find(|shape| shape.as_str() == s)
    }
}

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn sort1() -> Expr {
    Expr::sort(Level::one())
}

fn prop() -> Expr {
    Expr::sort(Level::zero())
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

/// `(x : Sort 1) -> ... -> leaf`, `levels` binders deep, none of them used in
/// the body (so the binder machinery prunes and the cost stays linear).
fn forall_nest(levels: u32, leaf: Expr) -> Expr {
    let mut e = leaf;
    for _ in 0..levels {
        e = Expr::forall_e(n("x"), sort1(), e, BinderInfo::Default);
    }
    e
}

/// `fun (x : Sort 1) => ... => leaf`, `levels` binders deep.
fn lam_nest(levels: u32, leaf: Expr) -> Expr {
    let mut e = leaf;
    for _ in 0..levels {
        e = Expr::lam(n("x"), sort1(), e, BinderInfo::Default);
    }
    e
}

/// What a probe run submits to the kernel's public authority.
enum Probe {
    Decl(Environment, Declaration),
    DefEq(Environment, Expr, Expr),
}

impl Probe {
    fn run(&self, budget: Budget) -> Outcome<Verdict> {
        match self {
            Probe::Decl(env, decl) => check(env, decl, budget),
            Probe::DefEq(env, lhs, rhs) => check_def_eq(env, &[], lhs, rhs, budget),
        }
    }
}

/// Builds a term guaranteed to force the descent past `levels` units of depth.
fn build_probe(shape: Shape, levels: u32) -> Probe {
    match shape {
        Shape::ForallInfer => {
            // `A : (x : Sort 1) -> ... -> Sort 1`. `check_inner` infers the
            // type, which walks the whole telescope.
            Probe::Decl(
                Environment::new(),
                axiom_decl("Probe", forall_nest(levels, sort1())),
            )
        }
        Shape::LamInfer => {
            // `d : (x : Sort 1) -> ... -> Sort 1 := fun x => ... => Prop`.
            // Both halves walk the telescope; the value's walk is the KR-107 arm.
            Probe::Decl(
                Environment::new(),
                defn_decl(
                    "Probe",
                    forall_nest(levels, sort1()),
                    lam_nest(levels, prop()),
                ),
            )
        }
        Shape::AppInfer => {
            // `T : Sort 1`, `f : T -> T`, `a : T`; term `f (f (... (f a)))`.
            // The spine is right-nested, so `infer_core` descends the argument.
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
        Shape::DefEqBinder => {
            // Two lambda telescopes of equal shape that differ only at the
            // leaf: KR-302 binder congruence must descend all the way before
            // it can decide, and it decides `false` at the bottom.
            Probe::DefEq(
                Environment::new(),
                lam_nest(levels, prop()),
                lam_nest(levels, sort1()),
            )
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
                ResourceReason::Heartbeats { .. } => "STEPS_EXHAUSTED".to_string(),
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
            let budget = Budget {
                steps: u64::MAX,
                depth,
            };
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
/// Every shape, because the guarantee is over the whole mutually recursive
/// descent, not over whichever one happened to be measured deepest.
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

impl Shape {
    /// The shape used by the reproduction witness: the deepest-per-level
    /// descent measured by `calibrate_stack_bytes_per_depth`, i.e. the one
    /// that overflows first.
    const WITNESS: Shape = Shape::DefEqBinder;
}
