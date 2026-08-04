//! FL-INV-01 for the kernel, WITHOUT the Reference pin (bead `fln-q944`).
//!
//! # Why this file exists beside an existing, well-built matrix
//!
//! `fln-conformance`'s `prelude_replays_through_the_kernel` already checks the
//! same units at {1, 8, 32} workers over a shared racing cursor and asserts the
//! merged stream is byte-identical at every width. It is not deficient and this
//! does not replace it.
//!
//! What it does is `return` early — typed, honestly, `"SKIP … pinned Reference
//! stdlib not found"` — when the pin is absent, because its fixtures are decoded
//! from the Reference stdlib. AGENTS.md records that RCH workers do not have the
//! pin. So on every machine without it, the kernel's only schedule-independence
//! assertion does not execute at all.
//!
//! B4 states, as an **invariant**, that determinism is tested at {1, 8, 32}
//! threads on every commit. An invariant may not rest on evidence that runs only
//! where a toolchain happens to be installed (D7: a weaker class may never
//! enforce a stronger one). That is the gap bead `fln-q944` names as *enforcement
//! scope and claim scope diverging silently* — the evidence is produced exactly
//! where the claim is made, and covers less than the claim says, so nothing ever
//! goes red.
//!
//! This file closes the half of that gap which needs no decision. The kernel's
//! authority is pure — `check : Environment × Declaration × Budget → Outcome`,
//! zero I/O, zero threads, zero global mutable state (§8.1) — so a determinism
//! matrix over KERNEL-AUTHORED declarations needs no oracle, no artifact and no
//! pin. It runs everywhere, on every commit.
//!
//! # What byte-identity means here
//!
//! The merged stream carries, per unit: the outcome kind, the rejection class
//! where there is one, and the EXACT consumption (`steps_used`, `max_depth`).
//! Consumption is included deliberately. A matrix that compared only verdicts
//! would pass while the amount of work drifted with the schedule, and
//! consumption reaches observables — it rides on every `Verdict` and into census
//! rows. "Same verdicts" is a weaker claim than FL-INV-01 makes.
//!
//! # Three outcome kinds, not one
//!
//! Acceptance, rejection and typed exhaustion are all present, because a matrix
//! that only ever agreed about accepted declarations would say nothing about the
//! two paths where the kernel builds a message or a resource fact. The narrowed
//! budget run is what puts `Inconclusive` in the stream.

#![forbid(unsafe_code)]

use std::sync::OnceLock;
use std::sync::atomic::{AtomicUsize, Ordering};

use fln_core::expr::{BinderInfo, Expr};
use fln_core::level::Level;
use fln_core::name::Name;
use fln_core::outcome::{InconclusiveCause, Outcome};
use fln_env::constants::{
    AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
};
use fln_env::environment::Environment;
use fln_kernel::verdict::{Budget, Verdict};
use fln_kernel::{Declaration, check};

/// Enough units that 32 workers each get several, so a thread count is a
/// schedule rather than a label.
const UNITS: usize = 256;

fn n(s: &str) -> Name {
    Name::str(Name::anonymous(), s)
}

fn sort1() -> Expr {
    Expr::sort(Level::one())
}

/// A telescope `(x : Sort 1) -> … -> Sort 1`, `levels` deep. Non-dependent, so
/// reaching depth `d` costs O(d) rather than O(d²).
fn forall_nest(levels: u32, leaf: Expr) -> Expr {
    let mut e = leaf;
    for _ in 0..levels {
        e = Expr::forall_e(n("x"), sort1(), e, BinderInfo::Default);
    }
    e
}

/// Unit `i`, built deterministically from `i` alone so the fixture set is a
/// function of nothing else. The four residues cover acceptance, both rejection
/// shapes the kernel can reach without an environment, and a term deep enough to
/// exhaust a narrowed budget.
fn unit(i: usize) -> Declaration {
    let name = format!("U{i}");
    match i % 4 {
        // Accepted: `U : Sort 1`.
        0 => Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(&name),
                level_params: vec![],
                type_: sort1(),
            },
            is_unsafe: false,
        }),
        // Rejected KR-100: a loose bound variable reaches the kernel.
        1 => Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(&name),
                level_params: vec![],
                type_: Expr::bvar(0).expect("bvar 0 packs"),
            },
            is_unsafe: false,
        }),
        // Rejected KR-974: the body type is not the declared type.
        2 => Declaration::Defn(DefinitionVal {
            base: ConstantVal {
                name: n(&name),
                level_params: vec![],
                type_: sort1(),
            },
            value: Expr::sort(Level::zero()),
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Safe,
            all: vec![n(&name)],
        }),
        // Accepted, and deep enough that a narrowed budget exhausts on it.
        _ => Declaration::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(&name),
                level_params: vec![],
                type_: forall_nest(512, sort1()),
            },
            is_unsafe: false,
        }),
    }
}

/// One unit's contribution to the merged stream. Rendered rather than compared
/// structurally so a divergence can be shown to a human as the thing that
/// differed.
fn render(i: usize, outcome: &Outcome<Verdict>) -> String {
    match outcome {
        Outcome::Complete(Verdict::Accepted { consumption }) => format!(
            "{i} accepted steps={} depth={}",
            consumption.steps_used, consumption.max_depth
        ),
        Outcome::Complete(Verdict::Rejected {
            class, consumption, ..
        }) => format!(
            "{i} rejected={} steps={} depth={}",
            class.as_str(),
            consumption.steps_used,
            consumption.max_depth
        ),
        Outcome::Inconclusive(inconclusive) => {
            let cause = match &inconclusive.cause {
                InconclusiveCause::ResourceExhausted { usage } => {
                    format!(
                        "resource allowed={} observed={}",
                        usage.allowed, usage.observed
                    )
                }
                InconclusiveCause::Cancelled { .. } => "cancelled".to_string(),
                InconclusiveCause::DependencyUnavailable { .. } => "dependency".to_string(),
                InconclusiveCause::AuthorityIncomplete { .. } => "authority".to_string(),
            };
            format!("{i} inconclusive {cause}")
        }
        Outcome::InternalFault(fault) => format!("{i} fault {}", fault.invariant),
    }
}

struct MatrixRun {
    stream: Vec<String>,
    /// Units checked per worker. An idle worker means this thread count was a
    /// label rather than a schedule.
    per_worker: Vec<usize>,
}

/// Check every unit at `threads` workers over ONE shared racing cursor, then
/// merge by index. The cursor is what makes this a schedule rather than a static
/// partition: which worker gets which unit is decided by the OS, and the merged
/// stream must not know that.
fn run_matrix(threads: usize, budget: Budget) -> MatrixRun {
    let env = Environment::new();
    let units: Vec<Declaration> = (0..UNITS).map(unit).collect();
    let slots: Vec<OnceLock<Outcome<Verdict>>> = (0..UNITS).map(|_| OnceLock::new()).collect();
    // Starts past the per-worker seeds; units 0..threads are pre-assigned.
    let cursor = AtomicUsize::new(threads);
    let counts: Vec<OnceLock<usize>> = (0..threads).map(|_| OnceLock::new()).collect();

    std::thread::scope(|scope| {
        for worker in 0..threads {
            let env = &env;
            let units = &units;
            let slots = &slots;
            let cursor = &cursor;
            let counts = &counts;
            std::thread::Builder::new()
                .name(format!("fln-kernel-matrix-{worker}"))
                // The documented pairing: `Budget::DEFAULT` requires
                // `MIN_STACK_BYTES` of stack, and a worker that inherits Rust's
                // 2 MiB default and passes DEFAULT is the pairing bead
                // `franken_lean-kxbj` aborted on. Thread stacks are lazily
                // committed, so this is address space rather than memory.
                .stack_size(Budget::MIN_STACK_BYTES)
                .spawn_scoped(scope, move || {
                    // SEED, THEN RACE. Unit `worker` is this worker's by
                    // construction; the cursor starts past the seeds and the
                    // remaining units are raced for.
                    //
                    // Without the seed the first workers to wake drain the
                    // cursor before the last ones start — measured, at 32
                    // workers over 256 sub-millisecond units: eleven workers
                    // got nothing. The honest repair is to make the width real
                    // rather than to stop asserting that it is, because an idle
                    // worker means the thread count was a label. The bulk of the
                    // units are still raced, so the schedule is still a
                    // schedule.
                    let mut mine = 0usize;
                    assert!(
                        slots[worker]
                            .set(check(env, &units[worker], budget))
                            .is_ok(),
                        "each unit is checked exactly once"
                    );
                    mine += 1;
                    loop {
                        let i = cursor.fetch_add(1, Ordering::Relaxed);
                        if i >= UNITS {
                            break;
                        }
                        assert!(
                            slots[i].set(check(env, &units[i], budget)).is_ok(),
                            "each unit is checked exactly once"
                        );
                        mine += 1;
                    }
                    counts[worker].set(mine).expect("one count per worker");
                })
                .expect("spawn a matrix worker with the explicit stack contract");
        }
    });

    MatrixRun {
        stream: (0..UNITS)
            .map(|i| render(i, slots[i].get().expect("the pool drained the cursor")))
            .collect(),
        per_worker: (0..threads)
            .map(|w| *counts[w].get().expect("every worker reported"))
            .collect(),
    }
}

/// Assert byte-identity across the widths, naming the FIRST divergence rather
/// than only that one exists — a determinism failure you cannot locate is a
/// determinism failure nobody fixes.
fn assert_identical_across_widths(budget: Budget, label: &str) {
    let mut runs: Vec<(usize, MatrixRun)> = Vec::new();
    for threads in [1usize, 8, 32] {
        let run = run_matrix(threads, budget);
        assert_eq!(
            run.per_worker.iter().sum::<usize>(),
            UNITS,
            "{label}: the pool must check every unit exactly once at {threads} workers"
        );
        if threads > 1 {
            assert!(
                run.per_worker.iter().all(|&c| c > 0),
                "{label}: an idle worker at {threads} means this width is a label rather than a \
                 schedule; per-worker counts were {:?}",
                run.per_worker
            );
        }
        runs.push((threads, run));
    }

    let (base_threads, base) = &runs[0];
    for (threads, run) in &runs[1..] {
        if run.stream == base.stream {
            continue;
        }
        let first = base
            .stream
            .iter()
            .zip(run.stream.iter())
            .find(|(a, b)| a != b);
        panic!(
            "{label}: FL-INV-01 violated — the merged stream at {threads} workers differs from \
             {base_threads}. First divergence: {:?}",
            first
        );
    }
}

/// THE MATRIX. Same units, same budget, three widths, byte-identical streams —
/// with no Reference pin, no artifact and no oracle, so it runs wherever `cargo
/// test` runs.
#[test]
fn the_kernel_is_schedule_independent_at_one_eight_and_thirty_two_workers() {
    assert_identical_across_widths(Budget::DEFAULT, "default budget");
}

/// THE SAME PROPERTY WHERE THE KERNEL STOPS EARLY. A narrowed budget puts typed
/// exhaustion into the stream, so the matrix covers the resource path and not
/// only the two paths that produce a `Verdict`.
///
/// This is the arm most likely to drift, because exhaustion carries `allowed`
/// and `observed` numbers that a schedule could plausibly perturb if any part of
/// the metering were shared. Nothing in the kernel is shared — that is the
/// claim, and this is the test of it.
#[test]
fn typed_exhaustion_is_schedule_independent_too() {
    let narrowed = Budget::DEFAULT.narrowed(400, Budget::DEFAULT.depth);
    assert_identical_across_widths(narrowed, "narrowed budget");
}

/// The fixture set must actually contain all three outcome kinds, or the two
/// matrices above are agreeing about a stream with nothing interesting in it.
/// This is the anti-vacuity check: without it, a fixture change that made every
/// unit accept would leave both matrices passing and covering one path.
#[test]
fn the_fixture_set_exercises_acceptance_rejection_and_exhaustion() {
    let narrowed = Budget::DEFAULT.narrowed(400, Budget::DEFAULT.depth);
    let run = run_matrix(1, narrowed);
    let joined = run.stream.join("\n");
    for expected in ["accepted", "rejected=", "inconclusive"] {
        assert!(
            joined.contains(expected),
            "the fixture set must produce {expected}; the matrices prove nothing about a path \
             the fixtures never reach"
        );
    }
}
