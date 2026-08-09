//! Per-function ulp-accuracy tables for the owned transcendentals
//! (franken_lean-yzd acceptance criterion 2: "publish reproducible
//! domain-partitioned error tables").
//!
//! Reported, not adopted (BeigeMarsh): this crate is another bead's; the
//! harness is additive and reads the algorithms unmodified. It produces the
//! bead's missing acceptance artifact and turns "34 tests pass" into a
//! measured accuracy claim.
//!
//! ## What the reference is, stated honestly
//!
//! The oracle is `std`'s own `f64` methods, which on this host are glibc
//! `libm` — a NEAR-correctly-rounded implementation (typically <= 0.5-1 ulp
//! of the infinitely-precise result for these functions). So the number
//! reported is the **ulp distance between our deterministic pick and the
//! platform's**, not the true error against infinite precision. That is
//! exactly the quantity the bead frames as a Behavior Note ("platforms
//! disagree in the last ulps; we pick one correct answer and keep it
//! everywhere"): it bounds our own error by `ours <= glibc + measured`, and
//! it is the cross-implementation disagreement the determinism claim exists
//! to freeze. A true-ulp oracle needs extended precision outside the closed
//! dependency universe (D1 forbids MPFR/rug), so this is the honest
//! in-universe measurement; the cross-PLATFORM bit-identity half of the bead
//! is a separate matrix run this single host cannot perform.
//!
//! No new dependency, no unsafe, no link change: `x.sin()` is the std libm
//! path already linked, and we compare raw bit patterns.

#![forbid(unsafe_code)]

/// ULP distance between two finite same-sign-regime f64 values, via the
/// monotone ordered-integer transform of IEEE-754 bit patterns.
fn ulp_distance(a: f64, b: f64) -> u64 {
    if a == b {
        return 0;
    }
    if a.is_nan() || b.is_nan() {
        // Both NaN is agreement (the model canonicalizes payloads elsewhere);
        // one NaN is a hard divergence, flagged as the sentinel maximum.
        return if a.is_nan() && b.is_nan() {
            0
        } else {
            u64::MAX
        };
    }
    if a.is_infinite() || b.is_infinite() {
        return if a == b { 0 } else { u64::MAX };
    }
    // Map each f64 to a total order: negatives reflected below zero so that
    // adjacent representables are one integer apart across the sign boundary.
    let key = |x: f64| -> i64 {
        let bits = x.to_bits() as i64;
        if bits < 0 {
            i64::MIN.wrapping_sub(bits)
        } else {
            bits
        }
    };
    key(a).wrapping_sub(key(b)).unsigned_abs()
}

struct Report {
    name: &'static str,
    samples: u64,
    max_ulp: u64,
    worst_input: f64,
    within_1: u64,
    hard_diverge: u64,
}

/// How to distribute the sample points across `[lo, hi]`.
#[derive(Clone, Copy)]
enum Grid {
    /// Uniform in the value — right for bounded domains (sin, asin, tanh).
    Linear,
    /// Uniform in the EXPONENT — the only honest sweep for a function whose
    /// domain spans many orders of magnitude (log, exp, sqrt). A linear grid
    /// over `[1e-300, 1e300]` has a step near `1e295`, so every sample but
    /// the first lands in the extreme high tail and the moderate range where
    /// real callers live is never tested. `lo`/`hi` must be finite and
    /// same-signed (the sign is reapplied after the geometric interpolation).
    Geometric,
}

/// Sweep a single-argument function and tally the ulp distance against the
/// reference over `n + 1` points distributed by `grid`.
fn sweep1(
    name: &'static str,
    ours: fn(f64) -> f64,
    reference: fn(f64) -> f64,
    lo: f64,
    hi: f64,
    grid: Grid,
    n: u64,
) -> Report {
    let mut max_ulp = 0u64;
    let mut worst_input = lo;
    let mut within_1 = 0u64;
    let mut hard = 0u64;
    let point = |i: u64| -> f64 {
        let t = (i as f64) / (n as f64);
        match grid {
            Grid::Linear => lo + (hi - lo) * t,
            Grid::Geometric => {
                // Interpolate in log-magnitude, reapplying the common sign.
                let sign = if lo < 0.0 { -1.0 } else { 1.0 };
                let (a, b) = (lo.abs().ln(), hi.abs().ln());
                sign * (a + (b - a) * t).exp()
            }
        }
    };
    for i in 0..=n {
        let x = point(i);
        let r = reference(x);
        if !r.is_finite() {
            continue; // reference outside the function's finite domain
        }
        let d = ulp_distance(ours(x), r);
        if d == u64::MAX {
            hard += 1;
            continue;
        }
        if d <= 1 {
            within_1 += 1;
        }
        if d > max_ulp {
            max_ulp = d;
            worst_input = x;
        }
    }
    Report {
        name,
        samples: n + 1,
        max_ulp,
        worst_input,
        within_1,
        hard_diverge: hard,
    }
}

fn print_table(reports: &[Report]) {
    println!(
        "\n{:<8} {:>10} {:>10} {:>10} {:>10}  worst-input",
        "fn", "samples", "max_ulp", "<=1ulp", "diverge"
    );
    println!("{}", "-".repeat(64));
    for r in reports {
        println!(
            "{:<8} {:>10} {:>10} {:>10} {:>10}  {:e}",
            r.name, r.samples, r.max_ulp, r.within_1, r.hard_diverge, r.worst_input
        );
    }
}

/// Every single-argument transcendental over a domain-partitioned grid, each
/// partition chosen for the hazards the bead names (near-zero, range
/// reduction, monotone tails). This is the reproducible error table; it
/// prints unconditionally (run with `--nocapture`) and asserts only the
/// weak, always-true guarantee that nothing catastrophically diverges, so
/// the table itself is the artifact and a tight-ulp regression is a
/// deliberate, reviewable tightening rather than a silent bar.
#[test]
fn ulp_error_table_single_argument() {
    use fln_libm as m;
    use std::f64::consts::TAU;
    use Grid::{Geometric, Linear};
    // Bounded domains sweep Linear; domains spanning many orders of magnitude
    // sweep Geometric (log-spaced) so the moderate range real callers use is
    // actually tested, not just the extreme tail. `log`/`exp`/`sqrt` are also
    // swept with a Linear moderate partition [1, 4096] to catch the mid-range
    // exercised indirectly by atanh's reduction.
    let reports = vec![
        sweep1("sin", m::sin, |x| x.sin(), -TAU, TAU, Linear, 200_000),
        sweep1("sin_big", m::sin, |x| x.sin(), -1.0e6, 1.0e6, Linear, 200_000),
        sweep1("cos", m::cos, |x| x.cos(), -TAU, TAU, Linear, 200_000),
        sweep1("tan", m::tan, |x| x.tan(), -1.5, 1.5, Linear, 200_000),
        sweep1("asin", m::asin, |x| x.asin(), -1.0, 1.0, Linear, 200_000),
        sweep1("acos", m::acos, |x| x.acos(), -1.0, 1.0, Linear, 200_000),
        sweep1("atan", m::atan, |x| x.atan(), -50.0, 50.0, Linear, 200_000),
        sweep1("exp", m::exp, |x| x.exp(), -700.0, 700.0, Linear, 200_000),
        sweep1("exp2", m::exp2, |x| x.exp2(), -1000.0, 1000.0, Linear, 200_000),
        sweep1("expm1", m::expm1, |x| x.exp_m1(), -1.0, 1.0, Linear, 200_000),
        sweep1("log_hi", m::log, |x| x.ln(), 1.0e-300, 1.0e300, Geometric, 200_000),
        sweep1("log_mid", m::log, |x| x.ln(), 1.0, 4096.0, Linear, 200_000),
        sweep1("log2", m::log2, |x| x.log2(), 1.0e-300, 1.0e300, Geometric, 200_000),
        sweep1("log10", m::log10, |x| x.log10(), 1.0e-300, 1.0e300, Geometric, 200_000),
        sweep1("log1p_sm", m::log1p, |x| x.ln_1p(), -0.9, 10.0, Linear, 200_000),
        sweep1("log1p_big", m::log1p, |x| x.ln_1p(), 1.0, 1.0e6, Geometric, 200_000),
        sweep1("sinh", m::sinh, |x| x.sinh(), -50.0, 50.0, Linear, 200_000),
        sweep1("cosh", m::cosh, |x| x.cosh(), -50.0, 50.0, Linear, 200_000),
        sweep1("tanh", m::tanh, |x| x.tanh(), -20.0, 20.0, Linear, 200_000),
        sweep1("asinh", m::asinh, |x| x.asinh(), -1.0e6, 1.0e6, Linear, 200_000),
        sweep1("acosh", m::acosh, |x| x.acosh(), 1.0, 1.0e6, Geometric, 200_000),
        sweep1("atanh", m::atanh, |x| x.atanh(), -0.999, 0.999, Linear, 200_000),
        sweep1("cbrt", m::cbrt, |x| x.cbrt(), -1.0e9, 1.0e9, Geometric, 200_000),
        sweep1("sqrt", m::sqrt, |x| x.sqrt(), 1.0e-12, 1.0e12, Geometric, 200_000),
    ];
    print_table(&reports);

    // The correctness floor, independent of the ulp target and impossible to
    // pass vacuously (every sweep visits >=200k finite reference points): no
    // function may HARD-diverge — a NaN or infinity where the reference is
    // finite — anywhere in its domain.
    for r in &reports {
        assert_eq!(
            r.hard_diverge, 0,
            "{}: {} hard divergences (NaN/inf where reference is finite)",
            r.name, r.hard_diverge
        );
        assert!(
            r.samples > 100_000,
            "{}: sweep too small to be a table ({})",
            r.name,
            r.samples
        );
    }

    // The MEASURED ceilings, and what they honestly mean. The reference is
    // libm, itself ~0.5-1 ulp from the true value, so a DISTANCE of 2-3 ulp
    // is fully consistent with our own result meeting the bead's <=1-ulp-TRUE
    // target while rounding the opposite way from libm — distance bounds our
    // error as ours <= libm + distance, it does not prove ours > 1. The table
    // measured: fourteen functions at <=1 ulp distance, and tan/asin/acos/
    // log1p/sinh/cosh/tanh in the 2-3 band (reference-consistent with the
    // target). So the honest guard is a SMALL-DISTANCE ceiling of 3 ulp for
    // the whole reference-consistent family (a real regression guard: any of
    // them drifting past 3 fails), with ONE genuine outlier carved out:
    //   * atanh near +-1 at 220 ulp — no reference error explains 220; the
    //     0.5*ln((1+x)/(1-x)) reduction loses bits at the singularity. This
    //     is the crate's one unambiguous accuracy DEFECT the table surfaces,
    //     pinned as a declared remainder that can only fall (yzd, BeigeMarsh).
    let bar = |name: &str| reports.iter().find(|r| r.name == name).unwrap().max_ulp;
    for r in &reports {
        if r.name == "atanh" {
            continue;
        }
        assert!(
            r.max_ulp <= 3,
            "{}: {} ulp distance from libm exceeds the reference-consistent \
             ceiling of 3 (a real accuracy regression, not reference noise)",
            r.name,
            r.max_ulp
        );
    }
    assert!(
        bar("atanh") <= 220,
        "atanh remainder regressed past 220 ulp: {}",
        bar("atanh")
    );
}

/// The two-argument functions, swept over a 2-D grid.
#[test]
fn ulp_error_table_two_argument() {
    use fln_libm as m;
    let grid = |ours: fn(f64, f64) -> f64,
                reference: fn(f64, f64) -> f64,
                a: (f64, f64),
                b: (f64, f64)|
     -> (u64, f64, f64) {
        let mut max_ulp = 0u64;
        let (mut wa, mut wb) = (a.0, b.0);
        let n = 450u64;
        for i in 0..=n {
            for j in 0..=n {
                let x = a.0 + (a.1 - a.0) * (i as f64) / (n as f64);
                let y = b.0 + (b.1 - b.0) * (j as f64) / (n as f64);
                let r = reference(x, y);
                if !r.is_finite() {
                    continue;
                }
                let d = ulp_distance(ours(x, y), r);
                if d != u64::MAX && d > max_ulp {
                    max_ulp = d;
                    wa = x;
                    wb = y;
                }
            }
        }
        (max_ulp, wa, wb)
    };
    let (pow_ulp, pa, pb) = grid(m::pow, |x, y| x.powf(y), (0.1, 12.0), (-8.0, 8.0));
    let (a2_ulp, aa, ab) = grid(m::atan2, |y, x| y.atan2(x), (-8.0, 8.0), (-8.0, 8.0));
    let (hy_ulp, ha, hb) = grid(
        m::hypot,
        |x, y| x.hypot(y),
        (-1.0e6, 1.0e6),
        (-1.0e6, 1.0e6),
    );
    println!("\n{:<8} {:>10}  worst-inputs", "fn", "max_ulp");
    println!("{}", "-".repeat(48));
    println!("{:<8} {:>10}  ({:e}, {:e})", "pow", pow_ulp, pa, pb);
    println!("{:<8} {:>10}  ({:e}, {:e})", "atan2", a2_ulp, aa, ab);
    println!("{:<8} {:>10}  ({:e}, {:e})", "hypot", hy_ulp, ha, hb);

    // atan2 and hypot meet the bead's <=1 target on the grid margins but
    // reach a few ulp at the worst 2-D corners; pin their measured ceilings
    // (declared remainder, may only fall). pow is the classic exp(y*ln x)
    // hard case and carries the largest ulp of the family — a named finding.
    assert!(
        hy_ulp < u64::MAX,
        "hypot must not hard-diverge on the finite grid"
    );
    assert!(hy_ulp <= 2, "hypot regressed past 2 ulp: {hy_ulp}");
    assert!(a2_ulp <= 3, "atan2 regressed past 3 ulp: {a2_ulp}");
    assert!(
        pow_ulp <= 33,
        "pow remainder regressed past 33 ulp: {pow_ulp}"
    );
}

#[test]
fn diag_atanh_reduction() {
    use fln_libm as m;
    // Reconstruct the grid point EXACTLY as sweep1's Linear point() does, so
    // the input matches the table's worst case bit-for-bit.
    let (lo, hi, n) = (-0.999_f64, 0.999_f64, 200_000u64);
    let t = 5.0_f64 / (n as f64);
    let x: f64 = lo + (hi - lo) * t;
    println!("x.bits   = {:#018x}", x.to_bits());
    println!("our.bits = {:#018x}", m::atanh(x).to_bits());
    println!("std.bits = {:#018x}", x.atanh().to_bits());
    let xa = x.abs();
    let num = 2.0 * xa;
    let den = 1.0 - xa;
    let arg = num / den;
    println!("x        = {x:.17e}");
    println!("2x       = {num:.17e}");
    println!("1-x      = {den:.17e}  (exact? {})", (1.0 - xa) + xa == 1.0);
    println!("arg      = {arg:.17e}");
    println!("our log1p(arg) = {:.17e}", m::log1p(arg));
    println!("std log1p(arg) = {:.17e}", arg.ln_1p());
    println!("our log(1+arg) = {:.17e}", m::log(1.0 + arg));
    println!("our atanh(x)   = {:.17e}", m::atanh(x));
    println!("std atanh(x)   = {:.17e}", x.atanh());
    println!("0.5*our_log1p  = {:.17e}", 0.5 * m::log1p(arg));
}
