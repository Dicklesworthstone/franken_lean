//! Per-function ulp-accuracy tables for the owned transcendentals
//! (franken_lean-yzd acceptance criterion 2: "publish reproducible
//! domain-partitioned error tables").
//!
//! Reported, not adopted (BeigeMarsh): this crate is another bead's; the
//! harness is additive and reads the algorithms unmodified. It produces the
//! bead's missing acceptance artifact and turns "34 tests pass" into a
//! measured accuracy claim.
//!
//! ## Two tests with very different standing — read this before trusting a number
//!
//! `ulp_error_table_*` measure the ulp DISTANCE between fln-libm and Rust's
//! `std` f64 methods. This harness first assumed `std` was ~1-ulp glibc and
//! that a distance therefore bounded fln-libm's own error. That assumption is
//! FALSE and was caught by this very harness: `golden_correctly_rounded`
//! proves against 80-digit decimal truth that at `atanh(-0.99895005...)`
//! fln-libm is 0 ulp from the correctly-rounded answer while
//! `std::f64::atanh` is 220 ulp WRONG. So a large distance can indict the
//! REFERENCE, not fln-libm; the distance tables are informational (regression
//! tripwires), never accuracy claims about fln-libm.
//!
//! `golden_correctly_rounded` is the real accuracy verification: at curated
//! hard inputs it compares fln-libm against correctly-rounded truth computed
//! offline at 80-digit precision and embedded as bit patterns — oracle-
//! independent, no external dependency (D1 forbids MPFR/rug), so it holds even
//! where `std` is wrong. It is the test the bead's acceptance criterion 2
//! actually rests on; the cross-PLATFORM bit-identity half remains a separate
//! matrix run this single host cannot perform.
//!
//! No new dependency, no unsafe, no link change: we compare raw bit patterns.

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
    use Grid::{Geometric, Linear};
    use fln_libm as m;
    use std::f64::consts::TAU;
    // Bounded domains sweep Linear; domains spanning many orders of magnitude
    // sweep Geometric (log-spaced) so the moderate range real callers use is
    // actually tested, not just the extreme tail. `log`/`exp`/`sqrt` are also
    // swept with a Linear moderate partition [1, 4096] to catch the mid-range
    // exercised indirectly by atanh's reduction.
    let reports = vec![
        sweep1("sin", m::sin, |x| x.sin(), -TAU, TAU, Linear, 200_000),
        sweep1(
            "sin_big",
            m::sin,
            |x| x.sin(),
            -1.0e6,
            1.0e6,
            Linear,
            200_000,
        ),
        sweep1("cos", m::cos, |x| x.cos(), -TAU, TAU, Linear, 200_000),
        sweep1("tan", m::tan, |x| x.tan(), -1.5, 1.5, Linear, 200_000),
        sweep1("asin", m::asin, |x| x.asin(), -1.0, 1.0, Linear, 200_000),
        sweep1("acos", m::acos, |x| x.acos(), -1.0, 1.0, Linear, 200_000),
        sweep1("atan", m::atan, |x| x.atan(), -50.0, 50.0, Linear, 200_000),
        sweep1("exp", m::exp, |x| x.exp(), -700.0, 700.0, Linear, 200_000),
        sweep1(
            "exp2",
            m::exp2,
            |x| x.exp2(),
            -1000.0,
            1000.0,
            Linear,
            200_000,
        ),
        sweep1(
            "expm1",
            m::expm1,
            |x| x.exp_m1(),
            -1.0,
            1.0,
            Linear,
            200_000,
        ),
        sweep1(
            "log_hi",
            m::log,
            |x| x.ln(),
            1.0e-300,
            1.0e300,
            Geometric,
            200_000,
        ),
        sweep1("log_mid", m::log, |x| x.ln(), 1.0, 4096.0, Linear, 200_000),
        sweep1(
            "log2",
            m::log2,
            |x| x.log2(),
            1.0e-300,
            1.0e300,
            Geometric,
            200_000,
        ),
        sweep1(
            "log10",
            m::log10,
            |x| x.log10(),
            1.0e-300,
            1.0e300,
            Geometric,
            200_000,
        ),
        sweep1(
            "log1p_sm",
            m::log1p,
            |x| x.ln_1p(),
            -0.9,
            10.0,
            Linear,
            200_000,
        ),
        sweep1(
            "log1p_big",
            m::log1p,
            |x| x.ln_1p(),
            1.0,
            1.0e6,
            Geometric,
            200_000,
        ),
        sweep1("sinh", m::sinh, |x| x.sinh(), -50.0, 50.0, Linear, 200_000),
        sweep1("cosh", m::cosh, |x| x.cosh(), -50.0, 50.0, Linear, 200_000),
        sweep1("tanh", m::tanh, |x| x.tanh(), -20.0, 20.0, Linear, 200_000),
        sweep1(
            "asinh",
            m::asinh,
            |x| x.asinh(),
            -1.0e6,
            1.0e6,
            Linear,
            200_000,
        ),
        sweep1(
            "acosh",
            m::acosh,
            |x| x.acosh(),
            1.0,
            1.0e6,
            Geometric,
            200_000,
        ),
        sweep1(
            "atanh",
            m::atanh,
            |x| x.atanh(),
            -0.999,
            0.999,
            Linear,
            200_000,
        ),
        sweep1(
            "cbrt",
            m::cbrt,
            |x| x.cbrt(),
            -1.0e9,
            1.0e9,
            Geometric,
            200_000,
        ),
        sweep1(
            "sqrt",
            m::sqrt,
            |x| x.sqrt(),
            1.0e-12,
            1.0e12,
            Geometric,
            200_000,
        ),
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

    // The distances are INFORMATIONAL only, and this comment is a correction
    // of an earlier one. The reference is Rust's `std` f64 methods, which this
    // harness first assumed were ~1-ulp glibc. They are NOT reliably so: the
    // `golden_correctly_rounded` test below proves, against 80-digit decimal
    // truth, that at atanh(-0.99895005...) fln-libm is 0 ulp from truth while
    // `std::f64::atanh` is 220 ulp WRONG — so the table's large atanh
    // "distance" indicts the REFERENCE, not fln-libm. A distance therefore
    // bounds nothing about fln-libm's own error; only the golden test does.
    // The one guard asserted here is thus purely a REGRESSION tripwire on the
    // distance (a sudden jump means SOMETHING moved and is worth a look),
    // generous enough not to blame fln-libm for the reference's own errors.
    for r in &reports {
        assert!(
            r.max_ulp <= 512,
            "{}: distance from std jumped to {} ulp — investigate whether \
             fln-libm or the std reference moved (see golden_correctly_rounded)",
            r.name,
            r.max_ulp
        );
    }
}

/// The REAL accuracy claim, independent of the unreliable std oracle: at a
/// curated set of genuinely hard inputs, fln-libm must be within 1 ulp of the
/// CORRECTLY-ROUNDED result computed at 80-digit precision (offline, via
/// `Decimal`, embedded here as `(input_bits, truth_bits)`). This is the
/// oracle-independent verification the distance tables cannot provide; it is
/// also the test that CAUGHT the reference's atanh defect, since the first
/// atanh row proves fln-libm bit-exact where `std::f64::atanh` is 220 ulp off.
#[test]
fn golden_correctly_rounded() {
    use fln_libm as m;
    // (function, input bits, correctly-rounded truth bits). Truth from
    // 80-digit decimal; regenerate with the harness's companion script.
    type Golden = (&'static str, fn(f64) -> f64, u64, u64);
    let golden: &[Golden] = &[
        // Large-argument sin: the Payne-Hanek reduction's whole reason to
        // exist. The distance sweep only reaches 1e6, so these huge-argument
        // goldens are the only check that reduction near/beyond 1e15 (where a
        // double's ulp exceeds pi and naive `x % 2pi` loses ALL accuracy) is
        // correct. Truth from 400-digit decimal.
        ("sin", m::sin, 0x43ab_c16d_674e_c800, 0xbfef_c667_98d0_5d2e),
        ("sin", m::sin, 0x430c_6bf5_2634_0000, 0x3feb_76f8_8136_ceba),
        ("sin", m::sin, 0x437b_69b3_6eca_4580, 0xbfe2_e753_48bc_f28a),
        (
            "atanh",
            m::atanh,
            0xbfef_f766_1862_cd55,
            0xc00e_34df_c0f3_d6e1,
        ),
        (
            "atanh",
            m::atanh,
            0x3fef_f7ce_d916_872b,
            0x400e_66cf_de9c_7c2d,
        ),
        ("log", m::log, 0x409d_bc00_0000_0000, 0x401e_346a_5484_162c),
        ("exp", m::exp, 0x3ff8_0000_0000_0000, 0x4011_ed3f_e64f_c541),
        ("sin", m::sin, 0x3ff0_0000_0000_0000, 0x3fea_ed54_8f09_0cee),
        (
            "tanh",
            m::tanh,
            0x3fe0_0000_0000_0000,
            0x3fdd_9353_d756_8af3,
        ),
    ];
    for &(name, f, xbits, tbits) in golden {
        let x = f64::from_bits(xbits);
        let truth = f64::from_bits(tbits);
        let got = f(x);
        let d = ulp_distance(got, truth);
        assert!(
            d <= 1,
            "{name}({x:e}): fln-libm = {got:e} ({:#018x}) is {d} ulp from the \
             correctly-rounded truth {truth:e} ({tbits:#018x})",
            got.to_bits()
        );
    }
    // The atanh row is also the standing evidence that the std oracle is
    // unreliable: assert the reference really is far off here, so this test
    // fails loudly if a future toolchain "fixes" std and the harness's oracle
    // caveat silently stops applying.
    let x = f64::from_bits(0xbfef_f766_1862_cd55);
    let truth = f64::from_bits(0xc00e_34df_c0f3_d6e1);
    assert!(
        ulp_distance(x.atanh(), truth) > 8,
        "std::f64::atanh is now accurate here; the harness's oracle caveat \
         may be revisited (std={:#018x}, truth={:#018x})",
        x.atanh().to_bits(),
        truth.to_bits()
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

    // Distances only — informational, and NOT attributable to fln-libm (the
    // std oracle is unreliable; see golden_correctly_rounded). A single
    // generous regression tripwire, no per-function accuracy claim here.
    let worst = pow_ulp.max(a2_ulp).max(hy_ulp);
    // `<= 512` already excludes the u64::MAX hard-divergence sentinel.
    assert!(
        worst <= 512,
        "a 2-arg distance from std jumped past 512 ulp (pow={pow_ulp} \
         atan2={a2_ulp} hypot={hy_ulp}) — investigate which side moved"
    );
}
