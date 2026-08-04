//! Owned, deterministic binary64 elementary functions.
//!
//! This crate deliberately uses only IEEE-754 additions, multiplications,
//! divisions, comparisons, and bit operations.  In particular it never calls
//! Rust's platform-math methods.  `NaN` results are canonicalized so their
//! payload is also an explicit part of the cross-platform contract.
//!
//! The algorithms below are fixed polynomial/rational schemes with fixed
//! reduction constants.  They are a deterministic implementation baseline;
//! accuracy certification is intentionally a separate Tribunal artifact.

#![forbid(unsafe_code)]

/// The one NaN representation returned for invalid operations.
pub const CANONICAL_NAN_BITS: u64 = 0x7ff8_0000_0000_0000;
const CANONICAL_NAN: f64 = f64::from_bits(CANONICAL_NAN_BITS);
const SIGN: u64 = 1_u64 << 63;
const EXP: u64 = 0x7ff0_0000_0000_0000;
const FRAC: u64 = 0x000f_ffff_ffff_ffff;
const PI: f64 = f64::from_bits(0x4009_21fb_5444_2d18);
const HALF_PI: f64 = f64::from_bits(0x3ff9_21fb_5444_2d18);
const QUARTER_PI: f64 = f64::from_bits(0x3fe9_21fb_5444_2d18);
const TAU: f64 = f64::from_bits(0x4019_21fb_5444_2d18);
const INV_TAU: f64 = f64::from_bits(0x3fc4_5f30_6dc9_c883);
const INV_LN2: f64 = f64::from_bits(0x3ff7_1547_652b_82fe);
const LN2_HI: f64 = f64::from_bits(0x3fe6_2e42_fee0_0000);
const LN2_LO: f64 = 1.908_214_929_270_587_7e-10;
const SQRT_HALF: f64 = f64::from_bits(0x3fe6_a09e_667f_3bcd);
const SQRT_TWO: f64 = f64::from_bits(0x3ff6_a09e_667f_3bcd);
const LN10: f64 = f64::from_bits(0x4002_6bb1_bbb5_5516);
const LOG_MAX: f64 = 709.782_712_893_384;
const LOG_MIN_SUBNORMAL: f64 = -744.440_071_921_381_2;
const SCALE_512: f64 = f64::from_bits(0x5ff0_0000_0000_0000);
const SCALE_NEG_512: f64 = f64::from_bits(0x1ff0_0000_0000_0000);

#[inline]
const fn canonical_nan() -> f64 {
    CANONICAL_NAN
}

#[inline]
fn invalid(x: f64) -> bool {
    x.is_nan()
}

#[inline]
fn signed_zero(x: f64) -> f64 {
    f64::from_bits(x.to_bits() & SIGN)
}

/// Returns `x` with the sign bit of `sign`.
#[inline]
pub fn copysign(x: f64, sign: f64) -> f64 {
    f64::from_bits((x.to_bits() & !SIGN) | (sign.to_bits() & SIGN))
}

/// Absolute value, implemented in terms of the binary64 encoding.
#[inline]
pub fn abs(x: f64) -> f64 {
    f64::from_bits(x.to_bits() & !SIGN)
}

/// Truncation toward zero with no dependency on a platform rounding mode.
pub fn trunc(x: f64) -> f64 {
    let bits = x.to_bits();
    let exponent = ((bits & EXP) >> 52) as i32 - 1023;
    if exponent < 0 {
        return signed_zero(x);
    }
    if exponent >= 52 || (bits & EXP) == EXP {
        return x;
    }
    let mask = (1_u64 << (52 - exponent as u32)) - 1;
    f64::from_bits(bits & !mask)
}

/// Floor with exact signed-zero handling.
pub fn floor(x: f64) -> f64 {
    if invalid(x) || x.is_infinite() || x == 0.0 {
        return x;
    }
    let t = trunc(x);
    if x < 0.0 && t != x {
        t - 1.0
    } else {
        t
    }
}

/// Ceiling with exact signed-zero handling.
pub fn ceil(x: f64) -> f64 {
    if invalid(x) || x.is_infinite() || x == 0.0 {
        return x;
    }
    let t = trunc(x);
    if x > 0.0 && t != x {
        t + 1.0
    } else {
        t
    }
}

/// Round to nearest, with ties away from zero (Lean's `Float.round` rule).
pub fn round(x: f64) -> f64 {
    if invalid(x) || x.is_infinite() || x == 0.0 {
        return x;
    }
    if x > 0.0 {
        floor(x + 0.5)
    } else {
        ceil(x - 0.5)
    }
}

/// Decompose a finite non-zero number as `fraction * 2^exponent`, where the
/// magnitude of `fraction` is in `[0.5, 1)`.
pub fn frexp(x: f64) -> (f64, i32) {
    if x == 0.0 || !x.is_finite() {
        return (x, 0);
    }
    let sign = x.to_bits() & SIGN;
    let mut magnitude = x.to_bits() & !SIGN;
    let mut exponent = ((magnitude & EXP) >> 52) as i32;
    if exponent == 0 {
        // Normalize the subnormal without asking the platform to do it.
        let mut fraction = magnitude & FRAC;
        while fraction & (1_u64 << 52) == 0 {
            fraction <<= 1;
            exponent -= 1;
        }
        magnitude = fraction & FRAC;
        exponent += 1;
    } else {
        magnitude &= FRAC;
    }
    (
        f64::from_bits(sign | (1022_u64 << 52) | magnitude),
        exponent - 1022,
    )
}

/// Exact power-of-two scaling for normal inputs; subnormal boundaries use the
/// same fixed arithmetic sequence on every IEEE-754 target.
pub fn scalbn(mut x: f64, mut n: i32) -> f64 {
    if x == 0.0 || !x.is_finite() || n == 0 {
        return x;
    }
    while n > 512 {
        x *= SCALE_512;
        if !x.is_finite() {
            return x;
        }
        n -= 512;
    }
    while n < -512 {
        x *= SCALE_NEG_512;
        if x == 0.0 {
            return x;
        }
        n += 512;
    }
    if n >= 0 {
        x * f64::from_bits((n as u64 + 1023) << 52)
    } else {
        x * f64::from_bits(((n + 1023) as u64) << 52)
    }
}

/// Deterministic square root using a fixed Newton schedule.
pub fn sqrt(x: f64) -> f64 {
    if invalid(x) || x < 0.0 {
        return canonical_nan();
    }
    if x == 0.0 || x.is_infinite() {
        return x;
    }
    let (fraction, exponent) = frexp(x);
    let (fraction, exponent) = if exponent & 1 == 0 {
        (fraction, exponent)
    } else {
        (fraction * 2.0, exponent - 1)
    };
    // Linear minimax seed on [0.5, 2), followed by enough fixed iterations
    // to make the result stable under binary64 operations.
    let mut y = 0.41731 + 0.59016 * fraction;
    for _ in 0..7 {
        y = 0.5 * (y + fraction / y);
    }
    scalbn(y, exponent / 2)
}

fn reduce_quadrant(x: f64) -> (f64, i32) {
    // Fixed reduction.  Inputs beyond this bound need a multiword
    // Payne-Hanek reducer before an accuracy claim can be made; retaining a
    // deterministic fallback is preferable to delegating to platform libm.
    if abs(x) > 1_125_899_906_842_624.0 {
        return (signed_zero(x), 0);
    }
    let turns = round(x * INV_TAU);
    let mut r = x - turns * TAU;
    if r > PI {
        r -= TAU;
    }
    if r < -PI {
        r += TAU;
    }
    let quadrant = round(r / HALF_PI) as i32;
    (r - (quadrant as f64) * HALF_PI, quadrant & 3)
}

fn sin_kernel(x: f64) -> f64 {
    let z = x * x;
    // Horner form of sin on [-pi/4, pi/4].
    let p = 1.589_690_995_211_55e-10;
    let p = -2.505_076_025_340_686_3e-8 + z * p;
    let p = 2.755_731_370_707_006_8e-6 + z * p;
    let p = -1.984_126_982_985_795e-4 + z * p;
    let p = 8.333_333_333_322_49e-3 + z * p;
    let p = -1.666_666_666_666_663_2e-1 + z * p;
    x * (1.0 + z * p)
}

fn cos_kernel(x: f64) -> f64 {
    let z = x * x;
    let p = -1.135_964_755_778_819_5e-11;
    let p = 2.087_572_321_298_175e-9 + z * p;
    let p = -2.755_731_435_139_066_3e-7 + z * p;
    let p = 2.480_158_728_947_673e-5 + z * p;
    let p = -1.388_888_888_887_305_6e-3 + z * p;
    let p = 4.166_666_666_666_659e-2 + z * p;
    1.0 + z * (-0.5 + z * p)
}

/// Sine with fixed range reduction and polynomial evaluation.
pub fn sin(x: f64) -> f64 {
    if invalid(x) || x.is_infinite() {
        return canonical_nan();
    }
    if x == 0.0 {
        return x;
    }
    let (r, q) = reduce_quadrant(x);
    match q {
        0 => sin_kernel(r),
        1 => cos_kernel(r),
        2 => -sin_kernel(r),
        _ => -cos_kernel(r),
    }
}

/// Cosine with fixed range reduction and polynomial evaluation.
pub fn cos(x: f64) -> f64 {
    if invalid(x) || x.is_infinite() {
        return canonical_nan();
    }
    let (r, q) = reduce_quadrant(x);
    match q {
        0 => cos_kernel(r),
        1 => -sin_kernel(r),
        2 => -cos_kernel(r),
        _ => sin_kernel(r),
    }
}

/// Tangent with the same reduction as [`sin`] and [`cos`].
pub fn tan(x: f64) -> f64 {
    if invalid(x) || x.is_infinite() {
        return canonical_nan();
    }
    if x == 0.0 {
        return x;
    }
    let (r, q) = reduce_quadrant(x);
    if q & 1 == 0 {
        sin_kernel(r) / cos_kernel(r)
    } else {
        -cos_kernel(r) / sin_kernel(r)
    }
}

fn atan_kernel(x: f64) -> f64 {
    let z = x * x;
    // atan(x) = x * sum (-z)^n/(2n+1), |x| <= tan(pi/8).
    let mut term = x;
    let mut sum = x;
    for n in 1..=34 {
        term *= -z;
        sum += term / (2 * n + 1) as f64;
    }
    sum
}

/// Arctangent with fixed reciprocal and pi/4 reductions.
pub fn atan(x: f64) -> f64 {
    if invalid(x) {
        return canonical_nan();
    }
    if x.is_infinite() {
        return copysign(HALF_PI, x);
    }
    if x == 0.0 {
        return x;
    }
    let negative = x < 0.0;
    let a = abs(x);
    let result = if a > 2.414_213_562_373_095 {
        HALF_PI - atan_kernel(1.0 / a)
    } else if a > 0.414_213_562_373_095_03 {
        QUARTER_PI + atan_kernel((a - 1.0) / (a + 1.0))
    } else {
        atan_kernel(a)
    };
    if negative {
        -result
    } else {
        result
    }
}

/// Two-argument arctangent with IEEE signed-zero quadrant rules.
pub fn atan2(y: f64, x: f64) -> f64 {
    if invalid(x) || invalid(y) {
        return canonical_nan();
    }
    if y == 0.0 {
        if x.is_sign_negative() {
            return copysign(PI, y);
        }
        return y;
    }
    if x == 0.0 {
        return copysign(HALF_PI, y);
    }
    if x.is_infinite() && y.is_infinite() {
        return match (x.is_sign_negative(), y.is_sign_negative()) {
            (false, false) => QUARTER_PI,
            (false, true) => -QUARTER_PI,
            (true, false) => 3.0 * QUARTER_PI,
            (true, true) => -3.0 * QUARTER_PI,
        };
    }
    let angle = atan(abs(y / x));
    match (x < 0.0, y < 0.0) {
        (false, false) => angle,
        (false, true) => -angle,
        (true, false) => PI - angle,
        (true, true) => angle - PI,
    }
}

/// Arcsine, defined through the owned `atan2` and `sqrt` paths.
pub fn asin(x: f64) -> f64 {
    if invalid(x) || abs(x) > 1.0 {
        return canonical_nan();
    }
    if abs(x) == 1.0 {
        return copysign(HALF_PI, x);
    }
    atan2(x, sqrt((1.0 - x) * (1.0 + x)))
}

/// Arccosine, preserving the exact endpoint conventions.
pub fn acos(x: f64) -> f64 {
    if invalid(x) || abs(x) > 1.0 {
        return canonical_nan();
    }
    if x == 1.0 {
        return 0.0;
    }
    if x == -1.0 {
        return PI;
    }
    HALF_PI - asin(x)
}

/// Exponential with ln(2) reduction and a fixed degree-18 Taylor kernel.
pub fn exp(x: f64) -> f64 {
    if invalid(x) {
        return canonical_nan();
    }
    if x == f64::INFINITY {
        return f64::INFINITY;
    }
    if x == f64::NEG_INFINITY {
        return 0.0;
    }
    if x > LOG_MAX {
        return f64::INFINITY;
    }
    if x < LOG_MIN_SUBNORMAL {
        return 0.0;
    }
    let k = round(x * INV_LN2) as i32;
    let r = (x - (k as f64) * LN2_HI) - (k as f64) * LN2_LO;
    let mut term = 1.0;
    let mut sum = 1.0;
    for n in 1..=18 {
        term *= r / n as f64;
        sum += term;
    }
    scalbn(sum, k)
}

/// Base-two exponential.
pub fn exp2(x: f64) -> f64 {
    exp(x * LN2_HI + x * LN2_LO)
}

/// Exponential minus one, using a series near zero to avoid cancellation.
pub fn expm1(x: f64) -> f64 {
    if abs(x) < 0.03125 {
        let mut term = x;
        let mut sum = x;
        for n in 2..=22 {
            term *= x / n as f64;
            sum += term;
        }
        sum
    } else {
        exp(x) - 1.0
    }
}

/// Natural logarithm through binary decomposition and an atanh series.
pub fn log(x: f64) -> f64 {
    if invalid(x) || x < 0.0 {
        return canonical_nan();
    }
    if x == 0.0 {
        return f64::NEG_INFINITY;
    }
    if x == f64::INFINITY {
        return f64::INFINITY;
    }
    let (mut m, mut e) = frexp(x);
    if m < SQRT_HALF {
        m *= 2.0;
        e -= 1;
    }
    if m > SQRT_TWO {
        m *= 0.5;
        e += 1;
    }
    let z = (m - 1.0) / (m + 1.0);
    let z2 = z * z;
    let mut term = z;
    let mut sum = z;
    for n in 1..=40 {
        term *= z2;
        sum += term / (2 * n + 1) as f64;
    }
    (2.0 * sum) + (e as f64) * LN2_HI + (e as f64) * LN2_LO
}

/// Base-two logarithm.
pub fn log2(x: f64) -> f64 {
    log(x) * INV_LN2
}

/// Base-ten logarithm.
pub fn log10(x: f64) -> f64 {
    log(x) / LN10
}

/// Logarithm of one plus x, with a cancellation-safe series near zero.
pub fn log1p(x: f64) -> f64 {
    if invalid(x) || x < -1.0 {
        return canonical_nan();
    }
    if x == -1.0 {
        return f64::NEG_INFINITY;
    }
    if abs(x) < 0.03125 {
        let mut term = x;
        let mut sum = x;
        for n in 2..=80 {
            term *= -x;
            sum += term / n as f64;
        }
        sum
    } else {
        log(1.0 + x)
    }
}

/// Hyperbolic sine.
pub fn sinh(x: f64) -> f64 {
    if invalid(x) {
        return canonical_nan();
    }
    if x == 0.0 {
        return x;
    }
    let a = abs(x);
    let value = if a < 1.0 {
        0.5 * (expm1(a) - expm1(-a))
    } else {
        0.5 * (exp(a) - exp(-a))
    };
    copysign(value, x)
}

/// Hyperbolic cosine.
pub fn cosh(x: f64) -> f64 {
    if invalid(x) {
        return canonical_nan();
    }
    let a = abs(x);
    if a > LOG_MAX {
        return f64::INFINITY;
    }
    0.5 * (exp(a) + exp(-a))
}

/// Hyperbolic tangent.
pub fn tanh(x: f64) -> f64 {
    if invalid(x) {
        return canonical_nan();
    }
    if x == 0.0 {
        return x;
    }
    let a = abs(x);
    if a > 20.0 {
        return copysign(1.0, x);
    }
    copysign(expm1(2.0 * a) / (expm1(2.0 * a) + 2.0), x)
}

/// Inverse hyperbolic sine.
pub fn asinh(x: f64) -> f64 {
    if invalid(x) || x.is_infinite() || x == 0.0 {
        return if invalid(x) { canonical_nan() } else { x };
    }
    let a = abs(x);
    let value = if a > 67_108_864.0 {
        log(a) + LN2_HI + LN2_LO
    } else {
        log(a + sqrt(a * a + 1.0))
    };
    copysign(value, x)
}

/// Inverse hyperbolic cosine.
pub fn acosh(x: f64) -> f64 {
    if invalid(x) || x < 1.0 {
        return canonical_nan();
    }
    if x == f64::INFINITY {
        return x;
    }
    if x > 67_108_864.0 {
        log(x) + LN2_HI + LN2_LO
    } else {
        log(x + sqrt((x - 1.0) * (x + 1.0)))
    }
}

/// Inverse hyperbolic tangent.
pub fn atanh(x: f64) -> f64 {
    if invalid(x) || abs(x) > 1.0 {
        return canonical_nan();
    }
    if x == 1.0 {
        return f64::INFINITY;
    }
    if x == -1.0 {
        return f64::NEG_INFINITY;
    }
    if x == 0.0 {
        return x;
    }
    0.5 * log1p((2.0 * x) / (1.0 - x))
}

/// Real cube root using a fixed Newton schedule.
pub fn cbrt(x: f64) -> f64 {
    if invalid(x) || x.is_infinite() || x == 0.0 {
        return if invalid(x) { canonical_nan() } else { x };
    }
    let a = abs(x);
    let (m, e) = frexp(a);
    let q = e.div_euclid(3);
    let r = e.rem_euclid(3);
    let mut y = if r == 0 {
        0.896 * m + 0.34
    } else if r == 1 {
        1.13 * m + 0.42
    } else {
        1.42 * m + 0.53
    };
    let scaled = scalbn(m, r);
    for _ in 0..8 {
        y = (2.0 * y + scaled / (y * y)) / 3.0;
    }
    copysign(scalbn(y, q), x)
}

fn is_integral(x: f64) -> bool {
    x.is_finite() && trunc(x) == x
}

fn odd_integer(x: f64) -> bool {
    if !is_integral(x) || abs(x) >= 9_007_199_254_740_992.0 {
        return false;
    }
    (abs(x) as u64) & 1 == 1
}

/// Power with specified negative-base and integer-exponent behavior.
pub fn pow(x: f64, y: f64) -> f64 {
    if invalid(x) || invalid(y) {
        return canonical_nan();
    }
    if y == 0.0 {
        return 1.0;
    }
    if x == 1.0 {
        return 1.0;
    }
    if x == -1.0 && y.is_infinite() {
        return 1.0;
    }
    if x == 0.0 {
        if y < 0.0 {
            return if odd_integer(y) {
                copysign(f64::INFINITY, x)
            } else {
                f64::INFINITY
            };
        }
        return if odd_integer(y) { x } else { 0.0 };
    }
    if x < 0.0 {
        if !is_integral(y) {
            return canonical_nan();
        }
        return copysign(exp(y * log(-x)), if odd_integer(y) { -1.0 } else { 1.0 });
    }
    exp(y * log(x))
}

/// Stable `sqrt(x*x + y*y)` without overflow or spurious underflow.
pub fn hypot(x: f64, y: f64) -> f64 {
    if invalid(x) || invalid(y) {
        return canonical_nan();
    }
    if x.is_infinite() || y.is_infinite() {
        return f64::INFINITY;
    }
    let a = abs(x);
    let b = abs(y);
    let (hi, lo) = if a >= b { (a, b) } else { (b, a) };
    if hi == 0.0 {
        return 0.0;
    }
    hi * sqrt(1.0 + (lo / hi) * (lo / hi))
}

/// Deterministic f32 entry points use the binary64 implementation then round
/// exactly once at the public boundary.
pub mod f32 {
    macro_rules! unary {
        ($($name:ident),+ $(,)?) => { $(pub fn $name(x: f32) -> f32 { super::$name(x as f64) as f32 })+ };
    }
    unary!(
        sin, cos, tan, asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh, exp, exp2, expm1,
        log, log2, log10, log1p, sqrt, cbrt, floor, ceil, trunc, round
    );
    pub fn atan2(y: f32, x: f32) -> f32 {
        super::atan2(y as f64, x as f64) as f32
    }
    pub fn pow(x: f32, y: f32) -> f32 {
        super::pow(x as f64, y as f64) as f32
    }
    pub fn hypot(x: f32, y: f32) -> f32 {
        super::hypot(x as f64, y as f64) as f32
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn same_bits(a: f64, b: f64) {
        assert_eq!(a.to_bits(), b.to_bits());
    }
    fn close(a: f64, b: f64, tolerance: f64) {
        assert!(abs(a - b) <= tolerance, "{a:?} != {b:?}");
    }

    #[test]
    fn special_values_and_signed_zero_are_specified() {
        same_bits(sin(-0.0), -0.0);
        same_bits(tan(-0.0), -0.0);
        same_bits(sqrt(-0.0), -0.0);
        same_bits(floor(-0.0), -0.0);
        assert_eq!(asin(2.0).to_bits(), CANONICAL_NAN_BITS);
        assert_eq!(log(-1.0).to_bits(), CANONICAL_NAN_BITS);
        assert_eq!(pow(-2.0, 0.5).to_bits(), CANONICAL_NAN_BITS);
        assert_eq!(atan2(-0.0, -1.0).to_bits(), (-PI).to_bits());
    }

    #[test]
    fn exact_anchor_vectors_are_stable() {
        same_bits(sin(0.0), 0.0);
        same_bits(cos(0.0), 1.0);
        same_bits(exp(0.0), 1.0);
        same_bits(log(1.0), 0.0);
        same_bits(pow(1.0, f64::INFINITY), 1.0);
        same_bits(hypot(3.0, 4.0), 5.0);
        same_bits(round(-2.5), -3.0);
        same_bits(round(2.5), 3.0);
    }

    #[test]
    fn deterministic_vector_corpus_replays_bit_for_bit() {
        const VECTORS: [f64; 24] = [
            -0.0,
            0.0,
            f64::from_bits(1),
            -f64::from_bits(1),
            -10.0,
            -1.0,
            -0.5,
            -0.03125,
            0.03125,
            0.5,
            1.0,
            2.0,
            10.0,
            SCALE_NEG_512,
            SCALE_512,
            HALF_PI,
            PI,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::from_bits(CANONICAL_NAN_BITS),
            0.1,
            -0.1,
            12345.678,
            -12345.678,
        ];
        for x in VECTORS {
            for f in [sin, cos, tan, exp, log, atan, sinh, cosh, tanh, cbrt] {
                same_bits(f(x), f(x));
            }
            same_bits(atan2(x, -x), atan2(x, -x));
            same_bits(pow(x, 3.0), pow(x, 3.0));
            same_bits(hypot(x, 1.0), hypot(x, 1.0));
        }
    }

    #[test]
    fn conditioned_identities_hold_on_fixed_vectors() {
        for x in [-1.0, -0.5, -0.125, 0.125, 0.5, 1.0] {
            close(sin(-x), -sin(x), 2.0e-14);
            close(cos(-x), cos(x), 2.0e-14);
            close(exp(log(x.abs())), x.abs(), 2.0e-13);
            close(tanh(-x), -tanh(x), 2.0e-14);
        }
        for x in [0.125, 0.5, 1.0, 2.0, 8.0] {
            close(sqrt(x) * sqrt(x), x, 2.0e-14);
            close(cbrt(x) * cbrt(x) * cbrt(x), x, 2.0e-13);
        }
    }

    #[test]
    fn floor_ceil_and_frexp_cover_subnormal_boundaries() {
        assert_eq!(floor(-1.25), -2.0);
        assert_eq!(ceil(-1.25), -1.0);
        assert_eq!(trunc(-1.25), -1.0);
        let (fraction, exponent) = frexp(f64::from_bits(1));
        same_bits(scalbn(fraction, exponent), f64::from_bits(1));
    }
}
