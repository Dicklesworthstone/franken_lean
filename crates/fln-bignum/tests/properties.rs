//! Property and metamorphic laws for the owned bignum core (bead
//! `franken_lean-npl`, KR-313 / plan §8.4).
//!
//! `fln-bignum` replaces GMP under every literal the kernel reduces, so a defect
//! here is kernel-critical: it does not produce a wrong answer in one tactic, it
//! produces a wrong answer inside a trusted judgment. The committed corpus
//! (`fixtures/nat_vectors.txt`, 5 725 vectors from CPython) pins curated values;
//! this suite covers what a fixed corpus cannot — arbitrary operands, at limb
//! edges, under the algebraic laws that must hold for every one of them.
//!
//! **Lean `Nat` semantics are the specification, not mathematics.** Three of
//! them are exactly where an owned bignum drifts from a mathematical one, and a
//! naive implementation gets them wrong in the direction a plain arithmetic
//! property test calls *correct*:
//!
//! * truncated subtraction saturates at zero — never underflows, never wraps;
//! * `x / 0 = 0`;
//! * `x % 0 = x`.
//!
//! Three oracles, layered so each covers the others' blind spot: an independent
//! `u128` model for operands that fit (validated here against the committed
//! corpus where they overlap), the algebraic laws for operands that do not, and
//! representation invariants that must hold after every operation.
//!
//! Deterministic and replayable: fixed seeds, a dependency-free generator (D1
//! covers the apparatus too), and every failure prints the operands in decimal
//! and limb form plus the seed and trial that produced them.

use fln_bignum::interop::{bignat_from_literal, literal_from_bignat};
use fln_bignum::nat::BigNat;

// ---------------------------------------------------------------------------
// Deterministic generation
// ---------------------------------------------------------------------------

/// SplitMix64 — owned, so the corpus is reproducible without a dependency.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next_u64() % n
    }

    /// A limb drawn from a distribution that lands on the edges far more often
    /// than uniform sampling would: all-zero, all-one, and the values one step
    /// either side of a limb boundary are where carries and borrows break.
    fn limb(&mut self) -> u64 {
        match self.below(8) {
            0 => 0,
            1 => 1,
            2 => u64::MAX,
            3 => u64::MAX - 1,
            4 => 1u64 << 63,
            5 => (1u64 << 63) - 1,
            6 => 0xaaaa_aaaa_aaaa_aaaa,
            _ => self.next_u64(),
        }
    }

    fn bignat(&mut self, max_limbs: u64) -> BigNat {
        let count = self.below(max_limbs + 1);
        let limbs: Vec<u64> = (0..count).map(|_| self.limb()).collect();
        BigNat::from_limbs_le(limbs)
    }
}

const SEEDS: [u64; 3] = [
    0x0000_0000_0000_002a,
    0x5eed_bad0_c0ff_ee11,
    0xfeed_face_cafe_d00d,
];
const TRIALS: usize = 200;
/// Operands stay small enough that `mul`, `pow` and the division loop are cheap;
/// the laws do not get truer with wider inputs, and the corpus covers width.
const MAX_LIMBS: u64 = 4;

/// Values that sit exactly on the representation's seams: zero and one, the top
/// and bottom of a limb, both sides of every limb boundary up to three limbs,
/// and operands that straddle one.
fn edge_corpus() -> Vec<BigNat> {
    let mut out = vec![
        BigNat::zero(),
        BigNat::from_u64(1),
        BigNat::from_u64(2),
        BigNat::from_u64(u64::MAX),
        BigNat::from_u64(u64::MAX - 1),
        BigNat::from_u64(1u64 << 63),
        BigNat::from_limbs_le(vec![0, 1]),               // 2^64
        BigNat::from_limbs_le(vec![1, 1]),               // 2^64 + 1
        BigNat::from_limbs_le(vec![u64::MAX, 1]),        // 2^65 - 1
        BigNat::from_limbs_le(vec![u64::MAX, u64::MAX]), // 2^128 - 1
        BigNat::from_limbs_le(vec![0, 0, 1]),            // 2^128
        BigNat::from_limbs_le(vec![1, 0, 1]),            // 2^128 + 1
        BigNat::from_limbs_le(vec![u64::MAX, 0, 1]),
        BigNat::from_limbs_le(vec![0, u64::MAX, 0, 1]),
        BigNat::from_limbs_le(vec![u64::MAX, u64::MAX, u64::MAX]),
        BigNat::from_limbs_le(vec![0xaaaa_aaaa_aaaa_aaaa, 0x5555_5555_5555_5555]),
        BigNat::from_limbs_le(vec![0x5555_5555_5555_5555, 0xaaaa_aaaa_aaaa_aaaa]),
    ];
    // Straddlers: one below, at, and one above each limb boundary.
    for limbs in 1..=3u32 {
        let boundary = BigNat::from_u64(1).shl(u64::from(limbs) * 64);
        out.push(boundary.sub(&BigNat::from_u64(1)));
        out.push(boundary.clone());
        out.push(boundary.add(&BigNat::from_u64(1)));
    }
    out
}

fn show(value: &BigNat) -> String {
    format!("{} (limbs {:?})", value.to_decimal(), value.limbs_le())
}

// ---------------------------------------------------------------------------
// The independent `u128` model — Lean semantics, written out explicitly
// ---------------------------------------------------------------------------

fn to_u128(value: &BigNat) -> Option<u128> {
    match value.limbs_le() {
        [] => Some(0),
        [lo] => Some(u128::from(*lo)),
        [lo, hi] => Some((u128::from(*hi) << 64) | u128::from(*lo)),
        _ => None,
    }
}

fn from_u128(value: u128) -> BigNat {
    BigNat::from_limbs_le(vec![value as u64, (value >> 64) as u64])
}

/// Lean `Nat` operations on `u128`, saturating and zero-law-obeying. Checked
/// arithmetic everywhere, so the model reports "out of range" instead of
/// wrapping and silently agreeing with a wrapping bug.
mod model {
    pub fn add(a: u128, b: u128) -> Option<u128> {
        a.checked_add(b)
    }
    pub fn sub(a: u128, b: u128) -> u128 {
        a.saturating_sub(b)
    }
    pub fn mul(a: u128, b: u128) -> Option<u128> {
        a.checked_mul(b)
    }
    /// Lean: `x / 0 = 0`. The `unwrap_or` value *is* the law — `checked_div`
    /// yields `None` on exactly the divisor the law is about.
    pub fn div(a: u128, b: u128) -> u128 {
        a.checked_div(b).unwrap_or(0)
    }
    /// Lean: `x % 0 = x`, stated the same way as its `div` partner.
    pub fn rem(a: u128, b: u128) -> u128 {
        a.checked_rem(b).unwrap_or(a)
    }
    pub fn gcd(mut a: u128, mut b: u128) -> u128 {
        while b != 0 {
            let t = a % b;
            a = b;
            b = t;
        }
        a
    }
}

// ---------------------------------------------------------------------------
// Lean Nat semantics — the three laws a mathematical bignum gets wrong
// ---------------------------------------------------------------------------

#[test]
fn truncated_subtraction_saturates_at_zero_and_never_wraps() {
    let mut checked = 0usize;
    let mut check = |a: &BigNat, b: &BigNat, origin: &str| {
        let difference = a.sub(b);
        if a <= b {
            // Lean `Nat.sub` floors at zero. A wrapping or borrowing
            // implementation produces an enormous value here instead — the
            // single most dangerous bignum defect, because every downstream
            // law would still hold for it.
            assert!(
                difference.is_zero(),
                "{origin}: {} - {} must saturate to zero, got {}",
                show(a),
                show(b),
                show(&difference)
            );
        } else {
            // Above the floor, subtraction is exact: it must invert addition.
            assert_eq!(
                difference.add(b),
                *a,
                "{origin}: ({} - {}) + {} must be {}",
                show(a),
                show(b),
                show(b),
                show(a)
            );
            assert!(
                difference <= *a,
                "{origin}: {} - {} exceeded the minuend: {}",
                show(a),
                show(b),
                show(&difference)
            );
        }
        // The result is a valid, normalized representation either way.
        assert_ne!(
            difference.limbs_le().last(),
            Some(&0),
            "{origin}: {} - {} left an unnormalized result {:?}",
            show(a),
            show(b),
            difference.limbs_le()
        );
        checked += 1;
    };

    let corpus = edge_corpus();
    for a in &corpus {
        for b in &corpus {
            check(a, b, "edge sweep");
        }
    }
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS {
            let a = rng.bignat(MAX_LIMBS);
            let b = rng.bignat(MAX_LIMBS);
            let origin = format!("seed {seed:#x} trial {trial}");
            check(&a, &b, &origin);
            // Metamorphic: a - a is zero, a - 0 is a, 0 - a is zero, and
            // (a + b) - b recovers a exactly.
            assert!(a.sub(&a).is_zero(), "{origin}: {} - itself", show(&a));
            assert_eq!(a.sub(&BigNat::zero()), a, "{origin}: {} - 0", show(&a));
            assert!(
                BigNat::zero().sub(&a).is_zero(),
                "{origin}: 0 - {} must saturate",
                show(&a)
            );
            assert_eq!(
                a.add(&b).sub(&b),
                a,
                "{origin}: ({} + {}) - {}",
                show(&a),
                show(&b),
                show(&b)
            );
        }
    }
    assert!(checked > 1_000, "sub sweep covered only {checked} pairs");
}

#[test]
fn division_and_remainder_obey_the_zero_laws_and_agree_with_each_other() {
    let check = |a: &BigNat, b: &BigNat, origin: &str| {
        let (quotient, remainder) = a.div_rem(b);
        assert_eq!(
            quotient,
            a.div(b),
            "{origin}: div disagrees with div_rem for {} / {}",
            show(a),
            show(b)
        );
        assert_eq!(
            remainder,
            a.rem(b),
            "{origin}: rem disagrees with div_rem for {} % {}",
            show(a),
            show(b)
        );
        if b.is_zero() {
            // Lean: x / 0 = 0 and x % 0 = x. Not a mathematical truth — a
            // deliberate total-function choice this crate must reproduce.
            assert!(
                quotient.is_zero(),
                "{origin}: {} / 0 must be 0, got {}",
                show(a),
                show(&quotient)
            );
            assert_eq!(
                remainder,
                *a,
                "{origin}: {} % 0 must be {}, got {}",
                show(a),
                show(a),
                show(&remainder)
            );
            return;
        }
        // The division identity, and the remainder actually being reduced.
        assert_eq!(
            quotient.mul(b).add(&remainder),
            *a,
            "{origin}: ({} / {}) * {} + ({} % {}) must be {}",
            show(a),
            show(b),
            show(b),
            show(a),
            show(b),
            show(a)
        );
        assert!(
            remainder < *b,
            "{origin}: {} % {} = {} is not reduced",
            show(a),
            show(b),
            show(&remainder)
        );
    };

    let corpus = edge_corpus();
    for a in &corpus {
        for b in &corpus {
            check(a, b, "edge sweep");
        }
    }
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS {
            let a = rng.bignat(MAX_LIMBS);
            let b = rng.bignat(MAX_LIMBS);
            let origin = format!("seed {seed:#x} trial {trial}");
            check(&a, &b, &origin);
            // Metamorphic: scaling the dividend by the divisor divides exactly.
            if !b.is_zero() {
                assert_eq!(
                    a.mul(&b).div(&b),
                    a,
                    "{origin}: ({} * {}) / {}",
                    show(&a),
                    show(&b),
                    show(&b)
                );
                assert!(
                    a.mul(&b).rem(&b).is_zero(),
                    "{origin}: ({} * {}) % {} must vanish",
                    show(&a),
                    show(&b),
                    show(&b)
                );
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Algebraic laws
// ---------------------------------------------------------------------------

#[test]
fn addition_and_multiplication_form_a_commutative_semiring() {
    let corpus = edge_corpus();
    let check = |a: &BigNat, b: &BigNat, c: &BigNat, origin: &str| {
        let one = BigNat::from_u64(1);
        let zero = BigNat::zero();
        assert_eq!(a.add(b), b.add(a), "{origin}: add commutes");
        assert_eq!(a.mul(b), b.mul(a), "{origin}: mul commutes");
        assert_eq!(
            a.add(b).add(c),
            a.add(&b.add(c)),
            "{origin}: add associates over {}, {}, {}",
            show(a),
            show(b),
            show(c)
        );
        assert_eq!(
            a.mul(b).mul(c),
            a.mul(&b.mul(c)),
            "{origin}: mul associates over {}, {}, {}",
            show(a),
            show(b),
            show(c)
        );
        assert_eq!(
            a.mul(&b.add(c)),
            a.mul(b).add(&a.mul(c)),
            "{origin}: mul distributes over {}, {}, {}",
            show(a),
            show(b),
            show(c)
        );
        assert_eq!(a.add(&zero), *a, "{origin}: additive identity");
        assert_eq!(a.mul(&one), *a, "{origin}: multiplicative identity");
        assert!(a.mul(&zero).is_zero(), "{origin}: multiplicative zero");
        // Normalization survives every operation.
        for (label, value) in [
            ("add", a.add(b)),
            ("mul", a.mul(b)),
            ("sub", a.sub(b)),
            ("gcd", a.gcd(b)),
        ] {
            assert_ne!(
                value.limbs_le().last(),
                Some(&0),
                "{origin}: {label} left an unnormalized result {:?}",
                value.limbs_le()
            );
            assert_eq!(
                value.is_zero(),
                value.limbs_le().is_empty(),
                "{origin}: {label} broke the zero/empty-limbs invariant"
            );
        }
    };

    for (i, a) in corpus.iter().enumerate() {
        for (j, b) in corpus.iter().enumerate() {
            let c = &corpus[(i + j) % corpus.len()];
            check(a, b, c, "edge sweep");
        }
    }
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS {
            let a = rng.bignat(MAX_LIMBS);
            let b = rng.bignat(MAX_LIMBS);
            let c = rng.bignat(MAX_LIMBS);
            check(&a, &b, &c, &format!("seed {seed:#x} trial {trial}"));
        }
    }
}

#[test]
fn powers_agree_with_repeated_multiplication_and_split_over_exponents() {
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS / 4 {
            let base = rng.bignat(2);
            let m = rng.below(6) as u32;
            let n = rng.below(6) as u32;
            let origin = format!("seed {seed:#x} trial {trial}");
            let mut repeated = BigNat::from_u64(1);
            for _ in 0..m {
                repeated = repeated.mul(&base);
            }
            assert_eq!(
                base.pow(m),
                repeated,
                "{origin}: {}^{m} vs repeated multiplication",
                show(&base)
            );
            assert_eq!(
                base.pow(m + n),
                base.pow(m).mul(&base.pow(n)),
                "{origin}: {}^({m}+{n})",
                show(&base)
            );
            assert_eq!(base.pow(0), BigNat::from_u64(1), "{origin}: x^0 = 1");
            assert_eq!(base.pow(1), base, "{origin}: x^1 = x");
        }
    }
    // Lean's `Nat.pow 0 0 = 1`, which is a convention, not a limit.
    assert_eq!(BigNat::zero().pow(0), BigNat::from_u64(1), "0^0 = 1");
    assert!(BigNat::zero().pow(5).is_zero(), "0^5 = 0");
}

#[test]
fn gcd_is_symmetric_absorbs_zero_and_divides_both_operands() {
    let corpus = edge_corpus();
    let check = |a: &BigNat, b: &BigNat, origin: &str| {
        let g = a.gcd(b);
        assert_eq!(g, b.gcd(a), "{origin}: gcd commutes");
        assert_eq!(
            a.gcd(&BigNat::zero()),
            *a,
            "{origin}: gcd({}, 0) must be the operand",
            show(a)
        );
        if g.is_zero() {
            assert!(
                a.is_zero() && b.is_zero(),
                "{origin}: gcd({}, {}) vanished for nonzero operands",
                show(a),
                show(b)
            );
            return;
        }
        assert!(
            a.rem(&g).is_zero() && b.rem(&g).is_zero(),
            "{origin}: gcd({}, {}) = {} does not divide both",
            show(a),
            show(b),
            show(&g)
        );
    };
    for a in &corpus {
        for b in &corpus {
            check(a, b, "edge sweep");
        }
    }
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS {
            let a = rng.bignat(2);
            let b = rng.bignat(2);
            check(&a, &b, &format!("seed {seed:#x} trial {trial}"));
        }
    }
}

#[test]
fn bitwise_operations_are_commutative_idempotent_and_involutive() {
    let corpus = edge_corpus();
    let check = |a: &BigNat, b: &BigNat, origin: &str| {
        assert_eq!(a.land(b), b.land(a), "{origin}: and commutes");
        assert_eq!(a.lor(b), b.lor(a), "{origin}: or commutes");
        assert_eq!(a.lxor(b), b.lxor(a), "{origin}: xor commutes");
        assert_eq!(a.land(a), *a, "{origin}: and is idempotent");
        assert_eq!(a.lor(a), *a, "{origin}: or is idempotent");
        assert!(a.lxor(a).is_zero(), "{origin}: {} xor itself", show(a));
        assert_eq!(
            a.lxor(b).lxor(b),
            *a,
            "{origin}: xor by {} is involutive on {}",
            show(b),
            show(a)
        );
        assert!(
            a.land(b) <= *a && a.land(b) <= *b,
            "{origin}: and exceeded an operand"
        );
        assert!(
            a.lor(b) >= *a && a.lor(b) >= *b,
            "{origin}: or fell below an operand"
        );
        // and/or/xor decomposition: a | b == (a ^ b) + (a & b).
        assert_eq!(
            a.lor(b),
            a.lxor(b).add(&a.land(b)),
            "{origin}: or/xor/and decomposition for {}, {}",
            show(a),
            show(b)
        );
    };
    for a in &corpus {
        for b in &corpus {
            check(a, b, "edge sweep");
        }
    }
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS {
            let a = rng.bignat(MAX_LIMBS);
            let b = rng.bignat(MAX_LIMBS);
            check(&a, &b, &format!("seed {seed:#x} trial {trial}"));
        }
    }
}

#[test]
fn shifts_round_trip_and_match_powers_of_two() {
    let corpus = edge_corpus();
    let two = BigNat::from_u64(2);
    let check = |a: &BigNat, bits: u64, origin: &str| {
        let up = a.shl(bits);
        // Shifting left is multiplication by 2^bits, exactly.
        let factor = two.pow(u32::try_from(bits).expect("bounded"));
        assert_eq!(
            up,
            a.mul(&factor),
            "{origin}: {} << {bits} vs multiplication",
            show(a)
        );
        // …and is recoverable, because nothing was shifted off the top.
        assert_eq!(
            up.shr(bits),
            *a,
            "{origin}: ({} << {bits}) >> {bits}",
            show(a)
        );
        // Shifting right is division by 2^bits, exactly.
        assert_eq!(
            a.shr(bits),
            a.div(&factor),
            "{origin}: {} >> {bits} vs division",
            show(a)
        );
        // Shifting past the top yields zero, never a wrapped value.
        assert!(
            a.shr(a.bit_length() + bits).is_zero(),
            "{origin}: {} shifted past its top must vanish",
            show(a)
        );
    };
    // Boundaries first: 0, 1, and both sides of every limb edge.
    let boundary_shifts = [0u64, 1, 31, 32, 63, 64, 65, 127, 128, 129, 191, 192];
    for a in &corpus {
        for bits in boundary_shifts {
            check(a, bits, "edge sweep");
        }
    }
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS / 2 {
            let a = rng.bignat(MAX_LIMBS);
            let bits = rng.below(200);
            check(&a, bits, &format!("seed {seed:#x} trial {trial}"));
        }
    }
}

#[test]
fn comparisons_are_a_total_order_consistent_with_arithmetic() {
    let corpus = edge_corpus();
    let check = |a: &BigNat, b: &BigNat, origin: &str| {
        assert_eq!(
            a.beq(b),
            a == b,
            "{origin}: beq disagrees with equality on {}, {}",
            show(a),
            show(b)
        );
        assert_eq!(
            a.ble(b),
            a <= b,
            "{origin}: ble disagrees with ordering on {}, {}",
            show(a),
            show(b)
        );
        assert_eq!(
            a.ble(b) && b.ble(a),
            a.beq(b),
            "{origin}: antisymmetry on {}, {}",
            show(a),
            show(b)
        );
        // Monotonicity: adding cannot make a value smaller, and ordering is
        // preserved under a common addend.
        assert!(a.add(b) >= *a, "{origin}: addition decreased a value");
        assert_eq!(
            a.ble(b),
            a.add(b).ble(&b.add(b)),
            "{origin}: ordering not preserved under a common addend"
        );
        // bit_length is consistent with the value's magnitude.
        if !a.is_zero() {
            let top = a.bit_length();
            assert_eq!(
                a.shr(top - 1),
                BigNat::from_u64(1),
                "{origin}: bit_length {top} disagrees with the top bit of {}",
                show(a)
            );
            assert!(a.shr(top).is_zero(), "{origin}: bit_length {top} too small");
        } else {
            assert_eq!(a.bit_length(), 0, "{origin}: zero has no bits");
        }
    };
    for a in &corpus {
        for b in &corpus {
            check(a, b, "edge sweep");
        }
    }
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS {
            let a = rng.bignat(MAX_LIMBS);
            let b = rng.bignat(MAX_LIMBS);
            check(&a, &b, &format!("seed {seed:#x} trial {trial}"));
        }
    }
}

// ---------------------------------------------------------------------------
// Round trips
// ---------------------------------------------------------------------------

#[test]
fn decimal_limb_and_literal_round_trips_preserve_the_value() {
    let check = |a: &BigNat, origin: &str| {
        let decimal = a.to_decimal();
        assert_eq!(
            BigNat::from_decimal(&decimal).as_ref(),
            Some(a),
            "{origin}: decimal round trip through {decimal}"
        );
        assert_eq!(
            BigNat::from_limbs_le(a.limbs_le().to_vec()),
            *a,
            "{origin}: limb round trip for {}",
            show(a)
        );
        // Interop with the term-plane literal must be loss-free in both
        // directions — the kernel converts on every literal it reduces.
        assert_eq!(
            bignat_from_literal(&literal_from_bignat(a)),
            *a,
            "{origin}: NatLit round trip for {}",
            show(a)
        );
        // Redundant trailing zero limbs normalize to the same value.
        let mut padded = a.limbs_le().to_vec();
        padded.push(0);
        padded.push(0);
        assert_eq!(
            BigNat::from_limbs_le(padded),
            *a,
            "{origin}: padded limbs must normalize for {}",
            show(a)
        );
        if let Some(small) = to_u128(a) {
            assert_eq!(from_u128(small), *a, "{origin}: u128 round trip");
        }
        match a.limbs_le().len() {
            0 => assert_eq!(a.to_u64(), Some(0), "{origin}: zero converts to 0u64"),
            1 => assert!(a.to_u64().is_some(), "{origin}: single limb fits u64"),
            _ => assert!(
                a.to_u64().is_none(),
                "{origin}: multi-limb must not fit u64"
            ),
        }
    };
    for a in &edge_corpus() {
        check(a, "edge sweep");
    }
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS {
            let a = rng.bignat(MAX_LIMBS);
            check(&a, &format!("seed {seed:#x} trial {trial}"));
        }
    }
}

// ---------------------------------------------------------------------------
// Differential legs
// ---------------------------------------------------------------------------

#[test]
fn generated_operands_agree_with_the_independent_u128_model() {
    let mut compared = 0usize;
    let mut check = |a: &BigNat, b: &BigNat, origin: &str| {
        let (Some(x), Some(y)) = (to_u128(a), to_u128(b)) else {
            return;
        };
        if let Some(sum) = model::add(x, y) {
            assert_eq!(a.add(b), from_u128(sum), "{origin}: add {x} + {y}");
        }
        if let Some(product) = model::mul(x, y) {
            assert_eq!(a.mul(b), from_u128(product), "{origin}: mul {x} * {y}");
        }
        assert_eq!(
            a.sub(b),
            from_u128(model::sub(x, y)),
            "{origin}: sub {x} - {y}"
        );
        assert_eq!(
            a.div(b),
            from_u128(model::div(x, y)),
            "{origin}: div {x} / {y}"
        );
        assert_eq!(
            a.rem(b),
            from_u128(model::rem(x, y)),
            "{origin}: rem {x} % {y}"
        );
        assert_eq!(
            a.gcd(b),
            from_u128(model::gcd(x, y)),
            "{origin}: gcd {x}, {y}"
        );
        assert_eq!(a.land(b), from_u128(x & y), "{origin}: and {x}, {y}");
        assert_eq!(a.lor(b), from_u128(x | y), "{origin}: or {x}, {y}");
        assert_eq!(a.lxor(b), from_u128(x ^ y), "{origin}: xor {x}, {y}");
        compared += 1;
    };
    let corpus = edge_corpus();
    for a in &corpus {
        for b in &corpus {
            check(a, b, "edge sweep");
        }
    }
    for seed in SEEDS {
        let mut rng = SplitMix64(seed);
        for trial in 0..TRIALS {
            let a = rng.bignat(2);
            let b = rng.bignat(2);
            check(&a, &b, &format!("seed {seed:#x} trial {trial}"));
        }
    }
    assert!(
        compared > 500,
        "the model leg compared only {compared} pairs; the generator drifted \
         out of u128 range and this leg stopped testing anything"
    );
}

/// The committed corpus is CPython ground truth. Where it overlaps the model's
/// range, the model must reproduce it exactly — otherwise the model is wrong
/// and every agreement above is worthless. This is what earns the model the
/// right to be an oracle for operands the corpus does not contain.
#[test]
fn the_u128_model_reproduces_the_committed_vectors_where_they_overlap() {
    let raw = std::fs::read_to_string("fixtures/nat_vectors.txt")
        .expect("the committed vector corpus must be readable");
    let mut overlapped = 0usize;
    let mut seen_ops: Vec<&str> = Vec::new();
    for (number, line) in raw.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        // The corpus declares its schema; pin it rather than skipping past it,
        // so a regenerated corpus with a different shape fails here instead of
        // quietly reducing what this leg compares.
        if let Some(version) = line.strip_prefix("schema ") {
            assert_eq!(
                version,
                "fln-bignum-vectors/1",
                "fixtures/nat_vectors.txt:{}: unexpected corpus schema",
                number + 1
            );
            continue;
        }
        let fields: Vec<&str> = line.split('|').collect();
        let [op, a_str, b_str, expected_str] = fields.as_slice() else {
            panic!(
                "fixtures/nat_vectors.txt:{}: malformed vector {line}",
                number + 1
            );
        };
        if !seen_ops.contains(op) {
            seen_ops.push(op);
        }
        let (Ok(x), Ok(y)) = (a_str.parse::<u128>(), b_str.parse::<u128>()) else {
            continue;
        };
        let Ok(expected) = expected_str.parse::<u128>() else {
            continue;
        };
        let actual = match *op {
            "add" => model::add(x, y),
            "sub" => Some(model::sub(x, y)),
            "mul" => model::mul(x, y),
            "div" => Some(model::div(x, y)),
            "mod" => Some(model::rem(x, y)),
            "gcd" => Some(model::gcd(x, y)),
            "land" => Some(x & y),
            "lor" => Some(x | y),
            "lxor" => Some(x ^ y),
            _ => None,
        };
        let Some(actual) = actual else {
            continue;
        };
        assert_eq!(
            actual,
            expected,
            "fixtures/nat_vectors.txt:{}: the model disagrees with CPython \
             ground truth on {op}|{x}|{y}",
            number + 1
        );
        // And the crate itself must agree with both.
        let lhs = BigNat::from_decimal(a_str).expect("vector operand parses");
        let rhs = BigNat::from_decimal(b_str).expect("vector operand parses");
        let produced = match *op {
            "add" => lhs.add(&rhs),
            "sub" => lhs.sub(&rhs),
            "mul" => lhs.mul(&rhs),
            "div" => lhs.div(&rhs),
            "mod" => lhs.rem(&rhs),
            "gcd" => lhs.gcd(&rhs),
            "land" => lhs.land(&rhs),
            "lor" => lhs.lor(&rhs),
            "lxor" => lhs.lxor(&rhs),
            _ => unreachable!("op filtered above"),
        };
        assert_eq!(
            produced,
            from_u128(expected),
            "fixtures/nat_vectors.txt:{}: BigNat disagrees on {op}|{x}|{y}",
            number + 1
        );
        overlapped += 1;
    }
    assert!(
        overlapped > 1_000,
        "only {overlapped} committed vectors fell in the model's range; the \
         differential leg is not exercising the corpus (ops seen: {seen_ops:?})"
    );
}
