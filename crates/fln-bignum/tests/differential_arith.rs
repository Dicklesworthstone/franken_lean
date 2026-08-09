//! Differential and metamorphic arithmetic checks for `BigNat`
//! (franken_lean-npl). Reported, not adopted (BeigeMarsh): additive, reads
//! the ops unmodified.
//!
//! Two independent oracles, chosen so nothing is verified vacuously:
//!
//! 1. `u128` EXACT differential for the 1-2 limb regime. Native `u128`
//!    arithmetic is ground truth for add/sub/mul/div/rem/gcd/shift over
//!    operands below 2^128, and it straddles the single-limb-divisor ->
//!    Knuth-D crossover (which happens at exactly a 2-limb divisor).
//!
//! 2. ORACLE-FREE metamorphic reconstruction for the many-limb regime, where
//!    no fixed-width native oracle reaches: for random operands up to several
//!    limbs, `div_rem` must satisfy `q*b + r == a` and `r < b` EXACTLY, and
//!    `(a*b)/b == a`. These identities hold for any correct bignum at any
//!    size, so they catch carry/borrow/normalization and the rare Knuth-D
//!    add-back defects that a bounded oracle cannot reach. The widths are
//!    chosen to span the schoolbook -> Karatsuba -> Toom-3 multiplication
//!    crossovers and to force the add-back branch with crafted near-power
//!    divisors.

#![forbid(unsafe_code)]

use fln_bignum::nat::BigNat;

/// Deterministic SplitMix64 — no dependency, reproducible across runs.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
    /// A random BigNat of exactly `limbs` 64-bit words (top word forced
    /// non-zero so the width is real), or zero when `limbs == 0`.
    fn bignat(&mut self, limbs: usize) -> BigNat {
        if limbs == 0 {
            return BigNat::zero();
        }
        let mut v = vec![0u64; limbs];
        for w in v.iter_mut() {
            *w = self.next();
        }
        if v[limbs - 1] == 0 {
            v[limbs - 1] = 1;
        }
        BigNat::from_limbs_le(v)
    }
}

fn nat(u: u128) -> BigNat {
    BigNat::from_limbs_le(vec![u as u64, (u >> 64) as u64])
}

/// `u128` exact differential over the 1-2 limb regime.
#[test]
fn u128_exact_differential() {
    let mut rng = Rng(0x1234_5678_9abc_def0);
    for _ in 0..300_000 {
        // Mix full-width and small operands so single-limb paths, the
        // single->double limb boundary, and near-2^64 values all appear.
        let pick = |r: &mut Rng| -> u128 {
            match r.next() % 4 {
                0 => u128::from(r.next()),                       // 1 limb
                1 => u128::from(r.next() as u32),                // small
                2 => (u128::from(r.next()) << 64) | u128::from(r.next()), // 2 limb
                _ => u128::from(r.next()) << 64,                 // top-limb only
            }
        };
        let a = pick(&mut rng);
        let b = pick(&mut rng);

        assert_eq!(nat(a).add(&nat(b)).to_decimal(), (a.wrapping_add(b)).to_string(), "add {a}+{b}");
        // Lean-Nat TRUNCATED subtraction: a < b yields 0, not underflow.
        let sub_truth = a.saturating_sub(b);
        assert_eq!(nat(a).sub(&nat(b)).to_decimal(), sub_truth.to_string(), "sub {a}-{b} (truncated)");
        if let Some(prod) = a.checked_mul(b) {
            assert_eq!(nat(a).mul(&nat(b)).to_decimal(), prod.to_string(), "mul {a}*{b}");
        }
        if b != 0 {
            let (q, r) = nat(a).div_rem(&nat(b));
            assert_eq!(q.to_decimal(), (a / b).to_string(), "div {a}/{b}");
            assert_eq!(r.to_decimal(), (a % b).to_string(), "rem {a}%{b}");
        } else {
            // Lean-Nat: x / 0 = 0 and x % 0 = x.
            assert_eq!(nat(a).div(&nat(0)).to_decimal(), "0", "div-by-zero {a}/0");
            assert_eq!(nat(a).rem(&nat(0)).to_decimal(), a.to_string(), "rem-by-zero {a}%0");
        }
        assert_eq!(nat(a).gcd(&nat(b)).to_decimal(), gcd_u128(a, b).to_string(), "gcd({a},{b})");
        let s = (rng.next() % 200) as u64;
        assert_eq!(
            nat(a).shl(s).to_decimal(),
            {
                let mut acc = BigNat::from_limbs_le(vec![a as u64, (a >> 64) as u64]);
                acc = acc.shl(0); // no-op, keep type
                let _ = &acc;
                // reference: a << s via its own decimal (a is u128; shifting
                // may overflow u128, so use a BigNat-independent big shift by
                // decimal doubling is overkill — instead verify via shr round
                // trip below and exact small shifts here).
                shl_ref_decimal(a, s)
            },
            "shl {a}<<{s}"
        );
        // shr is exact in u128.
        assert_eq!(nat(a).shr(s).to_decimal(), (if s >= 128 { 0 } else { a >> s }).to_string(), "shr {a}>>{s}");
    }
}

fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// `a << s` as a decimal string, computed independently of BigNat by
/// repeated decimal doubling (so it is a genuine second implementation).
fn shl_ref_decimal(a: u128, s: u64) -> String {
    // a * 2^s in decimal, via schoolbook doubling on a byte-per-digit vector.
    let mut digits: Vec<u8> = a.to_string().into_bytes().into_iter().map(|c| c - b'0').collect();
    for _ in 0..s {
        let mut carry = 0u8;
        for d in digits.iter_mut().rev() {
            let v = *d * 2 + carry;
            *d = v % 10;
            carry = v / 10;
        }
        while carry > 0 {
            digits.insert(0, carry % 10);
            carry /= 10;
        }
    }
    let mut s: String = digits.into_iter().map(|d| (d + b'0') as char).collect();
    while s.len() > 1 && s.starts_with('0') {
        s.remove(0);
    }
    s
}

/// Oracle-free metamorphic reconstruction across the many-limb regime and
/// every multiplication algorithm crossover.
#[test]
fn multilimb_metamorphic_reconstruction() {
    let mut rng = Rng(0xdead_beef_cafe_babe);
    // Widths span single-limb through Toom-3 territory.
    let widths = [1usize, 2, 3, 4, 5, 8, 12, 20, 33, 48, 80];
    for _ in 0..4_000 {
        let aw = widths[(rng.next() as usize) % widths.len()];
        let bw = 1 + (rng.next() as usize) % aw.max(1);
        let a = rng.bignat(aw);
        let b = rng.bignat(bw);
        if b.beq(&BigNat::zero()) {
            continue;
        }
        // div_rem law: a == q*b + r with 0 <= r < b.
        let (q, r) = a.div_rem(&b);
        let recon = q.mul(&b).add(&r);
        assert!(recon.beq(&a), "reconstruction failed: aw={aw} bw={bw}");
        assert!(r.as_view().ble(b.as_view()) && !r.beq(&b), "remainder not < divisor");
        // mul/div inverse: (a*b)/b == a and (a*b)/a == b (a nonzero).
        let prod = a.mul(&b);
        assert!(prod.div(&b).beq(&a), "a*b/b != a: aw={aw} bw={bw}");
        if !a.beq(&BigNat::zero()) {
            assert!(prod.div(&a).beq(&b), "a*b/a != b: aw={aw} bw={bw}");
        }
    }
}

/// Force the Knuth-D add-back branch with near-power divisors, which random
/// sampling almost never hits: a divisor whose top limbs are all 0xFFFF...
/// makes qhat over-estimate and triggers the correction.
#[test]
fn knuth_addback_crafted() {
    let mut rng = Rng(0x0f0f_0f0f_1234_5678);
    for _ in 0..2_000 {
        let n = 2 + (rng.next() as usize) % 6; // 2..=7 limb divisor
        // Divisor near a power of the base: top limbs all-ones.
        let mut dv = vec![0u64; n];
        for w in dv.iter_mut() {
            *w = u64::MAX;
        }
        dv[0] = rng.next() | 1; // keep it odd/varied, still enormous
        let b = BigNat::from_limbs_le(dv);
        // Dividend a few limbs wider, random.
        let a = rng.bignat(n + 1 + (rng.next() as usize) % 4);
        let (q, r) = a.div_rem(&b);
        let recon = q.mul(&b).add(&r);
        assert!(recon.beq(&a), "add-back reconstruction failed n={n}");
        assert!(r.as_view().ble(b.as_view()) && !r.beq(&b), "add-back remainder not < divisor");
    }
}
