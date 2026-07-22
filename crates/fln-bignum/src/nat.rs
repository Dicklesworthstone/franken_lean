//! Arbitrary-precision unsigned naturals with Lean `Nat` semantics (plan §8.4).
//!
//! The operation set is exactly the kernel literal-acceleration set of KR-313:
//! `add`, `sub` (truncated), `mul`, `div`/`rem` (Lean division-by-zero laws),
//! `gcd`, `pow`, `beq`, `ble`, `land`, `lor`, `lxor`, `shl`, `shr`.
//!
//! Representation invariant: little-endian `u64` limbs, normalized — no
//! trailing zero limbs; the empty limb vector is zero. This is deliberately
//! identical to `fln_core::expr::NatLit`'s representation (interop is wired
//! elsewhere; this crate does not depend on `fln-core`).
//!
//! No code path in this module panics on any input, and no hot path recurses.

use std::cmp::Ordering;

/// Arbitrary-precision unsigned natural number (KR-313 / plan §8.4).
///
/// Invariant: `limbs` is little-endian and normalized (no trailing zeros).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BigNat {
    limbs: Vec<u64>,
}

/// `10^19`: the largest power of ten with `10^k - 1` representable in `u64`.
const DECIMAL_CHUNK_BASE: u128 = 10_000_000_000_000_000_000;
/// Digits per decimal chunk (`log10(DECIMAL_CHUNK_BASE)`).
const DECIMAL_CHUNK_DIGITS: usize = 19;

fn normalize(limbs: &mut Vec<u64>) {
    while limbs.last() == Some(&0) {
        limbs.pop();
    }
}

fn cmp_limbs(a: &[u64], b: &[u64]) -> Ordering {
    a.len().cmp(&b.len()).then_with(|| {
        for (x, y) in a.iter().rev().zip(b.iter().rev()) {
            let ord = x.cmp(y);
            if ord != Ordering::Equal {
                return ord;
            }
        }
        Ordering::Equal
    })
}

/// In-place `a -= b`. Precondition (caller-proven): `a >= b`, both normalized.
fn sub_in_place(a: &mut Vec<u64>, b: &[u64]) {
    let mut borrow = 0u64;
    let mut b_iter = b.iter();
    for limb in a.iter_mut() {
        let s = b_iter.next().copied().unwrap_or(0);
        let (d1, o1) = limb.overflowing_sub(s);
        let (d2, o2) = d1.overflowing_sub(borrow);
        *limb = d2;
        borrow = u64::from(o1 || o2);
    }
    normalize(a);
}

/// In-place `r <<= 1`. Preserves normalization.
fn shl1_in_place(r: &mut Vec<u64>) {
    let mut carry = 0u64;
    for limb in r.iter_mut() {
        let next_carry = *limb >> 63;
        *limb = (*limb << 1) | carry;
        carry = next_carry;
    }
    if carry != 0 {
        r.push(carry);
    }
}

impl BigNat {
    /// The natural number zero (empty limb vector).
    pub fn zero() -> BigNat {
        BigNat { limbs: Vec::new() }
    }

    /// Constructs from a machine word.
    pub fn from_u64(v: u64) -> BigNat {
        if v == 0 {
            BigNat::zero()
        } else {
            BigNat { limbs: vec![v] }
        }
    }

    /// Constructs from little-endian limbs, normalizing trailing zeros.
    pub fn from_limbs_le(mut limbs: Vec<u64>) -> BigNat {
        normalize(&mut limbs);
        BigNat { limbs }
    }

    /// Parses a decimal string. `None` on empty input or any non-digit byte;
    /// leading zeros are accepted.
    pub fn from_decimal(s: &str) -> Option<BigNat> {
        if s.is_empty() {
            return None;
        }
        let mut result = BigNat::zero();
        for chunk in s.as_bytes().chunks(DECIMAL_CHUNK_DIGITS) {
            let mut value = 0u64;
            let mut scale = 1u64;
            for &byte in chunk {
                if !byte.is_ascii_digit() {
                    return None;
                }
                value = value.wrapping_mul(10).wrapping_add(u64::from(byte - b'0'));
                scale = scale.wrapping_mul(10);
            }
            result = result.mul_small(scale).add_small(value);
        }
        Some(result)
    }

    /// The normalized little-endian limbs (empty slice for zero).
    pub fn limbs_le(&self) -> &[u64] {
        &self.limbs
    }

    /// Returns the value if it fits in a machine word.
    pub fn to_u64(&self) -> Option<u64> {
        match self.limbs.len() {
            0 => Some(0),
            1 => self.limbs.first().copied(),
            _ => None,
        }
    }

    /// Renders as a decimal string (zero renders as `"0"`, no leading zeros).
    pub fn to_decimal(&self) -> String {
        if self.is_zero() {
            return "0".to_string();
        }
        let mut rest = self.limbs.clone();
        let mut chunks: Vec<u64> = Vec::new();
        while !rest.is_empty() {
            let mut rem = 0u128;
            for limb in rest.iter_mut().rev() {
                let cur = (rem << 64) | u128::from(*limb);
                *limb = (cur / DECIMAL_CHUNK_BASE) as u64;
                rem = cur % DECIMAL_CHUNK_BASE;
            }
            normalize(&mut rest);
            chunks.push(rem as u64);
        }
        let mut out = String::new();
        let mut iter = chunks.iter().rev();
        if let Some(first) = iter.next() {
            out.push_str(&first.to_string());
        }
        for chunk in iter {
            out.push_str(&format!("{chunk:019}"));
        }
        out
    }

    /// True iff the value is zero (empty limb vector, by the invariant).
    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    /// Number of significant bits; `bit_length(0) = 0`.
    pub fn bit_length(&self) -> u64 {
        match self.limbs.last() {
            None => 0,
            Some(&top) => (self.limbs.len() as u64 - 1) * 64 + u64::from(64 - top.leading_zeros()),
        }
    }

    /// Kernel-facing `Nat.beq` (KR-313).
    pub fn beq(&self, other: &BigNat) -> bool {
        self == other
    }

    /// Kernel-facing `Nat.ble` (KR-313).
    pub fn ble(&self, other: &BigNat) -> bool {
        self <= other
    }

    /// `self + other`.
    #[allow(clippy::should_implement_trait)]
    pub fn add(&self, other: &BigNat) -> BigNat {
        let (longer, shorter) = if self.limbs.len() >= other.limbs.len() {
            (&self.limbs, &other.limbs)
        } else {
            (&other.limbs, &self.limbs)
        };
        let mut out = Vec::with_capacity(longer.len() + 1);
        let mut carry = 0u128;
        let mut short_iter = shorter.iter();
        for &a in longer {
            let b = short_iter.next().copied().unwrap_or(0);
            let sum = u128::from(a) + u128::from(b) + carry;
            out.push(sum as u64);
            carry = sum >> 64;
        }
        if carry != 0 {
            out.push(carry as u64);
        }
        BigNat { limbs: out }
    }

    /// Truncated subtraction, Lean `Nat.sub` semantics: `self - other`, floored
    /// at zero (KR-313).
    #[allow(clippy::should_implement_trait)]
    pub fn sub(&self, other: &BigNat) -> BigNat {
        if self <= other {
            return BigNat::zero();
        }
        let mut out = self.limbs.clone();
        sub_in_place(&mut out, &other.limbs);
        BigNat { limbs: out }
    }

    /// `self * other`, schoolbook with `u128` intermediates (KR-313;
    /// performance is gated later, PG-K).
    #[allow(clippy::should_implement_trait)]
    pub fn mul(&self, other: &BigNat) -> BigNat {
        if self.is_zero() || other.is_zero() {
            return BigNat::zero();
        }
        let mut out = vec![0u64; self.limbs.len() + other.limbs.len()];
        for (i, &x) in self.limbs.iter().enumerate() {
            let mut carry = 0u128;
            for (j, &y) in other.limbs.iter().enumerate() {
                if let Some(slot) = out.get_mut(i + j) {
                    let cur = u128::from(*slot) + u128::from(x) * u128::from(y) + carry;
                    *slot = cur as u64;
                    carry = cur >> 64;
                }
            }
            if let Some(slot) = out.get_mut(i + other.limbs.len()) {
                *slot = (u128::from(*slot) + carry) as u64;
            }
        }
        BigNat::from_limbs_le(out)
    }

    /// Euclidean quotient with Lean semantics: `x / 0 = 0` (KR-313).
    #[allow(clippy::should_implement_trait)]
    pub fn div(&self, other: &BigNat) -> BigNat {
        self.div_rem(other).0
    }

    /// Euclidean remainder with Lean semantics: `x % 0 = x` (KR-313).
    pub fn rem(&self, other: &BigNat) -> BigNat {
        self.div_rem(other).1
    }

    /// Quotient and remainder by shift-subtract long division.
    /// Lean laws: `(x, 0) -> (0, x)`. Invariant on exit for nonzero divisor:
    /// `self = q * other + r` with `r < other`.
    pub fn div_rem(&self, other: &BigNat) -> (BigNat, BigNat) {
        if other.is_zero() || self < other {
            return (BigNat::zero(), self.clone());
        }
        let bits = self.bit_length();
        let mut quotient = vec![0u64; self.limbs.len()];
        let mut remainder: Vec<u64> = Vec::with_capacity(other.limbs.len() + 1);
        for i in (0..bits).rev() {
            shl1_in_place(&mut remainder);
            let limb_idx = (i / 64) as usize;
            let bit = self
                .limbs
                .get(limb_idx)
                .map_or(0, |&limb| (limb >> (i % 64)) & 1);
            if bit == 1 {
                if let Some(first) = remainder.first_mut() {
                    *first |= 1;
                } else {
                    remainder.push(1);
                }
            }
            if cmp_limbs(&remainder, &other.limbs) != Ordering::Less {
                sub_in_place(&mut remainder, &other.limbs);
                if let Some(slot) = quotient.get_mut(limb_idx) {
                    *slot |= 1u64 << (i % 64);
                }
            }
        }
        (
            BigNat::from_limbs_le(quotient),
            BigNat::from_limbs_le(remainder),
        )
    }

    /// `self ^ exp` by iterative square-and-multiply; `x ^ 0 = 1` (KR-313
    /// caps the accelerated exponent at `2^24`; the cap is enforced by the
    /// kernel caller, not here).
    pub fn pow(&self, exp: u32) -> BigNat {
        let mut result = BigNat::from_u64(1);
        let mut base = self.clone();
        let mut e = exp;
        while e > 0 {
            if e & 1 == 1 {
                result = result.mul(&base);
            }
            e >>= 1;
            if e > 0 {
                base = base.mul(&base);
            }
        }
        result
    }

    /// Greatest common divisor, iterative Euclid via `rem`; `gcd(0, x) = x`
    /// (KR-313).
    pub fn gcd(&self, other: &BigNat) -> BigNat {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let r = a.rem(&b);
            a = b;
            b = r;
        }
        a
    }

    /// Bitwise AND (KR-313 `Nat.land`).
    pub fn land(&self, other: &BigNat) -> BigNat {
        let out: Vec<u64> = self
            .limbs
            .iter()
            .zip(other.limbs.iter())
            .map(|(&a, &b)| a & b)
            .collect();
        BigNat::from_limbs_le(out)
    }

    /// Bitwise OR (KR-313 `Nat.lor`).
    pub fn lor(&self, other: &BigNat) -> BigNat {
        let (longer, shorter) = if self.limbs.len() >= other.limbs.len() {
            (&self.limbs, &other.limbs)
        } else {
            (&other.limbs, &self.limbs)
        };
        let mut short_iter = shorter.iter();
        let out: Vec<u64> = longer
            .iter()
            .map(|&a| a | short_iter.next().copied().unwrap_or(0))
            .collect();
        BigNat { limbs: out }
    }

    /// Bitwise XOR (KR-313 `Nat.xor`).
    pub fn lxor(&self, other: &BigNat) -> BigNat {
        let (longer, shorter) = if self.limbs.len() >= other.limbs.len() {
            (&self.limbs, &other.limbs)
        } else {
            (&other.limbs, &self.limbs)
        };
        let mut short_iter = shorter.iter();
        let out: Vec<u64> = longer
            .iter()
            .map(|&a| a ^ short_iter.next().copied().unwrap_or(0))
            .collect();
        BigNat::from_limbs_le(out)
    }

    /// `self << bits` (KR-313 `Nat.shiftLeft`).
    pub fn shl(&self, bits: u64) -> BigNat {
        if self.is_zero() {
            return BigNat::zero();
        }
        let limb_shift = (bits / 64) as usize;
        let bit_shift = (bits % 64) as u32;
        let mut out = vec![0u64; limb_shift];
        out.reserve(self.limbs.len() + 1);
        if bit_shift == 0 {
            out.extend_from_slice(&self.limbs);
        } else {
            let mut carry = 0u64;
            for &limb in &self.limbs {
                out.push((limb << bit_shift) | carry);
                carry = limb >> (64 - bit_shift);
            }
            if carry != 0 {
                out.push(carry);
            }
        }
        BigNat::from_limbs_le(out)
    }

    /// `self >> bits` (KR-313 `Nat.shiftRight`); shifts past the top yield 0.
    pub fn shr(&self, bits: u64) -> BigNat {
        if bits >= self.bit_length() {
            return BigNat::zero();
        }
        let limb_shift = (bits / 64) as usize;
        let bit_shift = (bits % 64) as u32;
        let rest = self.limbs.get(limb_shift..).unwrap_or(&[]);
        let out: Vec<u64> = if bit_shift == 0 {
            rest.to_vec()
        } else {
            rest.iter()
                .enumerate()
                .map(|(i, &limb)| {
                    let hi = rest.get(i + 1).map_or(0, |&next| next << (64 - bit_shift));
                    (limb >> bit_shift) | hi
                })
                .collect()
        };
        BigNat::from_limbs_le(out)
    }

    /// `self * m` for a machine-word multiplier.
    fn mul_small(&self, m: u64) -> BigNat {
        if m == 0 || self.is_zero() {
            return BigNat::zero();
        }
        let mut out = Vec::with_capacity(self.limbs.len() + 1);
        let mut carry = 0u128;
        for &limb in &self.limbs {
            let cur = u128::from(limb) * u128::from(m) + carry;
            out.push(cur as u64);
            carry = cur >> 64;
        }
        if carry != 0 {
            out.push(carry as u64);
        }
        BigNat { limbs: out }
    }

    /// `self + a` for a machine-word addend.
    fn add_small(&self, a: u64) -> BigNat {
        let mut out = self.limbs.clone();
        let mut carry = u128::from(a);
        for limb in out.iter_mut() {
            if carry == 0 {
                break;
            }
            let cur = u128::from(*limb) + carry;
            *limb = cur as u64;
            carry = cur >> 64;
        }
        if carry != 0 {
            out.push(carry as u64);
        }
        BigNat { limbs: out }
    }
}

impl Ord for BigNat {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_limbs(&self.limbs, &other.limbs)
    }
}

impl PartialOrd for BigNat {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::BigNat;

    const VECTORS: &str = include_str!("../fixtures/nat_vectors.txt");
    const EXPECTED_VECTOR_COUNT: usize = 5725;

    fn parse(s: &str) -> BigNat {
        // A malformed fixture operand is a corrupt-corpus finding, surfaced via the
        // assert with the operand named (never a bare panic path).
        let parsed = BigNat::from_decimal(s);
        assert!(parsed.is_some(), "bad decimal operand in fixture: {s:?}");
        parsed.unwrap_or_else(BigNat::zero)
    }

    fn vector_lines()
    -> impl Iterator<Item = (&'static str, &'static str, &'static str, &'static str)> {
        VECTORS
            .lines()
            .filter(|line| {
                !line.is_empty() && !line.starts_with('#') && !line.starts_with("schema")
            })
            .map(|line| {
                let mut parts = line.split('|');
                let op = parts.next().expect("op field");
                let a = parts.next().expect("a field");
                let b = parts.next().expect("b field");
                let result = parts.next().expect("result field");
                assert!(parts.next().is_none(), "extra field in line: {line}");
                (op, a, b, result)
            })
    }

    #[test]
    fn golden_vectors() {
        let mut count = 0usize;
        for (op, a_str, b_str, expected) in vector_lines() {
            let a = parse(a_str);
            let got = match op {
                "beq" | "ble" => {
                    let b = parse(b_str);
                    let flag = match op {
                        "beq" => a.beq(&b),
                        _ => a.ble(&b),
                    };
                    if flag {
                        "1".to_string()
                    } else {
                        "0".to_string()
                    }
                }
                "shl" | "shr" => {
                    let shift: u64 = b_str.parse().expect("shift amount fits u64");
                    let r = match op {
                        "shl" => a.shl(shift),
                        _ => a.shr(shift),
                    };
                    r.to_decimal()
                }
                "pow" => {
                    let exp: u32 = b_str.parse().expect("exponent fits u32");
                    a.pow(exp).to_decimal()
                }
                _ => {
                    let b = parse(b_str);
                    let r = match op {
                        "add" => a.add(&b),
                        "sub" => a.sub(&b),
                        "mul" => a.mul(&b),
                        "div" => a.div(&b),
                        "mod" => a.rem(&b),
                        "gcd" => a.gcd(&b),
                        "land" => a.land(&b),
                        "lor" => a.lor(&b),
                        "lxor" => a.lxor(&b),
                        other => {
                            assert_eq!(other, "", "unknown op in vectors: {other}");
                            BigNat::zero()
                        }
                    };
                    r.to_decimal()
                }
            };
            assert_eq!(
                got, expected,
                "vector failed: {op}|{a_str}|{b_str}|{expected}"
            );
            count += 1;
        }
        assert_eq!(count, EXPECTED_VECTOR_COUNT);
    }

    #[test]
    fn decimal_round_trip_over_vector_operands() {
        for (op, a_str, b_str, _) in vector_lines() {
            let a = parse(a_str);
            assert_eq!(BigNat::from_decimal(&a.to_decimal()), Some(a.clone()));
            if !matches!(op, "shl" | "shr" | "pow") {
                let b = parse(b_str);
                assert_eq!(BigNat::from_decimal(&b.to_decimal()), Some(b.clone()));
            }
        }
    }

    fn lcg_next(state: &mut u64) -> u64 {
        *state = state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        *state
    }

    fn gen_u128(state: &mut u64) -> u128 {
        let raw = (u128::from(lcg_next(state)) << 64) | u128::from(lcg_next(state));
        let width = lcg_next(state) % 129;
        if width == 0 {
            0
        } else if width == 128 {
            raw
        } else {
            raw & ((1u128 << width) - 1)
        }
    }

    fn big(v: u128) -> BigNat {
        BigNat::from_limbs_le(vec![v as u64, (v >> 64) as u64])
    }

    fn model_mul_256(a: u128, b: u128) -> BigNat {
        let (a0, a1) = (u128::from(a as u64), a >> 64);
        let (b0, b1) = (u128::from(b as u64), b >> 64);
        let p00 = a0 * b0;
        let p01 = a0 * b1;
        let p10 = a1 * b0;
        let p11 = a1 * b1;
        let l0 = p00 as u64;
        let mid = (p00 >> 64) + u128::from(p01 as u64) + u128::from(p10 as u64);
        let l1 = mid as u64;
        let high = (mid >> 64) + (p01 >> 64) + (p10 >> 64) + u128::from(p11 as u64);
        let l2 = high as u64;
        let l3 = ((high >> 64) + (p11 >> 64)) as u64;
        BigNat::from_limbs_le(vec![l0, l1, l2, l3])
    }

    fn model_gcd(mut a: u128, mut b: u128) -> u128 {
        while b != 0 {
            let r = a % b;
            a = b;
            b = r;
        }
        a
    }

    #[test]
    fn u128_model_agreement() {
        let mut state = 0x5eed_f1ea_5eed_f1eau64;
        for _ in 0..2000 {
            let a = gen_u128(&mut state);
            let b = gen_u128(&mut state);
            let (ba, bb) = (big(a), big(b));

            let (sum, overflow) = a.overflowing_add(b);
            let expected_add =
                BigNat::from_limbs_le(vec![sum as u64, (sum >> 64) as u64, u64::from(overflow)]);
            assert_eq!(ba.add(&bb), expected_add, "add({a},{b})");

            assert_eq!(ba.sub(&bb), big(a.saturating_sub(b)), "sub({a},{b})");
            assert_eq!(ba.mul(&bb), model_mul_256(a, b), "mul({a},{b})");
            assert_eq!(
                ba.div(&bb),
                big(a.checked_div(b).unwrap_or(0)),
                "div({a},{b})"
            );
            assert_eq!(
                ba.rem(&bb),
                big(if b == 0 { a } else { a % b }),
                "rem({a},{b})"
            );
            assert_eq!(ba.gcd(&bb), big(model_gcd(a, b)), "gcd({a},{b})");
            assert_eq!(ba.beq(&bb), a == b, "beq({a},{b})");
            assert_eq!(ba.ble(&bb), a <= b, "ble({a},{b})");
            assert_eq!(ba.land(&bb), big(a & b), "land({a},{b})");
            assert_eq!(ba.lor(&bb), big(a | b), "lor({a},{b})");
            assert_eq!(ba.lxor(&bb), big(a ^ b), "lxor({a},{b})");

            let shl_amount = (lcg_next(&mut state) % 128) as u32;
            let lo = a.wrapping_shl(shl_amount);
            let hi = if shl_amount == 0 {
                0
            } else {
                a >> (128 - shl_amount)
            };
            let expected_shl = BigNat::from_limbs_le(vec![
                lo as u64,
                (lo >> 64) as u64,
                hi as u64,
                (hi >> 64) as u64,
            ]);
            assert_eq!(
                ba.shl(u64::from(shl_amount)),
                expected_shl,
                "shl({a},{shl_amount})"
            );

            let shr_amount = lcg_next(&mut state) % 200;
            let expected_shr = if shr_amount >= 128 {
                0
            } else {
                a >> shr_amount
            };
            assert_eq!(
                ba.shr(shr_amount),
                big(expected_shr),
                "shr({a},{shr_amount})"
            );

            let base = a % 65536;
            let exp = (b % 8) as u32;
            let mut expected_pow = 1u128;
            for _ in 0..exp {
                expected_pow *= base;
            }
            assert_eq!(big(base).pow(exp), big(expected_pow), "pow({base},{exp})");
        }
    }

    #[test]
    fn edge_laws() {
        let zero = BigNat::zero();
        let x = parse("340282366920938463463374607431768211457");
        let y = x.add(&BigNat::from_u64(12345));

        assert_eq!(x.sub(&y), zero, "x - y = 0 when y >= x");
        assert_eq!(x.sub(&x), zero, "x - x = 0");
        assert_eq!(x.div(&zero), zero, "x / 0 = 0");
        assert_eq!(x.rem(&zero), x, "x % 0 = x");
        assert_eq!(zero.gcd(&x), x, "gcd(0, x) = x");
        assert_eq!(x.gcd(&zero), x, "gcd(x, 0) = x");

        assert_eq!(x.shl(0), x, "shl by 0 is identity");
        assert_eq!(x.shr(0), x, "shr by 0 is identity");
        assert_eq!(
            x.shl(128).shr(128),
            x,
            "shl/shr by limb multiples round-trip"
        );
        assert_eq!(x.shl(64).limbs_le().first().copied(), Some(0));
        assert_eq!(zero.shl(64), zero);
        assert_eq!(zero.shr(64), zero);

        assert_eq!(zero.bit_length(), 0, "bit_length(0) = 0");
        let two_pow_64 = BigNat::from_u64(1).shl(64);
        assert_eq!(two_pow_64.bit_length(), 65, "bit_length(2^64) = 65");
        assert_eq!(two_pow_64.limbs_le(), &[0, 1]);

        assert_eq!(BigNat::from_decimal(""), None);
        assert_eq!(BigNat::from_decimal("12a3"), None);
        assert_eq!(BigNat::from_decimal("-1"), None);
        assert_eq!(BigNat::from_decimal("+1"), None);
        assert_eq!(
            BigNat::from_decimal("000042"),
            Some(BigNat::from_u64(42)),
            "leading zeros accepted"
        );
        assert_eq!(zero.to_decimal(), "0");
        assert_eq!(BigNat::from_limbs_le(vec![7, 0, 0]).limbs_le(), &[7]);
        assert_eq!(BigNat::from_limbs_le(vec![0, 0]), zero);
        assert_eq!(x.to_u64(), None);
        assert_eq!(BigNat::from_u64(9).to_u64(), Some(9));
        assert_eq!(zero.to_u64(), Some(0));
    }
}
