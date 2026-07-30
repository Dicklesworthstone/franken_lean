//! Arbitrary-precision unsigned naturals with Lean `Nat` semantics (plan §8.4).
//!
//! The operation set is exactly the kernel literal-acceleration set of KR-313:
//! `add`, `sub` (truncated), `mul`, `div`/`rem` (Lean division-by-zero laws),
//! `gcd`, `pow`, `beq`, `ble`, `land`, `lor`, `lxor`, `shl`, `shr`.
//!
//! Representation invariant: little-endian `u64` limbs, normalized — no
//! trailing zero limbs; the empty limb vector is zero. This is deliberately
//! identical to `fln_core::expr::NatLit`'s representation, which is what lets
//! `interop` move values across the term-plane boundary without reshaping them.
//! [`BigNatView`] applies the same invariant to borrowed storage by shortening
//! a slice only, so the ABI boundary can consume limbs without first copying
//! them into an owned value.
//!
//! Division and gcd are iterative. Karatsuba/Toom multiplication has only
//! logarithmic, size-decreasing recursion: [`MAX_LIMBS`] and the
//! [`KARATSUBA_THRESHOLD`] schoolbook floor cap its host-stack depth below 23
//! even at the allocation ceiling. The two operations whose *result* grows
//! without bound in their argument — [`BigNat::shl`] and [`BigNat::pow`] —
//! size that result before allocating it and refuse through
//! [`BigNat::checked_shl`] / [`BigNat::checked_pow`] when it would exceed
//! [`MAX_LIMBS`]. Refusal is what FL-INV-07 requires: resource exhaustion is a
//! typed outcome the caller can see, never an allocator abort that takes the
//! process with it.

use std::cmp::Ordering;

/// Arbitrary-precision unsigned natural number (KR-313 / plan §8.4).
///
/// Invariant: `limbs` is little-endian and normalized (no trailing zeros).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BigNat {
    limbs: Vec<u64>,
}

/// Immutable, zero-copy view of a natural-number magnitude.
///
/// The view borrows normalized little-endian limbs. Construction trims only
/// trailing zero limbs by shortening the slice; it never allocates or rewrites
/// the borrowed storage. This is the Marrow bridge: an ABI `mpz` limb buffer can
/// participate in arithmetic directly, with allocations reserved for results.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BigNatView<'a> {
    limbs: &'a [u64],
}

/// `10^19`: the largest power of ten with `10^k - 1` representable in `u64`.
const DECIMAL_CHUNK_BASE: u128 = 10_000_000_000_000_000_000;
/// Digits per decimal chunk (`log10(DECIMAL_CHUNK_BASE)`).
const DECIMAL_CHUNK_DIGITS: usize = 19;

/// The widest single value this crate will allocate: `2^28` limbs, or 2 GiB.
///
/// A *policy* bound, not a mathematical one — `Nat` is unbounded. It exists so
/// that an absurd growth request is answered rather than attempted: `x << 2^58`
/// names a number needing two exabytes of limbs, and asking the allocator for
/// that aborts the process instead of returning a verdict. The bound is far
/// above anything a kernel-accepted proof reaches (the pinned `pow` exponent cap
/// is `2^24`, and every kernel growth path charges its result size against a
/// budget first — see `fln_kernel::tc`), so refusing past it costs no reachable
/// arithmetic.
///
/// It is also what makes the sizing portable: the limb count is computed in
/// `u128` and compared here, so a 32-bit `usize` cannot truncate a large shift
/// into a small, silently *wrong* allocation.
pub const MAX_LIMBS: usize = 1 << 28;

/// Operand-width crossover from schoolbook to Karatsuba multiplication.
///
/// The value is pinned by the kernel-reduction profile and the boundary tests
/// below. The dispatcher also keeps strongly unbalanced products on the
/// schoolbook path, where splitting the wider operand adds work without
/// reducing the shorter dimension.
pub const KARATSUBA_THRESHOLD: usize = 80;

/// Operand-width crossover from Karatsuba to three-way Toom-Cook.
pub const TOOM3_THRESHOLD: usize = 2048;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MulAlgorithm {
    Schoolbook,
    Karatsuba,
    Toom3,
}

fn normalize(limbs: &mut Vec<u64>) {
    while limbs.last() == Some(&0) {
        limbs.pop();
    }
}

fn normalized_len(limbs: &[u64]) -> usize {
    limbs
        .iter()
        .rposition(|limb| *limb != 0)
        .map_or(0, |index| index + 1)
}

fn normalized_slice(limbs: &[u64]) -> &[u64] {
    &limbs[..normalized_len(limbs)]
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
#[cfg(test)]
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

fn bit_length_limbs(limbs: &[u64]) -> u64 {
    match limbs.last() {
        None => 0,
        Some(&top) => (limbs.len() as u64 - 1) * 64 + u64::from(64 - top.leading_zeros()),
    }
}

fn add_limbs(a: &[u64], b: &[u64]) -> BigNat {
    let (longer, shorter) = if a.len() >= b.len() { (a, b) } else { (b, a) };
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

fn sub_limbs(a: &[u64], b: &[u64]) -> BigNat {
    if cmp_limbs(a, b) != Ordering::Greater {
        return BigNat::zero();
    }
    let mut out = a.to_vec();
    sub_in_place(&mut out, b);
    BigNat { limbs: out }
}

fn schoolbook_mul_limbs(a: &[u64], b: &[u64]) -> BigNat {
    if a.is_empty() || b.is_empty() {
        return BigNat::zero();
    }
    let mut out = vec![0u64; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        let mut carry = 0u128;
        for (j, &y) in b.iter().enumerate() {
            if let Some(slot) = out.get_mut(i + j) {
                let cur = u128::from(*slot) + u128::from(x) * u128::from(y) + carry;
                *slot = cur as u64;
                carry = cur >> 64;
            }
        }
        if let Some(slot) = out.get_mut(i + b.len()) {
            *slot = (u128::from(*slot) + carry) as u64;
        }
    }
    BigNat::from_limbs_le(out)
}

fn mul_algorithm(a_len: usize, b_len: usize) -> MulAlgorithm {
    let shorter = a_len.min(b_len);
    let longer = a_len.max(b_len);
    if shorter < KARATSUBA_THRESHOLD || longer > shorter.saturating_mul(2) {
        MulAlgorithm::Schoolbook
    } else if shorter < TOOM3_THRESHOLD {
        MulAlgorithm::Karatsuba
    } else {
        MulAlgorithm::Toom3
    }
}

fn add_shifted_limbs(out: &mut Vec<u64>, addend: &[u64], shift: usize) {
    if addend.is_empty() {
        return;
    }
    let needed = shift
        .checked_add(addend.len())
        .and_then(|len| len.checked_add(1))
        .expect("bignum product length overflow");
    if out.len() < needed {
        out.resize(needed, 0);
    }
    let mut carry = 0u128;
    for (index, &limb) in addend.iter().enumerate() {
        let slot = shift + index;
        let sum = u128::from(out[slot]) + u128::from(limb) + carry;
        out[slot] = sum as u64;
        carry = sum >> 64;
    }
    let mut slot = shift + addend.len();
    while carry != 0 {
        if slot == out.len() {
            out.push(0);
        }
        let sum = u128::from(out[slot]) + carry;
        out[slot] = sum as u64;
        carry = sum >> 64;
        slot += 1;
    }
}

fn karatsuba_mul_limbs(a: &[u64], b: &[u64]) -> BigNat {
    if a.is_empty() || b.is_empty() {
        return BigNat::zero();
    }
    if mul_algorithm(a.len(), b.len()) == MulAlgorithm::Schoolbook {
        return schoolbook_mul_limbs(a, b);
    }
    karatsuba_mul_balanced(a, b)
}

fn karatsuba_mul_balanced(a: &[u64], b: &[u64]) -> BigNat {
    let split = a.len().max(b.len()).div_ceil(2);
    let a_split = split.min(a.len());
    let b_split = split.min(b.len());
    let (a0, a1) = a.split_at(a_split);
    let (b0, b1) = b.split_at(b_split);

    let z0 = mul_limbs(a0, b0);
    let z2 = mul_limbs(a1, b1);
    let a_sum = add_limbs(a0, a1);
    let b_sum = add_limbs(b0, b1);
    let middle_total = mul_limbs(a_sum.limbs_le(), b_sum.limbs_le());
    assert!(
        middle_total >= z0,
        "Karatsuba interpolation underflowed at z0"
    );
    let middle_without_z0 = middle_total.sub(&z0);
    assert!(
        middle_without_z0 >= z2,
        "Karatsuba interpolation underflowed at z2"
    );
    let middle = middle_without_z0.sub(&z2);

    let mut out = Vec::with_capacity(a.len() + b.len() + 1);
    add_shifted_limbs(&mut out, z0.limbs_le(), 0);
    add_shifted_limbs(&mut out, middle.limbs_le(), split);
    add_shifted_limbs(&mut out, z2.limbs_le(), split * 2);
    BigNat::from_limbs_le(out)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SignedLimbs {
    negative: bool,
    magnitude: BigNat,
}

impl SignedLimbs {
    fn from_magnitude(magnitude: BigNat) -> Self {
        SignedLimbs {
            negative: false,
            magnitude,
        }
    }

    fn from_limbs(limbs: &[u64]) -> Self {
        Self::from_magnitude(BigNat::from_limbs_le(limbs.to_vec()))
    }

    fn normalized(mut self) -> Self {
        if self.magnitude.is_zero() {
            self.negative = false;
        }
        self
    }

    fn negated(mut self) -> Self {
        if !self.magnitude.is_zero() {
            self.negative = !self.negative;
        }
        self
    }

    fn add(&self, other: &SignedLimbs) -> SignedLimbs {
        if self.negative == other.negative {
            return SignedLimbs {
                negative: self.negative,
                magnitude: self.magnitude.add(&other.magnitude),
            }
            .normalized();
        }
        match cmp_limbs(self.magnitude.limbs_le(), other.magnitude.limbs_le()) {
            Ordering::Greater => SignedLimbs {
                negative: self.negative,
                magnitude: self.magnitude.sub(&other.magnitude),
            },
            Ordering::Less => SignedLimbs {
                negative: other.negative,
                magnitude: other.magnitude.sub(&self.magnitude),
            },
            Ordering::Equal => SignedLimbs::from_magnitude(BigNat::zero()),
        }
        .normalized()
    }

    fn sub(&self, other: &SignedLimbs) -> SignedLimbs {
        self.add(&other.clone().negated())
    }

    fn mul(&self, other: &SignedLimbs) -> SignedLimbs {
        SignedLimbs {
            negative: self.negative ^ other.negative,
            magnitude: mul_limbs(self.magnitude.limbs_le(), other.magnitude.limbs_le()),
        }
        .normalized()
    }

    fn mul_small(&self, factor: u64) -> SignedLimbs {
        SignedLimbs {
            negative: self.negative,
            magnitude: self.magnitude.mul_small(factor),
        }
        .normalized()
    }

    fn div_exact_small(&self, divisor: u64) -> SignedLimbs {
        assert!(divisor != 0, "exact small division by zero");
        let mut quotient = vec![0; self.magnitude.limbs_le().len()];
        let mut remainder = 0u128;
        for (index, &limb) in self.magnitude.limbs_le().iter().enumerate().rev() {
            let value = (remainder << 64) | u128::from(limb);
            quotient[index] = (value / u128::from(divisor)) as u64;
            remainder = value % u128::from(divisor);
        }
        assert_eq!(remainder, 0, "Toom interpolation division must be exact");
        SignedLimbs {
            negative: self.negative,
            magnitude: BigNat::from_limbs_le(quotient),
        }
        .normalized()
    }

    fn into_nonnegative(self, coefficient: &str) -> BigNat {
        assert!(
            !self.negative,
            "Toom interpolation produced a negative {coefficient} coefficient"
        );
        self.magnitude
    }
}

fn split_three(limbs: &[u64], width: usize) -> (&[u64], &[u64], &[u64]) {
    let first = width.min(limbs.len());
    let second = width.saturating_mul(2).min(limbs.len());
    (
        normalized_slice(&limbs[..first]),
        normalized_slice(&limbs[first..second]),
        normalized_slice(&limbs[second..]),
    )
}

fn eval_toom_at_one(parts: (&[u64], &[u64], &[u64])) -> BigNat {
    add_limbs(add_limbs(parts.0, parts.1).limbs_le(), parts.2)
}

fn eval_toom_at_minus_one(parts: (&[u64], &[u64], &[u64])) -> SignedLimbs {
    SignedLimbs::from_limbs(parts.0)
        .sub(&SignedLimbs::from_limbs(parts.1))
        .add(&SignedLimbs::from_limbs(parts.2))
}

fn eval_toom_at_two(parts: (&[u64], &[u64], &[u64])) -> BigNat {
    let p0 = BigNat::from_limbs_le(parts.0.to_vec());
    let p1 = BigNat::from_limbs_le(parts.1.to_vec()).mul_small(2);
    let p2 = BigNat::from_limbs_le(parts.2.to_vec()).mul_small(4);
    p0.add(&p1).add(&p2)
}

fn toom3_mul_limbs(a: &[u64], b: &[u64]) -> BigNat {
    if a.is_empty() || b.is_empty() {
        return BigNat::zero();
    }
    if a.len().min(b.len()) < TOOM3_THRESHOLD
        || a.len().max(b.len()) > a.len().min(b.len()).saturating_mul(2)
    {
        return karatsuba_mul_limbs(a, b);
    }
    toom3_mul_balanced(a, b)
}

fn toom3_mul_balanced(a: &[u64], b: &[u64]) -> BigNat {
    let width = a.len().max(b.len()).div_ceil(3);
    let a_parts = split_three(a, width);
    let b_parts = split_three(b, width);

    let c0 = mul_limbs(a_parts.0, b_parts.0);
    let c4 = mul_limbs(a_parts.2, b_parts.2);
    let at_one_a = eval_toom_at_one(a_parts);
    let at_one_b = eval_toom_at_one(b_parts);
    let v1 = SignedLimbs::from_magnitude(mul_limbs(at_one_a.limbs_le(), at_one_b.limbs_le()));
    let vm1 = eval_toom_at_minus_one(a_parts).mul(&eval_toom_at_minus_one(b_parts));
    let at_two_a = eval_toom_at_two(a_parts);
    let at_two_b = eval_toom_at_two(b_parts);
    let v2 = SignedLimbs::from_magnitude(mul_limbs(at_two_a.limbs_le(), at_two_b.limbs_le()));
    let c0_signed = SignedLimbs::from_magnitude(c0.clone());
    let c4_signed = SignedLimbs::from_magnitude(c4.clone());

    let c1_plus_c3 = v1.sub(&vm1).div_exact_small(2);
    let c2 = v1
        .add(&vm1)
        .div_exact_small(2)
        .sub(&c0_signed)
        .sub(&c4_signed);
    let c1_plus_four_c3 = v2
        .sub(&c0_signed)
        .sub(&c2.mul_small(4))
        .sub(&c4_signed.mul_small(16))
        .div_exact_small(2);
    let c3 = c1_plus_four_c3.sub(&c1_plus_c3).div_exact_small(3);
    let c1 = c1_plus_c3.sub(&c3);

    let c1 = c1.into_nonnegative("x");
    let c2 = c2.into_nonnegative("x^2");
    let c3 = c3.into_nonnegative("x^3");
    let mut out = Vec::with_capacity(a.len() + b.len() + 1);
    add_shifted_limbs(&mut out, c0.limbs_le(), 0);
    add_shifted_limbs(&mut out, c1.limbs_le(), width);
    add_shifted_limbs(&mut out, c2.limbs_le(), width * 2);
    add_shifted_limbs(&mut out, c3.limbs_le(), width * 3);
    add_shifted_limbs(&mut out, c4.limbs_le(), width * 4);
    BigNat::from_limbs_le(out)
}

fn mul_limbs(a: &[u64], b: &[u64]) -> BigNat {
    let a = normalized_slice(a);
    let b = normalized_slice(b);
    match mul_algorithm(a.len(), b.len()) {
        MulAlgorithm::Schoolbook => schoolbook_mul_limbs(a, b),
        MulAlgorithm::Karatsuba => karatsuba_mul_limbs(a, b),
        MulAlgorithm::Toom3 => toom3_mul_limbs(a, b),
    }
}

#[cfg(test)]
fn bitwise_div_rem_limbs(dividend: &[u64], divisor: &[u64]) -> (BigNat, BigNat) {
    if divisor.is_empty() || cmp_limbs(dividend, divisor) == Ordering::Less {
        return (BigNat::zero(), BigNat::from_limbs_le(dividend.to_vec()));
    }
    let bits = bit_length_limbs(dividend);
    let mut quotient = vec![0u64; dividend.len()];
    let mut remainder: Vec<u64> = Vec::with_capacity(divisor.len() + 1);
    for i in (0..bits).rev() {
        shl1_in_place(&mut remainder);
        let limb_idx = (i / 64) as usize;
        let bit = dividend
            .get(limb_idx)
            .map_or(0, |&limb| (limb >> (i % 64)) & 1);
        if bit == 1 {
            if let Some(first) = remainder.first_mut() {
                *first |= 1;
            } else {
                remainder.push(1);
            }
        }
        if cmp_limbs(&remainder, divisor) != Ordering::Less {
            sub_in_place(&mut remainder, divisor);
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

fn shift_left_bits(limbs: &[u64], shift: u32) -> Vec<u64> {
    if shift == 0 || limbs.is_empty() {
        return limbs.to_vec();
    }
    let mut out = Vec::with_capacity(limbs.len() + 1);
    let mut carry = 0u64;
    for &limb in limbs {
        out.push((limb << shift) | carry);
        carry = limb >> (64 - shift);
    }
    if carry != 0 {
        out.push(carry);
    }
    out
}

fn shift_right_bits(limbs: &[u64], shift: u32) -> Vec<u64> {
    if shift == 0 || limbs.is_empty() {
        return limbs.to_vec();
    }
    let mut out = vec![0; limbs.len()];
    let mut carry = 0u64;
    for (index, &limb) in limbs.iter().enumerate().rev() {
        out[index] = (limb >> shift) | carry;
        carry = limb << (64 - shift);
    }
    normalize(&mut out);
    out
}

fn div_rem_single_limb(dividend: &[u64], divisor: u64) -> (BigNat, BigNat) {
    let mut quotient = vec![0; dividend.len()];
    let mut remainder = 0u128;
    for (index, &limb) in dividend.iter().enumerate().rev() {
        let value = (remainder << 64) | u128::from(limb);
        quotient[index] = (value / u128::from(divisor)) as u64;
        remainder = value % u128::from(divisor);
    }
    (
        BigNat::from_limbs_le(quotient),
        BigNat::from_u64(remainder as u64),
    )
}

fn knuth_div_rem_limbs(dividend: &[u64], divisor: &[u64]) -> (BigNat, BigNat) {
    debug_assert!(divisor.len() >= 2);
    debug_assert!(cmp_limbs(dividend, divisor) != Ordering::Less);

    const BASE: u128 = 1u128 << 64;
    let n = divisor.len();
    let m = dividend.len() - n;
    let shift = divisor[n - 1].leading_zeros();
    let normalized_divisor = shift_left_bits(divisor, shift);
    assert_eq!(
        normalized_divisor.len(),
        n,
        "normalizing a divisor must not add a limb"
    );
    let mut normalized_dividend = shift_left_bits(dividend, shift);
    normalized_dividend.resize(dividend.len() + 1, 0);
    let mut quotient = vec![0u64; m + 1];

    for j in (0..=m).rev() {
        let top = normalized_dividend[j + n];
        let next = normalized_dividend[j + n - 1];
        let divisor_top = normalized_divisor[n - 1];
        assert!(
            top <= divisor_top,
            "Knuth-D quotient estimate exceeds one radix digit"
        );
        let (mut qhat, mut rhat) = if top == divisor_top {
            (u64::MAX, u128::from(next) + u128::from(divisor_top))
        } else {
            let numerator = (u128::from(top) << 64) | u128::from(next);
            (
                (numerator / u128::from(divisor_top)) as u64,
                numerator % u128::from(divisor_top),
            )
        };
        let next_divisor = normalized_divisor[n - 2];
        let next_dividend = normalized_dividend[j + n - 2];
        while rhat < BASE
            && u128::from(qhat) * u128::from(next_divisor)
                > (rhat << 64) | u128::from(next_dividend)
        {
            qhat -= 1;
            rhat += u128::from(divisor_top);
        }

        let mut borrow = 0u128;
        for (index, &divisor_limb) in normalized_divisor.iter().enumerate() {
            let product = u128::from(qhat) * u128::from(divisor_limb) + borrow;
            let (difference, underflow) =
                normalized_dividend[j + index].overflowing_sub(product as u64);
            normalized_dividend[j + index] = difference;
            borrow = (product >> 64) + u128::from(underflow);
        }
        let high = normalized_dividend[j + n];
        let negative = u128::from(high) < borrow;
        normalized_dividend[j + n] = high.wrapping_sub(borrow as u64);
        if negative {
            qhat -= 1;
            let mut carry = 0u128;
            for (index, &divisor_limb) in normalized_divisor.iter().enumerate() {
                let sum =
                    u128::from(normalized_dividend[j + index]) + u128::from(divisor_limb) + carry;
                normalized_dividend[j + index] = sum as u64;
                carry = sum >> 64;
            }
            normalized_dividend[j + n] = normalized_dividend[j + n].wrapping_add(carry as u64);
        }
        quotient[j] = qhat;
    }

    let remainder = shift_right_bits(&normalized_dividend[..n], shift);
    (
        BigNat::from_limbs_le(quotient),
        BigNat::from_limbs_le(remainder),
    )
}

fn div_rem_limbs(dividend: &[u64], divisor: &[u64]) -> (BigNat, BigNat) {
    let dividend = normalized_slice(dividend);
    let divisor = normalized_slice(divisor);
    if divisor.is_empty() || cmp_limbs(dividend, divisor) == Ordering::Less {
        return (BigNat::zero(), BigNat::from_limbs_le(dividend.to_vec()));
    }
    if divisor.len() == 1 {
        return div_rem_single_limb(dividend, divisor[0]);
    }
    knuth_div_rem_limbs(dividend, divisor)
}

fn trailing_zero_bits_limbs(limbs: &[u64]) -> u64 {
    for (index, &limb) in limbs.iter().enumerate() {
        if limb != 0 {
            return index as u64 * 64 + u64::from(limb.trailing_zeros());
        }
    }
    0
}

fn binary_gcd_limbs(a: &[u64], b: &[u64]) -> BigNat {
    if a.is_empty() {
        return BigNat::from_limbs_le(b.to_vec());
    }
    if b.is_empty() {
        return BigNat::from_limbs_le(a.to_vec());
    }

    let common_shift = trailing_zero_bits_limbs(a).min(trailing_zero_bits_limbs(b));
    let mut a = BigNat::from_limbs_le(a.to_vec()).shr(trailing_zero_bits_limbs(a));
    let mut b = BigNat::from_limbs_le(b.to_vec()).shr(trailing_zero_bits_limbs(b));
    while !b.is_zero() {
        if cmp_limbs(a.limbs_le(), b.limbs_le()) == Ordering::Greater {
            std::mem::swap(&mut a, &mut b);
        }
        b = b.sub(&a);
        if !b.is_zero() {
            b = b.shr(trailing_zero_bits_limbs(b.limbs_le()));
        }
    }
    a.shl(common_shift)
}

fn checked_pow_limbs(limbs: &[u64], exp: u32) -> Option<BigNat> {
    let result_bits = u128::from(bit_length_limbs(limbs)) * u128::from(exp);
    if result_bits / 64 + 1 > MAX_LIMBS as u128 {
        return None;
    }
    let source = BigNatView::from_limbs_le(limbs);
    let mut result = BigNat::from_u64(1);
    let mut squared: Option<BigNat> = None;
    let mut e = exp;
    while e > 0 {
        if e & 1 == 1 {
            result = match squared.as_ref() {
                Some(base) => mul_limbs(result.limbs_le(), base.limbs_le()),
                None => mul_limbs(result.limbs_le(), source.limbs_le()),
            };
        }
        e >>= 1;
        if e > 0 {
            squared = Some(match squared.as_ref() {
                Some(base) => mul_limbs(base.limbs_le(), base.limbs_le()),
                None => mul_limbs(source.limbs_le(), source.limbs_le()),
            });
        }
    }
    Some(result)
}

impl<'a> BigNatView<'a> {
    /// Borrow little-endian limbs, normalizing by shortening the view only.
    pub fn from_limbs_le(mut limbs: &'a [u64]) -> Self {
        while limbs.last() == Some(&0) {
            limbs = &limbs[..limbs.len() - 1];
        }
        Self { limbs }
    }

    /// The borrowed normalized little-endian limbs.
    pub fn limbs_le(self) -> &'a [u64] {
        self.limbs
    }

    /// Materialize an owned value when ownership is explicitly required.
    pub fn to_owned(self) -> BigNat {
        BigNat::from_limbs_le(self.limbs.to_vec())
    }

    pub fn is_zero(self) -> bool {
        self.limbs.is_empty()
    }

    pub fn bit_length(self) -> u64 {
        bit_length_limbs(self.limbs)
    }

    pub fn to_u64(self) -> Option<u64> {
        match self.limbs {
            [] => Some(0),
            [value] => Some(*value),
            _ => None,
        }
    }

    pub fn beq(self, other: BigNatView<'_>) -> bool {
        cmp_limbs(self.limbs, other.limbs) == Ordering::Equal
    }

    pub fn ble(self, other: BigNatView<'_>) -> bool {
        cmp_limbs(self.limbs, other.limbs) != Ordering::Greater
    }

    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: BigNatView<'_>) -> BigNat {
        add_limbs(self.limbs, other.limbs)
    }

    #[allow(clippy::should_implement_trait)]
    pub fn sub(self, other: BigNatView<'_>) -> BigNat {
        sub_limbs(self.limbs, other.limbs)
    }

    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, other: BigNatView<'_>) -> BigNat {
        mul_limbs(self.limbs, other.limbs)
    }

    #[allow(clippy::should_implement_trait)]
    pub fn div(self, other: BigNatView<'_>) -> BigNat {
        self.div_rem(other).0
    }

    #[allow(clippy::should_implement_trait)]
    pub fn rem(self, other: BigNatView<'_>) -> BigNat {
        self.div_rem(other).1
    }

    pub fn div_rem(self, other: BigNatView<'_>) -> (BigNat, BigNat) {
        div_rem_limbs(self.limbs, other.limbs)
    }

    pub fn checked_pow(self, exp: u32) -> Option<BigNat> {
        checked_pow_limbs(self.limbs, exp)
    }

    /// # Panics
    /// If the result would exceed [`MAX_LIMBS`] limbs.
    pub fn pow(self, exp: u32) -> BigNat {
        self.checked_pow(exp).unwrap_or_else(|| {
            panic!(
                "BigNatView::pow: raising a {}-bit value to {exp} exceeds MAX_LIMBS \
                 ({MAX_LIMBS}); the caller must charge the result size before exponentiating",
                self.bit_length()
            )
        })
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

    /// Borrow this value without copying its limb storage.
    pub fn as_view(&self) -> BigNatView<'_> {
        BigNatView { limbs: &self.limbs }
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
        bit_length_limbs(&self.limbs)
    }

    /// Kernel-facing `Nat.beq` (KR-313).
    pub fn beq(&self, other: &BigNat) -> bool {
        self.as_view().beq(other.as_view())
    }

    /// Kernel-facing `Nat.ble` (KR-313).
    pub fn ble(&self, other: &BigNat) -> bool {
        self.as_view().ble(other.as_view())
    }

    /// `self + other`.
    #[allow(clippy::should_implement_trait)]
    pub fn add(&self, other: &BigNat) -> BigNat {
        add_limbs(&self.limbs, &other.limbs)
    }

    /// Truncated subtraction, Lean `Nat.sub` semantics: `self - other`, floored
    /// at zero (KR-313).
    #[allow(clippy::should_implement_trait)]
    pub fn sub(&self, other: &BigNat) -> BigNat {
        sub_limbs(&self.limbs, &other.limbs)
    }

    /// `self * other`, selecting schoolbook, Karatsuba, or three-way Toom-Cook
    /// by the corpus-pinned operand-width thresholds.
    #[allow(clippy::should_implement_trait)]
    pub fn mul(&self, other: &BigNat) -> BigNat {
        mul_limbs(&self.limbs, &other.limbs)
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

    /// Quotient and remainder by one-limb division or normalized Knuth-D.
    /// Lean laws: `(x, 0) -> (0, x)`. Invariant on exit for nonzero divisor:
    /// `self = q * other + r` with `r < other`.
    pub fn div_rem(&self, other: &BigNat) -> (BigNat, BigNat) {
        div_rem_limbs(&self.limbs, &other.limbs)
    }

    /// `self ^ exp` by iterative square-and-multiply; `x ^ 0 = 1` (KR-313
    /// caps the accelerated exponent at `2^24`; the cap is enforced by the
    /// kernel caller, not here).
    ///
    /// # Panics
    /// If the result would exceed [`MAX_LIMBS`] limbs. As with
    /// [`BigNat::shl`], the kernel charges the result size first; callers that
    /// cannot use [`BigNat::checked_pow`].
    pub fn pow(&self, exp: u32) -> BigNat {
        self.checked_pow(exp).unwrap_or_else(|| {
            panic!(
                "BigNat::pow: raising a {}-bit value to {exp} exceeds MAX_LIMBS ({MAX_LIMBS}); \
                 the caller must charge the result size before exponentiating",
                self.bit_length()
            )
        })
    }

    /// `self ^ exp`, or `None` when the result would exceed [`MAX_LIMBS`].
    ///
    /// The bound is decided from `bit_length · exp` before any multiplication
    /// runs. Square-and-multiply never builds a value wider than the result it
    /// is heading for — the loop stops squaring once the exponent is exhausted
    /// — so bounding the result bounds every intermediate too.
    pub fn checked_pow(&self, exp: u32) -> Option<BigNat> {
        checked_pow_limbs(&self.limbs, exp)
    }

    /// Greatest common divisor by Stein's binary algorithm; `gcd(0, x) = x`
    /// (KR-313).
    pub fn gcd(&self, other: &BigNat) -> BigNat {
        binary_gcd_limbs(&self.limbs, &other.limbs)
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
    ///
    /// The caller must already have established that the result fits — as the
    /// kernel does, by charging `bits / 64` against its budget before reducing a
    /// `Nat.shiftLeft` application. Violating that is an invariant failure, not
    /// a user diagnostic, so it panics here; callers that cannot make the
    /// guarantee use [`BigNat::checked_shl`] and handle the refusal.
    ///
    /// # Panics
    /// If the result would exceed [`MAX_LIMBS`] limbs.
    pub fn shl(&self, bits: u64) -> BigNat {
        self.checked_shl(bits).unwrap_or_else(|| {
            panic!(
                "BigNat::shl: {bits}-bit shift of a {}-limb value exceeds MAX_LIMBS ({MAX_LIMBS}); \
                 the caller must charge the result size before shifting",
                self.limbs.len()
            )
        })
    }

    /// `self << bits`, or `None` when the result would exceed [`MAX_LIMBS`].
    ///
    /// The refusal is decided from the operand sizes alone, before a single
    /// limb is allocated, so an unrepresentable request costs nothing and never
    /// reaches the allocator.
    pub fn checked_shl(&self, bits: u64) -> Option<BigNat> {
        if self.is_zero() {
            return Some(BigNat::zero());
        }
        // Sized in u128: on a 32-bit target `(bits / 64) as usize` truncates,
        // which would allocate a small buffer and return a wrong value rather
        // than refusing.
        let limb_shift = u128::from(bits / 64);
        let bit_shift = (bits % 64) as u32;
        let possible_carry = u128::from(bit_shift != 0);
        let needed = limb_shift + self.limbs.len() as u128 + possible_carry;
        if needed > MAX_LIMBS as u128 {
            return None;
        }
        // In range by the check above, so this conversion cannot truncate.
        let limb_shift = limb_shift as usize;
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
        Some(BigNat::from_limbs_le(out))
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
    use super::{
        BigNat, KARATSUBA_THRESHOLD, MulAlgorithm, TOOM3_THRESHOLD, bitwise_div_rem_limbs,
        div_rem_limbs, karatsuba_mul_balanced, mul_algorithm, mul_limbs, schoolbook_mul_limbs,
        toom3_mul_balanced,
    };

    const VECTORS: &str = include_str!("../fixtures/nat_vectors.txt");
    const KERNEL_REDUCTION_PROFILE: &str = include_str!("../fixtures/kernel_reduction_profile.tsv");
    const EXPECTED_VECTOR_COUNT: usize = 5725;

    #[test]
    fn kernel_reduction_profile_binds_thresholds_and_crossover_samples() {
        use std::collections::BTreeMap;

        let mut source_rows = 0usize;
        let mut decisions = BTreeMap::new();
        let mut samples = BTreeMap::new();
        let mut saw_schema = false;
        let mut saw_population = false;
        let mut saw_limitation = false;
        for line in KERNEL_REDUCTION_PROFILE.lines() {
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let fields: Vec<&str> = line.split('\t').collect();
            match fields.as_slice() {
                ["schema", "fln.bignum-kernel-reduction-profile/1"] => {
                    saw_schema = true;
                }
                ["source", _, _, _, _] => {
                    source_rows += 1;
                }
                ["population", "bounded-bootstrap-kernel-and-C4-fixtures"] => {
                    saw_population = true;
                }
                ["limitation", "not-a-mathlib-wide-operation-frequency-claim"] => {
                    saw_limitation = true;
                }
                [
                    "sample",
                    "width",
                    "rounds",
                    "schoolbook_ns",
                    "karatsuba_ns",
                    "toom3_ns",
                ] => {}
                ["sample", width, rounds, schoolbook, karatsuba, toom3] => {
                    let parsed = (
                        rounds.parse::<usize>().expect("sample rounds"),
                        schoolbook.parse::<u128>().expect("schoolbook sample"),
                        karatsuba.parse::<u128>().expect("Karatsuba sample"),
                        toom3.parse::<u128>().expect("Toom-3 sample"),
                    );
                    assert!(
                        samples
                            .insert(width.parse::<usize>().expect("sample width"), parsed)
                            .is_none(),
                        "duplicate sample width"
                    );
                }
                ["decision", name, value, _] => {
                    assert!(
                        decisions
                            .insert(*name, value.parse::<usize>().expect("decision value"))
                            .is_none(),
                        "duplicate threshold decision"
                    );
                }
                _ => {}
            }
        }

        assert!(saw_schema && saw_population && saw_limitation);
        assert_eq!(source_rows, 2, "profile source-row floor");
        assert_eq!(
            decisions.get("karatsuba-threshold-limbs"),
            Some(&KARATSUBA_THRESHOLD)
        );
        assert_eq!(
            decisions.get("toom3-threshold-limbs"),
            Some(&TOOM3_THRESHOLD)
        );
        assert!(samples.len() >= 14, "profile sample floor");
        assert!(
            samples[&KARATSUBA_THRESHOLD].2 < samples[&KARATSUBA_THRESHOLD].1,
            "Karatsuba must beat schoolbook at its selected crossover"
        );
        assert!(
            samples[&(TOOM3_THRESHOLD - 512)].3 > samples[&(TOOM3_THRESHOLD - 512)].2,
            "the pre-threshold regression must remain represented"
        );
        for (_, schoolbook, karatsuba, toom3) in
            samples.range(TOOM3_THRESHOLD..).map(|(_, sample)| *sample)
        {
            assert!(karatsuba < schoolbook, "Karatsuba high-width sample");
            assert!(toom3 < karatsuba, "Toom-3 high-width sample");
        }
    }

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

    fn wide(state: &mut u64, limbs: usize) -> BigNat {
        let mut value: Vec<u64> = (0..limbs).map(|_| lcg_next(state)).collect();
        if let Some(top) = value.last_mut() {
            *top |= 1 << 63;
        }
        BigNat::from_limbs_le(value)
    }

    #[test]
    fn multiplication_crossovers_are_pinned_and_both_sides_are_equivalent() {
        assert_eq!(
            mul_algorithm(KARATSUBA_THRESHOLD - 1, KARATSUBA_THRESHOLD),
            MulAlgorithm::Schoolbook
        );
        assert_eq!(
            mul_algorithm(KARATSUBA_THRESHOLD, KARATSUBA_THRESHOLD),
            MulAlgorithm::Karatsuba
        );
        assert_eq!(
            mul_algorithm(TOOM3_THRESHOLD - 1, TOOM3_THRESHOLD - 1),
            MulAlgorithm::Karatsuba
        );
        assert_eq!(
            mul_algorithm(TOOM3_THRESHOLD, TOOM3_THRESHOLD),
            MulAlgorithm::Toom3
        );
        assert_eq!(
            mul_algorithm(KARATSUBA_THRESHOLD, KARATSUBA_THRESHOLD * 2 + 1),
            MulAlgorithm::Schoolbook,
            "strongly unbalanced products stay on the linear-short-side path"
        );

        let mut state = 0x4D53_4F55_4D55_4C31;
        for width in [
            KARATSUBA_THRESHOLD - 1,
            KARATSUBA_THRESHOLD,
            KARATSUBA_THRESHOLD + 1,
            TOOM3_THRESHOLD - 1,
            TOOM3_THRESHOLD,
            TOOM3_THRESHOLD + 1,
        ] {
            let a = wide(&mut state, width);
            let b = wide(&mut state, width);
            let schoolbook = schoolbook_mul_limbs(a.limbs_le(), b.limbs_le());
            assert_eq!(
                mul_limbs(a.limbs_le(), b.limbs_le()),
                schoolbook,
                "dispatcher differs from schoolbook at width {width}"
            );
            if width + 1 >= KARATSUBA_THRESHOLD {
                assert_eq!(
                    karatsuba_mul_balanced(a.limbs_le(), b.limbs_le()),
                    schoolbook,
                    "Karatsuba differs at width {width}"
                );
            }
            if width + 1 >= TOOM3_THRESHOLD {
                assert_eq!(
                    toom3_mul_balanced(a.limbs_le(), b.limbs_le()),
                    schoolbook,
                    "Toom-3 differs at width {width}"
                );
            }
        }
        if std::env::var("FLN_BIGNUM_CALIBRATE").as_deref() == Ok("1") {
            threshold_calibration_report();
        }
    }

    #[test]
    fn toom3_signed_evaluations_and_carry_chains_match_schoolbook() {
        let mut negative_at_minus_one = vec![1, 0, 0, 0];
        negative_at_minus_one.extend([u64::MAX; 4]);
        negative_at_minus_one.extend([2, 0, 0, 1]);
        let mut positive_at_minus_one = vec![u64::MAX; 4];
        positive_at_minus_one.extend([1, 0, 0, 0]);
        positive_at_minus_one.extend([u64::MAX; 4]);
        for (a, b, label) in [
            (
                negative_at_minus_one,
                positive_at_minus_one,
                "opposite-signed evaluation",
            ),
            (
                vec![u64::MAX; 12],
                vec![u64::MAX; 12],
                "max-limb carry chain",
            ),
        ] {
            assert_eq!(
                toom3_mul_balanced(&a, &b),
                schoolbook_mul_limbs(&a, &b),
                "{label}"
            );
        }
    }

    fn threshold_calibration_report() {
        use std::hint::black_box;
        use std::time::Instant;

        let mut state = 0x4D53_4F55_4245_4E43;
        for width in [
            48usize, 64, 72, 80, 88, 96, 112, 128, 192, 256, 320, 384, 448, 512, 640, 768, 896,
            1024, 1280, 1536, 2048, 2560, 3072, 4096, 5120, 6144, 8192, 12288,
        ] {
            let rounds = (8192 / width).max(1);
            let mut elapsed = [0u128; 3];
            for _ in 0..5 {
                let a = wide(&mut state, width);
                let b = wide(&mut state, width);
                for _ in 0..rounds {
                    let started = Instant::now();
                    black_box(schoolbook_mul_limbs(
                        black_box(a.limbs_le()),
                        black_box(b.limbs_le()),
                    ));
                    elapsed[0] += started.elapsed().as_nanos();

                    let started = Instant::now();
                    black_box(karatsuba_mul_balanced(
                        black_box(a.limbs_le()),
                        black_box(b.limbs_le()),
                    ));
                    elapsed[1] += started.elapsed().as_nanos();

                    let started = Instant::now();
                    black_box(toom3_mul_balanced(
                        black_box(a.limbs_le()),
                        black_box(b.limbs_le()),
                    ));
                    elapsed[2] += started.elapsed().as_nanos();
                }
            }
            let observations = u128::from(rounds as u64) * 5;
            eprintln!(
                "width={width} rounds={rounds} schoolbook_ns={} karatsuba_ns={} toom3_ns={}",
                elapsed[0] / observations,
                elapsed[1] / observations,
                elapsed[2] / observations
            );
        }
    }

    #[test]
    fn knuth_d_matches_the_bitwise_model_and_reconstructs_the_dividend() {
        let mut state = 0x4D53_4F55_4449_5631;
        for trial in 0..2_000 {
            let dividend_len = 1 + (lcg_next(&mut state) as usize % 12);
            let divisor_len = 1 + (lcg_next(&mut state) as usize % 8);
            let dividend = wide(&mut state, dividend_len);
            let divisor = wide(&mut state, divisor_len);
            let expected = bitwise_div_rem_limbs(dividend.limbs_le(), divisor.limbs_le());
            let actual = div_rem_limbs(dividend.limbs_le(), divisor.limbs_le());
            assert_eq!(actual, expected, "division model mismatch at trial {trial}");
            let rebuilt = actual.0.mul(&divisor).add(&actual.1);
            assert_eq!(rebuilt, dividend, "q*d+r mismatch at trial {trial}");
            assert!(
                actual.1 < divisor,
                "remainder is not below the divisor at trial {trial}"
            );
        }

        let dividend = wide(&mut state, 9);
        assert_eq!(
            div_rem_limbs(dividend.limbs_le(), &[]),
            (BigNat::zero(), dividend),
            "Lean division-by-zero law"
        );
    }

    #[test]
    fn binary_gcd_matches_an_independent_euclidean_loop() {
        let mut state = 0x4D53_4F55_4743_4431;
        for trial in 0..120 {
            let a_len = 1 + (lcg_next(&mut state) as usize % 8);
            let b_len = 1 + (lcg_next(&mut state) as usize % 8);
            let a = wide(&mut state, a_len);
            let b = wide(&mut state, b_len);
            let mut model_a = a.clone();
            let mut model_b = b.clone();
            while !model_b.is_zero() {
                let (_, remainder) = bitwise_div_rem_limbs(model_a.limbs_le(), model_b.limbs_le());
                model_a = model_b;
                model_b = remainder;
            }
            assert_eq!(
                a.gcd(&b),
                model_a,
                "binary and Euclidean gcd differ at trial {trial}"
            );
        }
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

    /// FL-INV-07 at the crate boundary: a result too large to represent is
    /// refused from the operand sizes alone, before the allocator is asked for
    /// anything. `shl` previously computed `(bits / 64) as usize` and handed it
    /// straight to `vec![0u64; n]`, so these inputs aborted the process — an
    /// exhaustion the caller could neither see nor survive.
    #[test]
    fn oversized_growth_is_refused_before_allocating() {
        let one = BigNat::from_u64(1);
        let wide = BigNat::from_limbs_le(vec![u64::MAX; 4]);

        // 2^58 limbs is two exabytes. Refused, and cheaply — if this test ever
        // takes measurable time, the refusal moved after the allocation.
        assert_eq!(one.checked_shl(u64::MAX), None);
        assert_eq!(one.checked_shl(1 << 40), None);
        assert_eq!(wide.checked_shl(u64::MAX), None);

        // The 32-bit case, which failed differently and worse: this shift needs
        // 2^32 limbs, and `as usize` on a 32-bit target truncates that to 0 —
        // a small buffer and a silently *wrong* answer rather than a crash.
        // Sizing in u128 refuses it on every target.
        assert_eq!(one.checked_shl(1 << 38), None);

        // pow is bounded by `bit_length · exp` the same way.
        assert_eq!(BigNat::from_u64(u64::MAX).checked_pow(u32::MAX), None);
        assert_eq!(wide.checked_pow(1 << 27), None);

        // Operations that cannot grow stay total, so the bound costs no
        // reachable arithmetic: 0 << n, 1^n, and x^0 all still answer.
        assert_eq!(BigNat::zero().checked_shl(u64::MAX), Some(BigNat::zero()));
        assert_eq!(one.checked_pow(u32::MAX), Some(one.clone()));
        assert_eq!(wide.checked_pow(0), Some(one.clone()));
    }

    /// Below the cap the checked spelling is the infallible one — refusal is the
    /// only behavior that was added, not a change of results.
    #[test]
    fn checked_growth_agrees_with_the_infallible_spelling_below_the_cap() {
        let values = [
            BigNat::zero(),
            BigNat::from_u64(1),
            BigNat::from_u64(u64::MAX),
            BigNat::from_limbs_le(vec![u64::MAX, 0, 1]),
        ];
        for value in &values {
            for bits in [0u64, 1, 63, 64, 65, 127, 128, 1000] {
                assert_eq!(
                    value.checked_shl(bits),
                    Some(value.shl(bits)),
                    "checked_shl disagrees at {bits} bits"
                );
            }
            for exp in [0u32, 1, 2, 5, 17] {
                assert_eq!(
                    value.checked_pow(exp),
                    Some(value.pow(exp)),
                    "checked_pow disagrees at exponent {exp}"
                );
            }
        }
    }

    /// The infallible spelling is for callers that have already charged the
    /// result size, as `fln-kernel` does before reducing `Nat.shiftLeft`.
    /// Breaking that contract is an invariant failure with an attributable
    /// message, never an allocator abort that takes the process down anonymously.
    #[test]
    #[should_panic(expected = "exceeds MAX_LIMBS")]
    fn shl_past_the_cap_is_an_attributable_invariant_failure() {
        let _ = BigNat::from_u64(1).shl(u64::MAX);
    }

    #[test]
    #[should_panic(expected = "exceeds MAX_LIMBS")]
    fn pow_past_the_cap_is_an_attributable_invariant_failure() {
        let _ = BigNat::from_u64(u64::MAX).pow(u32::MAX);
    }
}
