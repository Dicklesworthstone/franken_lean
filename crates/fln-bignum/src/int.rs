//! Arbitrary-precision signed integers over the owned [`BigNat`] magnitude.
//!
//! Lean's runtime-private `mpz` is sign-and-magnitude, so the same normalized
//! little-endian limbs used for `Nat` are also the exact storage shape for
//! `Int`. [`BigIntView`] keeps that sign beside a borrowed [`BigNatView`]:
//! Marrow can therefore execute signed arithmetic directly over an ABI object's
//! limbs and allocate only the result.
//!
//! Division follows the pinned runtime's two distinct families. [`BigInt::div`]
//! and [`BigInt::rem`] truncate toward zero, matching GMP `tdiv`; [`BigInt::ediv`]
//! and [`BigInt::emod`] adjust a negative remainder so the remainder is always
//! non-negative, exactly like `mpz::ediv` / `mpz::emod`.

use std::cmp::Ordering;

use crate::nat::{BigNat, BigNatView};

/// An owned arbitrary-precision signed integer.
///
/// Invariant: zero is never negative, and `magnitude` is normalized by
/// [`BigNat`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BigInt {
    negative: bool,
    magnitude: BigNat,
}

/// Immutable zero-copy view of a signed magnitude.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BigIntView<'a> {
    negative: bool,
    magnitude: BigNatView<'a>,
}

impl<'a> BigIntView<'a> {
    /// Borrow a sign-and-magnitude value, normalizing only by shortening the
    /// limb slice and by excluding negative zero.
    pub fn from_sign_limbs_le(negative: bool, limbs: &'a [u64]) -> Self {
        Self::from_sign_magnitude(negative, BigNatView::from_limbs_le(limbs))
    }

    /// Pair a sign with an already-normalized borrowed magnitude.
    pub fn from_sign_magnitude(negative: bool, magnitude: BigNatView<'a>) -> Self {
        Self {
            negative: negative && !magnitude.is_zero(),
            magnitude,
        }
    }

    /// Whether this value is strictly negative.
    pub const fn is_negative(self) -> bool {
        self.negative
    }

    /// Whether this value is zero.
    pub fn is_zero(self) -> bool {
        self.magnitude.is_zero()
    }

    /// Borrow the unsigned magnitude.
    pub const fn magnitude(self) -> BigNatView<'a> {
        self.magnitude
    }

    /// Materialize an owned signed integer when ownership is required.
    pub fn to_owned(self) -> BigInt {
        BigInt::from_sign_magnitude(self.negative, self.magnitude.to_owned())
    }

    /// Return `-self`, preserving the no-negative-zero invariant.
    #[allow(clippy::should_implement_trait)]
    pub fn neg(self) -> BigInt {
        BigInt::from_sign_magnitude(!self.negative, self.magnitude.to_owned())
    }

    /// Exact signed comparison.
    #[allow(clippy::should_implement_trait)]
    pub fn cmp(self, other: BigIntView<'_>) -> Ordering {
        match (self.negative, other.negative) {
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
            (false, false) => compare_magnitudes(self.magnitude, other.magnitude),
            (true, true) => compare_magnitudes(other.magnitude, self.magnitude),
        }
    }

    pub fn beq(self, other: BigIntView<'_>) -> bool {
        self.cmp(other) == Ordering::Equal
    }

    pub fn ble(self, other: BigIntView<'_>) -> bool {
        self.cmp(other) != Ordering::Greater
    }

    #[allow(clippy::should_implement_trait)]
    pub fn add(self, other: BigIntView<'_>) -> BigInt {
        if self.negative == other.negative {
            return BigInt::from_sign_magnitude(self.negative, self.magnitude.add(other.magnitude));
        }
        match compare_magnitudes(self.magnitude, other.magnitude) {
            Ordering::Less => {
                BigInt::from_sign_magnitude(other.negative, other.magnitude.sub(self.magnitude))
            }
            Ordering::Equal => BigInt::zero(),
            Ordering::Greater => {
                BigInt::from_sign_magnitude(self.negative, self.magnitude.sub(other.magnitude))
            }
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn sub(self, other: BigIntView<'_>) -> BigInt {
        if self.negative != other.negative {
            return BigInt::from_sign_magnitude(self.negative, self.magnitude.add(other.magnitude));
        }
        match compare_magnitudes(self.magnitude, other.magnitude) {
            Ordering::Less => {
                BigInt::from_sign_magnitude(!self.negative, other.magnitude.sub(self.magnitude))
            }
            Ordering::Equal => BigInt::zero(),
            Ordering::Greater => {
                BigInt::from_sign_magnitude(self.negative, self.magnitude.sub(other.magnitude))
            }
        }
    }

    #[allow(clippy::should_implement_trait)]
    pub fn mul(self, other: BigIntView<'_>) -> BigInt {
        BigInt::from_sign_magnitude(
            self.negative ^ other.negative,
            self.magnitude.mul(other.magnitude),
        )
    }

    /// Truncating quotient and remainder. The quotient rounds toward zero and
    /// the remainder has the dividend's sign. Division by zero returns
    /// `(0, self)`, matching Lean's total `Int` laws.
    pub fn div_rem(self, other: BigIntView<'_>) -> (BigInt, BigInt) {
        if other.is_zero() {
            return (BigInt::zero(), self.to_owned());
        }
        let (quotient, remainder) = self.magnitude.div_rem(other.magnitude);
        (
            BigInt::from_sign_magnitude(self.negative ^ other.negative, quotient),
            BigInt::from_sign_magnitude(self.negative, remainder),
        )
    }

    #[allow(clippy::should_implement_trait)]
    pub fn div(self, other: BigIntView<'_>) -> BigInt {
        self.div_rem(other).0
    }

    #[allow(clippy::should_implement_trait)]
    pub fn rem(self, other: BigIntView<'_>) -> BigInt {
        self.div_rem(other).1
    }

    /// Exact quotient, or `None` when the divisor is zero or the remainder is
    /// nonzero.
    pub fn checked_div_exact(self, other: BigIntView<'_>) -> Option<BigInt> {
        if other.is_zero() {
            return None;
        }
        let (quotient, remainder) = self.div_rem(other);
        remainder.is_zero().then_some(quotient)
    }

    /// Euclidean quotient and remainder. A nonzero remainder is always
    /// non-negative and strictly smaller than `|other|`.
    pub fn ediv_rem(self, other: BigIntView<'_>) -> (BigInt, BigInt) {
        if other.is_zero() {
            return (BigInt::zero(), self.to_owned());
        }
        let (mut quotient, remainder) = self.div_rem(other);
        if !remainder.is_negative() {
            return (quotient, remainder);
        }

        let one = BigInt::from_i64(1);
        quotient = if other.is_negative() {
            quotient.add(&one)
        } else {
            quotient.sub(&one)
        };
        let magnitude = other.magnitude.sub(remainder.magnitude.as_view());
        (quotient, BigInt::from_sign_magnitude(false, magnitude))
    }

    pub fn ediv(self, other: BigIntView<'_>) -> BigInt {
        self.ediv_rem(other).0
    }

    pub fn emod(self, other: BigIntView<'_>) -> BigInt {
        self.ediv_rem(other).1
    }

    /// Low 64 bits in two's-complement form, matching `mpz::mod64`.
    pub fn low_u64(self) -> u64 {
        let low = self.magnitude.limbs_le().first().copied().unwrap_or(0);
        if self.negative {
            low.wrapping_neg()
        } else {
            low
        }
    }

    /// Convert when the exact value fits in `i128`.
    pub fn to_i128(self) -> Option<i128> {
        let magnitude = magnitude_to_u128(self.magnitude)?;
        if self.negative {
            if magnitude == 1u128 << 127 {
                Some(i128::MIN)
            } else {
                i128::try_from(magnitude).ok().map(|value| -value)
            }
        } else {
            i128::try_from(magnitude).ok()
        }
    }
}

impl BigInt {
    pub fn zero() -> Self {
        Self {
            negative: false,
            magnitude: BigNat::zero(),
        }
    }

    pub fn from_sign_magnitude(negative: bool, magnitude: BigNat) -> Self {
        Self {
            negative: negative && !magnitude.is_zero(),
            magnitude,
        }
    }

    pub fn from_sign_limbs_le(negative: bool, limbs: Vec<u64>) -> Self {
        Self::from_sign_magnitude(negative, BigNat::from_limbs_le(limbs))
    }

    pub fn from_i64(value: i64) -> Self {
        Self::from_i128(i128::from(value))
    }

    pub fn from_i128(value: i128) -> Self {
        let magnitude = value.unsigned_abs();
        let limbs = if magnitude == 0 {
            Vec::new()
        } else {
            let low = magnitude as u64;
            let high = (magnitude >> 64) as u64;
            if high == 0 {
                vec![low]
            } else {
                vec![low, high]
            }
        };
        Self::from_sign_limbs_le(value.is_negative(), limbs)
    }

    pub fn from_u64(value: u64) -> Self {
        Self::from_sign_magnitude(false, BigNat::from_u64(value))
    }

    pub fn from_decimal(text: &str) -> Option<Self> {
        let (negative, digits) = text
            .strip_prefix('-')
            .map(|digits| (true, digits))
            .or_else(|| text.strip_prefix('+').map(|digits| (false, digits)))
            .unwrap_or((false, text));
        let magnitude = BigNat::from_decimal(digits)?;
        Some(Self::from_sign_magnitude(negative, magnitude))
    }

    pub fn to_decimal(&self) -> String {
        let magnitude = self.magnitude.to_decimal();
        if self.negative {
            format!("-{magnitude}")
        } else {
            magnitude
        }
    }

    pub fn as_view(&self) -> BigIntView<'_> {
        BigIntView::from_sign_magnitude(self.negative, self.magnitude.as_view())
    }

    pub const fn is_negative(&self) -> bool {
        self.negative
    }

    pub fn is_zero(&self) -> bool {
        self.magnitude.is_zero()
    }

    pub const fn magnitude(&self) -> &BigNat {
        &self.magnitude
    }

    pub fn to_i128(&self) -> Option<i128> {
        self.as_view().to_i128()
    }

    pub fn to_i64(&self) -> Option<i64> {
        self.to_i128().and_then(|value| i64::try_from(value).ok())
    }

    pub fn low_u64(&self) -> u64 {
        self.as_view().low_u64()
    }

    pub fn neg(&self) -> BigInt {
        self.as_view().neg()
    }

    pub fn beq(&self, other: &BigInt) -> bool {
        self.as_view().beq(other.as_view())
    }

    pub fn ble(&self, other: &BigInt) -> bool {
        self.as_view().ble(other.as_view())
    }

    pub fn add(&self, other: &BigInt) -> BigInt {
        self.as_view().add(other.as_view())
    }

    pub fn sub(&self, other: &BigInt) -> BigInt {
        self.as_view().sub(other.as_view())
    }

    pub fn mul(&self, other: &BigInt) -> BigInt {
        self.as_view().mul(other.as_view())
    }

    pub fn div_rem(&self, other: &BigInt) -> (BigInt, BigInt) {
        self.as_view().div_rem(other.as_view())
    }

    pub fn div(&self, other: &BigInt) -> BigInt {
        self.as_view().div(other.as_view())
    }

    pub fn rem(&self, other: &BigInt) -> BigInt {
        self.as_view().rem(other.as_view())
    }

    pub fn checked_div_exact(&self, other: &BigInt) -> Option<BigInt> {
        self.as_view().checked_div_exact(other.as_view())
    }

    pub fn ediv_rem(&self, other: &BigInt) -> (BigInt, BigInt) {
        self.as_view().ediv_rem(other.as_view())
    }

    pub fn ediv(&self, other: &BigInt) -> BigInt {
        self.as_view().ediv(other.as_view())
    }

    pub fn emod(&self, other: &BigInt) -> BigInt {
        self.as_view().emod(other.as_view())
    }
}

impl Ord for BigInt {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_view().cmp(other.as_view())
    }
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn compare_magnitudes(left: BigNatView<'_>, right: BigNatView<'_>) -> Ordering {
    if left.beq(right) {
        Ordering::Equal
    } else if left.ble(right) {
        Ordering::Less
    } else {
        Ordering::Greater
    }
}

fn magnitude_to_u128(magnitude: BigNatView<'_>) -> Option<u128> {
    match magnitude.limbs_le() {
        [] => Some(0),
        [low] => Some(u128::from(*low)),
        [low, high] => Some(u128::from(*low) | (u128::from(*high) << 64)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::BigInt;

    fn as_i128(value: &BigInt) -> i128 {
        value.to_i128().expect("test value fits i128")
    }

    #[test]
    fn signed_arithmetic_matches_the_independent_i128_model() {
        for left in -65i128..=65 {
            for right in -17i128..=17 {
                let a = BigInt::from_i128(left);
                let b = BigInt::from_i128(right);
                assert_eq!(as_i128(&a.add(&b)), left + right);
                assert_eq!(as_i128(&a.sub(&b)), left - right);
                assert_eq!(as_i128(&a.mul(&b)), left * right);
                assert_eq!(a.cmp(&b), left.cmp(&right));

                let (quotient, remainder) = a.div_rem(&b);
                if right == 0 {
                    assert_eq!(as_i128(&quotient), 0);
                    assert_eq!(as_i128(&remainder), left);
                } else {
                    assert_eq!(as_i128(&quotient), left / right);
                    assert_eq!(as_i128(&remainder), left % right);
                    let (euclidean_quotient, euclidean_remainder) = a.ediv_rem(&b);
                    assert_eq!(as_i128(&euclidean_quotient), left.div_euclid(right));
                    assert_eq!(as_i128(&euclidean_remainder), left.rem_euclid(right));
                }
            }
        }
    }

    #[test]
    fn decimal_boundaries_and_negative_zero_are_canonical() {
        let values = [
            "0",
            "-0",
            "1",
            "-1",
            "9223372036854775808",
            "-9223372036854775808",
            "340282366920938463463374607431768211457",
            "-340282366920938463463374607431768211457",
        ];
        for text in values {
            let parsed = BigInt::from_decimal(text).expect("valid decimal");
            let expected = if text == "-0" { "0" } else { text };
            assert_eq!(parsed.to_decimal(), expected);
        }
        assert!(!BigInt::from_decimal("-0").unwrap().is_negative());
        assert!(BigInt::from_decimal("").is_none());
        assert!(BigInt::from_decimal("-").is_none());
        assert!(BigInt::from_decimal("12x").is_none());
    }

    #[test]
    fn large_sign_magnitude_operations_and_low_bits_are_exact() {
        let two_128_plus_one =
            BigInt::from_decimal("340282366920938463463374607431768211457").unwrap();
        let negative = two_128_plus_one.neg();
        assert_eq!(two_128_plus_one.add(&negative), BigInt::zero());
        assert_eq!(negative.low_u64(), u64::MAX);
        assert_eq!(two_128_plus_one.low_u64(), 1);

        let three = BigInt::from_i64(3);
        let product = two_128_plus_one.mul(&three);
        assert_eq!(
            product.to_decimal(),
            "1020847100762815390390123822295304634371"
        );
        assert_eq!(product.checked_div_exact(&three), Some(two_128_plus_one));
        assert!(product.checked_div_exact(&BigInt::from_i64(5)).is_none());
    }
}
