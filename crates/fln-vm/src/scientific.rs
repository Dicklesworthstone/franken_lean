//! Bounded conversion of Lean scientific literals to their runtime bits.
//!
//! This follows the pinned `Init/Data/OfScientific.lean` integer algorithm,
//! including its truncation to a 64-bit binary mantissa before rounding to
//! Float or Float32. It is a compiler helper, not an additional extern row.
//! No decimal parser or platform math library participates in conversion.

use fln_bignum::nat::{BigNat, BigNatView, MAX_LIMBS};
use std::fmt;

/// The IEEE representation requested by an admitted scientific literal.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScientificFloatWidth {
    Float,
    Float32,
}

/// A conversion refusal before an unbounded arithmetic allocation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ScientificFloatError {
    /// An input or conservative arithmetic growth bound exceeds the policy.
    LimbLimit {
        operation: &'static str,
        required: u128,
        limit: usize,
    },
    /// Nonzero literals currently require a decimal exponent fitting `u32`.
    ExponentTooLarge,
    /// The bignum library's independent shift ceiling refused the operation.
    BignumLimit { operation: &'static str },
}

impl fmt::Display for ScientificFloatError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LimbLimit {
                operation,
                required,
                limit,
            } => write!(
                formatter,
                "scientific literal {operation} requires up to {required} limbs; limit is {limit}"
            ),
            Self::ExponentTooLarge => {
                formatter.write_str("scientific literal exponent exceeds the bounded u32 range")
            }
            Self::BignumLimit { operation } => {
                write!(
                    formatter,
                    "scientific literal {operation} exceeds the bignum ceiling"
                )
            }
        }
    }
}

impl std::error::Error for ScientificFloatError {}

/// Convert a nonnegative mantissa and decimal exponent into IEEE bits.
///
/// Both inputs contain little-endian `u64` Nat limbs; trailing zero limbs
/// are accepted. `negative_exponent` selects division by a power of ten.
/// Float32 results occupy the low 32 bits of the returned word. A source
/// unary minus is separate, so even underflow here produces positive zero.
///
/// `max_limbs`, capped by the bignum library's own ceiling, bounds each input
/// and conservative arithmetic operand/result growth. It is not a bound on
/// the sum of simultaneously live buffers or the library's multiplication
/// scratch space. Powers, shifts, and products are checked before allocating
/// them. An enormous exponent may be refused even if its mathematical result
/// would overflow or underflow; such a refusal is never a fabricated number.
pub fn scientific_float_bits(
    mantissa: &[u64],
    negative_exponent: bool,
    exponent: &[u64],
    width: ScientificFloatWidth,
    max_limbs: usize,
) -> Result<u64, ScientificFloatError> {
    let limit = max_limbs.min(MAX_LIMBS);
    ensure_limbs("mantissa input", mantissa.len() as u128, limit)?;
    ensure_limbs("exponent input", exponent.len() as u128, limit)?;
    let mantissa = BigNatView::from_limbs_le(mantissa);
    if mantissa.is_zero() {
        return Ok(0);
    }
    let exponent = BigNatView::from_limbs_le(exponent)
        .to_u64()
        .and_then(|value| u32::try_from(value).ok())
        .ok_or(ScientificFloatError::ExponentTooLarge)?;
    if exponent == 0 {
        return Ok(binary_scientific_bits(mantissa, 0, width));
    }

    // 5^e < 2^(3e). Two spare limbs also cover the product allocations
    // used by exponentiation by squaring, before normalization trims them.
    let power_limbs = (u128::from(exponent) * 3).div_ceil(64) + 2;
    ensure_limbs("power of five", power_limbs, limit)?;
    let spare = 64_u64.saturating_sub(mantissa.bit_length().saturating_sub(1));
    let shift = u64::from(exponent) * 3 + spare;
    if negative_exponent {
        ensure_limbs(
            "mantissa shift",
            u128::from(shift / 64)
                + mantissa.limbs_le().len() as u128
                + u128::from(!shift.is_multiple_of(64)),
            limit,
        )?;
    } else {
        ensure_limbs(
            "mantissa product",
            mantissa.limbs_le().len() as u128 + power_limbs,
            limit,
        )?;
    }
    let power = power_of_five(exponent, limit)?;
    if negative_exponent {
        let shifted = mantissa
            .checked_shl(shift)
            .ok_or(ScientificFloatError::BignumLimit {
                operation: "mantissa shift",
            })?;
        let quotient = shifted.div(&power);
        Ok(binary_scientific_bits(
            quotient.as_view(),
            -4 * i64::from(exponent) - spare as i64,
            width,
        ))
    } else {
        let product = bounded_product(mantissa, power.as_view(), "mantissa product", limit)?;
        Ok(binary_scientific_bits(
            product.as_view(),
            i64::from(exponent),
            width,
        ))
    }
}

fn ensure_limbs(
    operation: &'static str,
    required: u128,
    limit: usize,
) -> Result<(), ScientificFloatError> {
    if required > limit as u128 {
        Err(ScientificFloatError::LimbLimit {
            operation,
            required,
            limit,
        })
    } else {
        Ok(())
    }
}

fn bounded_product(
    left: BigNatView<'_>,
    right: BigNatView<'_>,
    operation: &'static str,
    limit: usize,
) -> Result<BigNat, ScientificFloatError> {
    ensure_limbs(
        operation,
        left.limbs_le().len() as u128 + right.limbs_le().len() as u128,
        limit,
    )?;
    Ok(left.mul(right))
}

fn power_of_five(mut exponent: u32, limit: usize) -> Result<BigNat, ScientificFloatError> {
    let mut result = BigNat::from_u64(1);
    let mut base = BigNat::from_u64(5);
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = bounded_product(result.as_view(), base.as_view(), "power of five", limit)?;
        }
        exponent >>= 1;
        if exponent != 0 {
            base = bounded_product(base.as_view(), base.as_view(), "power of five", limit)?;
        }
    }
    Ok(result)
}

fn binary_scientific_bits(
    mantissa: BigNatView<'_>,
    exponent: i64,
    width: ScientificFloatWidth,
) -> u64 {
    if mantissa.is_zero() {
        return 0;
    }
    // `m.log2 - 63` is Nat subtraction. Extract the retained top 64 bits
    // without allocating another large integer, exactly as `(m >>> s).toUInt64`.
    let shift = mantissa.bit_length().saturating_sub(64);
    let word = (shift / 64) as usize;
    let offset = (shift % 64) as u32;
    let limbs = mantissa.limbs_le();
    let mut retained = limbs[word] >> offset;
    if offset != 0 {
        retained |= limbs.get(word + 1).copied().unwrap_or(0) << (64 - offset);
    }
    let exponent = exponent + shift as i64;
    match width {
        ScientificFloatWidth::Float => {
            scale_positive_bits((retained as f64).to_bits(), exponent, 52, 11)
        }
        ScientificFloatWidth::Float32 => {
            // The direct integer-to-f32 rounding precedes scaling in the pin.
            // Rounding through f64 here changes values just above a midpoint.
            scale_positive_bits(u64::from((retained as f32).to_bits()), exponent, 23, 8)
        }
    }
}

/// Exact power-of-two scaling of the finite, nonzero, positive normal value
/// produced by converting a retained UInt64. Subnormal output receives one
/// ties-to-even rounding, including the carry into the minimum normal value.
fn scale_positive_bits(bits: u64, exponent: i64, fraction_bits: u32, exponent_bits: u32) -> u64 {
    let exponent_mask = (1_u64 << exponent_bits) - 1;
    let fraction_mask = (1_u64 << fraction_bits) - 1;
    let original_exponent = (bits >> fraction_bits) & exponent_mask;
    let scaled_exponent = original_exponent as i64 + exponent;
    if scaled_exponent >= exponent_mask as i64 {
        return exponent_mask << fraction_bits;
    }
    if scaled_exponent > 0 {
        return ((scaled_exponent as u64) << fraction_bits) | (bits & fraction_mask);
    }
    let shift = 1 - scaled_exponent;
    if shift > i64::from(fraction_bits + 1) {
        return 0;
    }
    let shift = shift as u32;
    let significand = (1_u64 << fraction_bits) | (bits & fraction_mask);
    let quotient = significand >> shift;
    let remainder = significand & ((1_u64 << shift) - 1);
    let halfway = 1_u64 << (shift - 1);
    quotient + u64::from(remainder > halfway || (remainder == halfway && quotient & 1 != 0))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn convert(mantissa: u64, negative: bool, exponent: u64, width: ScientificFloatWidth) -> u64 {
        scientific_float_bits(&[mantissa], negative, &[exponent], width, 256).unwrap()
    }

    #[test]
    fn scientific_literals_match_pinned_bits_and_integer_rounding_order() {
        for (mantissa, negative, exponent, float, float32) in [
            (1245, true, 3, 4_608_285_800_708_723_180, 1_067_408_425),
            (21, true, 1, 0x4000_cccc_cccc_cccd, 0x4006_6666),
            (1, false, 20, 0x4415_af1d_78b5_8c40, 0x60ad_78ec),
            (1, false, 0, 0x3ff0_0000_0000_0000, 0x3f80_0000),
        ] {
            assert_eq!(
                convert(mantissa, negative, exponent, ScientificFloatWidth::Float),
                float
            );
            assert_eq!(
                convert(mantissa, negative, exponent, ScientificFloatWidth::Float32),
                float32
            );
        }
        assert_eq!(
            convert(
                (1_u64 << 63) + (1_u64 << 39) + 1,
                false,
                0,
                ScientificFloatWidth::Float32
            ),
            0x5f00_0001
        );
        // The pin discards bits below its retained 64-bit mantissa before
        // rounding. A correctly rounded decimal parser would round this up.
        assert_eq!(
            scientific_float_bits(&[2049, 1], false, &[], ScientificFloatWidth::Float, 2).unwrap(),
            0x43f0_0000_0000_0000
        );
    }

    #[test]
    fn scientific_literals_cover_subnormal_normal_and_overflow_boundaries() {
        // 24703282292062328e-340 is mathematically above half of the
        // minimum subnormal, but the pin first rounds its retained integer
        // mantissa to Float. That rounds to the exact halfway value before
        // scaleB rounds again to zero. The ...330 input survives both steps.
        for (mantissa, negative, exponent, width, expected) in [
            (5, true, 324, ScientificFloatWidth::Float, 1),
            (2, true, 324, ScientificFloatWidth::Float, 0),
            (
                24_703_282_292_062_327,
                true,
                340,
                ScientificFloatWidth::Float,
                0,
            ),
            (
                24_703_282_292_062_328,
                true,
                340,
                ScientificFloatWidth::Float,
                0,
            ),
            (
                24_703_282_292_062_330,
                true,
                340,
                ScientificFloatWidth::Float,
                1,
            ),
            (
                22_250_738_585_072_014,
                true,
                324,
                ScientificFloatWidth::Float,
                0x0010_0000_0000_0000,
            ),
            (
                17_976_931_348_623_157,
                false,
                292,
                ScientificFloatWidth::Float,
                0x7fef_ffff_ffff_ffff,
            ),
            (
                1,
                false,
                309,
                ScientificFloatWidth::Float,
                0x7ff0_0000_0000_0000,
            ),
            (1, true, 45, ScientificFloatWidth::Float32, 1),
            (7, true, 46, ScientificFloatWidth::Float32, 0),
            (8, true, 46, ScientificFloatWidth::Float32, 1),
            (
                11_754_943_508_222_875,
                true,
                54,
                ScientificFloatWidth::Float32,
                0x0080_0000,
            ),
            (
                3_402_823_466_385_288_598,
                false,
                20,
                ScientificFloatWidth::Float32,
                0x7f7f_ffff,
            ),
            (1, false, 39, ScientificFloatWidth::Float32, 0x7f80_0000),
        ] {
            assert_eq!(
                convert(mantissa, negative, exponent, width),
                expected,
                "{mantissa} * 10^{}{exponent} as {width:?}",
                if negative { "-" } else { "" }
            );
        }
    }

    #[test]
    fn binary_scaling_rounds_subnormal_ties_once_and_carries_into_normal() {
        for (bits, exponent, expected) in [
            (1.0_f64.to_bits(), -1075, 0),
            (1.0_f64.to_bits(), -1074, 1),
            (1.5_f64.to_bits(), -1074, 2),
            (0x3fff_ffff_ffff_ffff, -1023, 0x0010_0000_0000_0000),
            (1.0_f64.to_bits(), 1024, 0x7ff0_0000_0000_0000),
        ] {
            assert_eq!(scale_positive_bits(bits, exponent, 52, 11), expected);
        }
        for (bits, exponent, expected) in [
            (1.0_f32.to_bits(), -150, 0),
            (1.0_f32.to_bits(), -149, 1),
            (1.5_f32.to_bits(), -149, 2),
            (0x3fff_ffff, -127, 0x0080_0000),
            (1.0_f32.to_bits(), 128, 0x7f80_0000),
        ] {
            assert_eq!(
                scale_positive_bits(u64::from(bits), exponent, 23, 8),
                expected
            );
        }
    }

    #[test]
    fn scientific_conversion_refuses_growth_before_work_and_recovers() {
        assert_eq!(
            scientific_float_bits(&[], true, &[], ScientificFloatWidth::Float, 0),
            Ok(0)
        );
        assert_eq!(
            scientific_float_bits(&[0], true, &[0, 1], ScientificFloatWidth::Float32, 2),
            Ok(0)
        );
        assert!(matches!(
            scientific_float_bits(&[1, 1], false, &[], ScientificFloatWidth::Float, 1),
            Err(ScientificFloatError::LimbLimit {
                operation: "mantissa input",
                ..
            })
        ));
        assert_eq!(
            scientific_float_bits(&[1], false, &[0, 1], ScientificFloatWidth::Float, 2),
            Err(ScientificFloatError::ExponentTooLarge)
        );
        assert!(matches!(
            scientific_float_bits(
                &[1],
                false,
                &[u32::MAX as u64],
                ScientificFloatWidth::Float,
                8
            ),
            Err(ScientificFloatError::LimbLimit {
                operation: "power of five",
                ..
            })
        ));
        assert!(matches!(
            scientific_float_bits(&[1, 0, 1], true, &[64], ScientificFloatWidth::Float, 5),
            Err(ScientificFloatError::LimbLimit {
                operation: "mantissa shift",
                ..
            })
        ));
        assert_eq!(
            convert(15, true, 1, ScientificFloatWidth::Float),
            1.5_f64.to_bits()
        );
    }
}
