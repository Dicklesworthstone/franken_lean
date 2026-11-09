//! The pinned `Lean.Syntax.decodeNatLitVal?` decoder for generated syntax.
//!
//! This is distinct from source lexing: macros may construct an empty radix
//! prefix or trailing separators, and the public decoder accepts them. A
//! leading decimal zero still requires a second decimal digit before any
//! separator (`0_1` is invalid, while `00_1` is one).

use super::{BigNat, DECIMAL_CHUNK_BASE, DECIMAL_CHUNK_DIGITS};

/// A validated, allocation-free view of a numeric syntax atom.
///
/// Callers that impose resource budgets can inspect the significant size and
/// try the machine-sized value before allocating an arbitrary-precision result.
#[derive(Clone, Copy, Debug)]
pub struct NatLiteral<'a> {
    digits: &'a [u8],
    radix: u32,
    significant_digits: usize,
    first_digit: u32,
}

impl NatLiteral<'_> {
    /// The selected radix: two, eight, ten, or sixteen.
    pub fn radix(self) -> u32 {
        self.radix
    }

    /// Digits from the first nonzero digit onward, excluding separators.
    pub fn significant_digits(self) -> usize {
        self.significant_digits
    }

    /// The first nonzero digit, or zero when the complete value is zero.
    pub fn first_digit(self) -> u32 {
        self.first_digit
    }

    /// Decode a machine-sized value without allocating a magnitude buffer.
    pub fn to_u64(self) -> Option<u64> {
        let mut value = 0u64;
        for &byte in self.digits {
            if byte != b'_' {
                value = value
                    .checked_mul(u64::from(self.radix))?
                    .checked_add(u64::from(digit(byte)?))?;
            }
        }
        Some(value)
    }

    /// Decode the validated value after the caller's resource preflight.
    ///
    /// Decimal arithmetic processes nineteen digits per multiplication. Other
    /// radices pack directly into limbs, avoiding a whole-number multiplication
    /// for every input digit.
    pub fn to_nat(self) -> BigNat {
        if self.significant_digits == 0 {
            return BigNat::zero();
        }
        if self.radix == 10 {
            let mut value = BigNat::zero();
            let mut chunk = 0u64;
            let mut count = 0usize;
            for &byte in self.digits {
                if byte == b'_' {
                    continue;
                }
                chunk = chunk * 10 + u64::from(byte - b'0');
                count += 1;
                if count == DECIMAL_CHUNK_DIGITS {
                    value = value.mul_small(DECIMAL_CHUNK_BASE as u64).add_small(chunk);
                    chunk = 0;
                    count = 0;
                }
            }
            if count != 0 {
                value = value.mul_small(10u64.pow(count as u32)).add_small(chunk);
            }
            value
        } else {
            let width = match self.radix {
                2 => 1,
                8 => 3,
                16 => 4,
                _ => unreachable!("validated numeral radix"),
            };
            let bits = (self.significant_digits - 1) * width
                + (u32::BITS - self.first_digit.leading_zeros()) as usize;
            let mut limbs = vec![0u64; bits.div_ceil(64)];
            let mut offset = 0usize;
            for &byte in self.digits.iter().rev() {
                if byte == b'_' {
                    continue;
                }
                let value = u64::from(digit(byte).expect("validated numeral digit"));
                let index = offset / 64;
                let shift = offset % 64;
                limbs[index] |= value << shift;
                if shift + width > 64 && index + 1 < limbs.len() {
                    limbs[index + 1] |= value >> (64 - shift);
                }
                offset += width;
            }
            BigNat::from_limbs_le(limbs)
        }
    }
}

fn digit(byte: u8) -> Option<u32> {
    match byte {
        b'0'..=b'9' => Some(u32::from(byte - b'0')),
        b'a'..=b'f' => Some(u32::from(byte - b'a') + 10),
        b'A'..=b'F' => Some(u32::from(byte - b'A') + 10),
        _ => None,
    }
}

/// Validate exactly the pin's public numeric literal spelling without allocating.
///
/// `Init/Meta/Defs.lean::decodeNatLitVal?` selects a radix before its auxiliary
/// loop skips underscores. In particular, it accepts `0x`, `0x__`, and `1_`,
/// but rejects `0_`, `_1`, signs, whitespace, and non-ASCII digits.
pub fn parse_nat_literal(spelling: &str) -> Option<NatLiteral<'_>> {
    let bytes = spelling.as_bytes();
    let (radix, digits) = match bytes {
        [b'0', b'b' | b'B', rest @ ..] => (2, rest),
        [b'0', b'o' | b'O', rest @ ..] => (8, rest),
        [b'0', b'x' | b'X', rest @ ..] => (16, rest),
        [b'0'] | [b'0', b'0'..=b'9', ..] | [b'1'..=b'9', ..] => (10, bytes),
        _ => return None,
    };
    let mut start = digits.len();
    let mut significant_digits = 0;
    let mut first_digit = 0;
    for (index, &byte) in digits.iter().enumerate() {
        if byte == b'_' {
            continue;
        }
        let value = digit(byte)?;
        if value >= radix {
            return None;
        }
        if significant_digits != 0 || value != 0 {
            if significant_digits == 0 {
                start = index;
                first_digit = value;
            }
            significant_digits += 1;
        }
    }
    Some(NatLiteral {
        digits: &digits[start..],
        radix,
        significant_digits,
        first_digit,
    })
}

/// Decode a numeric syntax atom using the pin's public decoder semantics.
pub fn decode_nat_literal(spelling: &str) -> Option<BigNat> {
    Some(parse_nat_literal(spelling)?.to_nat())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn public_decoder_keeps_the_pins_prefix_and_separator_boundaries() {
        for (text, expected) in [
            ("0", "0"),
            ("00_1", "1"),
            ("1_", "1"),
            ("1__2", "12"),
            ("001_", "1"),
            ("0x", "0"),
            ("0X", "0"),
            ("0b", "0"),
            ("0B__", "0"),
            ("0o", "0"),
            ("0O_", "0"),
            ("0x__", "0"),
            ("0x_f_", "15"),
            ("0Xff", "255"),
            ("0b_101_", "5"),
            ("0o_77_", "63"),
            ("18446744073709551615", "18446744073709551615"),
            ("18446744073709551616", "18446744073709551616"),
            ("0x1_0000_0000_0000_0000_", "18446744073709551616"),
            ("0o2000000000000000000000", "18446744073709551616"),
        ] {
            let value = parse_nat_literal(text).unwrap_or_else(|| panic!("{text}"));
            let expected = BigNat::from_decimal(expected).unwrap();
            assert_eq!(value.to_nat(), expected, "{text}");
            assert_eq!(value.to_u64(), expected.to_u64(), "{text}");
        }
        for text in [
            "", "_", "_1", "0_", "0_1", "0__1", "-1", "+1", " 1", "1 ", "1.0", "1e2", "0b2", "0o8",
            "0xg", "0y1", "٠1", "１２", "1λ", "0x\0",
        ] {
            assert!(parse_nat_literal(text).is_none(), "{text:?}");
        }
    }

    #[test]
    fn descriptor_counts_only_significant_digits_before_allocation() {
        for (text, radix, count, first, value) in [
            ("0", 10, 0, 0, 0),
            ("000__", 10, 0, 0, 0),
            ("0x__", 16, 0, 0, 0),
            ("000_0042_", 10, 2, 4, 42),
            ("0x__000f_f_", 16, 2, 15, 255),
            ("0o0000100__", 8, 3, 1, 64),
            ("0b000_101_", 2, 3, 1, 5),
        ] {
            let literal = parse_nat_literal(text).unwrap();
            assert_eq!(literal.radix(), radix);
            assert_eq!(literal.significant_digits(), count);
            assert_eq!(literal.first_digit(), first);
            assert_eq!(literal.to_u64(), Some(value));
        }
    }

    #[test]
    fn every_radix_preserves_values_across_many_limb_boundaries() {
        let expected = BigNat::from_u64(1).shl(1024);
        for text in [
            format!("0b1{}", "0".repeat(1024)),
            format!("0o2{}", "0".repeat(341)),
            format!("0x1{}", "0".repeat(256)),
            expected.to_decimal(),
        ] {
            let literal = parse_nat_literal(&text).unwrap();
            assert_eq!(literal.to_nat(), expected);
            assert_eq!(literal.to_u64(), None);
        }
        for bits in 1..=195 {
            let expected = BigNat::from_u64(1).shl(bits).sub(&BigNat::from_u64(1));
            let grouped = |width: u64, prefix: &str, digit: char| {
                let remainder = bits % width;
                let first = if remainder == 0 {
                    String::new()
                } else {
                    format!("{:x}", (1u64 << remainder) - 1)
                };
                format!(
                    "{prefix}{first}{}",
                    digit.to_string().repeat((bits / width) as usize)
                )
            };
            for text in [
                format!("0b{}", "1".repeat(bits as usize)),
                grouped(3, "0o", '7'),
                grouped(4, "0x", 'f'),
                expected.to_decimal(),
            ] {
                assert_eq!(decode_nat_literal(&text), Some(expected.clone()), "{text}");
            }
        }
    }
}
