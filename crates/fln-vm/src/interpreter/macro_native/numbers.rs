//! Numeric literal constructors and inspection, using the same pure grammar as
//! source elaboration. Arbitrary precision never passes through a host index.

use super::super::{ensure_nat_bits, finish_nat_result, with_nat_view};
use super::{
    IntrinsicFailure, Name, Obj, expansion_layout, inject_name, limit, literals, source_info,
};
use fln_bignum::nat::BigNat;
use fln_bignum::nat::literal::{NatLiteral, parse_nat_literal};

// Decimal conversion performs repeated limb arithmetic. A byte ceiling alone
// would admit quadratic work on multi-megabyte tokens. Bound an upper estimate
// of limb operations before constructing a magnitude or formatting one.
const MAX_LITERAL_ARITHMETIC_WORK: u64 = 8_000_000;
const MAX_LITERAL_BYTES: u64 = 16 * 1024 * 1024;

fn num_kind() -> Name {
    Name::str(Name::anonymous(), "num")
}

pub(super) fn mk_num_lit(text: &Obj, info: &Obj) -> Result<Obj, IntrinsicFailure> {
    // `mkNumLit` deliberately retains arbitrary spellings, including ones that
    // `isNatLit?` rejects. Validation belongs to the inspector, not this API.
    literals::mk_lit(&inject_name(&num_kind()), text, info)
}

pub(super) fn mk_nat_lit(
    value: &Obj,
    info: &Obj,
    max_nat_magnitude_bytes: u64,
) -> Result<Obj, IntrinsicFailure> {
    source_info(info)?;
    let text = decimal_text(value, "Lean.Syntax.mkNatLit", max_nat_magnitude_bytes)?;
    mk_num_lit(&Obj::mk_string(&text), info)
}

pub(super) fn nat_repr_fast(
    value: &Obj,
    max_nat_magnitude_bytes: u64,
) -> Result<Obj, IntrinsicFailure> {
    Ok(Obj::mk_string(&decimal_text(
        value,
        "Nat.reprFast",
        max_nat_magnitude_bytes,
    )?))
}

fn decimal_text(
    value: &Obj,
    operation: &'static str,
    max_nat_magnitude_bytes: u64,
) -> Result<String, IntrinsicFailure> {
    with_nat_view(value, operation, 0, |value| {
        let bits = u128::from(value.bit_length());
        ensure_nat_bits(max_nat_magnitude_bytes, bits)?;
        // log10(2) < 30103/100000. This includes the zero spelling and bounds
        // both the output and every 19-digit division pass in `to_decimal`.
        let digits = bits.saturating_mul(30_103) / 100_000 + 1;
        limit_u128("numeric formatting bytes", MAX_LITERAL_BYTES, digits)?;
        let limbs = bits.div_ceil(64);
        let chunks = digits.div_ceil(19);
        limit_u128(
            "numeric literal arithmetic work",
            MAX_LITERAL_ARITHMETIC_WORK,
            limbs.saturating_mul(chunks),
        )?;
        Ok::<_, IntrinsicFailure>(value.to_owned().to_decimal())
    })?
}

pub(super) fn is_nat_lit(
    value: &Obj,
    max_nat_magnitude_bytes: u64,
) -> Result<Obj, IntrinsicFailure> {
    Ok(decoded_value(value, max_nat_magnitude_bytes)?.map_or_else(
        || Obj::mk_nat(expansion_layout::OPTION_NONE_TAG),
        |value| Obj::mk_ctor(expansion_layout::OPTION_SOME.tag, vec![value], &[]),
    ))
}

pub(super) fn get_nat(value: &Obj, max_nat_magnitude_bytes: u64) -> Result<Obj, IntrinsicFailure> {
    Ok(decoded_value(value, max_nat_magnitude_bytes)?.unwrap_or_else(|| Obj::mk_nat(0)))
}

fn decoded_value(
    value: &Obj,
    max_nat_magnitude_bytes: u64,
) -> Result<Option<Obj>, IntrinsicFailure> {
    let Some(text) = literals::literal_value(&num_kind(), value)? else {
        return Ok(None);
    };
    let Some(literal) = parse_nat_literal(literals::literal_text(&text)?) else {
        return Ok(None);
    };
    let value = if let Some(value) = literal.to_u64() {
        // Preserve the exact tagged-scalar and one-limb boundaries even with a
        // zero-byte magnitude allowance. No decimal logarithm estimate here.
        ensure_nat_bits(
            max_nat_magnitude_bytes,
            u128::from(64 - value.leading_zeros()),
        )?;
        BigNat::from_u64(value)
    } else {
        let bits = magnitude_bound(&literal);
        ensure_nat_bits(max_nat_magnitude_bytes, bits)?;
        let digits = literal.significant_digits() as u128;
        let limbs = bits.div_ceil(64);
        let work = if literal.radix() == 10 {
            // Each chunk multiplies and adds at most `limbs` words. Charging
            // every chunk at the final width is a conservative upper bound.
            digits.div_ceil(19).saturating_mul(limbs).saturating_mul(2)
        } else {
            // Binary, octal and hexadecimal construction packs bits directly.
            digits.saturating_add(limbs)
        };
        limit_u128(
            "numeric literal arithmetic work",
            MAX_LITERAL_ARITHMETIC_WORK,
            work,
        )?;
        literal.to_nat()
    };
    // The shared runtime constructor chooses tagged Nat or positive Mpz from
    // the actual value and checks the caller's unchanged magnitude allowance.
    Ok(Some(
        finish_nat_result(value, max_nat_magnitude_bytes)?.into_object(),
    ))
}

fn magnitude_bound(literal: &NatLiteral<'_>) -> u128 {
    let digits = literal.significant_digits() as u128;
    if digits == 0 {
        return 0;
    }
    let shift = match literal.radix() {
        2 => 1,
        8 => 3,
        16 => 4,
        // log2(10) < 3322/1000. A conservative allocation estimate, not a
        // truncation or approximation of the returned natural number.
        10 => return digits.saturating_mul(3322).div_ceil(1000),
        _ => unreachable!("validated numeric literal radix"),
    };
    (digits - 1).saturating_mul(shift)
        + u128::from(u32::BITS - literal.first_digit().leading_zeros())
}

fn limit_u128(
    resource: &'static str,
    allowed: u64,
    observed: u128,
) -> Result<(), IntrinsicFailure> {
    limit(
        resource,
        allowed,
        u64::try_from(observed).unwrap_or(u64::MAX),
    )
}
