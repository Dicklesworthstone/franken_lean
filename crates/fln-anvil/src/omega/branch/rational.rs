//! Exact rational reconstruction of an integer-valid linear relaxation.
//! This arithmetic is search data only; no rational value enters a certificate.

use super::super::*;
use std::cmp::Ordering;

struct Rational {
    numerator: BigInt,
    denominator: BigInt,
}

impl Rational {
    fn new(numerator: BigInt, denominator: BigInt, meter: &mut Meter<'_>) -> Attempt<Self> {
        meter.integer(&numerator)?;
        meter.integer(&denominator)?;
        if denominator.is_zero() || denominator.is_negative() {
            return Err(OmegaInconclusive::IntegerSearchRequired);
        }
        let (numerator, denominator) = if numerator.is_zero() {
            (BigInt::zero(), BigInt::from_i64(1))
        } else {
            let gcd = meter.gcd(numerator.magnitude(), denominator.magnitude())?;
            if gcd == BigNat::from_u64(1) {
                (numerator, denominator)
            } else {
                let gcd = BigInt::from_sign_magnitude(false, gcd);
                (meter.div(&numerator, &gcd)?, meter.div(&denominator, &gcd)?)
            }
        };
        meter.storage(
            numerator
                .magnitude()
                .limbs_le()
                .len()
                .saturating_add(denominator.magnitude().limbs_le().len())
                .saturating_mul(8)
                .saturating_add(std::mem::size_of::<Self>()),
        )?;
        Ok(Self {
            numerator,
            denominator,
        })
    }

    fn integer(value: &BigInt, meter: &mut Meter<'_>) -> Attempt<Self> {
        Self::new(meter.copy_int(value)?, BigInt::from_i64(1), meter)
    }

    fn add_sub(&self, other: &Self, subtract: bool, meter: &mut Meter<'_>) -> Attempt<Self> {
        let common = meter.gcd(self.denominator.magnitude(), other.denominator.magnitude())?;
        let common = BigInt::from_sign_magnitude(false, common);
        let left_scale = meter.div(&other.denominator, &common)?;
        let right_scale = meter.div(&self.denominator, &common)?;
        let left = meter.mul(&self.numerator, &left_scale)?;
        let right = meter.mul(&other.numerator, &right_scale)?;
        let numerator = if subtract {
            meter.sub(&left, &right)?
        } else {
            meter.add(&left, &right)?
        };
        let denominator = meter.mul(&self.denominator, &left_scale)?;
        Self::new(numerator, denominator, meter)
    }

    fn mul_integer(&self, value: &BigInt, meter: &mut Meter<'_>) -> Attempt<Self> {
        // Cancel before multiplication so an exactly small product does not
        // acquire an unnecessarily large numerator or denominator.
        let common = meter.gcd(value.magnitude(), self.denominator.magnitude())?;
        let common = BigInt::from_sign_magnitude(false, common);
        let value = meter.div(value, &common)?;
        let denominator = meter.div(&self.denominator, &common)?;
        let numerator = meter.mul(&self.numerator, &value)?;
        Self::new(numerator, denominator, meter)
    }

    fn div_integer(&self, value: &BigInt, meter: &mut Meter<'_>) -> Attempt<Self> {
        if value.is_zero() {
            return Err(OmegaInconclusive::IntegerSearchRequired);
        }
        let common = meter.gcd(self.numerator.magnitude(), value.magnitude())?;
        let common = BigInt::from_sign_magnitude(false, common);
        let numerator = meter.div(&self.numerator, &common)?;
        let numerator = if value.is_negative() {
            meter.sub(&BigInt::zero(), &numerator)?
        } else {
            numerator
        };
        let magnitude = BigInt::from_sign_magnitude(false, meter.copy_nat(value.magnitude())?);
        let factor = meter.div(&magnitude, &common)?;
        let denominator = meter.mul(&self.denominator, &factor)?;
        Self::new(numerator, denominator, meter)
    }

    fn compare(&self, other: &Self, meter: &mut Meter<'_>) -> Attempt<Ordering> {
        let left = meter.mul(&self.numerator, &other.denominator)?;
        let right = meter.mul(&other.numerator, &self.denominator)?;
        meter.tick(
            left.magnitude()
                .limbs_le()
                .len()
                .max(right.magnitude().limbs_le().len()) as u64
                + 1,
        )?;
        Ok(left.cmp(&right))
    }
}

pub(super) enum Point {
    Integer(Vec<BigInt>),
    Fractional { variable: usize, cut: BigInt },
}

/// The recorded elimination bounds describe a rational feasible set even
/// though gcd cuts tightened it for integer solutions. Reconstruct one exact
/// point, verify it against the original rows, and select a fractional variable
/// by original ordinal. All traversals are iterative and all numbers metered.
pub(super) fn reconstruct(solver: &mut Solver<'_, '_>) -> Attempt<Point> {
    let mut values = Vec::new();
    solver.meter.reserve(&mut values, solver.dimensions)?;
    for _ in 0..solver.dimensions {
        values.push(Rational::integer(&BigInt::zero(), solver.meter)?);
    }
    for elimination in solver.eliminations.iter().rev() {
        let (mut lower, mut upper): (Option<Rational>, Option<Rational>) = (None, None);
        for &id in &elimination.bounds {
            solver.meter.tick(1)?;
            let row = &solver.rows[id].constraint;
            let mut remaining = Rational::integer(&row.bound, solver.meter)?;
            for (variable, coefficient) in row.coeffs.iter().enumerate() {
                solver.meter.tick(1)?;
                if variable == elimination.variable || coefficient.is_zero() {
                    continue;
                }
                let term = values[variable].mul_integer(coefficient, solver.meter)?;
                remaining = remaining.add_sub(&term, true, solver.meter)?;
            }
            let coefficient = &row.coeffs[elimination.variable];
            let bound = remaining.div_integer(coefficient, solver.meter)?;
            let slot = if coefficient.is_negative() {
                &mut lower
            } else {
                &mut upper
            };
            let stronger = if let Some(previous) = slot {
                let comparison = bound.compare(previous, solver.meter)?;
                if coefficient.is_negative() {
                    comparison.is_gt()
                } else {
                    comparison.is_lt()
                }
            } else {
                true
            };
            if stronger {
                *slot = Some(bound);
            }
        }
        if let (Some(lower), Some(upper)) = (&lower, &upper)
            && lower.compare(upper, solver.meter)?.is_gt()
        {
            return Err(OmegaInconclusive::IntegerSearchRequired);
        }
        values[elimination.variable] = match (lower, upper) {
            (Some(lower), _) if lower.numerator > BigInt::zero() => lower,
            (_, Some(upper)) if upper.numerator.is_negative() => upper,
            _ => Rational::integer(&BigInt::zero(), solver.meter)?,
        };
    }
    // Do not trust reconstruction to have respected every discarded or
    // dominated inequality. A candidate split is chosen only after this check.
    for row in solver.inputs {
        let mut total = Rational::integer(&BigInt::zero(), solver.meter)?;
        for (coefficient, value) in row.coeffs.iter().zip(&values) {
            solver.meter.tick(1)?;
            if coefficient.is_zero() {
                continue;
            }
            let term = value.mul_integer(coefficient, solver.meter)?;
            total = total.add_sub(&term, false, solver.meter)?;
        }
        let bound = Rational::integer(&row.bound, solver.meter)?;
        if total.compare(&bound, solver.meter)?.is_gt() {
            return Err(OmegaInconclusive::IntegerSearchRequired);
        }
    }
    for (variable, value) in values.iter().enumerate() {
        solver.meter.tick(1)?;
        if value.denominator != BigInt::from_i64(1) {
            return Ok(Point::Fractional {
                variable,
                cut: solver.meter.div(&value.numerator, &value.denominator)?,
            });
        }
    }
    let mut witness = Vec::new();
    solver.meter.reserve(&mut witness, values.len())?;
    for value in values {
        witness.push(value.numerator);
    }
    if !satisfies(solver.inputs, &witness, solver.meter)? {
        return Err(OmegaInconclusive::IntegerSearchRequired);
    }
    Ok(Point::Integer(witness))
}
