//! Native integer linear arithmetic with replayable contradiction certificates.
//!
//! Fourier–Motzkin elimination combines upper bounds with positive integer
//! multipliers. Gcd division with floor rounding tightens every derived bound.
//! Selection prefers one-sided elimination, then a side with unit coefficients,
//! then fewer generated pairs, with original variable ordinals breaking ties.
//!
//! The explicit integer-search entry point extends failed reconstruction with
//! exact rational reconstruction and bounded integer case splitting. Each
//! contradiction leaf retains its linear certificate and exact assumptions.
//! The default entry points preserve the pinned elimination coverage; extended
//! search is a frontier capability, not full Presburger coverage. Every
//! `Sat` witness satisfies the original input; every `Unsat` remains untrusted
//! data for the elaborator's ordinary kernel-checked proof replay. No external
//! solver, upstream execution, global state or machine-width numeric bound is used.

use fln_bignum::{int::BigInt, nat::BigNat};
pub use fln_elab::arithmetic::{
    LinearConstraint, OMEGA_BRANCH_CERTIFICATE_VERSION, OMEGA_CERTIFICATE_VERSION,
    OmegaBranchCertificate, OmegaBranchNode, OmegaCertificate, OmegaInconclusive, OmegaLimits,
    OmegaOutcome, OmegaResource, OmegaStep,
};

mod branch;
pub use branch::{check_branch_certificate, decode_branch_certificate, encode_branch_certificate};
mod certificate;
pub use certificate::{
    CertificateError, check_certificate, decode_certificate, encode_certificate,
};

type Attempt<T> = Result<T, OmegaInconclusive>;

struct Meter<'a> {
    limits: OmegaLimits,
    used: u64,
    // Conservatively charge retained candidate/certificate storage, including
    // discarded candidates, so allocation churn cannot escape the storage cap.
    bytes: usize,
    cancelled: &'a mut dyn FnMut() -> bool,
}

impl Meter<'_> {
    fn limit(resource: OmegaResource, limit: usize, observed: usize) -> OmegaInconclusive {
        OmegaInconclusive::ResourceLimit {
            resource,
            limit: u64::try_from(limit).unwrap_or(u64::MAX),
            observed: u64::try_from(observed).unwrap_or(u64::MAX),
        }
    }

    fn tick(&mut self, amount: u64) -> Attempt<()> {
        if (self.cancelled)() {
            return Err(OmegaInconclusive::Cancelled);
        }
        let next = self.used.saturating_add(amount);
        if next > self.limits.max_steps || amount > u64::MAX - self.used {
            return Err(OmegaInconclusive::ResourceLimit {
                resource: OmegaResource::Steps,
                limit: self.limits.max_steps,
                observed: next,
            });
        }
        self.used = next;
        Ok(())
    }

    fn width(&mut self, limbs: usize) -> Attempt<()> {
        self.tick(1)?;
        if limbs > self.limits.max_coefficient_limbs {
            return Err(Self::limit(
                OmegaResource::CoefficientLimbs,
                self.limits.max_coefficient_limbs,
                limbs,
            ));
        }
        Ok(())
    }

    fn integer(&mut self, n: &BigInt) -> Attempt<()> {
        self.width(n.magnitude().limbs_le().len())
    }

    fn storage(&mut self, bytes: usize) -> Attempt<()> {
        self.tick(1)?;
        let next = self.bytes.saturating_add(bytes);
        if next > self.limits.max_certificate_bytes || bytes > usize::MAX - self.bytes {
            return Err(Self::limit(
                OmegaResource::CertificateBytes,
                self.limits.max_certificate_bytes,
                next,
            ));
        }
        self.bytes = next;
        Ok(())
    }

    fn reserve<T>(&mut self, values: &mut Vec<T>, additional: usize) -> Attempt<()> {
        self.storage(additional.saturating_mul(std::mem::size_of::<T>()))?;
        values.try_reserve(additional).map_err(|_| {
            Self::limit(
                OmegaResource::Allocation,
                values.capacity(),
                values.len().saturating_add(additional),
            )
        })
    }

    fn copy_nat(&mut self, n: &BigNat) -> Attempt<BigNat> {
        let limbs = n.limbs_le().len();
        self.width(limbs)?;
        self.tick(limbs as u64)?;
        self.storage(limbs.saturating_mul(8))?;
        Ok(n.clone())
    }

    fn copy_int(&mut self, n: &BigInt) -> Attempt<BigInt> {
        let limbs = n.magnitude().limbs_le().len();
        self.width(limbs)?;
        self.tick(limbs as u64)?;
        self.storage(limbs.saturating_mul(8))?;
        Ok(n.clone())
    }

    fn add(&mut self, a: &BigInt, b: &BigInt) -> Attempt<BigInt> {
        let width = a
            .magnitude()
            .limbs_le()
            .len()
            .max(b.magnitude().limbs_le().len());
        self.width(width)?;
        self.tick(width as u64 + 1)?;
        let result = a.add(b);
        self.integer(&result)?;
        Ok(result)
    }

    fn sub(&mut self, a: &BigInt, b: &BigInt) -> Attempt<BigInt> {
        let width = a
            .magnitude()
            .limbs_le()
            .len()
            .max(b.magnitude().limbs_le().len());
        self.width(width)?;
        self.tick(width as u64 + 1)?;
        let result = a.sub(b);
        self.integer(&result)?;
        Ok(result)
    }

    fn mul(&mut self, a: &BigInt, b: &BigInt) -> Attempt<BigInt> {
        if a.is_zero() || b.is_zero() {
            self.tick(1)?;
            return Ok(BigInt::zero());
        }
        let aw = a.magnitude().limbs_le().len();
        let bw = b.magnitude().limbs_le().len();
        // At most one extra limb is allocated temporarily; the normalized
        // result must meet the configured width before it can be retained.
        self.width(aw.saturating_add(bw).saturating_sub(1))?;
        self.tick((aw as u64).saturating_mul(bw as u64).saturating_add(1))?;
        let result = a.mul(b);
        self.integer(&result)?;
        Ok(result)
    }

    fn div(&mut self, a: &BigInt, b: &BigInt) -> Attempt<BigInt> {
        let aw = a.magnitude().limbs_le().len();
        let bw = b.magnitude().limbs_le().len();
        self.width(aw.max(bw))?;
        self.tick(
            (aw as u64 + 1)
                .saturating_mul(bw as u64 + 1)
                .saturating_mul(64),
        )?;
        Ok(a.ediv(b))
    }

    fn gcd(&mut self, a: &BigNat, b: &BigNat) -> Attempt<BigNat> {
        let width = a.limbs_le().len().max(b.limbs_le().len());
        self.width(width)?;
        self.tick((width as u64 + 1).saturating_pow(2).saturating_mul(128))?;
        Ok(a.gcd(b))
    }

    fn dimensions(&mut self, inputs: &[LinearConstraint]) -> Attempt<usize> {
        self.tick(1)?;
        let row_limit = self.limits.max_rows.min(u32::MAX as usize);
        if inputs.len() > row_limit {
            return Err(Self::limit(OmegaResource::Rows, row_limit, inputs.len()));
        }
        let mut dimensions = 0;
        for row in inputs {
            self.tick(1)?;
            dimensions = dimensions.max(row.coeffs.len());
            let variable_limit = self.limits.max_variables.min(u32::MAX as usize);
            if dimensions > variable_limit {
                return Err(Self::limit(
                    OmegaResource::Variables,
                    variable_limit,
                    dimensions,
                ));
            }
            self.integer(&row.bound)?;
            for coefficient in &row.coeffs {
                self.integer(coefficient)?;
            }
        }
        Ok(dimensions)
    }

    fn copy_row(&mut self, row: &LinearConstraint, dimensions: usize) -> Attempt<LinearConstraint> {
        let mut coeffs = Vec::new();
        self.reserve(&mut coeffs, dimensions)?;
        for coefficient in &row.coeffs {
            coeffs.push(self.copy_int(coefficient)?);
        }
        while coeffs.len() < dimensions {
            self.tick(1)?;
            coeffs.push(BigInt::zero());
        }
        Ok(LinearConstraint {
            coeffs,
            bound: self.copy_int(&row.bound)?,
        })
    }
}

struct Row {
    constraint: LinearConstraint,
    justification: OmegaStep,
}

struct Elimination {
    variable: usize,
    bounds: Vec<usize>,
}

struct Solver<'a, 'b> {
    meter: &'a mut Meter<'b>,
    inputs: &'a [LinearConstraint],
    dimensions: usize,
    rows: Vec<Row>,
    active: Vec<usize>,
    eliminations: Vec<Elimination>,
}

impl Solver<'_, '_> {
    fn record(&mut self, constraint: LinearConstraint, justification: OmegaStep) -> Attempt<usize> {
        let id = self.rows.len();
        if id >= self.meter.limits.max_rows || id >= u32::MAX as usize {
            return Err(Meter::limit(
                OmegaResource::Rows,
                self.meter.limits.max_rows,
                id.saturating_add(1),
            ));
        }
        for n in constraint
            .coeffs
            .iter()
            .chain(std::iter::once(&constraint.bound))
        {
            self.meter
                .storage(n.magnitude().limbs_le().len().saturating_mul(8))?;
        }
        self.meter.reserve(&mut self.rows, 1)?;
        self.rows.push(Row {
            constraint,
            justification,
        });
        Ok(id)
    }

    fn normalize(&mut self, id: usize) -> Attempt<usize> {
        let row = &self.rows[id].constraint;
        let mut divisor = BigNat::zero();
        for coefficient in &row.coeffs {
            self.meter.tick(1)?;
            if coefficient.is_zero() {
                continue;
            }
            divisor = if divisor.is_zero() {
                coefficient.magnitude().clone()
            } else {
                self.meter.gcd(&divisor, coefficient.magnitude())?
            };
            if divisor == BigNat::from_u64(1) {
                return Ok(id);
            }
        }
        if divisor.is_zero() {
            return Ok(id);
        }
        let divisor = BigInt::from_sign_magnitude(false, divisor);
        let mut coeffs = Vec::new();
        self.meter.reserve(&mut coeffs, self.dimensions)?;
        for coefficient in &row.coeffs {
            coeffs.push(self.meter.div(coefficient, &divisor)?);
        }
        let bound = self.meter.div(&row.bound, &divisor)?;
        self.record(
            LinearConstraint { coeffs, bound },
            OmegaStep::DivideGcd { source: id as u32 },
        )
    }

    fn insert(&mut self, id: usize, active: &mut Vec<usize>) -> Attempt<Option<usize>> {
        let row = &self.rows[id].constraint;
        self.meter.tick(self.dimensions as u64 + 1)?;
        if row.coeffs.iter().all(BigInt::is_zero) {
            return Ok(row.bound.is_negative().then_some(id));
        }
        for old in active.iter_mut() {
            // Ordered dominance elimination: a weaker bound on the exact same
            // coefficient vector contributes no information.
            let earlier = &self.rows[*old].constraint;
            let mut same_coefficients = true;
            for (a, b) in earlier.coeffs.iter().zip(&row.coeffs) {
                self.meter.tick(
                    a.magnitude()
                        .limbs_le()
                        .len()
                        .max(b.magnitude().limbs_le().len()) as u64
                        + 1,
                )?;
                if a != b {
                    same_coefficients = false;
                    break;
                }
            }
            if same_coefficients {
                self.meter.tick(
                    row.bound
                        .magnitude()
                        .limbs_le()
                        .len()
                        .max(earlier.bound.magnitude().limbs_le().len()) as u64
                        + 1,
                )?;
                if row.bound < earlier.bound {
                    *old = id;
                }
                return Ok(None);
            }
        }
        self.meter.reserve(active, 1)?;
        active.push(id);
        Ok(None)
    }

    fn select(&mut self) -> Attempt<Option<usize>> {
        let mut selected = None;
        for variable in 0..self.dimensions {
            let (mut positive, mut negative) = (0usize, 0usize);
            let (mut positive_unit, mut negative_unit) = (true, true);
            for &id in &self.active {
                self.meter.tick(1)?;
                let coefficient = &self.rows[id].constraint.coeffs[variable];
                if coefficient.is_zero() {
                    continue;
                }
                let unit = coefficient.magnitude() == &BigNat::from_u64(1);
                if coefficient.is_negative() {
                    negative += 1;
                    negative_unit &= unit;
                } else {
                    positive += 1;
                    positive_unit &= unit;
                }
            }
            if positive == 0 && negative == 0 {
                continue;
            }
            let pairs = positive.saturating_mul(negative);
            let score = (
                pairs != 0,
                !(positive_unit || negative_unit),
                pairs,
                variable,
            );
            if selected.as_ref().is_none_or(|(best, _)| score < *best) {
                selected = Some((score, variable));
            }
        }
        Ok(selected.map(|(_, variable)| variable))
    }

    fn combine(&mut self, left: usize, right: usize, variable: usize) -> Attempt<usize> {
        let a = &self.rows[left].constraint;
        let b = &self.rows[right].constraint;
        let common = self.meter.gcd(
            a.coeffs[variable].magnitude(),
            b.coeffs[variable].magnitude(),
        )?;
        let common = BigInt::from_sign_magnitude(false, common);
        let positive_a = BigInt::from_sign_magnitude(false, a.coeffs[variable].magnitude().clone());
        let positive_b = BigInt::from_sign_magnitude(false, b.coeffs[variable].magnitude().clone());
        let left_scale = self.meter.div(&positive_b, &common)?;
        let right_scale = self.meter.div(&positive_a, &common)?;
        let mut coeffs = Vec::new();
        self.meter.reserve(&mut coeffs, self.dimensions)?;
        for (x, y) in a.coeffs.iter().zip(&b.coeffs) {
            let x = self.meter.mul(x, &left_scale)?;
            let y = self.meter.mul(y, &right_scale)?;
            coeffs.push(self.meter.add(&x, &y)?);
        }
        let left_bound = self.meter.mul(&a.bound, &left_scale)?;
        let right_bound = self.meter.mul(&b.bound, &right_scale)?;
        let bound = self.meter.add(&left_bound, &right_bound)?;
        // The retained justification can be large even when cancellation
        // produces a tiny row, so charge its magnitudes before cloning them.
        let left_scale = self.meter.copy_nat(left_scale.magnitude())?;
        let right_scale = self.meter.copy_nat(right_scale.magnitude())?;
        self.record(
            LinearConstraint { coeffs, bound },
            OmegaStep::Combine {
                left: left as u32,
                right: right as u32,
                left_scale,
                right_scale,
            },
        )
    }

    fn eliminate(&mut self, variable: usize) -> Attempt<Option<usize>> {
        let (mut positive, mut negative, mut next) = (Vec::new(), Vec::new(), Vec::new());
        for &id in &self.active {
            self.meter.tick(1)?;
            let coefficient = &self.rows[id].constraint.coeffs[variable];
            let destination = if coefficient.is_zero() {
                &mut next
            } else if coefficient.is_negative() {
                &mut negative
            } else {
                &mut positive
            };
            self.meter.reserve(destination, 1)?;
            destination.push(id);
        }
        let mut bounds = Vec::new();
        self.meter
            .reserve(&mut bounds, positive.len().saturating_add(negative.len()))?;
        bounds.extend_from_slice(&positive);
        bounds.extend_from_slice(&negative);
        self.meter.reserve(&mut self.eliminations, 1)?;
        self.eliminations.push(Elimination { variable, bounds });
        for &left in &positive {
            for &right in &negative {
                self.meter.tick(1)?;
                let id = self.combine(left, right, variable)?;
                let id = self.normalize(id)?;
                if let Some(contradiction) = self.insert(id, &mut next)? {
                    return Ok(Some(contradiction));
                }
            }
        }
        self.active = next;
        Ok(None)
    }

    fn certificate(&mut self, conclusion: usize) -> Attempt<OmegaCertificate> {
        // Keep only contradiction ancestors; an iterative DAG walk never turns
        // a long elimination history into host recursion.
        let mut needed = Vec::new();
        self.meter.reserve(&mut needed, self.rows.len())?;
        needed.resize(self.rows.len(), false);
        needed[conclusion] = true;
        for id in (0..=conclusion).rev() {
            self.meter.tick(1)?;
            if !needed[id] {
                continue;
            }
            match self.rows[id].justification {
                OmegaStep::Input { .. } => {}
                OmegaStep::Combine { left, right, .. } => {
                    needed[left as usize] = true;
                    needed[right as usize] = true;
                }
                OmegaStep::DivideGcd { source } => needed[source as usize] = true,
            }
        }
        let mut ids = Vec::new();
        self.meter.reserve(&mut ids, self.rows.len())?;
        ids.resize(self.rows.len(), 0u32);
        let mut steps = Vec::new();
        for (id, keep) in needed.into_iter().enumerate() {
            self.meter.tick(1)?;
            if !keep {
                continue;
            }
            ids[id] = steps.len() as u32;
            let step = match &self.rows[id].justification {
                OmegaStep::Input { index } => OmegaStep::Input { index: *index },
                OmegaStep::Combine {
                    left,
                    right,
                    left_scale,
                    right_scale,
                } => OmegaStep::Combine {
                    left: ids[*left as usize],
                    right: ids[*right as usize],
                    left_scale: self.meter.copy_nat(left_scale)?,
                    right_scale: self.meter.copy_nat(right_scale)?,
                },
                OmegaStep::DivideGcd { source } => OmegaStep::DivideGcd {
                    source: ids[*source as usize],
                },
            };
            self.meter.reserve(&mut steps, 1)?;
            steps.push(step);
        }
        let mut inputs = Vec::new();
        self.meter.reserve(&mut inputs, self.inputs.len())?;
        for input in self.inputs {
            inputs.push(self.meter.copy_row(input, input.coeffs.len())?);
        }
        Ok(OmegaCertificate {
            version: OMEGA_CERTIFICATE_VERSION,
            inputs,
            steps,
            conclusion: ids[conclusion],
        })
    }

    fn witness(&mut self) -> Attempt<Vec<BigInt>> {
        let mut witness = Vec::new();
        self.meter.reserve(&mut witness, self.dimensions)?;
        witness.resize_with(self.dimensions, BigInt::zero);
        for elimination in self.eliminations.iter().rev() {
            let (mut lower, mut upper): (Option<BigInt>, Option<BigInt>) = (None, None);
            for &id in &elimination.bounds {
                let row = &self.rows[id].constraint;
                let mut remaining = self.meter.copy_int(&row.bound)?;
                for (variable, (coefficient, value)) in row.coeffs.iter().zip(&witness).enumerate()
                {
                    self.meter.tick(1)?;
                    if variable == elimination.variable || coefficient.is_zero() {
                        continue;
                    }
                    let term = self.meter.mul(coefficient, value)?;
                    remaining = self.meter.sub(&remaining, &term)?;
                }
                let coefficient = &row.coeffs[elimination.variable];
                // Euclidean division is floor for a positive divisor, ceiling
                // for a negative divisor: the exact integer bounds on a*x<=b.
                let value = self.meter.div(&remaining, coefficient)?;
                if coefficient.is_negative() {
                    if lower.as_ref().is_none_or(|old| value > *old) {
                        lower = Some(value);
                    }
                } else if upper.as_ref().is_none_or(|old| value < *old) {
                    upper = Some(value);
                }
            }
            if let (Some(lower), Some(upper)) = (&lower, &upper)
                && lower > upper
            {
                return Err(OmegaInconclusive::IntegerSearchRequired);
            }
            witness[elimination.variable] = match (lower, upper) {
                (Some(lower), _) if lower > BigInt::zero() => lower,
                (_, Some(upper)) if upper.is_negative() => upper,
                _ => BigInt::zero(),
            };
        }
        if !satisfies(self.inputs, &witness, self.meter)? {
            return Err(OmegaInconclusive::IntegerSearchRequired);
        }
        Ok(witness)
    }

    fn run(&mut self) -> Attempt<Result<OmegaCertificate, Vec<BigInt>>> {
        let mut active = Vec::new();
        for index in 0..self.inputs.len() {
            let constraint = self.meter.copy_row(&self.inputs[index], self.dimensions)?;
            let id = self.record(
                constraint,
                OmegaStep::Input {
                    index: index as u32,
                },
            )?;
            let id = self.normalize(id)?;
            if let Some(contradiction) = self.insert(id, &mut active)? {
                return self.certificate(contradiction).map(Ok);
            }
        }
        self.active = active;
        while let Some(variable) = self.select()? {
            if let Some(contradiction) = self.eliminate(variable)? {
                return self.certificate(contradiction).map(Ok);
            }
        }
        self.witness().map(Err)
    }
}

fn satisfies(
    inputs: &[LinearConstraint],
    witness: &[BigInt],
    meter: &mut Meter<'_>,
) -> Attempt<bool> {
    let dimensions = meter.dimensions(inputs)?;
    if witness.len() != dimensions {
        return Ok(false);
    }
    for value in witness {
        meter.integer(value)?;
    }
    for row in inputs {
        let mut total = BigInt::zero();
        for (coefficient, value) in row.coeffs.iter().zip(witness) {
            let term = meter.mul(coefficient, value)?;
            total = meter.add(&total, &term)?;
        }
        meter.tick(1)?;
        if total > row.bound {
            return Ok(false);
        }
    }
    Ok(true)
}

/// Check a witness independently of elimination history. A resource stop is
/// never interpreted as `false`.
pub fn check_witness(
    inputs: &[LinearConstraint],
    witness: &[BigInt],
    limits: OmegaLimits,
) -> Attempt<bool> {
    let mut never_cancel = || false;
    satisfies(
        inputs,
        witness,
        &mut Meter {
            limits,
            used: 0,
            bytes: 0,
            cancelled: &mut never_cancel,
        },
    )
}

/// Run the native solver with explicit deterministic resource bounds.
pub fn solve(inputs: &[LinearConstraint], limits: OmegaLimits) -> OmegaOutcome {
    solve_with_cancel(inputs, limits, &mut || false)
}

/// As [`solve`], with cooperative cancellation at every metered step.
pub fn solve_with_cancel(
    inputs: &[LinearConstraint],
    limits: OmegaLimits,
    cancelled: &mut dyn FnMut() -> bool,
) -> OmegaOutcome {
    solve_internal(inputs, limits, cancelled, false)
}

/// Extend elimination with bounded exact integer case search. This can close
/// goals the pinned Reference refuses, so embeddings must select it explicitly
/// for their frontier lane rather than widening a faithful tactic silently.
pub fn solve_with_integer_search(inputs: &[LinearConstraint], limits: OmegaLimits) -> OmegaOutcome {
    solve_with_integer_search_and_cancel(inputs, limits, &mut || false)
}

/// As [`solve_with_integer_search`], with cancellation throughout elimination,
/// rational reconstruction, branch construction and witness validation.
pub fn solve_with_integer_search_and_cancel(
    inputs: &[LinearConstraint],
    limits: OmegaLimits,
    cancelled: &mut dyn FnMut() -> bool,
) -> OmegaOutcome {
    solve_internal(inputs, limits, cancelled, true)
}

fn solve_internal(
    inputs: &[LinearConstraint],
    limits: OmegaLimits,
    cancelled: &mut dyn FnMut() -> bool,
    integer_search: bool,
) -> OmegaOutcome {
    let mut meter = Meter {
        limits,
        used: 0,
        bytes: 0,
        cancelled,
    };
    let result = if integer_search {
        branch::solve(inputs, &mut meter)
    } else {
        meter.dimensions(inputs).and_then(|dimensions| {
            Solver {
                meter: &mut meter,
                inputs,
                dimensions,
                rows: Vec::new(),
                active: Vec::new(),
                eliminations: Vec::new(),
            }
            .run()
            .map(|result| match result {
                Ok(certificate) => branch::Result::Linear(certificate),
                Err(witness) => branch::Result::Sat(witness),
            })
        })
    };
    match result {
        Ok(branch::Result::Linear(certificate)) => OmegaOutcome::Unsat {
            certificate,
            steps_used: meter.used,
        },
        Ok(branch::Result::Branches(certificate)) => OmegaOutcome::UnsatBranches {
            certificate,
            steps_used: meter.used,
        },
        Ok(branch::Result::Sat(witness)) => OmegaOutcome::Sat {
            witness,
            steps_used: meter.used,
        },
        Err(reason) => OmegaOutcome::Inconclusive {
            reason,
            steps_used: meter.used,
        },
    }
}

#[cfg(test)]
mod tests;
