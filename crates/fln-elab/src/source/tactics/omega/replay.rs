//! Kernel-replayed certificates for native integer linear arithmetic.
//!
//! Native rows a · v ≤ b are represented by the dual lower bound
//! -b ≤ (-a) · v. Every numeric operation below is repeated by ordinary
//! kernel conversion in an admitted theorem application. The provider and
//! this data checker have no admission authority.

mod branches;

use super::super::*;
use super::normalize::Normalization;
use crate::arithmetic::{
    LinearConstraint, OMEGA_CERTIFICATE_VERSION, OmegaCertificate, OmegaInconclusive, OmegaLimits,
    OmegaOutcome, OmegaResource, OmegaStep,
};
use fln_bignum::{int::BigInt, interop::literal_from_bignat, nat::BigNat};

pub(super) fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_components(name.split('.')), vec![])
}
pub(super) fn apply(head: Expr, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    arguments.into_iter().fold(head, Expr::app)
}
pub(super) fn natural(value: &BigNat) -> Expr {
    Expr::lit(Literal::Nat(literal_from_bignat(value)))
}
pub(super) fn integer(value: &BigInt) -> Expr {
    if value.is_negative() {
        apply(
            constant("Int.negSucc"),
            [natural(&value.magnitude().sub(&BigNat::from_u64(1)))],
        )
    } else {
        apply(constant("Int.ofNat"), [natural(value.magnitude())])
    }
}
pub(super) fn int_list(values: impl DoubleEndedIterator<Item = Expr>) -> Expr {
    let int = constant("Int");
    let mut result = apply(
        Expr::const_(Name::from_components(["List", "nil"]), vec![Level::zero()]),
        [int.clone()],
    );
    for value in values.rev() {
        result = apply(
            Expr::const_(Name::from_components(["List", "cons"]), vec![Level::zero()]),
            [int.clone(), value, result],
        );
    }
    result
}
pub(super) fn coefficients(values: &[BigInt]) -> Expr {
    int_list(values.iter().map(integer))
}
pub(super) fn equation(alpha: Expr, left: Expr, right: Expr) -> Expr {
    apply(
        Expr::const_(Name::from_components(["Eq"]), vec![Level::one()]),
        [alpha, left, right],
    )
}
pub(super) fn reflexivity(alpha: Expr, value: Expr) -> Expr {
    apply(
        Expr::const_(Name::from_components(["Eq", "refl"]), vec![Level::one()]),
        [alpha, value],
    )
}
pub(super) fn int_symmetry(left: Expr, right: Expr, proof: Expr) -> Expr {
    apply(
        Expr::const_(Name::from_components(["Eq", "symm"]), vec![Level::one()]),
        [constant("Int"), left, right, proof],
    )
}
pub(super) fn int_transitivity(
    left: Expr,
    middle: Expr,
    right: Expr,
    first: Expr,
    second: Expr,
) -> Expr {
    apply(
        Expr::const_(Name::from_components(["Eq", "trans"]), vec![Level::one()]),
        [constant("Int"), left, middle, right, first, second],
    )
}
pub(super) fn resource(
    kind: OmegaResource,
    limit: usize,
    observed: usize,
) -> NatDefinitionElabError {
    failure(SourceInferenceError::ArithmeticInconclusive(Box::new(
        OmegaInconclusive::ResourceLimit {
            resource: kind,
            limit: limit.try_into().unwrap_or(u64::MAX),
            observed: observed.try_into().unwrap_or(u64::MAX),
        }
        .into_source_outcome(),
    )))
}
pub(super) fn check_integer(
    value: &BigInt,
    limits: OmegaLimits,
) -> Result<(), NatDefinitionElabError> {
    let size = value.magnitude().limbs_le().len();
    if size > limits.max_coefficient_limbs {
        return Err(resource(
            OmegaResource::CoefficientLimbs,
            limits.max_coefficient_limbs,
            size,
        ));
    }
    Ok(())
}

/// Proofs are stored once, with references to earlier lets. A certificate DAG
/// cannot turn into an exponentially expanded proof tree.
pub(super) struct Proofs {
    bindings: Vec<(Expr, Expr)>,
    produced_nodes: u64,
    max_nodes: u64,
}
impl Proofs {
    fn new(limits: OmegaLimits, produced_nodes: u64) -> Self {
        Self {
            bindings: Vec::new(),
            produced_nodes,
            max_nodes: limits.max_steps,
        }
    }

    /// Reserve work before constructing a proof fragment. This separate bound
    /// remains finite even when the enclosing source heartbeat limit is zero.
    fn precharge(
        &mut self,
        context: &mut Context,
        nodes: usize,
    ) -> Result<(), NatDefinitionElabError> {
        let amount = u64::try_from(nodes).unwrap_or(u64::MAX);
        let observed = self.produced_nodes.saturating_add(amount);
        if amount > self.max_nodes.saturating_sub(self.produced_nodes) {
            return Err(resource(
                OmegaResource::Steps,
                usize::try_from(self.max_nodes).unwrap_or(usize::MAX),
                usize::try_from(observed).unwrap_or(usize::MAX),
            ));
        }
        for _ in 0..nodes {
            context.tick()?;
        }
        self.produced_nodes = observed;
        Ok(())
    }

    /// One integer list entry creates at most seven Expr nodes. Reserving 32
    /// per coefficient/constant slot covers repeated affine lists in the
    /// normalization recipes; 64 covers the fixed theorem/type applications.
    /// Callers include every distinct source affine used by the fragment.
    pub(super) fn precharge_affines(
        &mut self,
        context: &mut Context,
        slots: usize,
    ) -> Result<(), NatDefinitionElabError> {
        self.precharge(
            context,
            64_usize.saturating_add(32_usize.saturating_mul(slots)),
        )
    }

    pub(super) fn push(
        &mut self,
        context: &mut Context,
        type_: Expr,
        value: Expr,
    ) -> Result<usize, NatDefinitionElabError> {
        // Pay for the let node now, before finish materializes the wrappers.
        self.precharge(context, 1)?;
        if self.bindings.len() >= u32::MAX as usize {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        self.bindings
            .try_reserve(1)
            .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
        let handle = self.bindings.len();
        self.bindings.push((type_, value));
        Ok(handle)
    }
    pub(super) fn reference(&self, handle: usize) -> Result<Expr, NatDefinitionElabError> {
        let index = self
            .bindings
            .len()
            .checked_sub(handle.saturating_add(1))
            .and_then(|index| u32::try_from(index).ok())
            .ok_or_else(|| error(TacticError::ArithmeticInvalidCertificate))?;
        Expr::bvar(index).map_err(|_| failure(SourceInferenceError::ResourceLimit))
    }
    fn finish(self, mut body: Expr) -> Expr {
        for (index, (type_, value)) in self.bindings.into_iter().enumerate().rev() {
            body = Expr::let_e(
                Name::num(Name::from_components(["_fln_omega_proof"]), index as u64),
                type_,
                value,
                body,
                false,
            );
        }
        body
    }
}

/// One account covers the entire proof, including every branch leaf.
#[derive(Default)]
struct ReplayBudget {
    rows: usize,
    bytes: usize,
    produced_nodes: u64,
}
impl ReplayBudget {
    fn reserve_rows(
        &mut self,
        amount: usize,
        limits: OmegaLimits,
    ) -> Result<(), NatDefinitionElabError> {
        let observed = self.rows.saturating_add(amount);
        if amount > limits.max_rows.saturating_sub(self.rows) {
            return Err(resource(OmegaResource::Rows, limits.max_rows, observed));
        }
        self.rows = observed;
        Ok(())
    }

    fn precharge(
        &mut self,
        context: &mut Context,
        amount: usize,
        limits: OmegaLimits,
    ) -> Result<(), NatDefinitionElabError> {
        let mut proofs = Proofs::new(limits, self.produced_nodes);
        proofs.precharge(context, amount)?;
        self.produced_nodes = proofs.produced_nodes;
        Ok(())
    }
}

struct BranchInput {
    row: LinearConstraint,
    proof: Expr,
}

struct ReplayInputs<'a> {
    normalization: &'a Normalization,
    roots: &'a [LinearConstraint],
    branches: &'a [BranchInput],
}

fn lower_constraint(bound: &BigInt) -> Expr {
    let int = constant("Int");
    let some = apply(
        Expr::const_(
            Name::from_components(["Option", "some"]),
            vec![Level::zero()],
        ),
        [int.clone(), integer(&bound.neg())],
    );
    let none = apply(
        Expr::const_(
            Name::from_components(["Option", "none"]),
            vec![Level::zero()],
        ),
        [int],
    );
    apply(constant("Lean.Omega.Constraint.mk"), [some, none])
}
fn dual_coefficients(row: &LinearConstraint) -> Expr {
    int_list(
        row.coeffs
            .iter()
            .map(|coefficient| integer(&coefficient.neg())),
    )
}
fn row_type(row: &LinearConstraint, atoms: &Expr) -> Expr {
    equation(
        constant("Bool"),
        apply(
            constant("Lean.Omega.Constraint.sat'"),
            [
                lower_constraint(&row.bound),
                dual_coefficients(row),
                atoms.clone(),
            ],
        ),
        constant("Bool.true"),
    )
}
fn check_row(row: &LinearConstraint, limits: OmegaLimits) -> Result<usize, NatDefinitionElabError> {
    if row.coeffs.len() > limits.max_variables {
        return Err(resource(
            OmegaResource::Variables,
            limits.max_variables,
            row.coeffs.len(),
        ));
    }
    let mut bytes = 16_usize;
    for value in row.coeffs.iter().chain(std::iter::once(&row.bound)) {
        check_integer(value, limits)?;
        bytes = bytes
            .checked_add(9 + 8 * value.magnitude().limbs_le().len())
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
    }
    Ok(bytes)
}
fn add_bytes(
    bytes: &mut usize,
    added: usize,
    limits: OmegaLimits,
) -> Result<(), NatDefinitionElabError> {
    *bytes = bytes
        .checked_add(added)
        .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
    if *bytes > limits.max_certificate_bytes {
        return Err(resource(
            OmegaResource::CertificateBytes,
            limits.max_certificate_bytes,
            *bytes,
        ));
    }
    Ok(())
}
fn combine_rows(
    context: &mut Context,
    left: &LinearConstraint,
    right: &LinearConstraint,
    left_scale: &BigNat,
    right_scale: &BigNat,
    limits: OmegaLimits,
) -> Result<LinearConstraint, NatDefinitionElabError> {
    if left_scale.is_zero() || right_scale.is_zero() {
        return Err(error(TacticError::ArithmeticInvalidCertificate));
    }
    for scale in [left_scale, right_scale] {
        if scale.limbs_le().len() > limits.max_coefficient_limbs {
            return Err(resource(
                OmegaResource::CoefficientLimbs,
                limits.max_coefficient_limbs,
                scale.limbs_le().len(),
            ));
        }
    }
    let a = BigInt::from_sign_magnitude(false, left_scale.clone());
    let b = BigInt::from_sign_magnitude(false, right_scale.clone());
    let length = left.coeffs.len().max(right.coeffs.len());
    let zero = BigInt::zero();
    let mut coeffs = Vec::new();
    coeffs
        .try_reserve_exact(length)
        .map_err(|_| resource(OmegaResource::Allocation, 0, length))?;
    for index in 0..length {
        context.tick()?;
        let x = left.coeffs.get(index).unwrap_or(&zero).mul(&a);
        let y = right.coeffs.get(index).unwrap_or(&zero).mul(&b);
        let coefficient = x.add(&y);
        check_integer(&coefficient, limits)?;
        coeffs.push(coefficient);
    }
    let bound = left.bound.mul(&a).add(&right.bound.mul(&b));
    check_integer(&bound, limits)?;
    // Coeffs.combo preserves list length. The solver may trim trailing zeros,
    // but its certificate describes operations rather than intermediate lists.
    Ok(LinearConstraint { coeffs, bound })
}
fn divide_row(
    context: &mut Context,
    source: &LinearConstraint,
    limits: OmegaLimits,
) -> Result<(LinearConstraint, BigNat), NatDefinitionElabError> {
    let mut gcd = BigNat::zero();
    for coefficient in &source.coeffs {
        context.tick()?;
        gcd = gcd.gcd(coefficient.magnitude());
    }
    if gcd.is_zero() {
        return Err(error(TacticError::ArithmeticInvalidCertificate));
    }
    let divisor = BigInt::from_sign_magnitude(false, gcd.clone());
    let mut coeffs = Vec::new();
    coeffs
        .try_reserve_exact(source.coeffs.len())
        .map_err(|_| resource(OmegaResource::Allocation, 0, source.coeffs.len()))?;
    for coefficient in &source.coeffs {
        context.tick()?;
        let quotient = coefficient
            .checked_div_exact(&divisor)
            .ok_or_else(|| error(TacticError::ArithmeticInvalidCertificate))?;
        check_integer(&quotient, limits)?;
        coeffs.push(quotient);
    }
    let bound = source.bound.ediv(&divisor);
    check_integer(&bound, limits)?;
    Ok((LinearConstraint { coeffs, bound }, gcd))
}

impl Context {
    pub(super) fn omega_contradiction(
        &mut self,
        facts: Vec<(Expr, Expr)>,
    ) -> Result<Expr, NatDefinitionElabError> {
        let provider = self
            .source_scope
            .arithmetic
            .ok_or_else(|| error(TacticError::ArithmeticUnsupported))?;
        for required in [
            "Lean.Omega.Constraint.addInequality_sat",
            "Lean.Omega.combo_sat'",
            "Lean.Omega.Constraint.div_sat'",
            "Lean.Omega.normalize_sat",
            "Lean.Omega.Constraint.not_sat'_of_isImpossible",
            "Lean.Omega.LinearCombo.add_eval",
            "Lean.Omega.LinearCombo.sub_eval",
            "Lean.Omega.LinearCombo.neg_eval",
            "Lean.Omega.LinearCombo.mul_eval_of_const_left",
            "Lean.Omega.LinearCombo.mul_eval_of_const_right",
        ] {
            if !self
                .txn
                .env
                .contains(&Name::from_components(required.split('.')))
            {
                return Err(error(TacticError::ArithmeticUnsupported));
            }
        }
        let mut limits = OmegaLimits::default();
        let normalization = Normalization::collect(self, facts, limits)?;
        let inputs = normalization.inputs();
        if self.txn.budget.max_heartbeats != 0 {
            limits.max_steps = limits.max_steps.min(
                self.txn
                    .budget
                    .max_heartbeats
                    .saturating_sub(self.txn.budget.heartbeats_consumed),
            );
        }
        if limits.max_steps == 0 {
            return Err(failure(SourceInferenceError::ResourceLimit));
        }
        let outcome = provider.0(&inputs, limits);
        let steps_used = match &outcome {
            OmegaOutcome::Unsat { steps_used, .. }
            | OmegaOutcome::UnsatBranches { steps_used, .. }
            | OmegaOutcome::Sat { steps_used, .. }
            | OmegaOutcome::Inconclusive { steps_used, .. } => *steps_used,
        };
        if steps_used > limits.max_steps {
            return Err(resource(
                OmegaResource::Steps,
                limits.max_steps as usize,
                steps_used as usize,
            ));
        }
        self.txn.budget.heartbeats_consumed = self
            .txn
            .budget
            .heartbeats_consumed
            .checked_add(steps_used)
            .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
        match outcome {
            OmegaOutcome::Unsat { certificate, .. } => {
                self.tick()?;
                self.omega_replay(normalization, inputs, certificate, limits)
            }
            OmegaOutcome::UnsatBranches { certificate, .. } => {
                self.tick()?;
                self.omega_replay_branches(&normalization, &inputs, &certificate, limits)
            }
            OmegaOutcome::Sat { .. } => Err(error(TacticError::ArithmeticNoContradiction)),
            OmegaOutcome::Inconclusive { reason, .. } => {
                Err(failure(SourceInferenceError::ArithmeticInconclusive(
                    Box::new(reason.into_source_outcome()),
                )))
            }
        }
    }

    fn omega_replay(
        &mut self,
        normalization: Normalization,
        inputs: Vec<LinearConstraint>,
        certificate: OmegaCertificate,
        limits: OmegaLimits,
    ) -> Result<Expr, NatDefinitionElabError> {
        self.omega_replay_leaf(
            ReplayInputs {
                normalization: &normalization,
                roots: &inputs,
                branches: &[],
            },
            &certificate,
            limits,
            &mut ReplayBudget::default(),
        )
    }

    fn omega_replay_leaf(
        &mut self,
        inputs: ReplayInputs<'_>,
        certificate: &OmegaCertificate,
        limits: OmegaLimits,
        budget: &mut ReplayBudget,
    ) -> Result<Expr, NatDefinitionElabError> {
        let normalization = inputs.normalization;
        let input_count = inputs.roots.len().saturating_add(inputs.branches.len());
        if certificate.version != OMEGA_CERTIFICATE_VERSION
            || certificate.inputs.len() != input_count
        {
            return Err(error(TacticError::ArithmeticInvalidCertificate));
        }
        budget.reserve_rows(certificate.steps.len(), limits)?;
        add_bytes(&mut budget.bytes, 32, limits)?;
        for (claimed, actual) in certificate.inputs.iter().zip(
            inputs
                .roots
                .iter()
                .chain(inputs.branches.iter().map(|input| &input.row)),
        ) {
            self.tick()?;
            add_bytes(&mut budget.bytes, check_row(claimed, limits)?, limits)?;
            if claimed != actual {
                return Err(error(TacticError::ArithmeticInvalidCertificate));
            }
        }
        let mut proofs = Proofs::new(limits, budget.produced_nodes);
        proofs.precharge_affines(self, normalization.atom_count())?;
        let atoms = normalization.atoms_expression();
        let normalized_proofs = normalization.proofs(self, &mut proofs, &atoms)?;
        let mut input_proofs = Vec::new();
        input_proofs
            .try_reserve_exact(input_count)
            .map_err(|_| resource(OmegaResource::Allocation, 0, input_count))?;
        for (index, (root, hypothesis)) in normalization.facts.iter().enumerate() {
            self.tick()?;
            let node = &normalization.nodes[*root];
            proofs.precharge_affines(
                self,
                node.affine
                    .coefficients
                    .len()
                    .saturating_add(1)
                    .saturating_mul(2)
                    .saturating_add(inputs.roots[index].coeffs.len().saturating_add(1)),
            )?;
            let evaluation = node.affine.evaluation(&atoms);
            let evidence = apply(
                Expr::const_(
                    Name::from_components(["le_of_le_of_eq"]),
                    vec![Level::zero()],
                ),
                [
                    constant("Int"),
                    integer(&BigInt::zero()),
                    node.expression.clone(),
                    evaluation,
                    constant("Int.instLEInt"),
                    hypothesis.clone(),
                    proofs.reference(normalized_proofs[*root])?,
                ],
            );
            let value = apply(
                constant("Lean.Omega.Constraint.addInequality_sat"),
                [
                    integer(&node.affine.constant),
                    coefficients(&node.affine.coefficients),
                    atoms.clone(),
                    evidence,
                ],
            );
            input_proofs.push(proofs.push(self, row_type(&inputs.roots[index], &atoms), value)?);
        }
        for input in inputs.branches {
            proofs.precharge_affines(self, input.row.coeffs.len().saturating_add(1))?;
            input_proofs.push(proofs.push(
                self,
                row_type(&input.row, &atoms),
                input.proof.clone(),
            )?);
        }
        let mut rows: Vec<LinearConstraint> = Vec::new();
        let mut handles = Vec::new();
        rows.try_reserve_exact(certificate.steps.len())
            .map_err(|_| resource(OmegaResource::Allocation, 0, certificate.steps.len()))?;
        handles
            .try_reserve_exact(certificate.steps.len())
            .map_err(|_| resource(OmegaResource::Allocation, 0, certificate.steps.len()))?;
        for step in &certificate.steps {
            self.tick()?;
            let (row, handle) = match step {
                OmegaStep::Input { index } => {
                    let index = *index as usize;
                    let row = certificate
                        .inputs
                        .get(index)
                        .ok_or_else(|| error(TacticError::ArithmeticInvalidCertificate))?
                        .clone();
                    let handle = *input_proofs
                        .get(index)
                        .ok_or_else(|| error(TacticError::ArithmeticInvalidCertificate))?;
                    (row, handle)
                }
                OmegaStep::Combine {
                    left,
                    right,
                    left_scale,
                    right_scale,
                } => {
                    let left = *left as usize;
                    let right = *right as usize;
                    let x = rows
                        .get(left)
                        .ok_or_else(|| error(TacticError::ArithmeticInvalidCertificate))?;
                    let y = rows
                        .get(right)
                        .ok_or_else(|| error(TacticError::ArithmeticInvalidCertificate))?;
                    let row = combine_rows(self, x, y, left_scale, right_scale, limits)?;
                    add_bytes(
                        &mut budget.bytes,
                        24 + 8 * left_scale.limbs_le().len() + 8 * right_scale.limbs_le().len(),
                        limits,
                    )?;
                    proofs.precharge_affines(
                        self,
                        x.coeffs
                            .len()
                            .saturating_add(y.coeffs.len())
                            .saturating_add(row.coeffs.len())
                            .saturating_add(5),
                    )?;
                    let value = apply(
                        constant("Lean.Omega.combo_sat'"),
                        [
                            lower_constraint(&x.bound),
                            lower_constraint(&y.bound),
                            integer(&BigInt::from_sign_magnitude(false, left_scale.clone())),
                            dual_coefficients(x),
                            integer(&BigInt::from_sign_magnitude(false, right_scale.clone())),
                            dual_coefficients(y),
                            atoms.clone(),
                            proofs.reference(handles[left])?,
                            proofs.reference(handles[right])?,
                        ],
                    );
                    let handle = proofs.push(self, row_type(&row, &atoms), value)?;
                    (row, handle)
                }
                OmegaStep::DivideGcd { source } => {
                    let source = *source as usize;
                    let original = rows
                        .get(source)
                        .ok_or_else(|| error(TacticError::ArithmeticInvalidCertificate))?;
                    let (row, gcd) = divide_row(self, original, limits)?;
                    proofs.precharge_affines(
                        self,
                        original
                            .coeffs
                            .len()
                            .saturating_add(row.coeffs.len())
                            .saturating_add(3),
                    )?;
                    // The kernel recomputes the stated gcd from constructor numerals.
                    let nonzero = apply(
                        constant("Nat.succ_ne_zero"),
                        [natural(&gcd.sub(&BigNat::from_u64(1)))],
                    );
                    let value = apply(
                        constant("Lean.Omega.Constraint.div_sat'"),
                        [
                            lower_constraint(&original.bound),
                            dual_coefficients(original),
                            atoms.clone(),
                            nonzero,
                            proofs.reference(handles[source])?,
                        ],
                    );
                    let handle = proofs.push(self, row_type(&row, &atoms), value)?;
                    (row, handle)
                }
            };
            add_bytes(&mut budget.bytes, 16 + check_row(&row, limits)?, limits)?;
            rows.push(row);
            handles.push(handle);
        }
        let conclusion = certificate.conclusion as usize;
        let row = rows
            .get(conclusion)
            .ok_or_else(|| error(TacticError::ArithmeticInvalidCertificate))?;
        if !row.bound.is_negative() || row.coeffs.iter().any(|coefficient| !coefficient.is_zero()) {
            return Err(error(TacticError::ArithmeticInvalidCertificate));
        }
        proofs.precharge_affines(self, row.coeffs.len().saturating_add(1))?;
        let values = dual_coefficients(row);
        let normalized = apply(
            constant("Lean.Omega.normalize_sat"),
            [
                lower_constraint(&row.bound),
                values.clone(),
                atoms.clone(),
                proofs.reference(handles[conclusion])?,
            ],
        );
        // A lower-only bound is not intrinsically impossible. With a zero
        // vector, normalize_sat computes the unsatisfied value at zero and
        // changes it into the genuinely impossible interval [1, 0].
        let contradiction = apply(
            constant("Lean.Omega.Constraint.not_sat'_of_isImpossible"),
            [
                constant("Lean.Omega.Constraint.impossible"),
                reflexivity(constant("Bool"), constant("Bool.true")),
                values,
                atoms,
                normalized,
            ],
        );
        budget.produced_nodes = proofs.produced_nodes;
        Ok(proofs.finish(contradiction))
    }
}
