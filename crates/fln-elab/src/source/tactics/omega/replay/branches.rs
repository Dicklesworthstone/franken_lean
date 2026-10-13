//! Exhaustive integer splits, replayed as ordinary disjunction elimination.
//!
//! The numeric tree is untrusted. Every leaf is rebound to the root facts and
//! its ordered path assumptions; fresh branch variables are closed before the
//! resulting proof leaves this module. All work shares the root replay budget.

use super::super::normalize::Affine;
use super::*;
use crate::arithmetic::{
    OMEGA_BRANCH_CERTIFICATE_VERSION, OmegaBranchCertificate, OmegaBranchNode,
};
use std::collections::HashSet;

struct Assumption {
    id: FVarId,
    type_: Expr,
    input: BranchInput,
}

struct BranchRequest<'a> {
    variable: usize,
    cut: &'a BigInt,
    greater: bool,
}

struct BranchScope<'a> {
    normalization: &'a Normalization,
    roots: &'a [LinearConstraint],
    dimension: usize,
    atoms: Expr,
    limits: OmegaLimits,
}

enum Work {
    Visit(usize),
    Enter {
        node: usize,
        assumption: Assumption,
    },
    Exit {
        id: FVarId,
        type_: Expr,
    },
    Join {
        greater: Expr,
        lesser: Expr,
        dichotomy: Expr,
    },
}

fn invalid() -> NatDefinitionElabError {
    error(TacticError::ArithmeticInvalidCertificate)
}

fn reserve<T>(values: &mut Vec<T>, amount: usize) -> Result<(), NatDefinitionElabError> {
    values
        .try_reserve_exact(amount)
        .map_err(|_| resource(OmegaResource::Allocation, 0, amount))
}

/// Validate the entire tree before making any branch proof. Strictly earlier
/// children and one incoming edge for each nonroot node imply reachability and
/// exclude both cycles and shared subtrees with incompatible assumptions.
fn validate(
    context: &mut Context,
    inputs: &[LinearConstraint],
    certificate: &OmegaBranchCertificate,
    limits: OmegaLimits,
    budget: &mut ReplayBudget,
) -> Result<usize, NatDefinitionElabError> {
    if certificate.version != OMEGA_BRANCH_CERTIFICATE_VERSION
        || certificate.inputs.len() != inputs.len()
        || certificate.nodes.is_empty()
        || certificate.conclusion as usize != certificate.nodes.len() - 1
    {
        return Err(invalid());
    }
    budget.reserve_rows(certificate.nodes.len(), limits)?;
    add_bytes(&mut budget.bytes, 32, limits)?;
    let mut dimension = 0;
    for (claimed, actual) in certificate.inputs.iter().zip(inputs) {
        context.tick()?;
        add_bytes(&mut budget.bytes, check_row(claimed, limits)?, limits)?;
        if claimed != actual {
            return Err(invalid());
        }
        dimension = dimension.max(actual.coeffs.len());
    }
    let mut incoming = Vec::new();
    reserve(&mut incoming, certificate.nodes.len())?;
    incoming.resize(certificate.nodes.len(), false);
    let mut total_rows = certificate.nodes.len();
    for (index, node) in certificate.nodes.iter().enumerate() {
        context.tick()?;
        add_bytes(&mut budget.bytes, 16, limits)?;
        match node {
            OmegaBranchNode::Leaf { certificate } => {
                if certificate.version != OMEGA_CERTIFICATE_VERSION
                    || certificate.steps.is_empty()
                    || certificate.conclusion as usize != certificate.steps.len() - 1
                {
                    return Err(invalid());
                }
                total_rows = total_rows.saturating_add(certificate.steps.len());
                if total_rows > limits.max_rows {
                    return Err(resource(OmegaResource::Rows, limits.max_rows, total_rows));
                }
            }
            OmegaBranchNode::Split {
                variable,
                cut,
                le,
                gt,
            } => {
                if *variable as usize >= dimension || le == gt {
                    return Err(invalid());
                }
                check_integer(cut, limits)?;
                add_bytes(
                    &mut budget.bytes,
                    9_usize
                        .saturating_add(8_usize.saturating_mul(cut.magnitude().limbs_le().len())),
                    limits,
                )?;
                for child in [*le as usize, *gt as usize] {
                    if child >= index || incoming[child] {
                        return Err(invalid());
                    }
                    incoming[child] = true;
                }
            }
        }
    }
    if incoming[certificate.nodes.len() - 1]
        || incoming[..certificate.nodes.len() - 1]
            .iter()
            .any(|seen| !seen)
    {
        return Err(invalid());
    }
    Ok(dimension)
}

/// A full-width zero vector lets subtraction produce the exact canonical
/// padded path row. Its dot product is proved zero rather than assumed to
/// reduce on symbolic atoms.
fn constant_evaluation(scalar: &Expr, combo: &Expr, zeros: &Expr, atoms: &Expr) -> Expr {
    let zero = integer(&BigInt::zero());
    let zero_nat = natural(&BigNat::zero());
    let gcd_is_zero = equation(
        constant("Nat"),
        apply(constant("Lean.Omega.Coeffs.gcd"), [zeros.clone()]),
        zero_nat.clone(),
    );
    let all_zero = apply(constant("Lean.Omega.Coeffs.isZero"), [zeros.clone()]);
    let zero_evidence = apply(
        constant("Iff.mp"),
        [
            gcd_is_zero,
            all_zero,
            apply(constant("Lean.Omega.IntList.gcd_eq_zero"), [zeros.clone()]),
            reflexivity(constant("Nat"), zero_nat),
        ],
    );
    let dot = apply(
        constant("Lean.Omega.Coeffs.dot"),
        [zeros.clone(), atoms.clone()],
    );
    let dot_zero = apply(
        constant("Lean.Omega.IntList.dot_of_left_zero"),
        [zeros.clone(), atoms.clone(), zero_evidence],
    );
    let evaluation = apply(
        constant("Lean.Omega.LinearCombo.eval"),
        [combo.clone(), atoms.clone()],
    );
    let middle = apply(constant("Int.add"), [scalar.clone(), zero.clone()]);
    let addition = apply(
        constant("Lean.Omega.Int.add_congr"),
        [
            scalar.clone(),
            scalar.clone(),
            dot,
            zero,
            reflexivity(constant("Int"), scalar.clone()),
            dot_zero,
        ],
    );
    int_transitivity(
        evaluation,
        middle,
        scalar.clone(),
        addition,
        apply(constant("Int.add_zero"), [scalar.clone()]),
    )
}

fn assumption(
    context: &mut Context,
    request: BranchRequest<'_>,
    scope: &BranchScope<'_>,
    budget: &mut ReplayBudget,
) -> Result<Assumption, NatDefinitionElabError> {
    let limits = scope.limits;
    let atom = scope
        .normalization
        .atom_expression(request.variable)
        .ok_or_else(invalid)?
        .clone();
    context.tick()?;
    let scalar = if request.greater {
        request.cut.add(&BigInt::from_i64(1))
    } else {
        request.cut.clone()
    };
    check_integer(&scalar, limits)?;
    // Bound retained row data and all coefficient/proof constructors before
    // allocating the padded vectors or any theorem application.
    add_bytes(
        &mut budget.bytes,
        32_usize
            .saturating_add(17_usize.saturating_mul(scope.dimension))
            .saturating_add(8_usize.saturating_mul(scalar.magnitude().limbs_le().len())),
        limits,
    )?;
    budget.precharge(
        context,
        64_usize.saturating_add(
            32_usize.saturating_mul(
                5_usize
                    .saturating_mul(scope.dimension)
                    .saturating_add(request.variable)
                    .saturating_add(20),
            ),
        ),
        limits,
    )?;
    let mut zeros = Vec::new();
    reserve(&mut zeros, scope.dimension)?;
    zeros.resize(scope.dimension, BigInt::zero());
    let mut coordinate = Vec::new();
    reserve(&mut coordinate, request.variable + 1)?;
    coordinate.resize(request.variable + 1, BigInt::zero());
    coordinate[request.variable] = BigInt::from_i64(1);
    let mut row_coeffs = zeros.clone();
    row_coeffs[request.variable] = BigInt::from_i64(if request.greater { -1 } else { 1 });
    let row = LinearConstraint {
        coeffs: row_coeffs,
        bound: if request.greater {
            scalar.neg()
        } else {
            scalar.clone()
        },
    };
    let affine = Affine {
        constant: row.bound.clone(),
        coefficients: row.coeffs.iter().map(BigInt::neg).collect(),
    };
    let zero_list = coefficients(&zeros);
    let constant_combo = Affine {
        constant: scalar.clone(),
        coefficients: zeros,
    }
    .expression();
    let coordinate_combo = Affine {
        constant: BigInt::zero(),
        coefficients: coordinate,
    }
    .expression();
    let scalar_expression = integer(&scalar);
    let cut_expression = integer(request.cut);
    let id = FVarId(context.fresh_name()?);
    let type_ = if request.greater {
        apply(constant("Int.lt"), [cut_expression.clone(), atom.clone()])
    } else {
        apply(constant("Int.le"), [atom.clone(), cut_expression.clone()])
    };
    let hypothesis = Expr::fvar(id.clone());
    let constant_eval = apply(
        constant("Lean.Omega.LinearCombo.eval"),
        [constant_combo.clone(), scope.atoms.clone()],
    );
    let coordinate_eval = apply(
        constant("Lean.Omega.LinearCombo.eval"),
        [coordinate_combo.clone(), scope.atoms.clone()],
    );
    let constant_proof = constant_evaluation(
        &scalar_expression,
        &constant_combo,
        &zero_list,
        &scope.atoms,
    );
    let coordinate_proof = apply(
        constant("Lean.Omega.LinearCombo.coordinate_eval"),
        [
            natural(&BigNat::from_u64(request.variable as u64)),
            scope.atoms.clone(),
        ],
    );
    let (left, right, left_combo, right_combo, left_eval, right_eval, left_proof, right_proof) =
        if request.greater {
            (
                atom.clone(),
                scalar_expression.clone(),
                coordinate_combo,
                constant_combo,
                coordinate_eval,
                constant_eval,
                coordinate_proof,
                constant_proof,
            )
        } else {
            (
                scalar_expression.clone(),
                atom.clone(),
                constant_combo,
                coordinate_combo,
                constant_eval,
                coordinate_eval,
                constant_proof,
                coordinate_proof,
            )
        };
    let inequality = if request.greater {
        apply(
            constant("Int.add_one_le_of_lt"),
            [cut_expression, atom, hypothesis],
        )
    } else {
        hypothesis
    };
    let nonnegative = apply(
        constant("Int.sub_nonneg_of_le"),
        [left.clone(), right.clone(), inequality],
    );
    let expression = apply(constant("Int.sub"), [left.clone(), right.clone()]);
    let middle = apply(constant("Int.sub"), [left_eval.clone(), right_eval.clone()]);
    let evaluation = affine.evaluation(&scope.atoms);
    let congruence = apply(
        constant("Lean.Omega.Int.sub_congr"),
        [
            left.clone(),
            left_eval.clone(),
            right.clone(),
            right_eval.clone(),
            int_symmetry(left_eval, left, left_proof),
            int_symmetry(right_eval, right, right_proof),
        ],
    );
    let subtraction = apply(
        constant("Lean.Omega.LinearCombo.sub_eval"),
        [left_combo, right_combo, scope.atoms.clone()],
    );
    let normalized = int_transitivity(
        expression.clone(),
        middle.clone(),
        evaluation.clone(),
        congruence,
        int_symmetry(evaluation.clone(), middle, subtraction),
    );
    let evidence = apply(
        Expr::const_(
            Name::from_components(["le_of_le_of_eq"]),
            vec![Level::zero()],
        ),
        [
            constant("Int"),
            integer(&BigInt::zero()),
            expression,
            evaluation,
            constant("Int.instLEInt"),
            nonnegative,
            normalized,
        ],
    );
    let proof = apply(
        constant("Lean.Omega.Constraint.addInequality_sat"),
        [
            integer(&affine.constant),
            coefficients(&affine.coefficients),
            scope.atoms.clone(),
            evidence,
        ],
    );
    Ok(Assumption {
        id,
        type_,
        input: BranchInput { row, proof },
    })
}

/// Prepay the same (allocation identity, binder depth) traversal used by
/// Expr::abstract_fvar before it creates replacements. This includes captured
/// source expressions as well as generated proof nodes and remains bounded
/// when source heartbeats are otherwise unlimited.
fn close_branch(
    context: &mut Context,
    proof: Expr,
    binder: (FVarId, Expr),
    limits: OmegaLimits,
    budget: &mut ReplayBudget,
) -> Result<Expr, NatDefinitionElabError> {
    let mut seen = HashSet::new();
    let mut pending = vec![(proof.clone(), 0_u32)];
    while let Some((expression, depth)) = pending.pop() {
        budget.precharge(context, 1, limits)?;
        if !expression.has_fvar() || seen.contains(&(expression.allocation_identity(), depth)) {
            continue;
        }
        seen.try_reserve(1)
            .map_err(|_| resource(OmegaResource::Allocation, 0, 1))?;
        seen.insert((expression.allocation_identity(), depth));
        reserve(&mut pending, 3)?;
        match expression.node() {
            ExprNode::App { f, a } => {
                pending.push((f.clone(), depth));
                pending.push((a.clone(), depth));
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                let next = depth
                    .checked_add(1)
                    .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                pending.push((binder_type.clone(), depth));
                pending.push((body.clone(), next));
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                let next = depth
                    .checked_add(1)
                    .ok_or_else(|| failure(SourceInferenceError::ResourceLimit))?;
                pending.push((type_.clone(), depth));
                pending.push((value.clone(), depth));
                pending.push((body.clone(), next));
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => {
                pending.push((expr.clone(), depth));
            }
            _ => {}
        }
    }
    budget.precharge(context, 1, limits)?;
    let body = proof
        .abstract_fvar(&binder.0, 0)
        .map_err(|_| failure(SourceInferenceError::Scope))?;
    Ok(Expr::lam(binder.0.0, binder.1, body, BinderInfo::Default))
}

impl Context {
    pub(super) fn omega_replay_branches(
        &mut self,
        normalization: &Normalization,
        inputs: &[LinearConstraint],
        certificate: &OmegaBranchCertificate,
        limits: OmegaLimits,
    ) -> Result<Expr, NatDefinitionElabError> {
        for required in [
            "Int.lt_or_le",
            "Int.add_one_le_of_lt",
            "Int.sub_nonneg_of_le",
            "Int.add_zero",
            "Lean.Omega.LinearCombo.coordinate_eval",
            "Lean.Omega.IntList.gcd_eq_zero",
            "Lean.Omega.IntList.dot_of_left_zero",
            "Lean.Omega.Int.add_congr",
            "Lean.Omega.Int.sub_congr",
        ] {
            if !self
                .txn
                .env
                .contains(&Name::from_components(required.split('.')))
            {
                return Err(error(TacticError::ArithmeticUnsupported));
            }
        }
        let mut budget = ReplayBudget::default();
        let dimension = validate(self, inputs, certificate, limits, &mut budget)?;
        if dimension > normalization.atom_count() {
            return Err(invalid());
        }
        budget.precharge(
            self,
            64_usize.saturating_add(32_usize.saturating_mul(normalization.atom_count())),
            limits,
        )?;
        let scope = BranchScope {
            normalization,
            roots: inputs,
            dimension,
            atoms: normalization.atoms_expression(),
            limits,
        };
        let mut work = Vec::new();
        reserve(&mut work, certificate.nodes.len().saturating_mul(3))?;
        work.push(Work::Visit(certificate.conclusion as usize));
        let mut path = Vec::new();
        reserve(&mut path, certificate.nodes.len())?;
        let mut values = Vec::new();
        reserve(&mut values, certificate.nodes.len())?;
        while let Some(next) = work.pop() {
            self.tick()?;
            match next {
                Work::Visit(index) => match &certificate.nodes[index] {
                    OmegaBranchNode::Leaf { certificate } => {
                        let proof = self.omega_replay_leaf(
                            ReplayInputs {
                                normalization: scope.normalization,
                                roots: scope.roots,
                                branches: &path,
                            },
                            certificate,
                            limits,
                            &mut budget,
                        )?;
                        values.push(proof);
                    }
                    OmegaBranchNode::Split {
                        variable,
                        cut,
                        le,
                        gt,
                    } => {
                        let greater = assumption(
                            self,
                            BranchRequest {
                                variable: *variable as usize,
                                cut,
                                greater: true,
                            },
                            &scope,
                            &mut budget,
                        )?;
                        let lesser = assumption(
                            self,
                            BranchRequest {
                                variable: *variable as usize,
                                cut,
                                greater: false,
                            },
                            &scope,
                            &mut budget,
                        )?;
                        budget.precharge(self, 32, limits)?;
                        let dichotomy = apply(
                            constant("Int.lt_or_le"),
                            [
                                integer(cut),
                                normalization
                                    .atom_expression(*variable as usize)
                                    .ok_or_else(invalid)?
                                    .clone(),
                            ],
                        );
                        work.push(Work::Join {
                            greater: greater.type_.clone(),
                            lesser: lesser.type_.clone(),
                            dichotomy,
                        });
                        work.push(Work::Enter {
                            node: *le as usize,
                            assumption: lesser,
                        });
                        work.push(Work::Enter {
                            node: *gt as usize,
                            assumption: greater,
                        });
                    }
                },
                Work::Enter { node, assumption } => {
                    path.push(assumption.input);
                    work.push(Work::Exit {
                        id: assumption.id,
                        type_: assumption.type_,
                    });
                    work.push(Work::Visit(node));
                }
                Work::Exit { id, type_ } => {
                    path.pop().ok_or_else(invalid)?;
                    let proof = values.pop().ok_or_else(invalid)?;
                    values.push(close_branch(self, proof, (id, type_), limits, &mut budget)?);
                }
                Work::Join {
                    greater,
                    lesser,
                    dichotomy,
                } => {
                    let lesser_proof = values.pop().ok_or_else(invalid)?;
                    let greater_proof = values.pop().ok_or_else(invalid)?;
                    budget.precharge(self, 16, limits)?;
                    values.push(apply(
                        constant("Or.elim"),
                        [
                            greater,
                            lesser,
                            constant("False"),
                            dichotomy,
                            greater_proof,
                            lesser_proof,
                        ],
                    ));
                }
            }
        }
        if !path.is_empty() || values.len() != 1 {
            return Err(invalid());
        }
        values.pop().ok_or_else(invalid)
    }
}
