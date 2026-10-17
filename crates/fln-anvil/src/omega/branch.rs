//! Bounded integer branch search with a flat, scoped proof tree.

use super::*;

mod certificate;
mod rational;
pub use certificate::{
    check_branch_certificate, decode_branch_certificate, encode_branch_certificate,
};

pub(super) enum Result {
    Linear(OmegaCertificate),
    Branches(OmegaBranchCertificate),
    Sat(Vec<BigInt>),
}

enum NodeResult {
    Unsat(OmegaCertificate),
    Sat(Vec<BigInt>),
    Split { variable: usize, cut: BigInt },
}

fn solve_node(
    inputs: &[LinearConstraint],
    dimensions: usize,
    meter: &mut Meter<'_>,
) -> Attempt<NodeResult> {
    let mut solver = Solver {
        meter,
        inputs,
        dimensions,
        rows: Vec::new(),
        active: Vec::new(),
        eliminations: Vec::new(),
    };
    match solver.run() {
        Ok(Ok(certificate)) => Ok(NodeResult::Unsat(certificate)),
        Ok(Err(witness)) => Ok(NodeResult::Sat(witness)),
        Err(OmegaInconclusive::IntegerSearchRequired) => {
            match rational::reconstruct(&mut solver)? {
                rational::Point::Integer(witness) => Ok(NodeResult::Sat(witness)),
                rational::Point::Fractional { variable, cut } => {
                    Ok(NodeResult::Split { variable, cut })
                }
            }
        }
        Err(reason) => Err(reason),
    }
}

struct Frame {
    variable: u32,
    cut: BigInt,
    le: Option<u32>,
}

fn row_limit(count: usize, meter: &mut Meter<'_>) -> Attempt<()> {
    meter.tick(1)?;
    let limit = meter.limits.max_rows.min(u32::MAX as usize);
    if count > limit {
        return Err(Meter::limit(OmegaResource::Rows, limit, count));
    }
    Ok(())
}

fn record(
    nodes: &mut Vec<OmegaBranchNode>,
    node: OmegaBranchNode,
    rows_used: &mut usize,
    meter: &mut Meter<'_>,
) -> Attempt<u32> {
    let count = match &node {
        OmegaBranchNode::Leaf { certificate } => certificate.steps.len().saturating_add(1),
        OmegaBranchNode::Split { .. } => 1,
    };
    *rows_used = rows_used.saturating_add(count);
    row_limit(*rows_used, meter)?;
    meter.reserve(nodes, 1)?;
    let index = nodes.len() as u32;
    nodes.push(node);
    Ok(index)
}

fn assumption(
    dimensions: usize,
    variable: usize,
    cut: &BigInt,
    greater: bool,
    meter: &mut Meter<'_>,
) -> Attempt<LinearConstraint> {
    if variable >= dimensions {
        return Err(OmegaInconclusive::IntegerSearchRequired);
    }
    let mut coeffs = Vec::new();
    meter.reserve(&mut coeffs, dimensions)?;
    coeffs.resize_with(dimensions, BigInt::zero);
    coeffs[variable] = BigInt::from_i64(if greater { -1 } else { 1 });
    meter.storage(8)?;
    let bound = if greater {
        let next = meter.add(cut, &BigInt::from_i64(1))?;
        let bound = meter.sub(&BigInt::zero(), &next)?;
        meter.storage(bound.magnitude().limbs_le().len().saturating_mul(8))?;
        bound
    } else {
        meter.copy_int(cut)?
    };
    Ok(LinearConstraint { coeffs, bound })
}

pub(super) fn solve(inputs: &[LinearConstraint], meter: &mut Meter<'_>) -> Attempt<Result> {
    let dimensions = meter.dimensions(inputs)?;
    // Preserve the established cheap linear path, including its certificate
    // bytes and deterministic consumption when no branch search is required.
    let initial = solve_node(inputs, dimensions, meter)?;
    let (first_variable, first_cut) = match initial {
        NodeResult::Unsat(certificate) => return Ok(Result::Linear(certificate)),
        NodeResult::Sat(witness) => return Ok(Result::Sat(witness)),
        NodeResult::Split { variable, cut } => (variable, cut),
    };
    let mut current_inputs = Vec::new();
    meter.reserve(&mut current_inputs, inputs.len())?;
    for input in inputs {
        current_inputs.push(meter.copy_row(input, input.coeffs.len())?);
    }
    let mut frames = Vec::new();
    meter.reserve(&mut frames, 1)?;
    frames.push(Frame {
        variable: first_variable as u32,
        cut: meter.copy_int(&first_cut)?,
        le: None,
    });
    row_limit(current_inputs.len().saturating_add(1), meter)?;
    let first = assumption(dimensions, first_variable, &first_cut, false, meter)?;
    meter.reserve(&mut current_inputs, 1)?;
    current_inputs.push(first);
    let mut nodes = Vec::new();
    let mut rows_used = 0;
    loop {
        meter.tick(1)?;
        let mut completed = match solve_node(&current_inputs, dimensions, meter)? {
            NodeResult::Sat(witness) => {
                // A branch witness is an answer to the root problem only after
                // checking those exact original inputs again.
                if !satisfies(inputs, &witness, meter)? {
                    return Err(OmegaInconclusive::IntegerSearchRequired);
                }
                return Ok(Result::Sat(witness));
            }
            NodeResult::Unsat(certificate) => record(
                &mut nodes,
                OmegaBranchNode::Leaf { certificate },
                &mut rows_used,
                meter,
            )?,
            NodeResult::Split { variable, cut } => {
                row_limit(frames.len().saturating_add(1), meter)?;
                row_limit(current_inputs.len().saturating_add(1), meter)?;
                let row = assumption(dimensions, variable, &cut, false, meter)?;
                meter.reserve(&mut frames, 1)?;
                frames.push(Frame {
                    variable: variable as u32,
                    cut,
                    le: None,
                });
                meter.reserve(&mut current_inputs, 1)?;
                current_inputs.push(row);
                continue;
            }
        };
        loop {
            meter.tick(1)?;
            let Some(frame) = frames.last_mut() else {
                let mut root_inputs = Vec::new();
                meter.reserve(&mut root_inputs, inputs.len())?;
                for input in inputs {
                    root_inputs.push(meter.copy_row(input, input.coeffs.len())?);
                }
                return Ok(Result::Branches(OmegaBranchCertificate {
                    version: OMEGA_BRANCH_CERTIFICATE_VERSION,
                    inputs: root_inputs,
                    nodes,
                    conclusion: completed,
                }));
            };
            if let Some(le) = frame.le {
                let frame = frames
                    .pop()
                    .ok_or(OmegaInconclusive::IntegerSearchRequired)?;
                current_inputs
                    .pop()
                    .ok_or(OmegaInconclusive::IntegerSearchRequired)?;
                completed = record(
                    &mut nodes,
                    OmegaBranchNode::Split {
                        variable: frame.variable,
                        cut: frame.cut,
                        le,
                        gt: completed,
                    },
                    &mut rows_used,
                    meter,
                )?;
            } else {
                frame.le = Some(completed);
                let row = assumption(dimensions, frame.variable as usize, &frame.cut, true, meter)?;
                current_inputs
                    .pop()
                    .ok_or(OmegaInconclusive::IntegerSearchRequired)?;
                current_inputs.push(row);
                break;
            }
        }
    }
}

#[cfg(test)]
mod tests;
