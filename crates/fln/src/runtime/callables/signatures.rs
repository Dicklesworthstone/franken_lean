//! Remove repeated suffix rows without changing any source-owned interface.
//!
//! Exact raw signatures stay equal under every later closure-rank substitution.
//! Their unowned multiplicity cannot affect canonical ordering; owned rows still
//! each need their own source-id mapping. Keep the original suffix construction
//! and its table bound before this pass, including for duplicate rows.

use super::*;
use fln_comp::flbc::{ArgumentOwnership, CallableResultOwnership};

pub(super) mod sort;

#[derive(Eq, Hash, PartialEq)]
struct Key<'a> {
    parameters: &'a [ValueType],
    parameter_ownership: &'a [ArgumentOwnership],
    result: ValueType,
    result_ownership: CallableResultOwnership,
}

impl<'a> From<&'a ClosureSignature> for Key<'a> {
    fn from(signature: &'a ClosureSignature) -> Self {
        Self {
            parameters: &signature.parameters,
            parameter_ownership: &signature.parameter_ownership,
            result: signature.result,
            result_ownership: signature.result_ownership,
        }
    }
}

fn charge_key(
    signature: &ClosureSignature,
    limits: IngressLimits,
    visited: &mut usize,
) -> Result<(), IngressError> {
    for _ in &signature.parameters {
        charge_catalog_node(visited, limits)?;
    }
    for _ in &signature.parameter_ownership {
        charge_catalog_node(visited, limits)?;
    }
    charge_catalog_node(visited, limits)?;
    charge_catalog_node(visited, limits)
}

pub(super) fn deduplicate_unowned(
    signatures: &mut Vec<(Option<usize>, ClosureSignature)>,
    limits: IngressLimits,
    visited: &mut usize,
) -> Result<(), IngressError> {
    if signatures.len() > limits.fir.max_closure_types {
        return Err(IngressError::ResourceLimit {
            resource: IngressResource::ProgramTables,
            limit: limits.fir.max_closure_types,
            observed: signatures.len(),
        });
    }
    let mut seen = HashSet::new();
    let mut keep = Vec::new();
    for (owner, signature) in signatures.iter() {
        charge_catalog_node(visited, limits)?;
        let retained = if owner.is_some() {
            true
        } else {
            charge_key(signature, limits, visited)?;
            if seen.contains(&Key::from(signature)) {
                false
            } else {
                let observed = seen.len().saturating_add(1);
                seen.try_reserve(1)
                    .map_err(|_| IngressError::AllocationFailure {
                        resource: IngressResource::ProgramTables,
                        requested: observed,
                    })?;
                // Insertion hashes the full borrowed key a second time. No
                // source vectors are cloned or retained beyond this pass.
                charge_key(signature, limits, visited)?;
                seen.insert(Key::from(signature));
                true
            }
        };
        reserve(&mut keep, limits.fir.max_closure_types)?;
        keep.push(retained);
    }
    // All metering and allocation finish before changing the local row list.
    // Dropping the borrowed keys also releases its immutable borrows.
    drop(seen);
    let mut keep = keep.into_iter();
    signatures.retain(|_| keep.next().expect("one keep decision per signature"));
    Ok(())
}

#[cfg(test)]
mod tests;
