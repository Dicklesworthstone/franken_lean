//! Exact post-admission contracts for the bounded native ST representation.
//!
//! These models are recognition data, never declarations to publish. Ordinary
//! `runST`, `runEST`, bind, pure, and exception handlers keep their checked
//! bodies. Only explicitly decorated opaque primitives may select native rows.
//! The runtime adapter retains the logical result fields; this does not claim
//! that its object layout is the Reference's packed C ABI.

use super::*;

mod model;

fn matches(
    environment: &Environment,
    models: impl IntoIterator<Item = ConstantInfo>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let mut comparison = Comparison { visited, limits };
    for expected in models {
        if !comparison.constant(environment, expected)? {
            return Ok(false);
        }
    }
    Ok(true)
}

/// The exact token, ST/EST families, aliases, and Unit used by the adapter.
/// Callers may cache only a completed decision in their immutable preparation.
pub(crate) fn st_world_contract_matches(
    environment: &Environment,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    charge_catalog_node(visited, limits)?;
    matches(environment, model::world(), visited, limits)
}

/// The exact polymorphic reference representation. Keep the admitted Nat core
/// contract as well; payloads and their nested fields may use native Nats.
/// Runtime preparation separately proves each closed payload representation.
pub(crate) fn st_ref_contract_matches(
    environment: &Environment,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if !st_world_contract_matches(environment, visited, limits)? {
        return Ok(false);
    }
    let mut comparison = Comparison { visited, limits };
    if !comparison.declaration(
        environment,
        fln_elab::seed::nat_inductive_seed_declaration(),
    )? {
        return Ok(false);
    }
    matches(environment, model::references(), visited, limits)
}

/// Expose the original checked runner lambda so its type-polymorphic callback
/// can specialize at Unit. This recognizes no replacement implementation and
/// does not force a merely declared IO action. Changed bodies remain ordinary.
pub(crate) fn st_runner_matches(
    environment: &Environment,
    requested: &Name,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    charge_catalog_node(visited, limits)?;
    let Some(expected) = model::runner(requested) else {
        return Ok(false);
    };
    if !st_world_contract_matches(environment, visited, limits)? {
        return Ok(false);
    }
    Comparison { visited, limits }.constant(environment, expected)
}

/// Select no primitive by its spelling alone. An absent extern leaves the
/// ordinary compiler path available; a conflicting explicit contract refuses.
pub(crate) fn st_primitive_matches(
    environment: &Environment,
    requested: &Name,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let Some(label) = model::PRIMITIVES
        .iter()
        .copied()
        .find(|label| requested == &model::name(label))
    else {
        return Ok(false);
    };
    if !extern_attribute_matches(environment, requested, true, externs, visited, limits)? {
        return Ok(false);
    }
    let family_matches = if label == "Void.mk" {
        st_world_contract_matches(environment, visited, limits)?
    } else {
        st_ref_contract_matches(environment, visited, limits)?
    };
    let mut comparison = Comparison { visited, limits };
    if !family_matches
        || !comparison.constant(environment, ConstantInfo::Opaque(model::primitive(label)))?
    {
        return Err(IngressError::UnsupportedNode {
            kind: "native ST extern does not match its complete checked contract",
        });
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
