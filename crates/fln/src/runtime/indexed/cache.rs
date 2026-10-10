//! Reuse completed erasure of exact closed runtime types.
//!
//! This pass reads no caller telescope or provisional layout IDs. Its logical
//! environment is immutable; canonical definitions and native scalar carriers
//! are added with fresh keys. Both generations matter: a later definition can
//! expose a family, and a native carrier can make an index domain admissible.
//! Retain complete successful results only, with the limits used to derive them.

use super::*;

#[derive(Clone, Copy, Eq, PartialEq)]
struct Generation {
    definitions: usize,
    native: usize,
}

impl Generation {
    fn current(preparation: &Preparation<'_>) -> Self {
        Self {
            definitions: preparation.canonical_definition_generation(),
            native: preparation.value_types.native.len(),
        }
    }
}

#[derive(Clone, Copy, Eq, PartialEq)]
struct Limits {
    arguments: usize,
    depth: usize,
}

impl From<IngressLimits> for Limits {
    fn from(limits: IngressLimits) -> Self {
        Self {
            arguments: limits.max_application_args,
            depth: limits.max_context_depth,
        }
    }
}

struct Entry {
    generation: Generation,
    limits: Limits,
    result: Expr,
}

#[derive(Default)]
pub(in crate::runtime) struct Store {
    entries: HashMap<Expr, Entry>,
}

impl Store {
    fn remember(&mut self, source: Expr, entry: Entry, limit: usize) -> Result<(), IngressError> {
        let new = !self.entries.contains_key(&source);
        let observed = self.entries.len().saturating_add(usize::from(new));
        if observed > limit {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit,
                observed,
            });
        }
        if new {
            self.entries
                .try_reserve(1)
                .map_err(|_| IngressError::AllocationFailure {
                    resource: IngressResource::Nodes,
                    requested: observed,
                })?;
        }
        self.entries.insert(source, entry);
        Ok(())
    }
}

pub(super) fn erase_data_indices(
    preparation: &mut Preparation<'_>,
    input: &Expr,
) -> Result<Expr, IngressError> {
    if matches!(input.node(), ExprNode::Sort { .. }) {
        // A bare universe has no family, indices, children or head reduction.
        // Preserve its exact syntax with one visit and no descriptive row.
        preparation.tick()?;
        return Ok(input.clone());
    }
    if !specialize::closed(input) {
        return preparation.erase_data_indices_uncached(input);
    }
    preparation.tick()?;
    let generation = Generation::current(preparation);
    let limits = Limits::from(preparation.limits);
    if let Some(entry) = preparation.specializations.index_types.entries.get(input)
        && entry.generation == generation
        && entry.limits == limits
    {
        return Ok(entry.result.clone());
    }
    let result = preparation.erase_data_indices_uncached(input)?;
    if specialize::closed(&result) && Generation::current(preparation) == generation {
        preparation.tick()?;
        preparation.specializations.index_types.remember(
            input.clone(),
            Entry {
                generation,
                limits,
                result: result.clone(),
            },
            preparation.limits.max_nodes,
        )?;
    }
    Ok(result)
}

#[cfg(test)]
mod tests;
