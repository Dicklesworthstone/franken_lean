//! Reuse completed head reductions against the same declaration generation.
//!
//! This reducer reads no caller telescope: relative variables and metadata are
//! part of the exact expression key. The admitted environment is immutable,
//! and private canonical definitions are appended with fresh names. Growing
//! that table can give a previously opaque head a body, so every cached result
//! is guarded by its generation. Native type bridges retain their checked
//! carriers for the entire preparation; results contain no closure-table IDs.

use super::*;

#[derive(Clone, Copy, Eq, PartialEq)]
struct Limits {
    arguments: usize,
    projections: usize,
}

impl From<IngressLimits> for Limits {
    fn from(limits: IngressLimits) -> Self {
        Self {
            arguments: limits.max_application_args,
            projections: limits.max_context_depth,
        }
    }
}

struct Entry {
    generation: usize,
    limits: Limits,
    result: Expr,
}

#[derive(Default)]
pub(super) struct Store {
    entries: HashMap<Expr, Entry>,
}

fn remember(
    entries: &mut HashMap<Expr, Entry>,
    source: Expr,
    entry: Entry,
    limit: usize,
) -> Result<(), IngressError> {
    let new = !entries.contains_key(&source);
    let observed = entries.len().saturating_add(usize::from(new));
    if observed > limit {
        return Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        });
    }
    if new {
        entries
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::Nodes,
                requested: observed,
            })?;
    }
    entries.insert(source, entry);
    Ok(())
}

pub(super) fn type_head(
    preparation: &mut Preparation<'_>,
    source: &Expr,
) -> Result<Expr, IngressError> {
    preparation.tick()?;
    // With no application or metadata wrapper, these nodes are already head
    // normal forms. Keep their exact syntax without allocating a memo row or
    // entering the application-spine traversal.
    if matches!(
        source.node(),
        ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lam { .. }
            | ExprNode::ForallE { .. }
            | ExprNode::Lit { .. }
    ) {
        return Ok(source.clone());
    }
    let generation = preparation.specializations.definitions.len();
    let limits = Limits::from(preparation.limits);
    if let Some(entry) = preparation.specializations.heads.entries.get(source)
        && entry.generation == generation
        && entry.limits == limits
    {
        return Ok(entry.result.clone());
    }
    let result = preparation.reduce_type_head(source)?;
    // Reduction currently never creates canonical declarations. Retaining
    // this check also prevents an in-flight result from being published under
    // a newer generation if that changes in a later compiler extension.
    if preparation.specializations.definitions.len() == generation {
        preparation.tick()?;
        remember(
            &mut preparation.specializations.heads.entries,
            source.clone(),
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
