//! Reuse completed head reductions against immutable declarations.
//!
//! This reducer reads no caller telescope: relative variables and metadata are
//! part of the exact expression key. The admitted environment is immutable,
//! and private canonical definitions are appended with fresh names. Growing
//! that table can give a previously opaque head a body. Those results and
//! unresolved projections remain guarded by their generation; completed
//! terminal heads survive unrelated additions. Native type bridges retain their checked
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
    stable: bool,
    limits: Limits,
    result: Expr,
}

#[derive(Default)]
pub(super) struct Store {
    entries: HashMap<Expr, Entry>,
}

/// Adding a fresh private definition cannot change a completed head whose
/// identity already exists, or a nonconstant terminal. A stuck projection is
/// deliberately conservative: its unchanged receiver may hide an unresolved
/// name behind an unfolded definition, so it still needs the generation guard.
/// Only the returned head matters; its unevaluated arguments and lambda bodies
/// were never part of this reduction and retain their exact original syntax.
fn stable_head(preparation: &mut Preparation<'_>, result: &Expr) -> Result<bool, IngressError> {
    let mut head = result;
    loop {
        preparation.tick()?;
        match head.node() {
            ExprNode::App { f, .. } => head = f,
            ExprNode::Const { name, .. } => {
                return Ok(preparation.environment.contains(name)
                    || preparation.specializations.definitions.contains_key(name));
            }
            ExprNode::Proj { .. } | ExprNode::MData { .. } | ExprNode::LetE { .. } => {
                return Ok(false);
            }
            _ => return Ok(true),
        }
    }
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
        && (entry.stable || entry.generation == generation)
        && entry.limits == limits
    {
        return Ok(entry.result.clone());
    }
    let result = preparation.reduce_type_head(source)?;
    // Reduction currently never creates canonical declarations. Retaining
    // this check also prevents an in-flight result from being published under
    // a newer generation if that changes in a later compiler extension.
    if preparation.specializations.definitions.len() == generation {
        let stable = stable_head(preparation, &result)?;
        preparation.tick()?;
        remember(
            &mut preparation.specializations.heads.entries,
            source.clone(),
            Entry {
                generation,
                stable,
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
