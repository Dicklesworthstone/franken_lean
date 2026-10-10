//! Reuse completed sort classification for exact closed source types.
//!
//! The immutable admitted environment and append-only canonical definitions
//! determine logical types. Private projection keys additionally read completed
//! data-shape membership; those descriptions survive representation rollback.
//! Native carrier additions also guard the scalar-index normalization used by
//! that membership check. Every descriptive table grows with fresh keys.
//! No cached result contains a provisional record, constructor, or closure ID.
//! Unknown answers and failures are not evidence and never enter this table.

use super::*;
use std::collections::HashMap;

#[derive(Clone, Copy, Eq, PartialEq)]
struct Generation {
    definitions: usize,
    shapes: usize,
    native: usize,
}

impl Generation {
    fn current(preparation: &Preparation<'_>) -> Self {
        Self {
            definitions: preparation.canonical_definition_generation(),
            shapes: preparation.data_shapes.len(),
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
    proposition: bool,
}

#[derive(Default)]
pub(in crate::runtime) struct Store {
    entries: HashMap<(Expr, usize), Entry>,
}

impl Store {
    fn remember(
        &mut self,
        key: (Expr, usize),
        entry: Entry,
        limit: usize,
    ) -> Result<(), IngressError> {
        let new = !self.entries.contains_key(&key);
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
        self.entries.insert(key, entry);
        Ok(())
    }
}

pub(super) fn proposition_type(
    preparation: &mut Preparation<'_>,
    input: &Expr,
    context: &[Expr],
) -> Result<bool, IngressError> {
    preparation.proof_context_depth(context.len())?;
    if !specialize::closed(input) || matches!(input.node(), ExprNode::Sort { .. }) {
        // An open query must inspect its actual borrowed telescope. A Sort is
        // already classified in one visit and needs neither a key nor a row.
        return classify(preparation, input, context).map(|answer| answer.unwrap_or(false));
    }

    preparation.tick()?;
    let key = (input.clone(), context.len());
    let generation = Generation::current(preparation);
    let limits = Limits::from(preparation.limits);
    if let Some(entry) = preparation.proposition_queries.entries.get(&key)
        && entry.generation == generation
        && entry.limits == limits
    {
        return Ok(entry.proposition);
    }

    let Some(proposition) = classify(preparation, input, context)? else {
        return Ok(false);
    };
    // A query normally discovers no definitions or layouts. Do not publish
    // an in-flight answer under a later generation if that ever changes.
    if Generation::current(preparation) == generation {
        preparation.tick()?;
        preparation.proposition_queries.remember(
            key,
            Entry {
                generation,
                limits,
                proposition,
            },
            preparation.limits.max_nodes,
        )?;
    }
    Ok(proposition)
}

/// `None` distinguishes an unknown type from a checked non-proposition.
/// Both retain the public false answer, but only a completed Sort is reusable.
fn classify(
    preparation: &mut Preparation<'_>,
    input: &Expr,
    context: &[Expr],
) -> Result<Option<bool>, IngressError> {
    // Borrow the caller's original telescope. Only domains introduced while
    // inspecting this Pi spine belong to the local suffix. A closed input has
    // no outer captures, but its lexical depth still bounds added binders.
    let depth = context.len();
    let (prefix, omitted_depth) = if specialize::closed(input) {
        (&[][..], depth)
    } else {
        (context, 0)
    };
    let mut locals = Vec::new();
    let mut type_ = input.clone();
    loop {
        preparation.tick()?;
        match type_.node() {
            ExprNode::Sort { .. } => return Ok(Some(false)),
            ExprNode::ForallE {
                binder_type, body, ..
            } => {
                preparation
                    .proof_context_depth(depth.saturating_add(locals.len()).saturating_add(1))?;
                preparation.push_proof_local(&mut locals, binder_type.clone())?;
                type_ = body.clone();
            }
            _ => {
                let Some(sort) = preparation.projection_receiver_type_in(
                    &type_,
                    prefix,
                    &locals,
                    omitted_depth,
                )?
                else {
                    return Ok(None);
                };
                let sort = preparation.type_head(&sort)?;
                return Ok(match sort.node() {
                    ExprNode::Sort { level } => Some(level == &Level::zero()),
                    _ => None,
                });
            }
        }
    }
}

#[cfg(test)]
mod tests;
