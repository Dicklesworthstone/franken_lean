//! Reuse completed type reconstruction with its exact lexical dependency.
//!
//! Receiver inference descends a single expression head and can read only one
//! external de Bruijn domain. Lambda and let domains on that path are already
//! present in the input syntax. The returned type is descriptive Expr syntax,
//! not a provisional closure or constructor ID, and no source computation is
//! evaluated or replaced. Retaining the one actual borrowed domain permits
//! reuse across contexts which differ only in slots that inference never read.

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

pub(super) struct Local {
    /// Relative to the end of the combined incoming prefix and suffix.
    pub(super) index: usize,
    /// The original domain before its binder was introduced, not a lifted copy.
    pub(super) domain: Expr,
}

struct Entry {
    generation: Generation,
    limits: Limits,
    dependency: Option<Local>,
    type_: Expr,
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
        let additional = usize::from(!self.entries.contains_key(&key));
        let observed = self.entries.len().saturating_add(additional);
        if observed > limit {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit,
                observed,
            });
        }
        self.entries
            .try_reserve(additional)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::Nodes,
                requested: observed,
            })?;
        self.entries.insert(key, entry);
        Ok(())
    }
}

fn borrowed_domain<'a>(index: usize, context: &'a [Expr], suffix: &'a [Expr]) -> Option<&'a Expr> {
    if index < suffix.len() {
        suffix.get(suffix.len() - 1 - index)
    } else {
        context
            .len()
            .checked_sub(index - suffix.len())
            .and_then(|offset| offset.checked_sub(1))
            .and_then(|index| context.get(index))
    }
}

pub(super) fn receiver_type(
    preparation: &mut Preparation<'_>,
    source: &Expr,
    context: &[Expr],
    suffix: &[Expr],
    omitted_depth: usize,
) -> Result<Option<Expr>, IngressError> {
    let depth = omitted_depth
        .saturating_add(context.len())
        .saturating_add(suffix.len());
    preparation.proof_context_depth(depth)?;
    if !matches!(
        source.node(),
        ExprNode::App { .. }
            | ExprNode::Proj { .. }
            | ExprNode::Lam { .. }
            | ExprNode::LetE { .. }
            | ExprNode::MData { .. }
    ) {
        // Literal, constant and local heads already take a single descent.
        // Do not add a lookup or retain a row for those cheap terminal cases.
        return preparation.infer_receiver_type(source, context, suffix, omitted_depth, &mut None);
    }

    preparation.tick()?;
    let key = (source.clone(), depth);
    let generation = Generation::current(preparation);
    let limits = Limits::from(preparation.limits);
    // A hit still rechecks the one live domain. In particular, equal total
    // depth does not establish an equal omitted/live context split, nor does
    // a previous query grant authority to a missing or shadowed local slot.
    if let Some(entry) = preparation
        .specializations
        .receiver_queries
        .entries
        .get(&key)
        && entry.generation == generation
        && entry.limits == limits
    {
        match &entry.dependency {
            None => return Ok(Some(entry.type_.clone())),
            Some(local) => {
                let matches = borrowed_domain(local.index, context, suffix) == Some(&local.domain);
                let type_ = matches.then(|| entry.type_.clone());
                preparation.tick()?;
                if let Some(type_) = type_ {
                    return Ok(Some(type_));
                }
            }
        }
    }

    let mut dependency = None;
    let Some(type_) =
        preparation.infer_receiver_type(source, context, suffix, omitted_depth, &mut dependency)?
    else {
        return Ok(None);
    };
    // Only a completed descriptive answer is evidence. Do not store unknown
    // heads, errors, exhausted traversals or a result discovered while its
    // admitted-definition/private-description generation was changing.
    if Generation::current(preparation) == generation {
        preparation.tick()?;
        preparation.specializations.receiver_queries.remember(
            key,
            Entry {
                generation,
                limits,
                dependency,
                type_: type_.clone(),
            },
            preparation.limits.max_nodes,
        )?;
    }
    Ok(Some(type_))
}

#[cfg(test)]
mod tests;
