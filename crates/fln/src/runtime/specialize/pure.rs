//! Reuse completed, exact capture-avoiding syntax transformations.
//!
//! These operations inspect no environment, runtime value, layout or local type
//! context. Relative variables, binder metadata, replacement expressions and
//! ordered universe maps are all part of their input identity. Reusing the
//! resulting syntax neither shares execution nor authorizes a new substitution.

use super::*;
use std::hash::Hash;

type UniverseKey = (Expr, Vec<Name>, Vec<Level>);

#[derive(Default)]
pub(super) struct Store {
    substitutions: HashMap<(Expr, Expr), Expr>,
    universes: HashMap<UniverseKey, Expr>,
}

fn remember<K: Eq + Hash>(
    entries: &mut HashMap<K, Expr>,
    key: K,
    value: Expr,
    limit: usize,
) -> Result<(), IngressError> {
    let observed = entries.len().saturating_add(1);
    if observed > limit {
        return Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit,
            observed,
        });
    }
    entries
        .try_reserve(1)
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::Nodes,
            requested: observed,
        })?;
    entries.insert(key, value);
    Ok(())
}

fn copy_key_slice<T: Clone>(
    preparation: &mut Preparation<'_>,
    source: &[T],
) -> Result<Vec<T>, IngressError> {
    if source.len() > preparation.limits.max_nodes {
        return Err(IngressError::ResourceLimit {
            resource: IngressResource::Nodes,
            limit: preparation.limits.max_nodes,
            observed: source.len(),
        });
    }
    let mut copied = Vec::new();
    copied
        .try_reserve(source.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::Nodes,
            requested: source.len(),
        })?;
    for value in source {
        preparation.tick()?;
        copied.push(value.clone());
    }
    Ok(copied)
}

pub(super) fn universe_instance(
    preparation: &mut Preparation<'_>,
    source: &Expr,
    params: &[Name],
    levels: &[Level],
) -> Result<Expr, IngressError> {
    // These cases already avoid the universe walk. Preserve both their zero
    // work and their malformed-arity result; a cache lookup adds no value here.
    if params.len() != levels.len() || params.is_empty() || !source.has_level_param() {
        return fln_elab::universe::parameters::instantiate(
            || preparation.tick(),
            || unsupported("runtime universe substitution"),
            source,
            params,
            levels,
        );
    }
    preparation.tick()?;
    let key = (
        source.clone(),
        copy_key_slice(preparation, params)?,
        copy_key_slice(preparation, levels)?,
    );
    if let Some(value) = preparation.specializations.pure.universes.get(&key) {
        return Ok(value.clone());
    }
    let value = fln_elab::universe::parameters::instantiate(
        || preparation.tick(),
        || unsupported("runtime universe substitution"),
        source,
        params,
        levels,
    )?;
    preparation.tick()?;
    remember(
        &mut preparation.specializations.pure.universes,
        key,
        value.clone(),
        preparation.limits.max_nodes,
    )?;
    Ok(value)
}

pub(super) fn substitution(
    preparation: &mut Preparation<'_>,
    body: &Expr,
    replacement: &Expr,
) -> Result<Expr, IngressError> {
    // Closed bodies are cloned, and a lone variable either selects the
    // replacement at depth zero or decrements its own index. Preserve these
    // existing constant-cost paths instead of allocating trivial cache rows.
    let cacheable = body.has_loose_bvars() && !matches!(body.node(), ExprNode::BVar { .. });
    let key = if cacheable {
        preparation.tick()?;
        let key = (body.clone(), replacement.clone());
        if let Some(value) = preparation.specializations.pure.substitutions.get(&key) {
            return Ok(value.clone());
        }
        Some(key)
    } else {
        None
    };
    scope::charge(preparation, body, scope::Operation::Substitute(replacement))?;
    let value = body
        .subst_loose(0, std::slice::from_ref(replacement))
        .map_err(|_| unsupported("runtime substitution scope"))?;
    if let Some(key) = key {
        preparation.tick()?;
        remember(
            &mut preparation.specializations.pure.substitutions,
            key,
            value.clone(),
            preparation.limits.max_nodes,
        )?;
    }
    Ok(value)
}

#[cfg(test)]
mod tests;
