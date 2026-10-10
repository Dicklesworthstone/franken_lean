//! Shared recognition of executable source primitives.
//!
//! A successful binding has passed the complete logical-model and extern
//! checks against this preparation's immutable environment. Reusing that
//! binding cannot authorize another name, replace an explicit implementation,
//! or import a mutable private type. Only generated scalar signatures enter
//! this table; unknown names and all refusals still take the original path.

use super::*;
use std::collections::HashMap;

#[derive(Default)]
pub(super) struct Store {
    entries: HashMap<Name, IntrinsicBinding>,
}

fn copy_slice<T: Copy>(source: &[T]) -> Result<Vec<T>, IngressError> {
    let mut result = Vec::new();
    result
        .try_reserve_exact(source.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: source.len(),
        })?;
    result.extend_from_slice(source);
    Ok(result)
}

fn copy_binding(source: &IntrinsicBinding) -> Result<IntrinsicBinding, IngressError> {
    // These strings and argument arrays come only from the fixed generated
    // scalar catalog, so their size cannot grow with source expressions.
    // Copies remain fallible even though lookup and copying have fixed work.
    let mut row = String::new();
    row.try_reserve_exact(source.row.len())
        .map_err(|_| IngressError::AllocationFailure {
            resource: IngressResource::ProgramTables,
            requested: source.row.len(),
        })?;
    row.push_str(&source.row);
    Ok(IntrinsicBinding {
        name: source.name.clone(),
        universe_arity: source.universe_arity,
        row,
        arguments: copy_slice(&source.arguments)?,
        argument_ownership: copy_slice(&source.argument_ownership)?,
        result: source.result,
        result_ownership: source.result_ownership,
        effect: source.effect,
    })
}

impl Store {
    fn remember(
        &mut self,
        requested: &Name,
        value: &IntrinsicBinding,
        limit: usize,
    ) -> Result<(), IngressError> {
        let observed = self.entries.len().saturating_add(1);
        if observed > limit {
            return Err(IngressError::ResourceLimit {
                resource: IngressResource::Nodes,
                limit,
                observed,
            });
        }
        self.entries
            .try_reserve(1)
            .map_err(|_| IngressError::AllocationFailure {
                resource: IngressResource::Nodes,
                requested: observed,
            })?;
        let value = copy_binding(value)?;
        self.entries.insert(requested.clone(), value);
        Ok(())
    }

    fn binding(
        &mut self,
        environment: &Environment,
        requested: &Name,
        visited: &mut usize,
        limits: IngressLimits,
        externs: &mut Option<fln_elab::externs::ExternTable>,
    ) -> Result<Option<IntrinsicBinding>, IngressError> {
        if let Some(binding) = self.entries.get(requested) {
            charge_catalog_node(visited, limits)?;
            return copy_binding(binding).map(Some);
        }
        // Preserve existing zero-work negative lookups. Only a completed
        // positive model earns a cache row, after its last budget check and
        // every required allocation have succeeded. The recognizer consumes
        // no structural limit besides max_nodes and no private registry state.
        let binding =
            executable_intrinsic_binding_cached(environment, requested, visited, limits, externs)?;
        if let Some(binding) = &binding {
            charge_catalog_node(visited, limits)?;
            self.remember(requested, binding, limits.max_nodes)?;
        }
        Ok(binding)
    }
}

impl Preparation<'_> {
    pub(crate) fn native_intrinsic_binding(
        &mut self,
        requested: &Name,
    ) -> Result<Option<IntrinsicBinding>, IngressError> {
        self.native_intrinsics.binding(
            self.environment,
            requested,
            &mut self.visited,
            self.limits,
            &mut self.externs,
        )
    }

    /// Dependency discovery has its own work counter. Reuse the completed
    /// contract while charging the caller's independent meter and limits.
    pub(crate) fn catalog_native_intrinsic_binding(
        &mut self,
        requested: &Name,
        visited: &mut usize,
        limits: IngressLimits,
    ) -> Result<Option<IntrinsicBinding>, IngressError> {
        self.native_intrinsics.binding(
            self.environment,
            requested,
            visited,
            limits,
            &mut self.externs,
        )
    }
}

#[cfg(test)]
mod tests;
