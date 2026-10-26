//! Recognize the checked Task family before selecting native task objects.
//! These models supply no logical declarations or admission authority.

use super::*;

mod model;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Operation {
    Pure,
    Get,
    AsTask,
    Wait,
    MapTask,
    BindTask,
}

impl Operation {
    pub(crate) fn from_name(requested: &Name) -> Option<Self> {
        [
            Self::Pure,
            Self::Get,
            Self::AsTask,
            Self::Wait,
            Self::MapTask,
            Self::BindTask,
        ]
        .into_iter()
        .find(|operation| requested == &model::name(operation.label()))
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::Pure => "Task.pure",
            Self::Get => "Task.get",
            Self::AsTask => "BaseIO.asTask",
            Self::Wait => "IO.wait",
            Self::MapTask => "BaseIO.mapTask",
            Self::BindTask => "BaseIO.bindTask",
        }
    }
}

fn unsupported() -> IngressError {
    IngressError::UnsupportedNode {
        kind: "native Task differs from its complete checked logical contract",
    }
}

pub(crate) fn family_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if !extern_attribute_matches(
        environment,
        &model::name("Task.pure"),
        true,
        externs,
        visited,
        limits,
    )? {
        return Ok(false);
    }
    let Some(models) = model::family(environment) else {
        return Err(unsupported());
    };
    let mut comparison = Comparison { visited, limits };
    for expected in models {
        if !comparison.constant(environment, expected)? {
            return Err(unsupported());
        }
    }
    Ok(true)
}

pub(crate) fn operation_matches(
    environment: &Environment,
    operation: Operation,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if !extern_attribute_matches(
        environment,
        &model::name(operation.label()),
        true,
        externs,
        visited,
        limits,
    )? {
        return Ok(false);
    }
    if !family_matches(environment, externs, visited, limits)? {
        return Err(unsupported());
    }
    if matches!(
        operation,
        Operation::AsTask | Operation::Wait | Operation::MapTask | Operation::BindTask
    ) && !io::io_world_contract_matches(environment, externs, visited, limits)?
    {
        return Err(unsupported());
    }
    if operation != Operation::Pure
        && !model::operation_matches(environment, operation, &mut Comparison { visited, limits })?
    {
        return Err(unsupported());
    }
    if matches!(
        operation,
        Operation::AsTask | Operation::MapTask | Operation::BindTask
    ) {
        // The checked Priority abbreviation determines the adapter's Nat
        // argument layout. Its ordinary default is evaluated by the caller.
        check_selected_extern_attribute(
            environment,
            &model::name("Task.Priority"),
            externs,
            visited,
            limits,
        )?;
    }
    if matches!(
        operation,
        Operation::Wait | Operation::MapTask | Operation::BindTask
    ) {
        // The opaque model references this exact getter. The continuation's
        // native operation reads the task payload directly, so an absent
        // getter extern is harmless; a conflicting selected one must not vanish.
        check_selected_extern_attribute(
            environment,
            &model::name("Task.get"),
            externs,
            visited,
            limits,
        )?;
    }
    Ok(true)
}
