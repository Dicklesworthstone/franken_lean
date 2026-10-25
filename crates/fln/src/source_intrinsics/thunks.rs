//! Recognize the pinned lazy family before selecting Golem's memoized objects.
//!
//! These are post-admission models, never new logical declarations. A familiar
//! name, an extern symbol, or the constructor's type alone is insufficient:
//! the family, its elimination rule, and each selected operation must agree.
use super::*;

mod model;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Operation {
    New,
    Pure,
    Get,
}

impl Operation {
    pub(crate) fn from_name(requested: &Name) -> Option<Self> {
        [Self::New, Self::Pure, Self::Get]
            .into_iter()
            .find(|operation| requested == &model::name(operation.label()))
    }

    pub(crate) fn label(self) -> &'static str {
        match self {
            Self::New => "Thunk.mk",
            Self::Pure => "Thunk.pure",
            Self::Get => "Thunk.get",
        }
    }
}

fn unsupported() -> IngressError {
    IngressError::UnsupportedNode {
        kind: "native Thunk differs from its complete checked logical contract",
    }
}

/// The constructor's explicit extern selects the memoized representation.
/// Without it an ordinary same-named record retains ordinary compilation.
pub(crate) fn family_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if !extern_attribute_matches(
        environment,
        &model::name("Thunk.mk"),
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
    if !model::unit_matches(environment, &mut comparison)? {
        return Err(unsupported());
    }
    // Unit's checked aliases determine the adapter's argument representation.
    // Keep explicit foreign helper contracts outside this native model.
    for label in ["Unit", "Unit.unit", "PUnit.unit"] {
        check_selected_extern_attribute(
            environment,
            &model::name(label),
            externs,
            visited,
            limits,
        )?;
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
    if operation != Operation::New
        && !model::operation_matches(environment, operation, &mut Comparison { visited, limits })?
    {
        return Err(unsupported());
    }
    Ok(true)
}

/// The pin's public field is executable via a cached getter, not the raw
/// constructor closure (Init.Core's `Thunk.fn_eq_fnImpl`). Its logical
/// projection must still be exactly the field of the recognized family.
pub(crate) fn projection_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if !family_matches(environment, externs, visited, limits)? {
        return Ok(false);
    }
    check_selected_extern_attribute(
        environment,
        &model::name("Thunk.fn"),
        externs,
        visited,
        limits,
    )?;
    if !model::projection_matches(environment, &mut Comparison { visited, limits })? {
        return Err(unsupported());
    }
    Ok(true)
}
