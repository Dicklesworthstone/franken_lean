//! Exact contracts for the native Handle.mk and Handle.putStr leaves.
//!
//! Ordinary writeFile/withFile/bind bodies stay executable source. Only the
//! two decorated opaque declarations can select these effectful native rows.

use super::*;

mod model;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Operation {
    Open,
    PutStr,
}

impl Operation {
    pub(crate) fn from_name(requested: &Name) -> Option<Self> {
        [Self::Open, Self::PutStr]
            .into_iter()
            .find(|operation| requested == &operation.source_name())
    }

    pub(crate) fn source_name(self) -> Name {
        Name::from_components([
            "IO",
            "FS",
            "Handle",
            match self {
                Self::Open => "mk",
                Self::PutStr => "putStr",
            },
        ])
    }

    pub(crate) fn private_name(self) -> Name {
        Name::num(
            Name::from_components(["_fln_runtime_fs_primitive"]),
            self as u64,
        )
    }
}

/// Type representation alone grants no primitive execution. Compare the
/// opaque declaration before a compiler-private Handle carrier is registered.
pub(crate) fn handle_matches(
    environment: &Environment,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    let expected = model::handle();
    let mut comparison = Comparison { visited, limits };
    if !comparison.constant(environment, expected.clone())? {
        return Ok(false);
    }
    check_selected_extern_attribute(environment, expected.name(), externs, visited, limits)?;
    Ok(true)
}

pub(crate) fn primitive_matches(
    environment: &Environment,
    operation: Operation,
    externs: &mut Option<fln_elab::externs::ExternTable>,
    visited: &mut usize,
    limits: IngressLimits,
) -> Result<bool, IngressError> {
    if !extern_attribute_matches(
        environment,
        &operation.source_name(),
        true,
        externs,
        visited,
        limits,
    )? {
        return Ok(false);
    }
    if !handle_matches(environment, externs, visited, limits)?
        || !results::contract_matches(environment, externs, visited, limits)?
    {
        return Err(IngressError::UnsupportedNode {
            kind: "native filesystem extern requires the complete checked IO and Handle models",
        });
    }
    let mut models = vec![model::primitive(operation)];
    if operation == Operation::Open {
        models.extend(model::open_layout());
    }
    let mut comparison = Comparison { visited, limits };
    for expected in &models {
        if !comparison.constant(environment, expected.clone())? {
            return Err(IngressError::UnsupportedNode {
                kind: "native filesystem extern does not match its complete checked contract",
            });
        }
    }
    for expected in models {
        check_selected_extern_attribute(environment, expected.name(), externs, visited, limits)?;
    }
    Ok(true)
}

#[cfg(test)]
pub(crate) fn assert_pin_models(environment: &Environment) {
    for expected in model::open_layout().into_iter().chain([
        model::handle(),
        model::primitive(Operation::Open),
        model::primitive(Operation::PutStr),
    ]) {
        assert!(
            Comparison {
                visited: &mut 0,
                limits: IngressLimits::default(),
            }
            .constant(environment, expected.clone())
            .unwrap(),
            "filesystem model {} differs from the actual pinned declaration",
            expected.name().to_display_string(),
        );
    }
}
