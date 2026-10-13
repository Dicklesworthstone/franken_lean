//! Exact contracts for native Handle open, text and binary IO leaves.
//!
//! Ordinary writeFile/writeBinFile/withFile/bind bodies stay executable source.
//! Only decorated opaque declarations can select these effectful native rows.

use super::*;

mod bytes;
mod directory;
mod model;
pub(crate) use bytes::word_matches;
#[cfg(test)]
pub(crate) use bytes::{
    HELPERS as BYTE_HELPERS, WRITE_HELPERS as WRITE_BYTE_HELPERS,
    assert_pin_layouts as assert_pin_byte_layouts, assert_pin_write_dependencies,
};
#[cfg(test)]
pub(crate) use directory::HELPERS as DIRECTORY_HELPERS;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Operation {
    Open,
    PutStr,
    GetLine,
    Read,
    Write,
    ReadDir,
}

impl Operation {
    pub(crate) fn from_name(requested: &Name) -> Option<Self> {
        [
            Self::Open,
            Self::PutStr,
            Self::GetLine,
            Self::Read,
            Self::Write,
            Self::ReadDir,
        ]
        .into_iter()
        .find(|operation| requested == &operation.source_name())
    }

    pub(crate) fn source_name(self) -> Name {
        let label = match self {
            Self::Open => "IO.FS.Handle.mk",
            Self::PutStr => "IO.FS.Handle.putStr",
            Self::GetLine => "IO.FS.Handle.getLine",
            Self::Read => "IO.FS.Handle.read",
            Self::Write => "IO.FS.Handle.write",
            Self::ReadDir => "System.FilePath.readDir",
        };
        Name::from_components(label.split('.'))
    }

    pub(crate) fn source_arity(self) -> usize {
        match self {
            Self::GetLine | Self::ReadDir => 1,
            _ => 2,
        }
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
    if (operation != Operation::ReadDir && !handle_matches(environment, externs, visited, limits)?)
        || !results::contract_matches(environment, externs, visited, limits)?
    {
        return Err(IngressError::UnsupportedNode {
            kind: "native filesystem extern requires its complete checked IO and receiver models",
        });
    }
    let mut models = vec![model::primitive(operation)];
    if operation == Operation::Open {
        models.extend(model::open_layout());
    }
    if operation == Operation::GetLine {
        // This leaf produces native String values. Nominal recognition of
        // String alone cannot authorize a different checked logical layout.
        models.extend(crate::source_intrinsics::string_internal::scalar_records());
    }
    if operation == Operation::Read {
        bytes::contract_matches(environment, externs, visited, limits)?;
    }
    if operation == Operation::Write {
        bytes::write_contract_matches(environment, externs, visited, limits)?;
    }
    if operation == Operation::ReadDir {
        models.extend(model::directory_layout());
        models.extend(crate::source_intrinsics::string_internal::scalar_records());
        directory::contract_matches(environment, externs, visited, limits)?;
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
    for expected in model::open_layout()
        .into_iter()
        .chain(model::directory_layout())
        .chain([
            model::handle(),
            model::primitive(Operation::Open),
            model::primitive(Operation::PutStr),
            model::primitive(Operation::GetLine),
            model::primitive(Operation::Read),
            model::primitive(Operation::Write),
            model::primitive(Operation::ReadDir),
        ])
    {
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
