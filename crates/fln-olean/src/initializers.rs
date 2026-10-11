//! Data-only decoding of the pin's regular and builtin initialization journals.
//!
//! A named parameter replaces a declaration's stored value at runtime. An
//! anonymous parameter instead records a standalone `IO Unit` action. Neither
//! action is executed here, and decoding grants no declaration or execution
//! authority. Consumers must use the complete private journal of a module-system
//! artifact before treating an absent initializer as evidence about its body.
use crate::region::OpaqueExtensionBlock;
use crate::source_extension_format as layout;
use crate::source_extensions::{DecodeError, DecodeLimits};
use fln_core::name::Name;
use fln_rt::convert::Conversion;
use fln_rt::obj::Obj;
use fln_rt::region::{audit, materialize};
use std::collections::BTreeSet;

#[path = "initializer_format.rs"]
mod format;
pub use format::{BUILTIN_INIT_EXTENSION, REGULAR_INIT_EXTENSION};

/// One `ParametricAttribute Name` entry, in the order stored by the pin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InitEntry {
    pub declaration: Name,
    /// `None` denotes an anonymous parameter: run the declaration as `IO Unit`.
    /// `Some` denotes the action that supplies the declaration's runtime value.
    pub initializer: Option<Name>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InitJournals {
    pub regular: Vec<InitEntry>,
    pub builtin: Vec<InitEntry>,
}

fn shape(detail: &'static str) -> DecodeError {
    DecodeError::Shape { detail }
}
fn limit(resource: &'static str) -> DecodeError {
    DecodeError::Limit { resource }
}

/// Project an already audited and materialized entry. The shared source
/// metadata decoder can use this with its existing cumulative budget.
pub(crate) fn project_entry(
    conversion: &mut Conversion,
    object: &Obj,
) -> Result<InitEntry, DecodeError> {
    if object.is_scalar()
        || object.obj_tag() != 0
        || usize::from(object.header().other) != layout::PROD_POINTERS
    {
        return Err(shape("initializer entry is not a Name pair"));
    }
    let declaration = object
        .try_ctor_child(layout::PROD_FST)
        .ok_or_else(|| shape("missing initialized declaration"))?;
    let initializer = object
        .try_ctor_child(layout::PROD_SND)
        .ok_or_else(|| shape("missing initializer parameter"))?;
    let declaration = conversion
        .project_name(&declaration)
        .map_err(DecodeError::Conversion)?;
    if declaration.is_anonymous() {
        return Err(shape("anonymous initialized declaration"));
    }
    let initializer = conversion
        .project_name(&initializer)
        .map_err(DecodeError::Conversion)?;
    Ok(InitEntry {
        declaration,
        initializer: (!initializer.is_anonymous()).then_some(initializer),
    })
}

/// Decode both journal families under one cumulative byte/object/entry budget.
///
/// Unknown extensions are left uninterpreted; structural names, not display
/// strings, select the two supported families. Duplicate blocks are malformed.
/// A malformed suffix or a resource stop never returns a successful prefix.
/// Entries retain their order, including standalone initialization actions.
pub fn decode(
    blocks: &[OpaqueExtensionBlock],
    limits: DecodeLimits,
) -> Result<InitJournals, DecodeError> {
    let regular = Name::from_components(REGULAR_INIT_EXTENSION.split('.'));
    let builtin = Name::from_components(BUILTIN_INIT_EXTENSION.split('.'));
    let mut seen = BTreeSet::new();
    let mut bytes_left = limits.max_bytes;
    let mut objects_left = limits.max_objects;
    let mut entries_left = limits.max_entries;
    let mut conversion = Conversion::new();
    let mut journals = InitJournals::default();
    for block in blocks {
        if !seen.insert(block.name.clone()) {
            return Err(shape("duplicate extension block"));
        }
        let destination = if block.name == regular {
            &mut journals.regular
        } else if block.name == builtin {
            &mut journals.builtin
        } else {
            continue;
        };
        entries_left = entries_left
            .checked_sub(block.entries.len())
            .ok_or_else(|| limit("initializer entries"))?;
        for payload in &block.entries {
            bytes_left = bytes_left
                .checked_sub(payload.len())
                .ok_or_else(|| limit("initializer payload bytes"))?;
            let audited = audit(payload, 0).map_err(DecodeError::Region)?;
            objects_left = objects_left
                .checked_sub(audited.objects)
                .ok_or_else(|| limit("initializer objects"))?;
            let object = materialize(payload, 0).map_err(DecodeError::Region)?;
            destination.push(project_entry(&mut conversion, &object)?);
        }
    }
    Ok(journals)
}
