//! Complete, module-owned structure interfaces for the pin's `structureExt`.
//! Both journals are checked together: parent-subobject rows cannot disappear
//! merely because a caller omitted the corresponding structure identity.
use super::*;
use crate::records::inheritance;
use std::sync::Arc;

pub fn journal_name() -> Name {
    extension_name()
}

pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor() || *candidate == inheritance::descriptor()
}

#[derive(Debug, Default, PartialEq, Eq)]
pub struct Registrations {
    pub structures: Vec<StructureEntry>,
    pub work: usize,
    pub bytes_examined: usize,
}

struct Meter {
    remaining: usize,
    bytes: usize,
}

impl Meter {
    fn charge(&mut self, amount: usize) -> Result<(), RecordError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(RecordError::ResourceLimit)?;
        Ok(())
    }

    fn payload(&mut self, payload: &[u8]) -> Result<(), RecordError> {
        if payload.len() > MAX_PAYLOAD {
            return Err(RecordError::ResourceLimit);
        }
        self.charge(payload.len())?;
        self.bytes = self
            .bytes
            .checked_add(payload.len())
            .ok_or(RecordError::ResourceLimit)?;
        Ok(())
    }
}

/// Validate the whole journal and preserve its exact inherited prefix. Even a
/// byte-identical inherited payload must decode and agree with the declarations.
fn visit(
    base: &Environment,
    result: &Environment,
    expected: &ExtensionDescriptor,
    meter: &mut Meter,
    mut read: impl FnMut(bool, &[u8], &mut Meter) -> Result<(), RecordError>,
) -> Result<(), RecordError> {
    let prior = base.extension(&expected.name);
    let Some(current) = result.extension(&expected.name) else {
        return if prior.is_some() {
            Err(RecordError::InvalidTelescope)
        } else {
            Ok(())
        };
    };
    if current.descriptor != *expected
        || prior
            .is_some_and(|old| old.descriptor != current.descriptor || old.len() > current.len())
    {
        return Err(RecordError::InvalidTelescope);
    }
    if current.len() > MAX_ROWS {
        return Err(RecordError::ResourceLimit);
    }
    let inherited_count = prior.map_or(0, |old| old.len());
    let mut inherited = prior.map(|old| old.entries());
    let mut bytes_left = MAX_BYTES;
    for (index, row) in current.entries().enumerate() {
        meter.charge(1)?;
        if index < inherited_count {
            let old = inherited
                .as_mut()
                .and_then(Iterator::next)
                .ok_or(RecordError::InvalidTelescope)?;
            if !Arc::ptr_eq(&old.payload, &row.payload) {
                meter.payload(&old.payload)?;
                meter.payload(&row.payload)?;
                if old != row {
                    return Err(RecordError::InvalidTelescope);
                }
            }
        }
        bytes_left = bytes_left
            .checked_sub(row.payload.len())
            .ok_or(RecordError::ResourceLimit)?;
        meter.payload(&row.payload)?;
        read(index >= inherited_count, &row.payload, meter)?;
    }
    Ok(())
}

/// Only declarations owned by this module may acquire an exported structure
/// interface. This cannot turn an imported one-constructor inductive into a
/// structure or replace an imported structure's projections.
fn owned(
    base: &Environment,
    result: &Environment,
    row: &StructureEntry,
) -> Result<(), RecordError> {
    let child = family(result, &row.name)?;
    if base.contains(&row.name)
        || child.ctors.iter().any(|name| base.contains(name))
        || row
            .fields
            .iter()
            .any(|field| base.contains(&field.projection))
        || row
            .parents
            .iter()
            .any(|parent| base.contains(&parent.projection))
    {
        return Err(RecordError::InvalidTelescope);
    }
    Ok(())
}

/// Export the exact owned suffix after validating constructors, projection
/// bodies, binder styles, direct parent order, and the native traversal journal.
/// No ordinary inductive is guessed to be a structure from its kernel shape.
pub fn registrations(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Registrations, RecordError> {
    let mut meter = Meter {
        remaining: max_work,
        bytes: 0,
    };
    let mut cells_left = MAX_CELLS;
    let mut entries = BTreeMap::new();
    let mut expected = BTreeMap::new();
    let mut structures = Vec::new();
    let mut owned_names = BTreeSet::new();
    visit(
        base,
        result,
        &descriptor(),
        &mut meter,
        |is_owned, payload, meter| {
            let mut bytes = payload;
            let row = decode(&mut bytes, &mut cells_left)?;
            let parents = validate(result, &row, &mut meter.remaining)?;
            if is_owned {
                owned(base, result, &row)?;
                owned_names.insert(row.name.clone());
                structures.push(row.clone());
            }
            expected.insert(row.name.clone(), parents);
            if entries.insert(row.name.clone(), row).is_some() {
                return Err(RecordError::DuplicateField);
            }
            Ok(())
        },
    )?;
    let mut native: BTreeMap<Name, Vec<RecordParent>> = BTreeMap::new();
    let mut native_fields = BTreeSet::new();
    let mut native_parents = BTreeSet::new();
    visit(
        base,
        result,
        &inheritance::descriptor(),
        &mut meter,
        |is_owned, payload, meter| {
            let row = inheritance::decode(payload)?;
            inheritance::validate(result, &row, &mut meter.remaining)?;
            if !native_fields.insert((row.record.clone(), row.field))
                || !native_parents.insert((row.record.clone(), row.parent.clone()))
            {
                return Err(RecordError::DuplicateField);
            }
            if is_owned && !owned_names.contains(&row.record) {
                return Err(RecordError::InvalidTelescope);
            }
            native.entry(row.record.clone()).or_default().push(row);
            Ok(())
        },
    )?;
    for (name, expected) in expected {
        meter.charge(1 + expected.len())?;
        let actual = native.entry(name).or_default();
        actual.sort_by_key(|parent| parent.field);
        if *actual != expected {
            return Err(RecordError::InvalidTelescope);
        }
    }
    for name in owned_names {
        let row = entries.get(&name).ok_or(RecordError::InvalidTelescope)?;
        for parent in row.parents.iter().map(|parent| &parent.name).chain(
            row.fields
                .iter()
                .filter_map(|field| field.subobject.as_ref()),
        ) {
            meter.charge(1)?;
            if !entries.contains_key(parent) {
                return Err(RecordError::InvalidTelescope);
            }
        }
    }
    acyclic(&entries, entries.keys(), &mut meter.remaining)?;
    Ok(Registrations {
        structures,
        work: max_work - meter.remaining,
        bytes_examined: meter.bytes,
    })
}

#[cfg(test)]
mod tests;
