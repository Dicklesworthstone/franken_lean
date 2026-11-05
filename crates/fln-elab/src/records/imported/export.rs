//! Complete, module-owned structure interfaces for the pin's `structureExt`.
//! Both journals are checked together: parent-subobject rows cannot disappear
//! merely because a caller omitted the corresponding structure identity.
use super::*;
use crate::records::inheritance;
use std::cell::RefCell;
use std::sync::Arc;

// Library validation has its own finite allowance: both journals' byte caps
// plus the existing structure-validation node allowance. A declaration must
// not pay for those journals again out of its local elaboration allowance.
const MAX_PROJECTION_INDEX_WORK: usize = 2 * MAX_BYTES + MAX_NODES;

struct ProjectionIndex {
    environment: Environment,
    projections: Arc<BTreeSet<Name>>,
}

thread_local! {
    // Retain one immutable world per thread, not an unbounded history. Keeping
    // the environment alive also prevents declaration-root identity reuse.
    static LAST_PROJECTIONS: RefCell<Option<ProjectionIndex>> = const { RefCell::new(None) };
}

fn projection_index(env: &Environment) -> Result<Arc<BTreeSet<Name>>, RecordError> {
    let hit = LAST_PROJECTIONS.with(|last| {
        let last = last.borrow();
        let cached = last.as_ref()?;
        let same_journals = [extension_name(), inheritance::descriptor().name]
            .iter()
            .all(
                |name| match (env.extension(name), cached.environment.extension(name)) {
                    (None, None) => true,
                    (Some(left), Some(right)) => std::ptr::eq(left, right),
                    _ => false,
                },
            );
        (env.has_same_declarations(&cached.environment)
            && env.has_same_metadata_validation(&cached.environment)
            && same_journals)
            .then(|| Arc::clone(&cached.projections))
    });
    if let Some(projections) = hit {
        return Ok(projections);
    }
    // Use the complete export validator, including orphan parent rows and
    // exact projection bodies. A failed validation never populates the cache.
    let validated = registrations(&Environment::new(), env, MAX_PROJECTION_INDEX_WORK)?;
    let projections = Arc::new(
        validated
            .structures
            .into_iter()
            .flat_map(|row| row.fields.into_iter().map(|field| field.projection))
            .filter(|name| env.contains(name))
            .collect(),
    );
    LAST_PROJECTIONS.with(|last| {
        *last.borrow_mut() = Some(ProjectionIndex {
            environment: env.clone(),
            projections: Arc::clone(&projections),
        });
    });
    Ok(projections)
}

/// Query validated physical-field identity without charging a library walk to
/// each declaration. This index grants no constant-admission authority.
pub(crate) fn is_registered_projection(
    env: &Environment,
    declaration: &Name,
) -> Result<bool, RecordError> {
    Ok(projection_index(env)?.contains(declaration))
}

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
    mut read: impl FnMut(bool, &[u8], &Environment, &mut Meter) -> Result<(), RecordError>,
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
    for (index, (row, validation)) in result
        .metadata_validation_entries(&expected.name)
        .enumerate()
    {
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
        read(index >= inherited_count, &row.payload, validation, meter)?;
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
        |is_owned, payload, validation, meter| {
            let mut bytes = payload;
            let row = decode(&mut bytes, &mut cells_left)?;
            let parents = validate(validation, &row, &mut meter.remaining)?;
            if is_owned {
                owned(base, validation, &row)?;
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
        |is_owned, payload, validation, meter| {
            let row = inheritance::decode(payload)?;
            inheritance::validate(validation, &row, &mut meter.remaining)?;
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
