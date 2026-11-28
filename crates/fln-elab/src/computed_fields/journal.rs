//! Checked-generation provenance, including module visibility projection.
//!
//! A row is only a claim. Runtime consumers regenerate the complete family and
//! replacements against the current checked implementation before using it.
use super::*;
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeMap;

const MAGIC: &[u8] = b"FLNCOMPUTED\x01";
const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;
const MAX_FIELDS: usize = 1_024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComputedFieldEntry {
    pub family: Name,
    /// Declaration order also determines physical cache-slot order.
    pub fields: Vec<Name>,
    pub inline_fields: Vec<Name>,
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "computedFields", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

fn codec(error: InstanceRegistryError) -> ComputedFieldError {
    match error {
        InstanceRegistryError::Limit => ComputedFieldError::ResourceLimit,
        _ => ComputedFieldError::InvalidInventory,
    }
}

fn tag_error(error: crate::NatDefinitionElabError) -> ComputedFieldError {
    if matches!(
        error,
        crate::NatDefinitionElabError::Inference(
            crate::source::SourceInferenceError::ResourceLimit
        )
    ) {
        ComputedFieldError::ResourceLimit
    } else {
        ComputedFieldError::InvalidInventory
    }
}

fn shape(entry: &ComputedFieldEntry) -> Result<(), ComputedFieldError> {
    if entry.fields.len() > MAX_FIELDS || entry.inline_fields.len() > MAX_FIELDS {
        return Err(ComputedFieldError::ResourceLimit);
    }
    let mut fields = HashSet::new();
    if entry.family.is_anonymous()
        || entry.fields.is_empty()
        || entry
            .fields
            .iter()
            .any(|field| field.parent() != entry.family || !fields.insert(field))
    {
        return Err(ComputedFieldError::InvalidInventory);
    }
    let mut inline = HashSet::new();
    if entry
        .inline_fields
        .iter()
        .any(|field| !fields.contains(field) || !inline.insert(field))
    {
        return Err(ComputedFieldError::InvalidInventory);
    }
    Ok(())
}

fn encode_entry(entry: &ComputedFieldEntry) -> Result<Vec<u8>, ComputedFieldError> {
    shape(entry)?;
    let mut bytes = MAGIC.to_vec();
    write_name(&entry.family, &mut bytes).map_err(codec)?;
    bytes.extend_from_slice(&(entry.fields.len() as u32).to_le_bytes());
    for field in &entry.fields {
        write_name(field, &mut bytes).map_err(codec)?;
        bytes.push(u8::from(entry.inline_fields.contains(field)));
        if bytes.len() > MAX_ENTRY_BYTES {
            return Err(ComputedFieldError::ResourceLimit);
        }
    }
    Ok(bytes)
}

/// Decode syntax only. A well-formed row never grants representation authority.
pub fn decode_entry(payload: &[u8]) -> Result<ComputedFieldEntry, ComputedFieldError> {
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(ComputedFieldError::ResourceLimit);
    }
    let mut bytes = payload
        .strip_prefix(MAGIC)
        .ok_or(ComputedFieldError::InvalidInventory)?;
    let family = read_name(&mut bytes).map_err(codec)?;
    let count = bytes.get(..4).ok_or(ComputedFieldError::InvalidInventory)?;
    let count = u32::from_le_bytes(
        count
            .try_into()
            .map_err(|_| ComputedFieldError::InvalidInventory)?,
    ) as usize;
    bytes = &bytes[4..];
    if count > MAX_FIELDS {
        return Err(ComputedFieldError::ResourceLimit);
    }
    let mut fields = Vec::new();
    let mut inline_fields = Vec::new();
    fields
        .try_reserve_exact(count)
        .map_err(|_| ComputedFieldError::ResourceLimit)?;
    inline_fields
        .try_reserve_exact(count)
        .map_err(|_| ComputedFieldError::ResourceLimit)?;
    for _ in 0..count {
        let field = read_name(&mut bytes).map_err(codec)?;
        let (&inline, rest) = bytes
            .split_first()
            .ok_or(ComputedFieldError::InvalidInventory)?;
        bytes = rest;
        match inline {
            0 => {}
            1 => inline_fields.push(field.clone()),
            _ => return Err(ComputedFieldError::InvalidInventory),
        }
        fields.push(field);
    }
    if !bytes.is_empty() {
        return Err(ComputedFieldError::InvalidInventory);
    }
    let entry = ComputedFieldEntry {
        family,
        fields,
        inline_fields,
    };
    shape(&entry)?;
    Ok(entry)
}

fn charge(work: &mut Builder, amount: usize) -> Result<(), ComputedFieldError> {
    work.remaining = work
        .remaining
        .checked_sub(amount)
        .ok_or(ComputedFieldError::ResourceLimit)?;
    Ok(())
}

/// Cheap claim discovery accepts public getter headers. Exact executable
/// validation below additionally requires the private checked definitions.
fn read(
    env: &Environment,
    budget: RecordBudget,
) -> Result<BTreeMap<Name, ComputedFieldEntry>, ComputedFieldError> {
    let mut work = Builder {
        remaining: budget.max_nodes,
    };
    work.tick()?;
    let mut entries = BTreeMap::new();
    let Some(state) = env.extension(&journal_name()) else {
        return Ok(entries);
    };
    if !supports(&state.descriptor) {
        return Err(ComputedFieldError::InvalidInventory);
    }
    if state.len() > MAX_ROWS {
        return Err(ComputedFieldError::ResourceLimit);
    }
    charge(&mut work, state.len())?;
    for (stored, validation) in env.metadata_validation_entries(&journal_name()) {
        charge(&mut work, stored.payload.len())?;
        let entry = decode_entry(&stored.payload)?;
        if entry.fields.len() > budget.max_binders {
            return Err(ComputedFieldError::ResourceLimit);
        }
        let Some(ConstantInfo::Induct(inductive)) = validation.find(&entry.family) else {
            return Err(ComputedFieldError::InvalidInventory);
        };
        if inductive.is_unsafe || inductive.ctors.len() < 2 {
            return Err(ComputedFieldError::InvalidInventory);
        }
        for field in &entry.fields {
            work.tick()?;
            let info = validation
                .find(field)
                .ok_or(ComputedFieldError::InvalidInventory)?;
            if !matches!(info, ConstantInfo::Defn(value) if value.safety == DefinitionSafety::Safe)
                && !matches!(info, ConstantInfo::Axiom(value) if !value.is_unsafe)
            {
                return Err(ComputedFieldError::InvalidInventory);
            }
            work.scan(
                &info.constant_val().type_,
                &HashSet::new(),
                &Name::anonymous(),
            )?;
        }
        if let Some(previous) = entries.insert(entry.family.clone(), entry.clone())
            && previous != entry
        {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    entries.retain(|name, _| env.contains(name));
    Ok(entries)
}

pub fn families(env: &Environment, budget: RecordBudget) -> Result<Vec<Name>, ComputedFieldError> {
    Ok(read(env, budget)?.into_keys().collect())
}

fn append(
    env: &Environment,
    entry: ComputedFieldEntry,
    budget: RecordBudget,
) -> Result<Environment, ComputedFieldError> {
    let previous = read(env, budget)?;
    if let Some(prior) = previous.get(&entry.family) {
        return if prior == &entry {
            Ok(env.clone())
        } else {
            Err(ComputedFieldError::InvalidInventory)
        };
    }
    let payload = encode_entry(&entry)?;
    let env = match env.extension(&journal_name()) {
        Some(state) if !supports(&state.descriptor) => {
            return Err(ComputedFieldError::InvalidInventory);
        }
        Some(state) if state.len() >= MAX_ROWS => return Err(ComputedFieldError::ResourceLimit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| ComputedFieldError::InvalidInventory)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| ComputedFieldError::InvalidInventory)
}

pub fn register(
    env: &Environment,
    family: &Name,
    fields: &[Name],
    inline_fields: &[Name],
    kernel: Budget,
    budget: RecordBudget,
) -> Result<Environment, ComputedFieldError> {
    let entry = ComputedFieldEntry {
        family: family.clone(),
        fields: fields.to_vec(),
        inline_fields: inline_fields.to_vec(),
    };
    shape(&entry)?;
    validate_inventory(env, family, fields, kernel, budget)?;
    // Canonical field order also canonicalizes the inline subset on disk.
    let entry = ComputedFieldEntry {
        inline_fields: fields
            .iter()
            .filter(|field| inline_fields.contains(field))
            .cloned()
            .collect(),
        ..entry
    };
    let registered = append(env, entry, budget)?;
    super::tags::register_generated(&registered, env, fields).map_err(tag_error)
}

pub fn validated_family(
    env: &Environment,
    family: &Name,
    kernel: Budget,
    budget: RecordBudget,
) -> Result<Option<ComputedFamily>, ComputedFieldError> {
    let Some(entry) = read(env, budget)?.remove(family) else {
        return Ok(None);
    };
    let mut model = validate_inventory(env, family, &entry.fields, kernel, budget)?;
    model.inline_fields = entry.inline_fields;
    Ok(Some(model))
}

/// Preserve source module exposure: safe logical getters may be public axiom
/// headers while all representation declarations keep their checked bodies.
/// This projection never suffices for execution without the private overlay.
pub fn register_projected(
    public_env: &Environment,
    private_checked_env: &Environment,
    family: &Name,
    fields: &[Name],
    inline_fields: &[Name],
    kernel: Budget,
    budget: RecordBudget,
) -> Result<Environment, ComputedFieldError> {
    let entry = ComputedFieldEntry {
        family: family.clone(),
        fields: fields.to_vec(),
        inline_fields: inline_fields.to_vec(),
    };
    shape(&entry)?;
    let model = validate_inventory(private_checked_env, family, fields, kernel, budget)?;
    let mut build = Build::new(private_checked_env, kernel, budget);
    let generated_names = [
        model.family.clone(),
        model.implementation.clone(),
        model.cases_on.clone(),
        Name::str(model.family.clone(), "rec"),
        Name::str(model.implementation.clone(), "rec"),
        Name::str(model.implementation.clone(), "casesOn"),
    ];
    for name in generated_names
        .into_iter()
        .chain(
            model
                .constructors
                .iter()
                .flat_map(|ctor| [ctor.logical.clone(), ctor.implementation.clone()]),
        )
        .chain(
            model
                .overrides
                .iter()
                .map(|definition| definition.base.name.clone()),
        )
    {
        let expected = private_checked_env
            .find(&name)
            .ok_or(ComputedFieldError::InvalidInventory)?;
        build.scan_closed(&expected.constant_val().type_)?;
        match expected {
            ConstantInfo::Defn(value) => build.scan_closed(&value.value)?,
            ConstantInfo::Rec(value) => {
                for rule in &value.rules {
                    build.scan_closed(&rule.rhs)?;
                }
            }
            _ => {}
        }
        if public_env.find(&name) != Some(expected) {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    for field in &model.fields {
        let Some(ConstantInfo::Defn(expected)) = private_checked_env.find(&field.name) else {
            return Err(ComputedFieldError::InvalidInventory);
        };
        build.scan_closed(&expected.base.type_)?;
        match public_env.find(&field.name) {
            Some(ConstantInfo::Defn(actual)) if actual == expected => {}
            Some(ConstantInfo::Axiom(actual))
                if !actual.is_unsafe && actual.base == expected.base => {}
            _ => return Err(ComputedFieldError::InvalidInventory),
        }
    }
    let edges = crate::implemented_by::ImplementedByTable::read_metered(public_env, |amount| {
        build.charge(amount)
    })
    .map_err(|error| match error {
        crate::implemented_by::ImplementedByReadError::Budget(error) => error,
        crate::implemented_by::ImplementedByReadError::Registry(
            crate::implemented_by::ImplementedByError::Limit,
        ) => ComputedFieldError::ResourceLimit,
        _ => ComputedFieldError::InvalidInventory,
    })?;
    for (logical, implementation) in
        std::iter::once((model.cases_on.clone(), model.cases_on_override.clone()))
            .chain(
                model
                    .constructors
                    .iter()
                    .map(|ctor| (ctor.logical.clone(), ctor.override_.clone())),
            )
            .chain(model.fields.iter().map(|field| {
                (
                    field.name.clone(),
                    Name::str(field.name.clone(), "_override"),
                )
            }))
    {
        if edges.get(&logical) != Some(&implementation) || edges.get(&implementation).is_some() {
            return Err(ComputedFieldError::InvalidInventory);
        }
    }
    let entry = ComputedFieldEntry {
        inline_fields: fields
            .iter()
            .filter(|field| inline_fields.contains(field))
            .cloned()
            .collect(),
        ..entry
    };
    let registered = append(public_env, entry, budget)?;
    super::tags::register_generated(&registered, private_checked_env, fields).map_err(tag_error)
}
