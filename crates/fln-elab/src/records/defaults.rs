//! References to checked field-default helpers in an immutable native journal.
//!
//! A matching helper name alone never enables a default. Registration is separate
//! from candidate construction and only refers to already admitted definitions.
//! This schema is native, not the Reference structure-extension serialization.
use super::RecordError;
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::expr::{Expr, ExprNode};
use fln_core::name::Name;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{BTreeMap, HashSet};

const MAGIC: &[u8] = b"FLNRDEF\x01";
const MAX_ROWS: usize = 16_384;
const MAX_PAYLOAD: usize = 65_536;
const MAX_BYTES: usize = 16 * 1024 * 1024;
const MAX_NODES: usize = 100_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordDefault {
    pub record: Name,
    pub field: u32,
    pub helper: Name,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RecordDefaults {
    helpers: BTreeMap<(Name, u32), Name>,
}

fn extension_name() -> Name {
    Name::from_components(["FrankenLean", "sourceRecordDefaults", "v1"])
}
fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: extension_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}
fn codec_error(error: InstanceRegistryError) -> RecordError {
    if error == InstanceRegistryError::Limit {
        RecordError::ResourceLimit
    } else {
        RecordError::InvalidTelescope
    }
}
fn take<'a>(input: &mut &'a [u8], n: usize) -> Result<&'a [u8], RecordError> {
    if n > input.len() {
        return Err(RecordError::InvalidTelescope);
    }
    let (part, rest) = input.split_at(n);
    *input = rest;
    Ok(part)
}
fn charge(remaining: &mut usize) -> Result<(), RecordError> {
    *remaining = remaining.checked_sub(1).ok_or(RecordError::ResourceLimit)?;
    Ok(())
}
fn scan(expr: &Expr, remaining: &mut usize) -> Result<(), RecordError> {
    let mut pending = vec![expr];
    let mut seen = HashSet::new();
    while let Some(expr) = pending.pop() {
        if !seen.insert(expr.allocation_identity()) {
            continue;
        }
        charge(remaining)?;
        match expr.node() {
            ExprNode::App { f, a } => {
                pending.push(a);
                pending.push(f);
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                pending.push(body);
                pending.push(binder_type);
            }
            ExprNode::LetE {
                type_, value, body, ..
            } => {
                pending.push(body);
                pending.push(value);
                pending.push(type_);
            }
            ExprNode::MData { expr, .. } | ExprNode::Proj { expr, .. } => pending.push(expr),
            _ => {}
        }
    }
    Ok(())
}

pub fn helper_name(record: &Name, field: &Name) -> Name {
    Name::str(record.append_core(field), "_default")
}

/// Independently bind registration to the constructor's field telescope. This
/// checks metadata identity; it does not check or admit a candidate definition.
fn validate(
    env: &Environment,
    row: &RecordDefault,
    remaining: &mut usize,
) -> Result<(), RecordError> {
    let Some(ConstantInfo::Induct(family)) = env.find(&row.record) else {
        return Err(RecordError::InvalidTelescope);
    };
    if family.is_rec || family.is_unsafe || family.num_indices != 0 || family.ctors.len() != 1 {
        return Err(RecordError::InvalidTelescope);
    }
    let Some(ConstantInfo::Ctor(ctor)) = env.find(&family.ctors[0]) else {
        return Err(RecordError::InvalidTelescope);
    };
    if ctor.is_unsafe
        || ctor.induct != row.record
        || row.field >= ctor.num_fields
        || ctor.num_params != family.num_params
    {
        return Err(RecordError::InvalidTelescope);
    }
    let Some(ConstantInfo::Defn(helper)) = env.find(&row.helper) else {
        return Err(RecordError::InvalidTelescope);
    };
    if helper.safety != DefinitionSafety::Safe
        || helper.base.level_params != family.base.level_params
    {
        return Err(RecordError::InvalidTelescope);
    }
    scan(&ctor.base.type_, remaining)?;
    scan(&helper.base.type_, remaining)?;
    let prefix_len = family
        .num_params
        .checked_add(row.field)
        .ok_or(RecordError::ResourceLimit)?;
    if prefix_len > 256 {
        return Err(RecordError::ResourceLimit);
    }
    let mut prefix = Vec::new();
    let mut cursor = &ctor.base.type_;
    for _ in 0..prefix_len {
        charge(remaining)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            binder_info,
            body,
        } = cursor.node()
        else {
            return Err(RecordError::InvalidTelescope);
        };
        prefix.push((binder_name, binder_type, binder_info));
        cursor = body;
    }
    let ExprNode::ForallE {
        binder_name,
        binder_type,
        ..
    } = cursor.node()
    else {
        return Err(RecordError::InvalidTelescope);
    };
    if row.helper != helper_name(&row.record, binder_name) {
        return Err(RecordError::InvalidName);
    }
    let mut expected = binder_type.clone();
    for (name, domain, style) in prefix.into_iter().rev() {
        expected = Expr::forall_e(name.clone(), domain.clone(), expected, *style);
    }
    if helper.base.type_ != expected {
        return Err(RecordError::InvalidTelescope);
    }
    Ok(())
}

impl RecordDefaults {
    pub fn helper(&self, record: &Name, field: u32) -> Option<&Name> {
        self.helpers.get(&(record.clone(), field))
    }
    pub fn read(env: &Environment) -> Result<Self, RecordError> {
        let Some(extension) = env.extension(&extension_name()) else {
            return Ok(Self::default());
        };
        if extension.descriptor != descriptor() {
            return Err(RecordError::InvalidTelescope);
        }
        if extension.len() > MAX_ROWS {
            return Err(RecordError::ResourceLimit);
        }
        let mut remaining = MAX_NODES;
        let mut bytes_left = MAX_BYTES;
        let mut registry = Self::default();
        for entry in extension.entries() {
            if entry.payload.len() > MAX_PAYLOAD {
                return Err(RecordError::ResourceLimit);
            }
            bytes_left = bytes_left
                .checked_sub(entry.payload.len())
                .ok_or(RecordError::ResourceLimit)?;
            let mut input: &[u8] = &entry.payload;
            if take(&mut input, MAGIC.len())? != MAGIC {
                return Err(RecordError::InvalidTelescope);
            }
            let record = read_name(&mut input).map_err(codec_error)?;
            let field = u32::from_le_bytes(
                take(&mut input, 4)?
                    .try_into()
                    .map_err(|_| RecordError::InvalidTelescope)?,
            );
            let helper = read_name(&mut input).map_err(codec_error)?;
            if !input.is_empty() {
                return Err(RecordError::InvalidTelescope);
            }
            let row = RecordDefault {
                record,
                field,
                helper,
            };
            validate(env, &row, &mut remaining)?;
            if registry
                .helpers
                .insert((row.record, row.field), row.helper)
                .is_some()
            {
                return Err(RecordError::DuplicateField);
            }
        }
        Ok(registry)
    }
}

/// Publish a complete registration batch only after its record, projections and
/// helper definitions have passed the caller's normal admission policy.
pub fn register_defaults(
    env: &Environment,
    rows: &[RecordDefault],
) -> Result<Environment, RecordError> {
    if rows.is_empty() {
        return Ok(env.clone());
    }
    let mut registry = RecordDefaults::read(env)?;
    if registry.helpers.len().saturating_add(rows.len()) > MAX_ROWS {
        return Err(RecordError::ResourceLimit);
    }
    let mut remaining = MAX_NODES;
    let mut bytes_left = MAX_BYTES;
    if let Some(extension) = env.extension(&extension_name()) {
        for entry in extension.entries() {
            bytes_left = bytes_left
                .checked_sub(entry.payload.len())
                .ok_or(RecordError::ResourceLimit)?;
        }
    }
    let mut payloads = Vec::new();
    for row in rows {
        validate(env, row, &mut remaining)?;
        if registry
            .helpers
            .insert((row.record.clone(), row.field), row.helper.clone())
            .is_some()
        {
            return Err(RecordError::DuplicateField);
        }
        let mut payload = MAGIC.to_vec();
        write_name(&row.record, &mut payload).map_err(codec_error)?;
        payload.extend(row.field.to_le_bytes());
        write_name(&row.helper, &mut payload).map_err(codec_error)?;
        if payload.len() > MAX_PAYLOAD {
            return Err(RecordError::ResourceLimit);
        }
        bytes_left = bytes_left
            .checked_sub(payload.len())
            .ok_or(RecordError::ResourceLimit)?;
        payloads.push(payload);
    }
    let mut out = if env.extension(&extension_name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| RecordError::InvalidTelescope)?
    } else {
        env.clone()
    };
    for payload in payloads {
        out = out
            .push_extension_entry(&extension_name(), payload)
            .map_err(|_| RecordError::InvalidTelescope)?;
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn malformed_default_metadata_never_becomes_an_empty_registry() {
        for payload in [
            Vec::new(),
            b"FLNRDEF\x02".to_vec(),
            [MAGIC, &[0, 0]].concat(),
        ] {
            let env = Environment::new()
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&extension_name(), payload)
                .unwrap();
            assert!(RecordDefaults::read(&env).is_err());
        }
        let mut foreign = descriptor();
        foreign.provenance = PayloadProvenance::Opaque;
        let env = Environment::new().register_extension(foreign).unwrap();
        assert!(RecordDefaults::read(&env).is_err());
    }
    #[test]
    fn unadmitted_helpers_cannot_be_registered() {
        let env = Environment::new();
        let record = Name::from_components(["Missing"]);
        let row = RecordDefault {
            helper: helper_name(&record, &Name::from_components(["value"])),
            record,
            field: 0,
        };
        assert!(register_defaults(&env, &[row]).is_err());
        assert_eq!(
            RecordDefaults::read(&env).unwrap(),
            RecordDefaults::default()
        );
    }
}
