//! Native parent-subobject metadata, bound to already admitted constructor fields.
//!
//! This journal changes name resolution, never kernel authority. No parent row
//! can create a declaration or turn an ordinary function into a projection.
use super::{RecordBudget, RecordError};
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::expr::{Expr, ExprNode};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{BTreeMap, HashSet};

const MAGIC: &[u8] = b"FLNRPAR\x01";
const MAX_ROWS: usize = 16_384;
const MAX_BYTES: usize = 16 * 1024 * 1024;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RecordParent {
    pub record: Name,
    pub field: u32,
    pub parent: Name,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RecordParents {
    rows: BTreeMap<Name, Vec<RecordParent>>,
}

/// An inherited field is a chain of real constructor projections. Paths contain
/// the declaring structure and field index at each step, in receiver-first order.
#[derive(Debug, Clone)]
pub struct FieldPath {
    pub name: Name,
    pub path: Vec<(Name, u32)>,
}

fn extension_name() -> Name {
    Name::from_components(["FrankenLean", "sourceRecordParents", "v1"])
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
fn tick(remaining: &mut usize) -> Result<(), RecordError> {
    *remaining = remaining.checked_sub(1).ok_or(RecordError::ResourceLimit)?;
    Ok(())
}

/// Field names and raw dependent domains; domains are still scoped over the
/// constructor telescope. Callers must instantiate before using them as terms.
pub fn direct_fields(
    env: &Environment,
    name: &Name,
    remaining: &mut usize,
) -> Result<Vec<(Name, Expr)>, RecordError> {
    tick(remaining)?;
    let Some(ConstantInfo::Induct(family)) = env.find(name) else {
        return Err(RecordError::InvalidTelescope);
    };
    if family.is_rec || family.is_unsafe || family.num_indices != 0 || family.ctors.len() != 1 {
        return Err(RecordError::InvalidTelescope);
    }
    let Some(ConstantInfo::Ctor(ctor)) = env.find(&family.ctors[0]) else {
        return Err(RecordError::InvalidTelescope);
    };
    if ctor.is_unsafe || ctor.induct != *name || ctor.num_params != family.num_params {
        return Err(RecordError::InvalidTelescope);
    }
    let mut cursor = &ctor.base.type_;
    let mut fields = Vec::new();
    let count = ctor
        .num_params
        .checked_add(ctor.num_fields)
        .ok_or(RecordError::ResourceLimit)?;
    for index in 0..count {
        tick(remaining)?;
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } = cursor.node()
        else {
            return Err(RecordError::InvalidTelescope);
        };
        if index >= ctor.num_params {
            fields.push((binder_name.clone(), binder_type.clone()));
        }
        cursor = body;
    }
    Ok(fields)
}

fn validate(
    env: &Environment,
    row: &RecordParent,
    remaining: &mut usize,
) -> Result<(), RecordError> {
    if row.record == row.parent {
        return Err(RecordError::InvalidTelescope);
    }
    let fields = direct_fields(env, &row.record, remaining)?;
    let (_, mut domain) = fields
        .get(row.field as usize)
        .cloned()
        .ok_or(RecordError::InvalidTelescope)?;
    loop {
        tick(remaining)?;
        match domain.node() {
            ExprNode::App { f, .. } => domain = f.clone(),
            ExprNode::Const { name, .. } if name == &row.parent => break,
            _ => return Err(RecordError::InvalidTelescope),
        }
    }
    direct_fields(env, &row.parent, remaining)?;
    Ok(())
}

impl RecordParents {
    pub fn parents(&self, record: &Name) -> &[RecordParent] {
        self.rows.get(record).map_or(&[], Vec::as_slice)
    }

    /// Enumerate physical and inherited field names without recursion or name
    /// guessing. The supported disjoint-parent profile rejects ambiguous labels
    /// instead of silently choosing a branch of an unimplemented diamond layout.
    pub fn fields(
        &self,
        env: &Environment,
        record: &Name,
        budget: RecordBudget,
    ) -> Result<Vec<FieldPath>, RecordError> {
        let mut remaining = budget.max_nodes;
        let mut pending = vec![(record.clone(), Vec::new(), Vec::<Name>::new())];
        let mut output = Vec::new();
        let mut labels = HashSet::new();
        while let Some((name, path, mut ancestors)) = pending.pop() {
            tick(&mut remaining)?;
            if ancestors.contains(&name) {
                return Err(RecordError::InvalidTelescope);
            }
            if ancestors.len() >= budget.max_binders {
                return Err(RecordError::ResourceLimit);
            }
            ancestors.push(name.clone());
            let fields = direct_fields(env, &name, &mut remaining)?;
            for (index, (label, _)) in fields.into_iter().enumerate() {
                tick(&mut remaining)?;
                if output.len() >= budget.max_binders {
                    return Err(RecordError::ResourceLimit);
                }
                if !labels.insert(label.clone()) {
                    return Err(RecordError::DuplicateField);
                }
                let mut field_path = path.clone();
                field_path.push((name.clone(), index as u32));
                output.push(FieldPath {
                    name: label,
                    path: field_path,
                });
            }
            for parent in self.parents(&name).iter().rev() {
                tick(&mut remaining)?;
                let mut parent_path = path.clone();
                parent_path.push((name.clone(), parent.field));
                pending.push((parent.parent.clone(), parent_path, ancestors.clone()));
            }
        }
        Ok(output)
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
        let mut bytes_left = MAX_BYTES;
        let mut remaining = RecordBudget::default().max_nodes;
        let mut registry = Self::default();
        for entry in extension.entries() {
            bytes_left = bytes_left
                .checked_sub(entry.payload.len())
                .ok_or(RecordError::ResourceLimit)?;
            let mut input = entry
                .payload
                .strip_prefix(MAGIC)
                .ok_or(RecordError::InvalidTelescope)?;
            let record = read_name(&mut input).map_err(codec_error)?;
            let bytes = input.get(..4).ok_or(RecordError::InvalidTelescope)?;
            let field = u32::from_le_bytes(
                bytes
                    .try_into()
                    .map_err(|_| RecordError::InvalidTelescope)?,
            );
            input = &input[4..];
            let parent = read_name(&mut input).map_err(codec_error)?;
            if !input.is_empty() {
                return Err(RecordError::InvalidTelescope);
            }
            let row = RecordParent {
                record,
                field,
                parent,
            };
            validate(env, &row, &mut remaining)?;
            registry.insert(row)?;
        }
        Ok(registry)
    }

    fn insert(&mut self, row: RecordParent) -> Result<(), RecordError> {
        let parents = self.rows.entry(row.record.clone()).or_default();
        if parents
            .iter()
            .any(|p| p.field == row.field || p.parent == row.parent)
        {
            return Err(RecordError::DuplicateField);
        }
        parents.push(row);
        parents.sort_by_key(|row| row.field);
        Ok(())
    }
}

/// Atomic metadata registration, after the complete declaration batch has passed
/// its admission policy. A failed row returns no partially registered successor.
pub fn register_parents(
    env: &Environment,
    rows: &[RecordParent],
) -> Result<Environment, RecordError> {
    if rows.is_empty() {
        return Ok(env.clone());
    }
    let mut registry = RecordParents::read(env)?;
    let count: usize = registry.rows.values().map(Vec::len).sum();
    if count.saturating_add(rows.len()) > MAX_ROWS {
        return Err(RecordError::ResourceLimit);
    }
    let mut remaining = RecordBudget::default().max_nodes;
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
        registry.insert(row.clone())?;
        let mut payload = MAGIC.to_vec();
        write_name(&row.record, &mut payload).map_err(codec_error)?;
        payload.extend(row.field.to_le_bytes());
        write_name(&row.parent, &mut payload).map_err(codec_error)?;
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
    fn malformed_or_foreign_parent_metadata_is_not_an_empty_registry() {
        for payload in [
            Vec::new(),
            b"FLNRPAR\x02".to_vec(),
            [MAGIC, &[0, 0]].concat(),
        ] {
            let env = Environment::new()
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&extension_name(), payload)
                .unwrap();
            assert!(RecordParents::read(&env).is_err());
        }
        let mut foreign = descriptor();
        foreign.provenance = PayloadProvenance::Opaque;
        let env = Environment::new().register_extension(foreign).unwrap();
        assert!(RecordParents::read(&env).is_err());
    }
    #[test]
    fn absent_parent_fields_cannot_be_registered() {
        let env = Environment::new();
        let row = RecordParent {
            record: Name::from_components(["Child"]),
            field: 0,
            parent: Name::from_components(["Parent"]),
        };
        assert!(register_parents(&env, &[row]).is_err());
        assert_eq!(RecordParents::read(&env).unwrap(), RecordParents::default());
    }
}
