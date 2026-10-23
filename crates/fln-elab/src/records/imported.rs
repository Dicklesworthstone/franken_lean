//! Source and imported structure identities bound to admitted declarations.
//!
//! This journal retains the pin's physical fields and direct extends-clause
//! order. It does not guess parents from arbitrary field types, admit constants,
//! or interpret default helpers. Ordinary source record safety checks still
//! govern whether an imported structure can be constructed.
use super::inheritance::{RecordParent, RecordParents};
use super::{RecordBudget, RecordError};
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::expr::{BinderInfo, Expr, ExprNode};
use fln_core::level::Level;
use fln_core::name::{LeafView, Name};
use fln_env::constants::{ConstantInfo, DefinitionSafety, InductiveVal};
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{BTreeMap, BTreeSet};

mod equality;
pub mod export;
pub use equality::same_interface;

const MAGIC: &[u8] = b"FLNRIMP\x01";
const MAX_ROWS: usize = 16_384;
const MAX_BYTES: usize = 16 * 1024 * 1024;
const MAX_PAYLOAD: usize = 1024 * 1024;
const MAX_CELLS: usize = 65_536;
const MAX_NODES: usize = 1_000_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructureField {
    pub name: Name,
    pub projection: Name,
    pub subobject: Option<Name>,
    pub binder_info: BinderInfo,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructureParent {
    pub name: Name,
    pub subobject: bool,
    pub projection: Name,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructureEntry {
    pub name: Name,
    /// The actual constructor field order.
    pub fields: Vec<StructureField>,
    /// Direct parents in the original extends-clause order. A physical subobject
    /// can instead be an ancestor promoted by the pin's shared-field layout.
    pub parents: Vec<StructureParent>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ImportedStructures {
    entries: BTreeMap<Name, StructureEntry>,
}

fn extension_name() -> Name {
    Name::from_components(["FrankenLean", "importedStructures", "v1"])
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

fn family<'a>(env: &'a Environment, name: &Name) -> Result<&'a InductiveVal, RecordError> {
    let Some(ConstantInfo::Induct(family)) = env.find(name) else {
        return Err(RecordError::InvalidTelescope);
    };
    if family.num_indices != 0 || family.ctors.len() != 1 {
        return Err(RecordError::InvalidTelescope);
    }
    Ok(family)
}

fn record_head<'a>(mut expr: &'a Expr, remaining: &mut usize) -> Result<&'a Name, RecordError> {
    loop {
        tick(remaining)?;
        match expr.node() {
            ExprNode::App { f, .. } => expr = f,
            ExprNode::Const { name, .. } => return Ok(name),
            _ => return Err(RecordError::InvalidTelescope),
        }
    }
}

/// An admitted generated projection has the child's parameters followed by one
/// receiver. Its value and type must expose those same domains. Safe proof
/// fields use theorem declarations, as in the pin's `Meta.mkProjections`.
/// Binder styles may differ because implicit type parameters are inferred
/// independently; declaration kind and the complete body remain authoritative.
fn projection_body<'a>(
    env: &'a Environment,
    child: &InductiveVal,
    projection: &Name,
    remaining: &mut usize,
) -> Result<(&'a Expr, &'a Expr), RecordError> {
    tick(remaining)?;
    let (base, mut value) = match env.find(projection) {
        Some(ConstantInfo::Defn(definition))
            if definition.safety != DefinitionSafety::Partial
                && (definition.safety == DefinitionSafety::Safe || child.is_unsafe) =>
        {
            (&definition.base, &definition.value)
        }
        Some(ConstantInfo::Thm(theorem)) => (&theorem.base, &theorem.value),
        _ => return Err(RecordError::InvalidTelescope),
    };
    if base.level_params != child.base.level_params {
        return Err(RecordError::InvalidTelescope);
    }
    let count = usize::try_from(child.num_params).map_err(|_| RecordError::ResourceLimit)?;
    if count >= RecordBudget::default().max_binders {
        return Err(RecordError::ResourceLimit);
    }
    let mut type_ = &base.type_;
    let mut parameters = &child.base.type_;
    for index in 0..=count {
        tick(remaining)?;
        let (
            ExprNode::Lam {
                binder_type: value_domain,
                body: value_body,
                ..
            },
            ExprNode::ForallE {
                binder_type: type_domain,
                body: type_body,
                ..
            },
        ) = (value.node(), type_.node())
        else {
            return Err(RecordError::InvalidTelescope);
        };
        if !equality::expression(value_domain, type_domain, remaining)? {
            return Err(RecordError::InvalidTelescope);
        }
        if index < count {
            let ExprNode::ForallE {
                binder_type, body, ..
            } = parameters.node()
            else {
                return Err(RecordError::InvalidTelescope);
            };
            if !equality::expression(type_domain, binder_type, remaining)? {
                return Err(RecordError::InvalidTelescope);
            }
            parameters = body;
        } else {
            let mut receiver = Expr::const_(
                child.base.name.clone(),
                child
                    .base
                    .level_params
                    .iter()
                    .cloned()
                    .map(Level::param)
                    .collect(),
            );
            for parameter in 0..count {
                tick(remaining)?;
                let index =
                    u32::try_from(count - 1 - parameter).map_err(|_| RecordError::ResourceLimit)?;
                receiver = Expr::app(
                    receiver,
                    Expr::bvar(index).map_err(|_| RecordError::ResourceLimit)?,
                );
            }
            if !equality::expression(type_domain, &receiver, remaining)? {
                return Err(RecordError::InvalidTelescope);
            }
        }
        value = value_body;
        type_ = type_body;
    }
    Ok((value, type_))
}

fn validate(
    env: &Environment,
    row: &StructureEntry,
    remaining: &mut usize,
) -> Result<Vec<RecordParent>, RecordError> {
    tick(remaining)?;
    if row.name.is_anonymous() {
        return Err(RecordError::InvalidName);
    }
    let child = family(env, &row.name)?;
    let Some(ConstantInfo::Ctor(ctor)) = env.find(&child.ctors[0]) else {
        return Err(RecordError::InvalidTelescope);
    };
    if ctor.induct != row.name
        || ctor.num_params != child.num_params
        || ctor.base.level_params != child.base.level_params
        || ctor.is_unsafe != child.is_unsafe
        || usize::try_from(ctor.num_fields).ok() != Some(row.fields.len())
    {
        return Err(RecordError::InvalidTelescope);
    }
    let count = usize::try_from(ctor.num_params)
        .ok()
        .and_then(|parameters| parameters.checked_add(row.fields.len()))
        .ok_or(RecordError::ResourceLimit)?;
    if count > RecordBudget::default().max_binders
        || row.parents.len() > RecordBudget::default().max_binders
    {
        return Err(RecordError::ResourceLimit);
    }
    let mut cursor = &ctor.base.type_;
    for _ in 0..ctor.num_params {
        tick(remaining)?;
        let ExprNode::ForallE { body, .. } = cursor.node() else {
            return Err(RecordError::InvalidTelescope);
        };
        cursor = body;
    }
    let mut names = BTreeSet::new();
    let mut projections = BTreeSet::new();
    let mut subobjects = BTreeSet::new();
    let mut native_parents = Vec::new();
    for (index, field) in row.fields.iter().enumerate() {
        tick(remaining)?;
        if !field.name.parent().is_anonymous()
            || !matches!(field.name.leaf_view(), LeafView::Str(component) if !component.is_empty())
        {
            return Err(RecordError::InvalidName);
        }
        if !names.insert(field.name.clone()) || !projections.insert(field.projection.clone()) {
            return Err(RecordError::DuplicateField);
        }
        let ExprNode::ForallE {
            binder_name,
            binder_type,
            binder_info,
            body,
        } = cursor.node()
        else {
            return Err(RecordError::InvalidTelescope);
        };
        if binder_name != &field.name || binder_info != &field.binder_info {
            return Err(RecordError::InvalidTelescope);
        }
        let (projected, _) = projection_body(env, child, &field.projection, remaining)?;
        if !matches!(
            projected.node(),
            ExprNode::Proj { struct_name, idx, expr }
                if struct_name == &row.name
                    && *idx == index as u64
                    && matches!(expr.node(), ExprNode::BVar { idx: 0 })
        ) {
            return Err(RecordError::InvalidTelescope);
        }
        if let Some(parent) = &field.subobject {
            if parent == &row.name
                || !subobjects.insert(parent.clone())
                || record_head(binder_type, remaining)? != parent
            {
                return Err(RecordError::InvalidTelescope);
            }
            let parent_info = family(env, parent)?;
            // Metadata for unsafe/recursive records remains data. Only the
            // existing safe nonrecursive record profile gains field traversal.
            if !child.is_unsafe && !child.is_rec && !parent_info.is_unsafe && !parent_info.is_rec {
                native_parents.push(RecordParent {
                    record: row.name.clone(),
                    field: u32::try_from(index).map_err(|_| RecordError::ResourceLimit)?,
                    parent: parent.clone(),
                });
            }
        }
        cursor = body;
    }
    if record_head(cursor, remaining)? != &row.name {
        return Err(RecordError::InvalidTelescope);
    }
    let mut parents = BTreeSet::new();
    for parent in &row.parents {
        tick(remaining)?;
        if parent.name == row.name || !parents.insert(parent.name.clone()) {
            return Err(RecordError::InvalidTelescope);
        }
        family(env, &parent.name)?;
        let physical = row.fields.iter().find(|field| {
            field.subobject.as_ref() == Some(&parent.name) && field.projection == parent.projection
        });
        if parent.subobject {
            if physical.is_none() {
                return Err(RecordError::InvalidTelescope);
            }
        } else {
            if physical.is_some() {
                return Err(RecordError::InvalidTelescope);
            }
            let (_, target) = projection_body(env, child, &parent.projection, remaining)?;
            if record_head(target, remaining)? != &parent.name {
                return Err(RecordError::InvalidTelescope);
            }
        }
    }
    Ok(native_parents)
}

fn acyclic<'a>(
    entries: &BTreeMap<Name, StructureEntry>,
    roots: impl IntoIterator<Item = &'a Name>,
    remaining: &mut usize,
) -> Result<(), RecordError> {
    let mut complete = BTreeSet::new();
    let mut active = BTreeSet::new();
    for root in roots {
        let mut pending = vec![(root.clone(), false)];
        while let Some((name, leave)) = pending.pop() {
            tick(remaining)?;
            if leave {
                active.remove(&name);
                complete.insert(name);
                continue;
            }
            if complete.contains(&name) {
                continue;
            }
            if !active.insert(name.clone()) {
                return Err(RecordError::InvalidTelescope);
            }
            pending.push((name.clone(), true));
            if let Some(row) = entries.get(&name) {
                for parent in row
                    .fields
                    .iter()
                    .filter_map(|field| field.subobject.as_ref())
                    .chain(row.parents.iter().map(|parent| &parent.name))
                {
                    tick(remaining)?;
                    pending.push((parent.clone(), false));
                }
            }
        }
    }
    Ok(())
}

fn take<'a>(bytes: &mut &'a [u8], count: usize) -> Result<&'a [u8], RecordError> {
    let (part, rest) = bytes
        .split_at_checked(count)
        .ok_or(RecordError::InvalidTelescope)?;
    *bytes = rest;
    Ok(part)
}

fn byte(bytes: &mut &[u8]) -> Result<u8, RecordError> {
    Ok(take(bytes, 1)?[0])
}

fn count(bytes: &mut &[u8], cells: &mut usize) -> Result<usize, RecordError> {
    let value = u32::from_le_bytes(
        take(bytes, 4)?
            .try_into()
            .map_err(|_| RecordError::InvalidTelescope)?,
    ) as usize;
    *cells = cells.checked_sub(value).ok_or(RecordError::ResourceLimit)?;
    Ok(value)
}

fn decode(bytes: &mut &[u8], cells: &mut usize) -> Result<StructureEntry, RecordError> {
    if take(bytes, MAGIC.len())? != MAGIC {
        return Err(RecordError::InvalidTelescope);
    }
    let name = read_name(bytes).map_err(codec_error)?;
    let field_count = count(bytes, cells)?;
    let mut fields = Vec::new();
    fields
        .try_reserve_exact(field_count)
        .map_err(|_| RecordError::ResourceLimit)?;
    for _ in 0..field_count {
        let name = read_name(bytes).map_err(codec_error)?;
        let projection = read_name(bytes).map_err(codec_error)?;
        let subobject = match byte(bytes)? {
            0 => None,
            1 => Some(read_name(bytes).map_err(codec_error)?),
            _ => return Err(RecordError::InvalidTelescope),
        };
        let binder_info = match byte(bytes)? {
            0 => BinderInfo::Default,
            1 => BinderInfo::Implicit,
            2 => BinderInfo::StrictImplicit,
            3 => BinderInfo::InstImplicit,
            _ => return Err(RecordError::InvalidTelescope),
        };
        fields.push(StructureField {
            name,
            projection,
            subobject,
            binder_info,
        });
    }
    let parent_count = count(bytes, cells)?;
    let mut parents = Vec::new();
    parents
        .try_reserve_exact(parent_count)
        .map_err(|_| RecordError::ResourceLimit)?;
    for _ in 0..parent_count {
        let name = read_name(bytes).map_err(codec_error)?;
        let projection = read_name(bytes).map_err(codec_error)?;
        let subobject = match byte(bytes)? {
            0 => false,
            1 => true,
            _ => return Err(RecordError::InvalidTelescope),
        };
        parents.push(StructureParent {
            name,
            subobject,
            projection,
        });
    }
    if !bytes.is_empty() {
        return Err(RecordError::InvalidTelescope);
    }
    Ok(StructureEntry {
        name,
        fields,
        parents,
    })
}

fn encode(row: &StructureEntry) -> Result<Vec<u8>, RecordError> {
    let mut bytes = MAGIC.to_vec();
    write_name(&row.name, &mut bytes).map_err(codec_error)?;
    bytes.extend(
        u32::try_from(row.fields.len())
            .map_err(|_| RecordError::ResourceLimit)?
            .to_le_bytes(),
    );
    for field in &row.fields {
        write_name(&field.name, &mut bytes).map_err(codec_error)?;
        write_name(&field.projection, &mut bytes).map_err(codec_error)?;
        bytes.push(u8::from(field.subobject.is_some()));
        if let Some(parent) = &field.subobject {
            write_name(parent, &mut bytes).map_err(codec_error)?;
        }
        bytes.push(match field.binder_info {
            BinderInfo::Default => 0,
            BinderInfo::Implicit => 1,
            BinderInfo::StrictImplicit => 2,
            BinderInfo::InstImplicit => 3,
        });
    }
    bytes.extend(
        u32::try_from(row.parents.len())
            .map_err(|_| RecordError::ResourceLimit)?
            .to_le_bytes(),
    );
    for parent in &row.parents {
        write_name(&parent.name, &mut bytes).map_err(codec_error)?;
        write_name(&parent.projection, &mut bytes).map_err(codec_error)?;
        bytes.push(u8::from(parent.subobject));
    }
    if bytes.len() > MAX_PAYLOAD {
        return Err(RecordError::ResourceLimit);
    }
    Ok(bytes)
}

impl ImportedStructures {
    pub fn get(&self, name: &Name) -> Option<&StructureEntry> {
        self.entries.get(name)
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
        let mut cells_left = MAX_CELLS;
        let mut entries = BTreeMap::new();
        let native = RecordParents::read(env)?;
        for payload in extension.entries() {
            if payload.payload.len() > MAX_PAYLOAD {
                return Err(RecordError::ResourceLimit);
            }
            bytes_left = bytes_left
                .checked_sub(payload.payload.len())
                .ok_or(RecordError::ResourceLimit)?;
            let mut bytes: &[u8] = payload.payload.as_ref();
            let row = decode(&mut bytes, &mut cells_left)?;
            let parents = validate(env, &row, &mut remaining)?;
            if native.parents(&row.name) != parents.as_slice() {
                return Err(RecordError::InvalidTelescope);
            }
            if entries.insert(row.name.clone(), row).is_some() {
                return Err(RecordError::DuplicateField);
            }
        }
        acyclic(&entries, entries.keys(), &mut remaining)?;
        Ok(Self { entries })
    }
}

/// Register an entire module only after all decoded metadata agrees with its
/// checked declarations. The source importer separately checks module ownership.
/// Existing equal entries are idempotent; conflicting identities are refused.
pub fn register(env: &Environment, rows: &[StructureEntry]) -> Result<Environment, RecordError> {
    if rows.is_empty() {
        return Ok(env.clone());
    }
    Activation::read(env)?
        .register(env, rows)
        .map(|(_, env)| env)
}

/// This private state is kept only by ImportActivation, whose other methods
/// cannot add constants or change either record journal. It avoids re-reading
/// every preceding module's interfaces on every later module registration.
#[derive(Debug)]
pub(crate) struct Activation {
    registry: ImportedStructures,
    native: super::inheritance::Registration,
    cells_left: usize,
    bytes_left: usize,
}

impl Activation {
    pub(crate) fn read(env: &Environment) -> Result<Self, RecordError> {
        let registry = ImportedStructures::read(env)?;
        let native = super::inheritance::Registration::read(env)?;
        let mut cells_left = MAX_CELLS;
        let mut bytes_left = MAX_BYTES;
        if let Some(extension) = env.extension(&extension_name()) {
            for entry in extension.entries() {
                bytes_left = bytes_left
                    .checked_sub(entry.payload.len())
                    .ok_or(RecordError::ResourceLimit)?;
            }
        }
        for row in registry.entries.values() {
            cells_left = cells_left
                .checked_sub(row.fields.len().saturating_add(row.parents.len()))
                .ok_or(RecordError::ResourceLimit)?;
        }
        Ok(Self {
            registry,
            native,
            cells_left,
            bytes_left,
        })
    }

    pub(crate) fn register(
        mut self,
        env: &Environment,
        rows: &[StructureEntry],
    ) -> Result<(Self, Environment), RecordError> {
        if rows.is_empty() {
            return Ok((self, env.clone()));
        }
        let mut remaining = MAX_NODES;
        let mut seen = BTreeSet::new();
        let mut payloads = Vec::new();
        let mut parents = Vec::new();
        for row in rows {
            tick(&mut remaining)?;
            if !seen.insert(row.name.clone()) {
                return Err(RecordError::DuplicateField);
            }
            if let Some(existing) = self.registry.entries.get(&row.name) {
                if existing != row {
                    return Err(RecordError::InvalidTelescope);
                }
                continue;
            }
            if self.registry.entries.len() >= MAX_ROWS {
                return Err(RecordError::ResourceLimit);
            }
            self.cells_left = self
                .cells_left
                .checked_sub(row.fields.len().saturating_add(row.parents.len()))
                .ok_or(RecordError::ResourceLimit)?;
            let expected_parents = validate(env, row, &mut remaining)?;
            if self
                .native
                .parents(&row.name)
                .iter()
                .any(|existing| !expected_parents.contains(existing))
            {
                return Err(RecordError::InvalidTelescope);
            }
            parents.extend(expected_parents);
            let payload = encode(row)?;
            self.bytes_left = self
                .bytes_left
                .checked_sub(payload.len())
                .ok_or(RecordError::ResourceLimit)?;
            payloads.push(payload);
            self.registry.entries.insert(row.name.clone(), row.clone());
        }
        // A new edge can reach an earlier record. Only that new edge's reachable
        // graph needs walking; the retained predecessor was already acyclic.
        acyclic(
            &self.registry.entries,
            rows.iter().map(|row| &row.name),
            &mut remaining,
        )?;
        let mut additions = Vec::new();
        for parent in parents {
            tick(&mut remaining)?;
            if let Some(existing) =
                self.native.parents(&parent.record).iter().find(|existing| {
                    existing.field == parent.field || existing.parent == parent.parent
                })
            {
                if existing != &parent {
                    return Err(RecordError::InvalidTelescope);
                }
            } else {
                additions.push(parent);
            }
        }
        let (native, mut out) = self.native.append(env, &additions)?;
        self.native = native;
        if !payloads.is_empty() && out.extension(&extension_name()).is_none() {
            out = out
                .register_extension(descriptor())
                .map_err(|_| RecordError::InvalidTelescope)?;
        }
        for payload in payloads {
            out = out
                .push_extension_entry(&extension_name(), payload)
                .map_err(|_| RecordError::InvalidTelescope)?;
        }
        Ok((self, out))
    }
}

#[cfg(test)]
mod tests;
