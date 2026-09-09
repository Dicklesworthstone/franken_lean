//! Native source instance registrations, stored in the immutable environment.
//!
//! This versioned journal is not the Reference's serialized instance extension.
//! It contains references to already admitted declarations, never declarations
//! or proof authority. No negative cache outlives a search. Reading a malformed
//! journal is a refusal, not an empty instance set.

use fln_core::expr::{Expr, ExprNode};
use fln_core::name::{LeafView, Name};
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{BTreeMap, BTreeSet};

const MAGIC: &[u8] = b"FLNINST\x01";
const MAX_ROWS: usize = 16_384;
const MAX_ENTRY_BYTES: usize = 65_536;
const MAX_COMPONENTS: usize = 256;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InstanceRegistryError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    InvalidClass(Name),
    UnknownClass(Name),
    InvalidInstance(Name),
    DuplicateInstance(Name),
}

impl std::fmt::Display for InstanceRegistryError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native source instance registry"),
            Self::Limit => f.write_str("native source instance registry resource limit"),
            Self::UnknownDeclaration(n) => {
                write!(f, "unknown instance declaration {}", n.to_display_string())
            }
            Self::InvalidClass(n) => write!(
                f,
                "{} is not a supported class declaration",
                n.to_display_string()
            ),
            Self::UnknownClass(n) => {
                write!(f, "{} is not registered as a class", n.to_display_string())
            }
            Self::InvalidInstance(n) => {
                write!(f, "{} is not a safe class instance", n.to_display_string())
            }
            Self::DuplicateInstance(n) => write!(
                f,
                "instance {} is already registered",
                n.to_display_string()
            ),
        }
    }
}
impl std::error::Error for InstanceRegistryError {}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InstanceEntry {
    pub declaration: Name,
    pub priority: u32,
    /// Monotone registration order; newer equal-priority entries are tried first.
    pub order: usize,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct InstanceRegistry {
    classes: BTreeSet<Name>,
    instances: BTreeMap<Name, Vec<InstanceEntry>>,
}

fn extension_name() -> Name {
    Name::from_components(["FrankenLean", "sourceInstances", "v1"])
}
fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: extension_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// Syntactic result head, bounded and metadata-transparent. Alias class heads
/// require normalization by the elaborator, not a guess by the registry.
pub fn result_head(expr: &Expr) -> Option<Name> {
    let mut current = expr;
    for _ in 0..MAX_ENTRY_BYTES {
        match current.node() {
            ExprNode::ForallE { body, .. } | ExprNode::MData { expr: body, .. } => current = body,
            ExprNode::App { f, .. } => current = f,
            ExprNode::Const { name, .. } => return Some(name.clone()),
            _ => return None,
        }
    }
    None
}

impl InstanceRegistry {
    pub fn read(env: &Environment) -> Result<Self, InstanceRegistryError> {
        let Some(extension) = env.extension(&extension_name()) else {
            return Ok(Self::default());
        };
        if extension.descriptor != descriptor() {
            return Err(InstanceRegistryError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(InstanceRegistryError::Limit);
        }
        let mut out = Self::default();
        let mut seen = BTreeSet::new();
        for (order, entry) in extension.entries().enumerate() {
            if entry.payload.len() > MAX_ENTRY_BYTES {
                return Err(InstanceRegistryError::Limit);
            }
            let mut bytes: &[u8] = &entry.payload;
            if take(&mut bytes, MAGIC.len())? != MAGIC {
                return Err(InstanceRegistryError::Malformed);
            }
            let tag = take(&mut bytes, 1)?[0];
            let class = read_name(&mut bytes)?;
            match tag {
                0 => {
                    validate_class(env, &class)?;
                    if !out.classes.insert(class) {
                        return Err(InstanceRegistryError::Malformed);
                    }
                }
                1 => {
                    let declaration = read_name(&mut bytes)?;
                    let priority = u32::from_le_bytes(
                        take(&mut bytes, 4)?
                            .try_into()
                            .map_err(|_| InstanceRegistryError::Malformed)?,
                    );
                    if !out.classes.contains(&class) || !seen.insert(declaration.clone()) {
                        return Err(InstanceRegistryError::Malformed);
                    }
                    if validate_instance(env, &declaration)? != class {
                        return Err(InstanceRegistryError::Malformed);
                    }
                    out.instances.entry(class).or_default().push(InstanceEntry {
                        declaration,
                        priority,
                        order,
                    });
                }
                _ => return Err(InstanceRegistryError::Malformed),
            }
            if !bytes.is_empty() {
                return Err(InstanceRegistryError::Malformed);
            }
        }
        for entries in out.instances.values_mut() {
            entries.sort_by(|a, b| {
                b.priority
                    .cmp(&a.priority)
                    .then_with(|| b.order.cmp(&a.order))
            });
        }
        Ok(out)
    }
    pub fn is_class(&self, name: &Name) -> bool {
        self.classes.contains(name)
    }
    pub fn candidates(&self, class: &Name) -> &[InstanceEntry] {
        self.instances.get(class).map_or(&[], Vec::as_slice)
    }
}

fn validate_class(env: &Environment, name: &Name) -> Result<(), InstanceRegistryError> {
    match env.find(name) {
        Some(ConstantInfo::Induct(value)) if !value.is_unsafe && value.num_indices == 0 => Ok(()),
        _ => Err(InstanceRegistryError::InvalidClass(name.clone())),
    }
}
fn validate_instance(env: &Environment, name: &Name) -> Result<Name, InstanceRegistryError> {
    let info = env
        .find(name)
        .ok_or_else(|| InstanceRegistryError::UnknownDeclaration(name.clone()))?;
    let safe = match info {
        ConstantInfo::Defn(value) => value.safety == DefinitionSafety::Safe,
        ConstantInfo::Thm(_) => true,
        ConstantInfo::Opaque(value) => !value.is_unsafe,
        ConstantInfo::Axiom(value) => !value.is_unsafe,
        _ => false,
    };
    if !safe {
        return Err(InstanceRegistryError::InvalidInstance(name.clone()));
    }
    result_head(&info.constant_val().type_)
        .ok_or_else(|| InstanceRegistryError::InvalidInstance(name.clone()))
}

fn append(env: &Environment, payload: Vec<u8>) -> Result<Environment, InstanceRegistryError> {
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(InstanceRegistryError::Limit);
    }
    let env = if env.extension(&extension_name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| InstanceRegistryError::Malformed)?
    } else {
        env.clone()
    };
    if env
        .extension(&extension_name())
        .is_some_and(|state| state.len() >= MAX_ROWS)
    {
        return Err(InstanceRegistryError::Limit);
    }
    env.push_extension_entry(&extension_name(), payload)
        .map_err(|_| InstanceRegistryError::Malformed)
}

pub fn register_class(
    env: &Environment,
    class: &Name,
) -> Result<Environment, InstanceRegistryError> {
    let registry = InstanceRegistry::read(env)?;
    validate_class(env, class)?;
    if registry.is_class(class) {
        return Ok(env.clone());
    }
    let mut payload = MAGIC.to_vec();
    payload.push(0);
    write_name(class, &mut payload)?;
    append(env, payload)
}

/// Register an already admitted safe declaration; never admit or execute it.
pub fn register_instance(
    env: &Environment,
    declaration: &Name,
    priority: u32,
) -> Result<Environment, InstanceRegistryError> {
    let registry = InstanceRegistry::read(env)?;
    let class = validate_instance(env, declaration)?;
    if !registry.is_class(&class) {
        return Err(InstanceRegistryError::UnknownClass(class));
    }
    if registry
        .candidates(&class)
        .iter()
        .any(|row| &row.declaration == declaration)
    {
        return Err(InstanceRegistryError::DuplicateInstance(
            declaration.clone(),
        ));
    }
    let mut payload = MAGIC.to_vec();
    payload.push(1);
    write_name(&class, &mut payload)?;
    write_name(declaration, &mut payload)?;
    payload.extend(priority.to_le_bytes());
    append(env, payload)
}

fn take<'a>(bytes: &mut &'a [u8], n: usize) -> Result<&'a [u8], InstanceRegistryError> {
    if n > bytes.len() {
        return Err(InstanceRegistryError::Malformed);
    }
    let (head, tail) = bytes.split_at(n);
    *bytes = tail;
    Ok(head)
}
fn write_name(name: &Name, out: &mut Vec<u8>) -> Result<(), InstanceRegistryError> {
    let mut parts = Vec::new();
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        if parts.len() >= MAX_COMPONENTS {
            return Err(InstanceRegistryError::Limit);
        }
        parts.push(cursor.clone());
        cursor = cursor.parent();
    }
    if parts.is_empty() {
        return Err(InstanceRegistryError::Malformed);
    }
    out.extend(
        u16::try_from(parts.len())
            .map_err(|_| InstanceRegistryError::Limit)?
            .to_le_bytes(),
    );
    for part in parts.into_iter().rev() {
        match part.leaf_view() {
            LeafView::Str(s) => {
                if s.len() > MAX_ENTRY_BYTES {
                    return Err(InstanceRegistryError::Limit);
                }
                out.push(0);
                out.extend(
                    u32::try_from(s.len())
                        .map_err(|_| InstanceRegistryError::Limit)?
                        .to_le_bytes(),
                );
                out.extend(s.as_bytes());
            }
            LeafView::Num(v) => {
                out.push(if part.component_overflowed() { 2 } else { 1 });
                out.extend(v.to_le_bytes());
            }
            LeafView::Anonymous => return Err(InstanceRegistryError::Malformed),
        }
        if out.len() > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
    }
    Ok(())
}
fn read_name(bytes: &mut &[u8]) -> Result<Name, InstanceRegistryError> {
    let count = usize::from(u16::from_le_bytes(
        take(bytes, 2)?
            .try_into()
            .map_err(|_| InstanceRegistryError::Malformed)?,
    ));
    if count == 0 || count > MAX_COMPONENTS {
        return Err(InstanceRegistryError::Malformed);
    }
    let mut name = Name::anonymous();
    for _ in 0..count {
        match take(bytes, 1)?[0] {
            0 => {
                let len = u32::from_le_bytes(
                    take(bytes, 4)?
                        .try_into()
                        .map_err(|_| InstanceRegistryError::Malformed)?,
                );
                let text = std::str::from_utf8(take(
                    bytes,
                    usize::try_from(len).map_err(|_| InstanceRegistryError::Malformed)?,
                )?)
                .map_err(|_| InstanceRegistryError::Malformed)?;
                name = Name::str(name, text);
            }
            1 => {
                name = Name::num(
                    name,
                    u64::from_le_bytes(
                        take(bytes, 8)?
                            .try_into()
                            .map_err(|_| InstanceRegistryError::Malformed)?,
                    ),
                )
            }
            2 => {
                name = Name::num_overflowing(
                    name,
                    u64::from_le_bytes(
                        take(bytes, 8)?
                            .try_into()
                            .map_err(|_| InstanceRegistryError::Malformed)?,
                    ),
                )
            }
            _ => return Err(InstanceRegistryError::Malformed),
        }
    }
    Ok(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn registry_name_codec_preserves_structural_identity() {
        let names = [
            Name::from_components(["a.b"]),
            Name::from_components(["a", "b"]),
            Name::from_components(["a", "2"]),
            Name::num(Name::from_components(["a"]), 2),
            Name::num_overflowing(Name::from_components(["a"]), 2),
        ];
        let mut encodings = BTreeSet::new();
        for name in names {
            let mut bytes = Vec::new();
            write_name(&name, &mut bytes).unwrap();
            let mut input = bytes.as_slice();
            assert_eq!(read_name(&mut input).unwrap(), name);
            assert!(input.is_empty());
            assert!(encodings.insert(bytes));
        }
    }
    #[test]
    fn malformed_or_foreign_registry_is_not_an_empty_candidate_set() {
        for payload in [Vec::new(), b"FLNINST\x02".to_vec(), [MAGIC, &[9]].concat()] {
            let env = Environment::new()
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&extension_name(), payload)
                .unwrap();
            assert!(InstanceRegistry::read(&env).is_err());
        }
        let mut wrong = descriptor();
        wrong.provenance = PayloadProvenance::Opaque;
        let env = Environment::new().register_extension(wrong).unwrap();
        assert_eq!(
            InstanceRegistry::read(&env),
            Err(InstanceRegistryError::Malformed)
        );
    }
    #[test]
    fn empty_or_unadmitted_registrations_cannot_supply_instances() {
        let env = Environment::new();
        let name = Name::from_components(["absent"]);
        assert!(register_class(&env, &name).is_err());
        assert!(register_instance(&env, &name, 1000).is_err());
        assert!(
            InstanceRegistry::read(&env)
                .unwrap()
                .candidates(&name)
                .is_empty()
        );
    }
}
