//! Imported executable replacements from `Lean.Compiler.implementedByAttr`.
//!
//! The logical declarations remain unchanged. This journal records the pin's
//! compiler-only choice between already admitted constants; it grants neither
//! declaration authority nor an implementation for an unsupported runtime ABI.
//! Readers validate the whole journal, including overwritten rows, and resolve
//! replacement chains before any executable body is selected.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{HashMap, HashSet};
use std::convert::Infallible;

mod signature;

const MAGIC: &[u8] = b"FLNIMPLBY\x01";
const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;
const MAX_WORK: usize = 4_000_000;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplementedByError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    InvalidSignature {
        declaration: Name,
        implementation: Name,
    },
    SelfImplementation(Name),
    Cycle(Name),
}

impl std::fmt::Display for ImplementedByError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native implemented_by journal"),
            Self::Limit => f.write_str("native implemented_by journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "implemented_by names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::InvalidSignature {
                declaration,
                implementation,
            } => write!(
                f,
                "implemented_by target {} has a different type or universe arity from {}",
                implementation.to_display_string(),
                declaration.to_display_string()
            ),
            Self::SelfImplementation(name) => write!(
                f,
                "implemented_by declaration {} implements itself",
                name.to_display_string()
            ),
            Self::Cycle(name) => write!(
                f,
                "implemented_by replacement cycle at {}",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for ImplementedByError {}

/// Resource refusal from a compiler remains distinct from malformed metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImplementedByReadError<E> {
    Registry(ImplementedByError),
    Budget(E),
}

impl<E> From<ImplementedByError> for ImplementedByReadError<E> {
    fn from(error: ImplementedByError) -> Self {
        Self::Registry(error)
    }
}

fn codec(error: InstanceRegistryError) -> ImplementedByError {
    match error {
        InstanceRegistryError::Limit => ImplementedByError::Limit,
        _ => ImplementedByError::Malformed,
    }
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "sourceImplementedBy", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

pub fn supports(descriptor_: &ExtensionDescriptor) -> bool {
    *descriptor_ == descriptor()
}

fn encode_entry(declaration: &Name, implementation: &Name) -> Result<Vec<u8>, ImplementedByError> {
    let mut bytes = MAGIC.to_vec();
    write_name(declaration, &mut bytes).map_err(codec)?;
    write_name(implementation, &mut bytes).map_err(codec)?;
    Ok(bytes)
}

/// Exact native row syntax. This function alone says nothing about either
/// declaration's admission, type compatibility or executability.
pub fn decode_entry(payload: &[u8]) -> Result<(Name, Name), ImplementedByError> {
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(ImplementedByError::Limit);
    }
    let mut bytes = payload
        .strip_prefix(MAGIC)
        .ok_or(ImplementedByError::Malformed)?;
    let declaration = read_name(&mut bytes).map_err(codec)?;
    let implementation = read_name(&mut bytes).map_err(codec)?;
    if !bytes.is_empty() {
        return Err(ImplementedByError::Malformed);
    }
    Ok((declaration, implementation))
}

/// Append a compatible replacement without changing either logical constant.
/// As in the pin's parametric-attribute NameMap, a later row replaces an earlier
/// choice. Whole-journal readers additionally reject replacement cycles.
pub fn register(
    env: &Environment,
    declaration: &Name,
    implementation: &Name,
) -> Result<Environment, ImplementedByError> {
    let mut remaining = MAX_WORK;
    signature::validate(env, declaration, implementation, &mut |amount| {
        remaining = remaining
            .checked_sub(amount)
            .ok_or(ImplementedByError::Limit)?;
        Ok::<_, ImplementedByError>(())
    })?;
    let payload = encode_entry(declaration, implementation)?;
    let env = match env.extension(&journal_name()) {
        Some(state) if !supports(&state.descriptor) => return Err(ImplementedByError::Malformed),
        Some(state) if state.len() >= MAX_ROWS => return Err(ImplementedByError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| ImplementedByError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| ImplementedByError::Malformed)
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ImplementedByTable {
    entries: HashMap<Name, Name>,
    resolved: HashMap<Name, Name>,
}

impl ImplementedByTable {
    pub fn read(env: &Environment) -> Result<Self, ImplementedByError> {
        match Self::read_metered(env, |_| Ok::<_, Infallible>(())) {
            Ok(table) => Ok(table),
            Err(ImplementedByReadError::Registry(error)) => Err(error),
            Err(ImplementedByReadError::Budget(error)) => match error {},
        }
    }

    /// Charge payloads before decoding, and signature/chain visits before work.
    /// Failure returns no table, so it cannot silently mean "use logical code".
    pub fn read_metered<E>(
        env: &Environment,
        mut charge: impl FnMut(usize) -> Result<(), E>,
    ) -> Result<Self, ImplementedByReadError<E>> {
        let mut remaining = MAX_WORK;
        let mut spend = |amount| {
            remaining = remaining
                .checked_sub(amount)
                .ok_or(ImplementedByError::Limit)?;
            charge(amount).map_err(ImplementedByReadError::Budget)
        };
        spend(1)?;
        let Some(extension) = env.extension(&journal_name()) else {
            return Ok(Self::default());
        };
        if !supports(&extension.descriptor) {
            return Err(ImplementedByError::Malformed.into());
        }
        if extension.len() > MAX_ROWS {
            return Err(ImplementedByError::Limit.into());
        }
        spend(extension.len())?;
        let mut table = Self::default();
        for entry in extension.entries() {
            if entry.payload.len() > MAX_ENTRY_BYTES {
                return Err(ImplementedByError::Limit.into());
            }
            spend(entry.payload.len())?;
            let (declaration, implementation) = decode_entry(&entry.payload)?;
            signature::validate(env, &declaration, &implementation, &mut spend)?;
            table
                .entries
                .try_reserve(1)
                .map_err(|_| ImplementedByError::Limit)?;
            table.entries.insert(declaration, implementation);
        }
        table.resolve_chains(&mut spend)?;
        Ok(table)
    }

    fn resolve_chains<E: From<ImplementedByError>>(
        &mut self,
        spend: &mut impl FnMut(usize) -> Result<(), E>,
    ) -> Result<(), E> {
        spend(self.entries.len())?;
        let mut roots = Vec::new();
        roots
            .try_reserve_exact(self.entries.len())
            .map_err(|_| ImplementedByError::Limit)?;
        roots.extend(self.entries.keys().cloned());
        roots.sort_unstable();
        self.resolved
            .try_reserve(roots.len())
            .map_err(|_| ImplementedByError::Limit)?;
        for root in roots {
            let mut current = root;
            let mut path = Vec::new();
            let mut seen = HashSet::new();
            while let Some(next) = self.entries.get(&current) {
                spend(1)?;
                if let Some(terminal) = self.resolved.get(&current) {
                    current = terminal.clone();
                    break;
                }
                seen.try_reserve(1).map_err(|_| ImplementedByError::Limit)?;
                if !seen.insert(current.clone()) {
                    return Err(ImplementedByError::Cycle(current).into());
                }
                path.try_reserve(1).map_err(|_| ImplementedByError::Limit)?;
                path.push(current);
                current = next.clone();
            }
            for declaration in path {
                spend(1)?;
                self.resolved.insert(declaration, current.clone());
            }
        }
        Ok(())
    }

    /// The explicit one-step attribute parameter.
    pub fn get(&self, declaration: &Name) -> Option<&Name> {
        self.entries.get(declaration)
    }

    /// The final replacement, after validating every intermediate signature.
    pub fn implementation(&self, declaration: &Name) -> Option<&Name> {
        self.resolved.get(declaration)
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

#[cfg(test)]
mod tests;
