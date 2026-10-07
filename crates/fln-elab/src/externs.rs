//! Explicit native-call intentions retained from the pin's `Lean.externAttr`.
//!
//! These are attributes of declarations already admitted by the council, never
//! declaration authority or permission to run arbitrary native code. A compiler
//! must separately match the entire applicable entry and its supported ABI.
//! In particular, absence is not a default extern binding. The append-ordered
//! journal participates in ordinary environment identity and context replay.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::HashMap;
use std::convert::Infallible;

const MAGIC: &[u8] = b"FLNEXTERN\x01";
const MAX_ROWS: usize = 65_536;
const MAX_ENTRIES: usize = 4096;
const MAX_ENTRY_BYTES: usize = 65_536;

/// Every form of the pin's `ExternEntry`, retaining backend and text verbatim.
/// An unknown backend or symbol remains metadata, not a native implementation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternEntry {
    Adhoc { backend: Name },
    Inline { backend: Name, pattern: String },
    Standard { backend: Name, symbol: String },
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
}

impl std::fmt::Display for ExternError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native extern-attribute journal"),
            Self::Limit => f.write_str("native extern-attribute journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "an extern attribute names {}, which is not admitted",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for ExternError {}

/// Keep the caller's resource refusal intact, separate from malformed metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExternReadError<E> {
    Registry(ExternError),
    Budget(E),
}

impl<E> From<ExternError> for ExternReadError<E> {
    fn from(error: ExternError) -> Self {
        Self::Registry(error)
    }
}

fn codec(error: InstanceRegistryError) -> ExternError {
    match error {
        InstanceRegistryError::Limit => ExternError::Limit,
        _ => ExternError::Malformed,
    }
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "sourceExterns", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// Recognize this exact native journal contract, including replay semantics.
pub fn supports(descriptor_: &ExtensionDescriptor) -> bool {
    *descriptor_ == descriptor()
}

fn append(bytes: &mut Vec<u8>, added: &[u8]) -> Result<(), ExternError> {
    if bytes.len().saturating_add(added.len()) > MAX_ENTRY_BYTES {
        return Err(ExternError::Limit);
    }
    bytes
        .try_reserve(added.len())
        .map_err(|_| ExternError::Limit)?;
    bytes.extend_from_slice(added);
    Ok(())
}

fn write_backend(name: &Name, bytes: &mut Vec<u8>) -> Result<(), ExternError> {
    // Declaration names cannot be anonymous; backend names have no such rule.
    append(bytes, &[u8::from(!name.is_anonymous())])?;
    if !name.is_anonymous() {
        write_name(name, bytes).map_err(codec)?;
    }
    Ok(())
}

fn write_text(text: &str, bytes: &mut Vec<u8>) -> Result<(), ExternError> {
    if text.len().saturating_add(4).saturating_add(bytes.len()) > MAX_ENTRY_BYTES {
        return Err(ExternError::Limit);
    }
    let count = u32::try_from(text.len()).map_err(|_| ExternError::Limit)?;
    append(bytes, &count.to_le_bytes())?;
    append(bytes, text.as_bytes())
}

fn encode_entry(declaration: &Name, entries: &[ExternEntry]) -> Result<Vec<u8>, ExternError> {
    if entries.len() > MAX_ENTRIES {
        return Err(ExternError::Limit);
    }
    let mut bytes = MAGIC.to_vec();
    write_name(declaration, &mut bytes).map_err(codec)?;
    let count = u32::try_from(entries.len()).map_err(|_| ExternError::Limit)?;
    append(&mut bytes, &count.to_le_bytes())?;
    for entry in entries {
        match entry {
            ExternEntry::Adhoc { backend } => {
                append(&mut bytes, &[0])?;
                write_backend(backend, &mut bytes)?;
            }
            ExternEntry::Inline { backend, pattern } => {
                append(&mut bytes, &[1])?;
                write_backend(backend, &mut bytes)?;
                write_text(pattern, &mut bytes)?;
            }
            ExternEntry::Standard { backend, symbol } => {
                append(&mut bytes, &[2])?;
                write_backend(backend, &mut bytes)?;
                write_text(symbol, &mut bytes)?;
            }
            ExternEntry::Opaque => append(&mut bytes, &[3])?,
        }
    }
    Ok(bytes)
}

fn take<'a>(bytes: &mut &'a [u8], count: usize) -> Result<&'a [u8], ExternError> {
    if count > bytes.len() {
        return Err(ExternError::Malformed);
    }
    let (head, tail) = bytes.split_at(count);
    *bytes = tail;
    Ok(head)
}

fn count(bytes: &mut &[u8]) -> Result<usize, ExternError> {
    let value = u32::from_le_bytes(
        take(bytes, 4)?
            .try_into()
            .map_err(|_| ExternError::Malformed)?,
    );
    usize::try_from(value).map_err(|_| ExternError::Limit)
}

fn read_backend(bytes: &mut &[u8]) -> Result<Name, ExternError> {
    match take(bytes, 1)?[0] {
        0 => Ok(Name::anonymous()),
        1 => read_name(bytes).map_err(codec),
        _ => Err(ExternError::Malformed),
    }
}

fn read_text(bytes: &mut &[u8]) -> Result<String, ExternError> {
    let count = count(bytes)?;
    let text = std::str::from_utf8(take(bytes, count)?).map_err(|_| ExternError::Malformed)?;
    let mut value = String::new();
    value
        .try_reserve_exact(text.len())
        .map_err(|_| ExternError::Limit)?;
    value.push_str(text);
    Ok(value)
}

/// Decode one exact native journal row. This checks syntax and all bounds;
/// environment readers additionally require its declaration to be admitted.
pub fn decode_entry(payload: &[u8]) -> Result<(Name, Vec<ExternEntry>), ExternError> {
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(ExternError::Limit);
    }
    let mut bytes = payload;
    if take(&mut bytes, MAGIC.len())? != MAGIC {
        return Err(ExternError::Malformed);
    }
    let declaration = read_name(&mut bytes).map_err(codec)?;
    let count = count(&mut bytes)?;
    if count > MAX_ENTRIES {
        return Err(ExternError::Limit);
    }
    // Every entry has a tag: prove this minimum storage before allocating.
    if count > bytes.len() {
        return Err(ExternError::Malformed);
    }
    let mut entries = Vec::new();
    entries
        .try_reserve_exact(count)
        .map_err(|_| ExternError::Limit)?;
    for _ in 0..count {
        entries.push(match take(&mut bytes, 1)?[0] {
            0 => ExternEntry::Adhoc {
                backend: read_backend(&mut bytes)?,
            },
            1 => ExternEntry::Inline {
                backend: read_backend(&mut bytes)?,
                pattern: read_text(&mut bytes)?,
            },
            2 => ExternEntry::Standard {
                backend: read_backend(&mut bytes)?,
                symbol: read_text(&mut bytes)?,
            },
            3 => ExternEntry::Opaque,
            _ => return Err(ExternError::Malformed),
        });
    }
    if !bytes.is_empty() {
        return Err(ExternError::Malformed);
    }
    Ok((declaration, entries))
}

/// Append explicit metadata for an admitted declaration. A later registration
/// replaces the earlier list in full, as the pin's `NameMap.insert` does; an
/// empty list is retained and does not mean the declaration was unregistered.
/// Prior rows are validated by readers, rather than re-read on every append.
pub fn register(
    env: &Environment,
    declaration: &Name,
    entries: Vec<ExternEntry>,
) -> Result<Environment, ExternError> {
    if !env.contains(declaration) {
        return Err(ExternError::UnknownDeclaration(declaration.clone()));
    }
    let payload = encode_entry(declaration, &entries)?;
    let env = match env.extension(&journal_name()) {
        Some(state) if !supports(&state.descriptor) => return Err(ExternError::Malformed),
        Some(state) if state.len() >= MAX_ROWS => return Err(ExternError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| ExternError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| ExternError::Malformed)
}

/// Explicit last-write metadata only. No missing-name or backend defaults.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ExternTable {
    entries: HashMap<Name, Vec<ExternEntry>>,
}

impl ExternTable {
    pub fn read(env: &Environment) -> Result<Self, ExternError> {
        match Self::read_metered(env, |_| Ok::<(), Infallible>(())) {
            Ok(table) => Ok(table),
            Err(ExternReadError::Registry(error)) => Err(error),
            Err(ExternReadError::Budget(error)) => match error {},
        }
    }

    /// Charge before work: one lookup, all row visits before constructing the
    /// iterator, then each payload's bytes before parsing names, strings or tags.
    /// A compiler can retain a successful table for one immutable environment;
    /// a failed read returns no partial table and never silently means empty.
    pub fn read_metered<E>(
        env: &Environment,
        mut charge: impl FnMut(usize) -> Result<(), E>,
    ) -> Result<Self, ExternReadError<E>> {
        charge(1).map_err(ExternReadError::Budget)?;
        let Some(extension) = env.extension(&journal_name()) else {
            return Ok(Self::default());
        };
        if !supports(&extension.descriptor) {
            return Err(ExternError::Malformed.into());
        }
        if extension.len() > MAX_ROWS {
            return Err(ExternError::Limit.into());
        }
        charge(extension.len()).map_err(ExternReadError::Budget)?;
        let mut table = Self::default();
        for entry in extension.entries() {
            if entry.payload.len() > MAX_ENTRY_BYTES {
                return Err(ExternError::Limit.into());
            }
            charge(entry.payload.len()).map_err(ExternReadError::Budget)?;
            let (declaration, entries) = decode_entry(&entry.payload)?;
            if !env.contains(&declaration) {
                return Err(ExternError::UnknownDeclaration(declaration).into());
            }
            table
                .entries
                .try_reserve(1)
                .map_err(|_| ExternError::Limit)?;
            table.entries.insert(declaration, entries);
        }
        Ok(table)
    }

    pub fn get(&self, declaration: &Name) -> Option<&[ExternEntry]> {
        self.entries.get(declaration).map(Vec::as_slice)
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
