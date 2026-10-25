//! Explicit namespace registrations. An alias is a name-resolution edge and
//! does not register any namespace. This data-only journal also retains empty
//! namespaces and namespaces containing only re-exports across module imports.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNNS\x02";
const MAX_ROWS: usize = 65_536;
const MAX_NAMES: usize = 1 << 20;
const MAX_ENTRY_BYTES: usize = 16 << 20;

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "sourceNamespaces", "v2"])
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

/// Append one module's namespace registrations. Repetition across modules is
/// legal: namespace identity is a set, whereas the journal retains ownership.
/// No declaration is created or admitted by a registration.
pub fn register_module(
    env: &Environment,
    names: &[Name],
) -> Result<Environment, InstanceRegistryError> {
    if names.is_empty() {
        return Ok(env.clone());
    }
    if names.len() > MAX_NAMES {
        return Err(InstanceRegistryError::Limit);
    }
    let mut payload = MAGIC.to_vec();
    let mut seen = BTreeSet::new();
    for name in names {
        if !seen.insert(name) {
            return Err(InstanceRegistryError::Malformed);
        }
        // The generic declaration-name codec excludes the root namespace.
        // Version 2 tags it explicitly without widening that codec's domain.
        if name.is_anonymous() {
            payload.push(0);
        } else {
            payload.push(1);
            write_name(name, &mut payload)?;
        }
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
    }
    let env = if let Some(state) = env.extension(&journal_name()) {
        if !supports(&state.descriptor) {
            return Err(InstanceRegistryError::Malformed);
        }
        if state.len() >= MAX_ROWS {
            return Err(InstanceRegistryError::Limit);
        }
        env.clone()
    } else {
        env.register_extension(descriptor())
            .map_err(|_| InstanceRegistryError::Malformed)?
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| InstanceRegistryError::Malformed)
}

/// A source `namespace A.B` registers each entered prefix. Already registered
/// namespaces need no new local entry, as at the pinned public-import surface.
pub fn register_source(
    env: &Environment,
    namespace: &Name,
) -> Result<Environment, InstanceRegistryError> {
    if namespace.is_anonymous() {
        return Err(InstanceRegistryError::Malformed);
    }
    let inherited = read(env)?;
    let mut names = Vec::new();
    let mut current = namespace.clone();
    while !current.is_anonymous() {
        if !inherited.contains(&current) {
            names.push(current.clone());
        }
        current = current.parent();
    }
    register_module(env, &names)
}

#[derive(Debug, Default)]
pub struct Registrations {
    pub names: BTreeSet<Name>,
    pub work: usize,
    pub bytes_examined: usize,
}

/// Validate the complete journal and its inherited prefix before projecting
/// the module's additions. Limits charge inherited bytes too; malformed shared
/// metadata cannot become valid merely by appearing in both snapshots.
pub fn registrations(
    base: &Environment,
    result: &Environment,
    max_work: usize,
) -> Result<Registrations, InstanceRegistryError> {
    let prior = base.extension(&journal_name());
    let Some(current) = result.extension(&journal_name()) else {
        return if prior.is_some() {
            Err(InstanceRegistryError::Malformed)
        } else {
            Ok(Registrations::default())
        };
    };
    if !supports(&current.descriptor)
        || prior
            .is_some_and(|old| old.descriptor != current.descriptor || old.len() > current.len())
    {
        return Err(InstanceRegistryError::Malformed);
    }
    if current.len() > MAX_ROWS {
        return Err(InstanceRegistryError::Limit);
    }
    let inherited_count = prior.map_or(0, |old| old.len());
    let mut inherited = prior.map(|old| old.entries());
    let mut out = Registrations::default();
    for (index, row) in current.entries().enumerate() {
        let bytes = row.payload.len();
        out.work = out
            .work
            .checked_add(bytes.saturating_add(1))
            .filter(|work| *work <= max_work)
            .ok_or(InstanceRegistryError::Limit)?;
        out.bytes_examined = out
            .bytes_examined
            .checked_add(bytes)
            .ok_or(InstanceRegistryError::Limit)?;
        if bytes > MAX_ENTRY_BYTES {
            return Err(InstanceRegistryError::Limit);
        }
        if index < inherited_count && inherited.as_mut().and_then(Iterator::next) != Some(row) {
            return Err(InstanceRegistryError::Malformed);
        }
        let mut bytes = row
            .payload
            .strip_prefix(MAGIC)
            .filter(|bytes| !bytes.is_empty())
            .ok_or(InstanceRegistryError::Malformed)?;
        let mut seen = BTreeSet::new();
        while !bytes.is_empty() {
            let (tag, rest) = bytes
                .split_first()
                .ok_or(InstanceRegistryError::Malformed)?;
            bytes = rest;
            let name = match tag {
                0 => Name::anonymous(),
                1 => read_name(&mut bytes)?,
                _ => return Err(InstanceRegistryError::Malformed),
            };
            if !seen.insert(name.clone()) {
                return Err(InstanceRegistryError::Malformed);
            }
            if seen.len() > MAX_NAMES {
                return Err(InstanceRegistryError::Limit);
            }
            if index >= inherited_count {
                out.names.insert(name);
                if out.names.len() > MAX_NAMES {
                    return Err(InstanceRegistryError::Limit);
                }
            }
        }
    }
    Ok(out)
}

pub fn read(env: &Environment) -> Result<BTreeSet<Name>, InstanceRegistryError> {
    registrations(&Environment::new(), env, usize::MAX).map(|rows| rows.names)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_namespaces_are_data_and_module_suffixes_retain_ownership() {
        let empty = Environment::new();
        let a = Name::from_components(["Empty"]);
        let b = Name::str(a.clone(), "ReexportOnly");
        let base = register_module(&empty, std::slice::from_ref(&a)).unwrap();
        let next = register_module(&base, &[a.clone(), b.clone()]).unwrap();
        assert_eq!(read(&next).unwrap(), BTreeSet::from([a.clone(), b.clone()]));
        assert_eq!(
            registrations(&base, &next, usize::MAX).unwrap().names,
            BTreeSet::from([a, b])
        );
        assert_eq!(next.len(), 0);
        assert!(registrations(&base, &next, 0).is_err());
        assert!(registrations(&next, &base, usize::MAX).is_err());
    }

    #[test]
    fn malformed_versions_tags_duplicates_and_replaced_prefixes_are_refused() {
        let empty = Environment::new();
        assert!(register_source(&empty, &Name::anonymous()).is_err());
        let root = register_module(&empty, &[Name::anonymous()]).unwrap();
        assert_eq!(read(&root).unwrap(), BTreeSet::from([Name::anonymous()]));
        assert_eq!(root.len(), 0);
        assert!(register_module(&empty, &[Name::anonymous(), Name::anonymous()]).is_err());
        let a = Name::from_components(["A"]);
        let b = Name::from_components(["B"]);
        assert!(register_module(&empty, &[a.clone(), a.clone()]).is_err());
        let base = register_module(&empty, &[a]).unwrap();
        let foreign = register_module(&empty, &[b]).unwrap();
        assert!(registrations(&base, &foreign, usize::MAX).is_err());
        for payload in [
            b"FLNNS\x01\0".as_slice(),
            b"FLNNS\x03\0",
            b"FLNNS\x02",
            b"FLNNS\x02\x02",
            b"FLNNS\x02\0\0",
            b"FLNNS\x02\x01",
        ] {
            let malformed = empty
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&journal_name(), payload.to_vec())
                .unwrap();
            assert!(read(&malformed).is_err());
        }
    }
}
