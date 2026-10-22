//! The pin's delaborator attributes, read from imported modules: structures tagged
//! `@[pp_using_anonymous_constructor]` (`Lean.ppUsingAnonymousConstructorAttr`), functions
//! tagged `@[pp_nodot]` (`Lean.ppNoDotAttr`), and the constants an `@[app_unexpander]`
//! (`Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute`) is registered for, vendored
//! `src/Lean/PrettyPrinter/Delaborator/{Attributes,Basic}.lean`.
//!
//! The printer reads them. A tagged structure prints as `⟨…⟩`, a tagged function never with
//! field notation, and an application of a key goes through compiled code this door does not
//! run, so it is never printed as a structure instance. An unexpander's own declaration is
//! not recorded: nothing here executes it. Each imported module contributes its own rows in
//! one entry. A malformed journal is refused, not read as empty.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNDLBT\x01";
const MAX_ROWS: usize = 65_536;
const MAX_TAGS: usize = 1 << 20;
const MAX_ENTRY_BYTES: usize = 16 << 20;

const ANONYMOUS_CONSTRUCTOR: u8 = 0;
const NODOT: u8 = 1;
const UNEXPANDER: u8 = 2;

/// One imported delaborator tag.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum DelaboratorTag {
    /// `@[pp_using_anonymous_constructor]` on a structure.
    AnonymousConstructor(Name),
    /// `@[pp_nodot]` on a function.
    NoDot(Name),
    /// An `@[app_unexpander]` registered for applications of this constant, `scoped` to the
    /// given namespace or global.
    Unexpander { key: Name, scope: Option<Name> },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DelaboratorTagError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    NotInductive(Name),
    Duplicate(Name),
}

impl std::fmt::Display for DelaboratorTagError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed delaborator tag journal"),
            Self::Limit => f.write_str("delaborator tag journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "a delaborator tag names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::NotInductive(name) => write!(
                f,
                "pp_using_anonymous_constructor tags {}, which is not an inductive type",
                name.to_display_string()
            ),
            Self::Duplicate(name) => write!(
                f,
                "{} carries the same delaborator tag twice",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for DelaboratorTagError {}

fn codec(error: InstanceRegistryError) -> DelaboratorTagError {
    match error {
        InstanceRegistryError::Limit => DelaboratorTagError::Limit,
        _ => DelaboratorTagError::Malformed,
    }
}

/// Native append-only identity, distinct from the pin's serialized extensions.
pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "delaboratorTags", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

fn validate(env: &Environment, tag: &DelaboratorTag) -> Result<(), DelaboratorTagError> {
    let name = match tag {
        DelaboratorTag::AnonymousConstructor(name)
        | DelaboratorTag::NoDot(name)
        | DelaboratorTag::Unexpander { key: name, .. } => name,
    };
    if name.is_anonymous() {
        return Err(DelaboratorTagError::Malformed);
    }
    match (tag, env.find(name)) {
        (_, None) => Err(DelaboratorTagError::UnknownDeclaration(name.clone())),
        (DelaboratorTag::AnonymousConstructor(_), Some(ConstantInfo::Induct(_))) => Ok(()),
        (DelaboratorTag::AnonymousConstructor(_), Some(_)) => {
            Err(DelaboratorTagError::NotInductive(name.clone()))
        }
        (_, Some(_)) => Ok(()),
    }
}

fn encode(tag: &DelaboratorTag, payload: &mut Vec<u8>) -> Result<(), DelaboratorTagError> {
    match tag {
        DelaboratorTag::AnonymousConstructor(name) => {
            payload.push(ANONYMOUS_CONSTRUCTOR);
            write_name(name, payload).map_err(codec)
        }
        DelaboratorTag::NoDot(name) => {
            payload.push(NODOT);
            write_name(name, payload).map_err(codec)
        }
        DelaboratorTag::Unexpander { key, scope } => {
            payload.push(UNEXPANDER);
            write_name(key, payload).map_err(codec)?;
            match scope {
                None => payload.push(0),
                Some(scope) => {
                    payload.push(1);
                    write_name(scope, payload).map_err(codec)?;
                }
            }
            Ok(())
        }
    }
}

fn decode(bytes: &mut &[u8]) -> Result<DelaboratorTag, DelaboratorTagError> {
    let (&kind, rest) = bytes.split_first().ok_or(DelaboratorTagError::Malformed)?;
    *bytes = rest;
    let name = read_name(bytes).map_err(codec)?;
    Ok(match kind {
        ANONYMOUS_CONSTRUCTOR => DelaboratorTag::AnonymousConstructor(name),
        NODOT => DelaboratorTag::NoDot(name),
        UNEXPANDER => {
            let (&scoped, rest) = bytes.split_first().ok_or(DelaboratorTagError::Malformed)?;
            *bytes = rest;
            let scope = match scoped {
                0 => None,
                1 => Some(read_name(bytes).map_err(codec)?),
                _ => return Err(DelaboratorTagError::Malformed),
            };
            DelaboratorTag::Unexpander { key: name, scope }
        }
        _ => return Err(DelaboratorTagError::Malformed),
    })
}

/// Append one imported module's tags. The importer checks that a tag attribute names this
/// module's own declaration; here every name must be admitted, and a structure tag must name
/// an inductive type. A tag repeated within the module is refused.
pub fn register_module(
    env: &Environment,
    tags: &[DelaboratorTag],
) -> Result<Environment, DelaboratorTagError> {
    if tags.is_empty() {
        return Ok(env.clone());
    }
    if tags.len() > MAX_TAGS {
        return Err(DelaboratorTagError::Limit);
    }
    let mut seen = BTreeSet::new();
    let mut payload = MAGIC.to_vec();
    payload.extend(
        u32::try_from(tags.len())
            .map_err(|_| DelaboratorTagError::Limit)?
            .to_le_bytes(),
    );
    for tag in tags {
        validate(env, tag)?;
        if !matches!(tag, DelaboratorTag::Unexpander { .. }) && !seen.insert(tag) {
            return Err(DelaboratorTagError::Duplicate(match tag {
                DelaboratorTag::AnonymousConstructor(name) | DelaboratorTag::NoDot(name) => {
                    name.clone()
                }
                DelaboratorTag::Unexpander { key, .. } => key.clone(),
            }));
        }
        encode(tag, &mut payload)?;
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(DelaboratorTagError::Limit);
        }
    }
    let env = match env.extension(&journal_name()) {
        Some(state) if state.descriptor != descriptor() => {
            return Err(DelaboratorTagError::Malformed);
        }
        Some(state) if state.len() >= MAX_ROWS => return Err(DelaboratorTagError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| DelaboratorTagError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| DelaboratorTagError::Malformed)
}

/// The imported delaborator tags in force.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DelaboratorTags {
    anonymous_constructor: BTreeSet<Name>,
    nodot: BTreeSet<Name>,
    unexpanded: BTreeSet<Name>,
}

impl DelaboratorTags {
    /// Validate and read every recorded tag. A `scoped` unexpander counts as registered
    /// whatever namespace is open, which only ever withholds a structure instance.
    pub fn read(env: &Environment) -> Result<Self, DelaboratorTagError> {
        let Some(extension) = env.extension(&journal_name()) else {
            return Ok(Self::default());
        };
        if extension.descriptor != descriptor() {
            return Err(DelaboratorTagError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(DelaboratorTagError::Limit);
        }
        let mut tags = Self::default();
        let mut total = 0usize;
        for entry in extension.entries() {
            if entry.payload.len() > MAX_ENTRY_BYTES {
                return Err(DelaboratorTagError::Limit);
            }
            let mut bytes = entry
                .payload
                .strip_prefix(MAGIC)
                .ok_or(DelaboratorTagError::Malformed)?;
            if bytes.len() < 4 {
                return Err(DelaboratorTagError::Malformed);
            }
            let (count, rest) = bytes.split_at(4);
            let count = u32::from_le_bytes(
                count
                    .try_into()
                    .map_err(|_| DelaboratorTagError::Malformed)?,
            );
            let count = usize::try_from(count).map_err(|_| DelaboratorTagError::Limit)?;
            if count == 0 {
                return Err(DelaboratorTagError::Malformed);
            }
            total = total.saturating_add(count);
            if total > MAX_TAGS {
                return Err(DelaboratorTagError::Limit);
            }
            bytes = rest;
            for _ in 0..count {
                let tag = decode(&mut bytes)?;
                validate(env, &tag)?;
                match tag {
                    DelaboratorTag::AnonymousConstructor(name) => {
                        if !tags.anonymous_constructor.insert(name.clone()) {
                            return Err(DelaboratorTagError::Duplicate(name));
                        }
                    }
                    DelaboratorTag::NoDot(name) => {
                        if !tags.nodot.insert(name.clone()) {
                            return Err(DelaboratorTagError::Duplicate(name));
                        }
                    }
                    DelaboratorTag::Unexpander { key, .. } => {
                        tags.unexpanded.insert(key);
                    }
                }
            }
            if !bytes.is_empty() {
                return Err(DelaboratorTagError::Malformed);
            }
        }
        Ok(tags)
    }

    /// Whether `structure` is tagged `@[pp_using_anonymous_constructor]`.
    pub fn anonymous_constructor(&self, structure: &Name) -> bool {
        self.anonymous_constructor.contains(structure)
    }

    /// Whether `function` is tagged `@[pp_nodot]`.
    pub fn nodot(&self, function: &Name) -> bool {
        self.nodot.contains(function)
    }

    /// Whether an `@[app_unexpander]` is registered for applications of `constant`.
    pub fn unexpanded(&self, constant: &Name) -> bool {
        self.unexpanded.contains(constant)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn malformed_rows_are_refused_not_read_as_empty() {
        for bytes in [
            vec![],
            MAGIC.to_vec(),
            [MAGIC, &1u32.to_le_bytes(), &[9]].concat(),
            [MAGIC, &0u32.to_le_bytes()].concat(),
        ] {
            let env = Environment::new()
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&journal_name(), bytes)
                .unwrap();
            assert!(DelaboratorTags::read(&env).is_err());
        }
    }

    #[test]
    fn a_tag_must_name_an_admitted_declaration() {
        let env = Environment::new();
        assert_eq!(
            register_module(&env, &[DelaboratorTag::NoDot(Name::from_components(["f"]))]),
            Err(DelaboratorTagError::UnknownDeclaration(
                Name::from_components(["f"])
            ))
        );
    }
}
