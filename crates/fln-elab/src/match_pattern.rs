//! Persistent `[match_pattern]` declarations, as in the pin's
//! `Lean/Meta/Match/MatchPatternAttr.lean`. A tag authorizes pattern elaboration
//! to unfold an exposed definition; it does not authorize a declaration or
//! make an arbitrary reduced expression a constructor pattern.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNMPAT\x01";
pub const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MatchPatternError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    NotDefinition(Name),
}

impl std::fmt::Display for MatchPatternError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native match_pattern journal"),
            Self::Limit => f.write_str("native match_pattern journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "a match_pattern tag names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::NotDefinition(name) => write!(
                f,
                "[match_pattern] requires an exposed definition: {}",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for MatchPatternError {}

fn codec(error: InstanceRegistryError) -> MatchPatternError {
    match error {
        InstanceRegistryError::Limit => MatchPatternError::Limit,
        _ => MatchPatternError::Malformed,
    }
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "matchPattern", "v1"])
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

fn validate(env: &Environment, name: &Name) -> Result<(), MatchPatternError> {
    if name.is_anonymous() {
        return Err(MatchPatternError::Malformed);
    }
    match env.find(name) {
        Some(ConstantInfo::Defn(_)) => Ok(()),
        Some(_) => Err(MatchPatternError::NotDefinition(name.clone())),
        None => Err(MatchPatternError::UnknownDeclaration(name.clone())),
    }
}

/// Register a global tag in the declaration's owning module. Ownership is
/// enforced by the source/import driver. As at the pin, tagging is idempotent
/// and does not require the definition to reduce to a usable pattern yet.
pub fn register(env: &Environment, name: &Name) -> Result<Environment, MatchPatternError> {
    validate(env, name)?;
    if read(env)?.contains(name) {
        return Ok(env.clone());
    }
    let mut payload = MAGIC.to_vec();
    write_name(name, &mut payload).map_err(codec)?;
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(MatchPatternError::Limit);
    }
    let env = match env.extension(&journal_name()) {
        Some(state) if state.len() >= MAX_ROWS => return Err(MatchPatternError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| MatchPatternError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| MatchPatternError::Malformed)
}

/// Validate each row against its admission environment before projecting the
/// visible names. Consumers must still require a currently exposed body: a
/// public opaque projection is never permission to recover a hidden definition.
pub fn read(env: &Environment) -> Result<BTreeSet<Name>, MatchPatternError> {
    let Some(extension) = env.extension(&journal_name()) else {
        return Ok(BTreeSet::new());
    };
    if extension.descriptor != descriptor() {
        return Err(MatchPatternError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(MatchPatternError::Limit);
    }
    let mut names = BTreeSet::new();
    for (entry, validation) in env.metadata_validation_entries(&journal_name()) {
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(MatchPatternError::Limit);
        }
        let mut bytes = entry
            .payload
            .strip_prefix(MAGIC)
            .ok_or(MatchPatternError::Malformed)?;
        let name = read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty() || !names.insert(name.clone()) {
            return Err(MatchPatternError::Malformed);
        }
        validate(validation, &name)?;
    }
    names.retain(|name| env.contains(name));
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::{expr::Expr, level::Level};
    use fln_env::constants::{
        AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    fn definition() -> (Environment, Name) {
        let name = Name::from_components(["alias"]);
        let env = Environment::new()
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
                all: vec![name.clone()],
            }))
            .unwrap();
        (env, name)
    }

    #[test]
    fn tags_require_definitions_and_are_idempotent() {
        let (env, name) = definition();
        let env = register(&env, &name).unwrap();
        let env = register(&env, &name).unwrap();
        assert_eq!(read(&env).unwrap(), BTreeSet::from([name]));
        assert_eq!(env.extension(&journal_name()).unwrap().len(), 1);
        let name = Name::from_components(["axiom"]);
        let env = env
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap();
        assert_eq!(
            register(&env, &name),
            Err(MatchPatternError::NotDefinition(name))
        );
    }

    #[test]
    fn malformed_rows_never_become_empty_or_get_repaired() {
        let (env, name) = definition();
        let env = env
            .register_extension(descriptor())
            .unwrap()
            .push_extension_entry(&journal_name(), b"broken".to_vec())
            .unwrap();
        assert_eq!(read(&env), Err(MatchPatternError::Malformed));
        assert_eq!(register(&env, &name), Err(MatchPatternError::Malformed));
    }
}
