//! Persistent `[never_extract]` tags from `Lean/Compiler/NeverExtractAttr.lean`.
//! The pin prevents closed-call extraction and common-subexpression elimination.
//! Native FIR already preserves call multiplicity; these tags retain that policy
//! across source and physical module boundaries, including internal helper names.
//! The tag grants no declaration or executable-symbol authority.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::{LeafView, Name};
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNNEXT\x01";
pub const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NeverExtractError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
}

impl std::fmt::Display for NeverExtractError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native never_extract journal"),
            Self::Limit => f.write_str("native never_extract journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "a never_extract tag names {}, which is not admitted",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for NeverExtractError {}

fn codec(error: InstanceRegistryError) -> NeverExtractError {
    match error {
        InstanceRegistryError::Limit => NeverExtractError::Limit,
        _ => NeverExtractError::Malformed,
    }
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "neverExtract", "v1"])
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

fn validate(env: &Environment, name: &Name) -> Result<(), NeverExtractError> {
    if name.is_anonymous() {
        return Err(NeverExtractError::Malformed);
    }
    if !env.contains(name) {
        return Err(NeverExtractError::UnknownDeclaration(name.clone()));
    }
    Ok(())
}

/// Tag any admitted declaration once. Source/import drivers enforce global
/// scope and ownership; unlike several compiler tags, the pin restricts no kind.
pub fn register(env: &Environment, name: &Name) -> Result<Environment, NeverExtractError> {
    validate(env, name)?;
    if read(env)?.contains(name) {
        return Ok(env.clone());
    }
    let mut payload = MAGIC.to_vec();
    write_name(name, &mut payload).map_err(codec)?;
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(NeverExtractError::Limit);
    }
    let env = match env.extension(&journal_name()) {
        Some(state) if state.len() >= MAX_ROWS => return Err(NeverExtractError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| NeverExtractError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| NeverExtractError::Malformed)
}

/// Validate each row in its admission environment, then project visible names.
pub fn read(env: &Environment) -> Result<BTreeSet<Name>, NeverExtractError> {
    let Some(extension) = env.extension(&journal_name()) else {
        return Ok(BTreeSet::new());
    };
    if extension.descriptor != descriptor() {
        return Err(NeverExtractError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(NeverExtractError::Limit);
    }
    let mut names = BTreeSet::new();
    for (entry, validation) in env.metadata_validation_entries(&journal_name()) {
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(NeverExtractError::Limit);
        }
        let mut bytes = entry
            .payload
            .strip_prefix(MAGIC)
            .ok_or(NeverExtractError::Malformed)?;
        let name = read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty() || !names.insert(name.clone()) {
            return Err(NeverExtractError::Malformed);
        }
        validate(validation, &name)?;
    }
    names.retain(|name| env.contains(name));
    Ok(names)
}

/// The pin's `hasNeverExtractAttribute`: internal helpers inherit an enclosing
/// tag. Ordinary dotted children do not. Two bounded, iterative name walks avoid
/// recursive host calls and repeatedly rescanning prefixes of deep names.
pub fn has_tag(env: &Environment, name: &Name) -> Result<bool, NeverExtractError> {
    let names = read(env)?;
    if names.contains(name) {
        return Ok(true);
    }
    let mut cursor = name.clone();
    let mut stop = None;
    let mut depth = 0;
    while !cursor.is_anonymous() {
        if depth >= MAX_ENTRY_BYTES {
            return Err(NeverExtractError::Limit);
        }
        depth += 1;
        if matches!(cursor.leaf_view(), LeafView::Str(part) if part.starts_with('_')) {
            stop = Some(cursor.parent());
        }
        cursor = cursor.parent();
    }
    let Some(stop) = stop else {
        return Ok(false);
    };
    let mut cursor = name.clone();
    loop {
        if names.contains(&cursor) {
            return Ok(true);
        }
        if cursor == stop {
            return Ok(false);
        }
        cursor = cursor.parent();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::{expr::Expr, level::Level};
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

    fn n(value: &str) -> Name {
        Name::from_components(value.split('.'))
    }

    fn environment() -> Environment {
        Environment::new()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n("effect"),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap()
    }

    #[test]
    fn tags_accept_axioms_and_inherit_only_through_internal_names() {
        let env = register(&environment(), &n("effect")).unwrap();
        let env = register(&env, &n("effect")).unwrap();
        assert_eq!(env.extension(&journal_name()).unwrap().len(), 1);
        for name in [
            n("effect"),
            n("effect._lambda"),
            n("effect._lambda.child"),
            Name::num(n("effect._lambda"), 3),
        ] {
            assert!(has_tag(&env, &name).unwrap(), "{name:?}");
        }
        for name in [
            n("effect.child"),
            Name::num(n("effect"), 3),
            n("unrelated._lambda"),
        ] {
            assert!(!has_tag(&env, &name).unwrap(), "{name:?}");
        }
        assert_eq!(
            register(&env, &n("missing")),
            Err(NeverExtractError::UnknownDeclaration(n("missing")))
        );
    }

    #[test]
    fn malformed_or_unknown_rows_never_grant_a_policy() {
        let base = environment();
        let mut unknown = MAGIC.to_vec();
        write_name(&n("missing"), &mut unknown).unwrap();
        for payload in [b"broken".to_vec(), unknown] {
            let env = base
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&journal_name(), payload)
                .unwrap();
            assert!(read(&env).is_err());
            assert!(has_tag(&env, &n("effect")).is_err());
            assert!(register(&env, &n("effect")).is_err());
        }
    }
}
