//! The pin's `[unbox]` tag (`Lean/Compiler/IR/UnboxResult.lean`). It is global,
//! applies only to nonrecursive inductive types in the owning module, and is
//! persistent. At this pin the tag has no effect on generated code or layout.
//!
//! Source and imported tags share this validated journal. Module ownership is
//! checked by their respective admission drivers; recording a tag grants no
//! declaration authority. Repeating a source tag is idempotent, as for NameSet.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNUNBX\x01";
pub const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum UnboxError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    NotInductive(Name),
    RecursiveInductive(Name),
}

impl std::fmt::Display for UnboxError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native unbox journal"),
            Self::Limit => f.write_str("native unbox journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "an unbox tag names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::NotInductive(name) => write!(
                f,
                "[unbox] can only be added to inductive types: {}",
                name.to_display_string()
            ),
            Self::RecursiveInductive(name) => write!(
                f,
                "[unbox] does not support recursive inductive types: {}",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for UnboxError {}

fn codec(error: InstanceRegistryError) -> UnboxError {
    match error {
        InstanceRegistryError::Limit => UnboxError::Limit,
        _ => UnboxError::Malformed,
    }
}

pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "unbox", "v1"])
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

fn validate(env: &Environment, name: &Name) -> Result<(), UnboxError> {
    if name.is_anonymous() {
        return Err(UnboxError::Malformed);
    }
    match env.find(name) {
        Some(ConstantInfo::Induct(value)) if !value.is_rec => Ok(()),
        Some(ConstantInfo::Induct(_)) => Err(UnboxError::RecursiveInductive(name.clone())),
        Some(_) => Err(UnboxError::NotInductive(name.clone())),
        None => Err(UnboxError::UnknownDeclaration(name.clone())),
    }
}

/// Tag one admitted, nonrecursive inductive. Existing tags are retained once.
pub fn register(env: &Environment, name: &Name) -> Result<Environment, UnboxError> {
    validate(env, name)?;
    if read(env)?.contains(name) {
        return Ok(env.clone());
    }
    let mut payload = MAGIC.to_vec();
    write_name(name, &mut payload).map_err(codec)?;
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(UnboxError::Limit);
    }
    let env = match env.extension(&journal_name()) {
        Some(state) if state.len() >= MAX_ROWS => return Err(UnboxError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| UnboxError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| UnboxError::Malformed)
}

/// Read tags against the exact declaration environment that admitted each row.
/// Projection-hidden declarations are validated there, then omitted here.
pub fn read(env: &Environment) -> Result<BTreeSet<Name>, UnboxError> {
    let Some(extension) = env.extension(&journal_name()) else {
        return Ok(BTreeSet::new());
    };
    if extension.descriptor != descriptor() {
        return Err(UnboxError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(UnboxError::Limit);
    }
    let mut names = BTreeSet::new();
    for (entry, validation) in env.metadata_validation_entries(&journal_name()) {
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(UnboxError::Limit);
        }
        let mut bytes = entry
            .payload
            .strip_prefix(MAGIC)
            .ok_or(UnboxError::Malformed)?;
        let name = read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty() || !names.insert(name.clone()) {
            return Err(UnboxError::Malformed);
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
    use fln_env::constants::{AxiomVal, ConstantVal, InductiveVal};

    fn n(value: &str) -> Name {
        Name::from_components([value])
    }

    fn inductive(env: &Environment, name: &str, recursive: bool) -> Environment {
        env.add_decl(ConstantInfo::Induct(InductiveVal {
            base: ConstantVal {
                name: n(name),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            num_params: 0,
            num_indices: 0,
            all: vec![n(name)],
            ctors: Vec::new(),
            num_nested: 0,
            is_rec: recursive,
            is_unsafe: false,
            is_reflexive: false,
        }))
        .unwrap()
    }

    #[test]
    fn unbox_tags_are_validated_and_idempotent() {
        let env = inductive(&inductive(&Environment::new(), "Box", false), "List", true);
        let env = register(&env, &n("Box")).unwrap();
        let repeated = register(&env, &n("Box")).unwrap();
        assert_eq!(read(&repeated).unwrap(), BTreeSet::from([n("Box")]));
        assert_eq!(repeated.extension(&journal_name()).unwrap().len(), 1);
        assert_eq!(
            register(&env, &n("List")),
            Err(UnboxError::RecursiveInductive(n("List")))
        );
        assert_eq!(
            register(&env, &n("missing")),
            Err(UnboxError::UnknownDeclaration(n("missing")))
        );
        let axiom = env
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n("A"),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap();
        assert_eq!(
            register(&axiom, &n("A")),
            Err(UnboxError::NotInductive(n("A")))
        );
    }

    #[test]
    fn malformed_unbox_journal_is_never_read_as_empty_or_repaired() {
        let env = inductive(&Environment::new(), "Box", false)
            .register_extension(descriptor())
            .unwrap()
            .push_extension_entry(&journal_name(), b"broken".to_vec())
            .unwrap();
        assert_eq!(read(&env), Err(UnboxError::Malformed));
        assert_eq!(register(&env, &n("Box")), Err(UnboxError::Malformed));
    }
}
