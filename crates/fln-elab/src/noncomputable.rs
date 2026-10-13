//! Source `noncomputable` declarations: the pin's `noncomputableExt` (vendored
//! `src/Lean/Compiler/NoncomputableAttr.lean`). A `noncomputable def` is checked but never
//! compiled. Code that must run (a computable definition, an `#eval`) may not depend on it: the
//! pin's "failed to compile definition, consider marking it as 'noncomputable' because it depends
//! on 'a'". Theorems and propositions may.
//!
//! One journal entry per source declaration, written once the council has admitted it. The tag
//! grants no declaration authority and only ever removes a declaration from the runtime catalog.
//! A name must be an admitted declaration and is tagged once. A malformed or foreign journal is
//! refused, never read as empty, which would let code depend on a noncomputable definition again.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNNONC\x01";
/// Native tag journal row capacity; exported errors retain this exact bound.
pub const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum NoncomputableError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    Duplicate(Name),
}

impl std::fmt::Display for NoncomputableError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native noncomputable journal"),
            Self::Limit => f.write_str("native noncomputable journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "a noncomputable tag names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::Duplicate(name) => {
                write!(
                    f,
                    "{} is tagged noncomputable twice",
                    name.to_display_string()
                )
            }
        }
    }
}
impl std::error::Error for NoncomputableError {}

fn codec(error: InstanceRegistryError) -> NoncomputableError {
    match error {
        InstanceRegistryError::Limit => NoncomputableError::Limit,
        _ => NoncomputableError::Malformed,
    }
}

fn extension_name() -> Name {
    Name::from_components(["FrankenLean", "sourceNoncomputable", "v1"])
}

/// The native journal's extension name, for a refusal that names it.
pub fn journal_name() -> Name {
    extension_name()
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: extension_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// Exact native journal supported by the pinned-format noncomputable tag writer.
pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

/// Tag one admitted source declaration noncomputable.
pub fn register(env: &Environment, name: &Name) -> Result<Environment, NoncomputableError> {
    if name.is_anonymous() {
        return Err(NoncomputableError::Malformed);
    }
    if !env.contains(name) {
        return Err(NoncomputableError::UnknownDeclaration(name.clone()));
    }
    let mut payload = MAGIC.to_vec();
    write_name(name, &mut payload).map_err(codec)?;
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(NoncomputableError::Limit);
    }
    let env = if env.extension(&extension_name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| NoncomputableError::Malformed)?
    } else {
        env.clone()
    };
    if env
        .extension(&extension_name())
        .is_some_and(|state| state.len() >= MAX_ROWS)
    {
        return Err(NoncomputableError::Limit);
    }
    env.push_extension_entry(&extension_name(), payload)
        .map_err(|_| NoncomputableError::Malformed)
}

/// Every noncomputable declaration the journal records. A name the environment does not hold,
/// or one tagged twice, is refused, never kept or dropped quietly.
pub fn read(env: &Environment) -> Result<BTreeSet<Name>, NoncomputableError> {
    let Some(extension) = env.extension(&extension_name()) else {
        return Ok(BTreeSet::new());
    };
    if extension.descriptor != descriptor() {
        return Err(NoncomputableError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(NoncomputableError::Limit);
    }
    let mut names = BTreeSet::new();
    for entry in extension.entries() {
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(NoncomputableError::Limit);
        }
        let mut bytes: &[u8] = &entry.payload;
        if bytes.len() < MAGIC.len() || &bytes[..MAGIC.len()] != MAGIC {
            return Err(NoncomputableError::Malformed);
        }
        bytes = &bytes[MAGIC.len()..];
        let name = read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty() {
            return Err(NoncomputableError::Malformed);
        }
        if !env.contains(&name) {
            return Err(NoncomputableError::UnknownDeclaration(name));
        }
        if !names.insert(name.clone()) {
            return Err(NoncomputableError::Duplicate(name));
        }
    }
    Ok(names)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

    fn with_axiom(env: &Environment, name: &str) -> Environment {
        env.add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::from_components([name]),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            is_unsafe: false,
        }))
        .unwrap()
    }

    #[test]
    fn tags_are_admitted_declarations_recorded_once() {
        let env = with_axiom(&with_axiom(&Environment::new(), "a"), "b");
        assert!(read(&env).unwrap().is_empty());
        let a = Name::from_components(["a"]);
        let env = register(&env, &a).unwrap();
        assert_eq!(read(&env).unwrap(), BTreeSet::from([a.clone()]));
        assert_eq!(
            register(&env, &Name::from_components(["missing"])),
            Err(NoncomputableError::UnknownDeclaration(
                Name::from_components(["missing"])
            ))
        );
        let twice = register(&env, &a).unwrap();
        assert_eq!(read(&twice), Err(NoncomputableError::Duplicate(a)));
    }
}
