//! Auxiliary-recursion metadata from admitted native generators and the pin's
//! `Lean.auxRecExt` (`src/Lean/AuxRecursor.lean`). The tag authorizes the
//! elaborator's dependent-eliminator treatment, never declaration admission.
//!
//! There is no source attribute for these tags and no suffix-based inference:
//! an ordinary user definition called `casesOn` is still an ordinary function.
//! Each imported module contributes only its own tags after both checking seats
//! admitted its declarations. A malformed journal is refused, not read as empty.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNAUXR\x01";
const MAX_ROWS: usize = 65_536;
const MAX_NAMES: usize = 1 << 20;
const MAX_ENTRY_BYTES: usize = 16 << 20;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AuxRecursorError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    NotDefinition(Name),
    Duplicate(Name),
}

impl std::fmt::Display for AuxRecursorError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native auxiliary-recursor journal"),
            Self::Limit => f.write_str("native auxiliary-recursor journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "auxiliary recursor {} is not admitted",
                name.to_display_string()
            ),
            Self::NotDefinition(name) => write!(
                f,
                "auxiliary recursor {} is not a definition",
                name.to_display_string()
            ),
            Self::Duplicate(name) => write!(
                f,
                "{} is tagged as an auxiliary recursor twice",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for AuxRecursorError {}

fn codec(error: InstanceRegistryError) -> AuxRecursorError {
    match error {
        InstanceRegistryError::Limit => AuxRecursorError::Limit,
        _ => AuxRecursorError::Malformed,
    }
}

/// Native append-only identity, distinct from the pin's serialized extension.
pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "sourceAuxRecursors", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// Whether a journal can be exported as the pin's `Lean.auxRecExt` tag array.
pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}

pub fn journal_digest(env: &Environment) -> Option<[u8; 32]> {
    env.extension(&journal_name())
        .map(|extension| extension.content_digest().0)
}

fn validate(env: &Environment, name: &Name) -> Result<(), AuxRecursorError> {
    if name.is_anonymous() {
        return Err(AuxRecursorError::Malformed);
    }
    match env.find(name) {
        Some(ConstantInfo::Defn(_)) => Ok(()),
        Some(_) => Err(AuxRecursorError::NotDefinition(name.clone())),
        None => Err(AuxRecursorError::UnknownDeclaration(name.clone())),
    }
}

/// Append the tags of one checked module or one admitted native generation
/// batch. The source importer separately checks module ownership. Repeated names
/// within this batch fail immediately; repeats across batches are refused by
/// [`AuxRecursors::read`] without rereading the whole journal for every module.
pub fn register_module(env: &Environment, names: &[Name]) -> Result<Environment, AuxRecursorError> {
    if names.is_empty() {
        return Ok(env.clone());
    }
    if names.len() > MAX_NAMES {
        return Err(AuxRecursorError::Limit);
    }
    let mut seen = BTreeSet::new();
    let mut payload = MAGIC.to_vec();
    payload.extend(
        u32::try_from(names.len())
            .map_err(|_| AuxRecursorError::Limit)?
            .to_le_bytes(),
    );
    for name in names {
        validate(env, name)?;
        if !seen.insert(name) {
            return Err(AuxRecursorError::Duplicate(name.clone()));
        }
        write_name(name, &mut payload).map_err(codec)?;
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(AuxRecursorError::Limit);
        }
    }
    let env = match env.extension(&journal_name()) {
        Some(state) if state.descriptor != descriptor() => {
            return Err(AuxRecursorError::Malformed);
        }
        Some(state) if state.len() >= MAX_ROWS => return Err(AuxRecursorError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| AuxRecursorError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| AuxRecursorError::Malformed)
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AuxRecursors {
    names: BTreeSet<Name>,
}

impl AuxRecursors {
    /// Validate and read the exact tag set. Every entry must still name an
    /// admitted definition; suffix spelling does not grant membership.
    pub fn read(env: &Environment) -> Result<Self, AuxRecursorError> {
        let Some(extension) = env.extension(&journal_name()) else {
            return Ok(Self::default());
        };
        if extension.descriptor != descriptor() {
            return Err(AuxRecursorError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(AuxRecursorError::Limit);
        }
        let mut names = BTreeSet::new();
        for entry in extension.entries() {
            if entry.payload.len() > MAX_ENTRY_BYTES {
                return Err(AuxRecursorError::Limit);
            }
            let mut bytes = entry
                .payload
                .strip_prefix(MAGIC)
                .ok_or(AuxRecursorError::Malformed)?;
            if bytes.len() < 4 {
                return Err(AuxRecursorError::Malformed);
            }
            let (count, rest) = bytes.split_at(4);
            let count =
                u32::from_le_bytes(count.try_into().map_err(|_| AuxRecursorError::Malformed)?);
            let count = usize::try_from(count).map_err(|_| AuxRecursorError::Limit)?;
            if count == 0 {
                return Err(AuxRecursorError::Malformed);
            }
            if names.len().saturating_add(count) > MAX_NAMES {
                return Err(AuxRecursorError::Limit);
            }
            bytes = rest;
            for _ in 0..count {
                let name = read_name(&mut bytes).map_err(codec)?;
                validate(env, &name)?;
                if !names.insert(name.clone()) {
                    return Err(AuxRecursorError::Duplicate(name));
                }
            }
            if !bytes.is_empty() {
                return Err(AuxRecursorError::Malformed);
            }
        }
        Ok(Self { names })
    }

    pub fn contains(&self, name: &Name) -> bool {
        self.names.contains(name)
    }

    pub fn iter(&self) -> impl Iterator<Item = &Name> {
        self.names.iter()
    }

    pub fn len(&self) -> usize {
        self.names.len()
    }

    pub fn is_empty(&self) -> bool {
        self.names.is_empty()
    }
}

/// One elaboration's validated set. Definition applications read the set once
/// until either its journal content or the admitted constant population changes.
/// Errors are not cached; restoring an elaboration snapshot may discard this
/// cache without changing semantics.
#[derive(Clone, Default)]
pub(crate) struct AuxRecursorCache {
    last: std::cell::RefCell<Option<(CacheKey, std::sync::Arc<AuxRecursors>)>>,
}

type CacheKey = (Option<[u8; 32]>, usize);

impl AuxRecursorCache {
    pub(crate) fn contains(
        &self,
        env: &Environment,
        name: &Name,
    ) -> Result<bool, AuxRecursorError> {
        let key = (journal_digest(env), env.len());
        if let Some((cached, names)) = self.last.borrow().as_ref()
            && *cached == key
        {
            return Ok(names.contains(name));
        }
        let names = std::sync::Arc::new(AuxRecursors::read(env)?);
        let contains = names.contains(name);
        *self.last.borrow_mut() = Some((key, names));
        Ok(contains)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_env::constants::{
        AxiomVal, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
    };

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn declarations() -> Environment {
        let base = ConstantVal {
            name: n("Generated.recOn"),
            level_params: Vec::new(),
            type_: Expr::sort(Level::one()),
        };
        Environment::new()
            .add_decl(ConstantInfo::Defn(DefinitionVal {
                all: vec![base.name.clone()],
                base: base.clone(),
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Abbrev,
                safety: DefinitionSafety::Safe,
            }))
            .unwrap()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n("User.casesOn"),
                    ..base
                },
                is_unsafe: false,
            }))
            .unwrap()
    }

    #[test]
    fn names_gain_membership_only_through_an_admitted_definition_tag() {
        let env = declarations();
        let cache = AuxRecursorCache::default();
        assert!(AuxRecursors::read(&env).unwrap().is_empty());
        assert!(!cache.contains(&env, &n("Generated.recOn")).unwrap());
        assert_eq!(register_module(&env, &[]).unwrap(), env);
        let tagged = register_module(&env, &[n("Generated.recOn")]).unwrap();
        let names = AuxRecursors::read(&tagged).unwrap();
        assert!(cache.contains(&tagged, &n("Generated.recOn")).unwrap());
        assert!(cache.contains(&tagged, &n("Generated.recOn")).unwrap());
        assert!(!cache.contains(&env, &n("Generated.recOn")).unwrap());
        assert_eq!(names.len(), 1);
        assert!(names.contains(&n("Generated.recOn")));
        assert!(!names.contains(&n("User.casesOn")));
        assert!(AuxRecursors::read(&env).unwrap().is_empty());
        assert_eq!(
            register_module(&env, &[n("User.casesOn")]),
            Err(AuxRecursorError::NotDefinition(n("User.casesOn")))
        );
        assert_eq!(
            register_module(&env, &[n("Missing.recOn")]),
            Err(AuxRecursorError::UnknownDeclaration(n("Missing.recOn")))
        );
        let twice = register_module(&tagged, &[n("Generated.recOn")]).unwrap();
        assert_eq!(
            AuxRecursors::read(&twice),
            Err(AuxRecursorError::Duplicate(n("Generated.recOn")))
        );
        assert!(cache.contains(&twice, &n("Generated.recOn")).is_err());
        assert!(cache.contains(&tagged, &n("Generated.recOn")).unwrap());
    }

    #[test]
    fn malformed_and_foreign_journals_are_never_empty_successes() {
        let env = declarations();
        let tagged = register_module(&env, &[n("Generated.recOn")]).unwrap();
        let valid = tagged
            .extension(&journal_name())
            .unwrap()
            .entries()
            .next()
            .unwrap()
            .payload
            .to_vec();
        for bad in [
            Vec::new(),
            MAGIC.to_vec(),
            [MAGIC, &0_u32.to_le_bytes()].concat(),
            [MAGIC, &2_u32.to_le_bytes(), &valid[MAGIC.len() + 4..]].concat(),
            [valid.as_slice(), &[0]].concat(),
        ] {
            let broken = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&journal_name(), bad)
                .unwrap();
            assert!(AuxRecursors::read(&broken).is_err());
        }
        let mut foreign = descriptor();
        foreign.provenance = PayloadProvenance::Opaque;
        let broken = env.register_extension(foreign).unwrap();
        assert_eq!(
            AuxRecursors::read(&broken),
            Err(AuxRecursorError::Malformed)
        );
        assert_eq!(
            register_module(&broken, &[n("Generated.recOn")]),
            Err(AuxRecursorError::Malformed)
        );
    }
}
