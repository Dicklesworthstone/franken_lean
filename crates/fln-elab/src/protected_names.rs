//! Imported `protected` declarations: the pin's `protectedExt` (vendored
//! `src/Lean/Modifiers.lean`). An atomic identifier never resolves to a protected
//! declaration through a namespace, an opened namespace or an `export` alias
//! (`resolveQualifiedName` and `getAliases ... (skipProtected := id.isAtomic)`,
//! vendored `src/Lean/ResolveName.lean`): `open Nat` does not make `Nat.add`
//! available as `add`, though `Nat.add` stays reachable by any non-atomic name.
//!
//! The names come from two places. Imported modules are activated like the export
//! aliases, one journal entry per module, as the pin keeps one tag array per module.
//! A source `protected def`, `theorem` or `instance` is tagged once the council has
//! admitted it, one entry per declaration, as the pin's `applyVisibility` tags it.
//! A module's own tags are written into its `.olean` as `protectedExt` entries.
//! They grant no declaration authority and only ever narrow name resolution. A name
//! must be an admitted declaration, is tagged once, and a malformed or foreign
//! journal is refused, never read as empty, which would silently widen resolution
//! again.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNPROT\x01";
const MAX_ROWS: usize = 65_536;
const MAX_NAMES: usize = 1 << 20;
const MAX_ENTRY_BYTES: usize = 16 << 20;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProtectedError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    /// A name already tagged. The pin tags a declaration only in its own module.
    Duplicate(Name),
}

impl std::fmt::Display for ProtectedError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native protected-declaration journal"),
            Self::Limit => f.write_str("native protected-declaration journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "a protected tag names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::Duplicate(name) => {
                write!(f, "{} is tagged protected twice", name.to_display_string())
            }
        }
    }
}
impl std::error::Error for ProtectedError {}

fn codec(error: InstanceRegistryError) -> ProtectedError {
    match error {
        InstanceRegistryError::Limit => ProtectedError::Limit,
        _ => ProtectedError::Malformed,
    }
}

fn extension_name() -> Name {
    Name::from_components(["FrankenLean", "sourceProtected", "v1"])
}

/// The native journal's extension name, for a refusal that names it.
pub fn journal_name() -> Name {
    extension_name()
}

/// Whether `descriptor` is this journal's, which a module's `.olean` can carry:
/// its own tags become the pin's `protectedExt` entries.
pub fn supports(descriptor_: &ExtensionDescriptor) -> bool {
    *descriptor_ == descriptor()
}
fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: extension_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// The journal's content identity, if it exists: what a reader keyed on it can
/// cache.
pub fn journal_digest(env: &Environment) -> Option<[u8; 32]> {
    env.extension(&extension_name())
        .map(|extension| extension.content_digest().0)
}

/// Record a batch of protected declarations as one journal entry: one imported
/// module's tags, kept together as the pin keeps them, or one admitted source
/// declaration. Every name must be admitted and appear once in `names`; an empty
/// batch records nothing. A name some earlier entry already
/// tagged is not looked for here, which would re-read the whole journal per
/// module: [`ProtectedNames::read`] refuses it.
pub fn register_module(env: &Environment, names: &[Name]) -> Result<Environment, ProtectedError> {
    if names.is_empty() {
        return Ok(env.clone());
    }
    if names.len() > MAX_NAMES {
        return Err(ProtectedError::Limit);
    }
    let mut seen = BTreeSet::new();
    let mut payload = MAGIC.to_vec();
    payload.extend(
        u32::try_from(names.len())
            .map_err(|_| ProtectedError::Limit)?
            .to_le_bytes(),
    );
    for name in names {
        if name.is_anonymous() {
            return Err(ProtectedError::Malformed);
        }
        if !env.contains(name) {
            return Err(ProtectedError::UnknownDeclaration(name.clone()));
        }
        if !seen.insert(name) {
            return Err(ProtectedError::Duplicate(name.clone()));
        }
        write_name(name, &mut payload).map_err(codec)?;
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(ProtectedError::Limit);
        }
    }
    let env = if env.extension(&extension_name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| ProtectedError::Malformed)?
    } else {
        env.clone()
    };
    if env
        .extension(&extension_name())
        .is_some_and(|state| state.len() >= MAX_ROWS)
    {
        return Err(ProtectedError::Limit);
    }
    env.push_extension_entry(&extension_name(), payload)
        .map_err(|_| ProtectedError::Malformed)
}

/// Every protected declaration the journal records.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProtectedNames {
    names: BTreeSet<Name>,
}

impl ProtectedNames {
    /// The set the journal records. A name the environment does not hold, or one
    /// tagged twice, is refused, never kept or dropped quietly.
    pub fn read(env: &Environment) -> Result<Self, ProtectedError> {
        let Some(extension) = env.extension(&extension_name()) else {
            return Ok(Self::default());
        };
        if extension.descriptor != descriptor() {
            return Err(ProtectedError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(ProtectedError::Limit);
        }
        let mut names = BTreeSet::new();
        for entry in extension.entries() {
            if entry.payload.len() > MAX_ENTRY_BYTES {
                return Err(ProtectedError::Limit);
            }
            let mut bytes: &[u8] = &entry.payload;
            if bytes.len() < MAGIC.len() + 4 || &bytes[..MAGIC.len()] != MAGIC {
                return Err(ProtectedError::Malformed);
            }
            bytes = &bytes[MAGIC.len()..];
            let (count, rest) = bytes.split_at(4);
            let count =
                u32::from_le_bytes(count.try_into().map_err(|_| ProtectedError::Malformed)?);
            let count = usize::try_from(count).map_err(|_| ProtectedError::Limit)?;
            if count == 0 {
                return Err(ProtectedError::Malformed);
            }
            if names.len().saturating_add(count) > MAX_NAMES {
                return Err(ProtectedError::Limit);
            }
            bytes = rest;
            for _ in 0..count {
                let name = read_name(&mut bytes).map_err(codec)?;
                if !env.contains(&name) {
                    return Err(ProtectedError::UnknownDeclaration(name));
                }
                if names.contains(&name) {
                    return Err(ProtectedError::Duplicate(name));
                }
                names.insert(name);
            }
            if !bytes.is_empty() {
                return Err(ProtectedError::Malformed);
            }
        }
        Ok(Self { names })
    }

    /// Whether `name` is a protected declaration.
    pub fn contains(&self, name: &Name) -> bool {
        self.names.contains(name)
    }

    /// Every protected declaration, in `Name` order.
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

/// One elaboration's protected set, re-read only when what
/// [`ProtectedNames::read`] reads can have changed: the journal, or the constants
/// it validates against (by count). A failed read is never kept.
#[derive(Clone, Default)]
pub(crate) struct ProtectedCache {
    last: std::cell::RefCell<Option<(CacheKey, std::sync::Arc<ProtectedNames>)>>,
}

/// The journal's digest (if any) and the environment's constant count.
type CacheKey = (Option<[u8; 32]>, usize);

impl ProtectedCache {
    pub(crate) fn read(
        &self,
        env: &Environment,
    ) -> Result<std::sync::Arc<ProtectedNames>, ProtectedError> {
        let key = (journal_digest(env), env.len());
        if let Some((cached, names)) = self.last.borrow().as_ref()
            && *cached == key
        {
            return Ok(std::sync::Arc::clone(names));
        }
        let names = std::sync::Arc::new(ProtectedNames::read(env)?);
        *self.last.borrow_mut() = Some((key, std::sync::Arc::clone(&names)));
        Ok(names)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn with_axioms(names: &[&str]) -> Environment {
        names.iter().fold(Environment::new(), |env, name| {
            env.add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: n(name),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap()
        })
    }

    #[test]
    fn each_module_records_its_tags_and_the_journal_reads_them_all() {
        let env = with_axioms(&["Nat.add", "Nat.sub", "List.map"]);
        assert!(ProtectedNames::read(&env).unwrap().is_empty());
        let empty = register_module(&env, &[]).unwrap();
        assert_eq!(empty, env, "an empty module records nothing");
        let env = register_module(&env, &[n("Nat.add"), n("Nat.sub")]).unwrap();
        let env = register_module(&env, &[n("List.map")]).unwrap();
        let names = ProtectedNames::read(&env).unwrap();
        assert_eq!(names.len(), 3);
        assert!(names.contains(&n("Nat.add")) && names.contains(&n("List.map")));
        assert!(!names.contains(&n("Nat.mul")));
    }

    #[test]
    fn a_tag_must_name_one_admitted_declaration_once() {
        let env = with_axioms(&["Nat.add"]);
        assert_eq!(
            register_module(&env, &[n("Nat.missing")]),
            Err(ProtectedError::UnknownDeclaration(n("Nat.missing")))
        );
        assert_eq!(
            register_module(&env, &[Name::anonymous()]),
            Err(ProtectedError::Malformed)
        );
        assert_eq!(
            register_module(&env, &[n("Nat.add"), n("Nat.add")]),
            Err(ProtectedError::Duplicate(n("Nat.add")))
        );
        // Two modules tagging one name: recorded, then refused when read.
        let twice = register_module(&env, &[n("Nat.add")]).unwrap();
        let twice = register_module(&twice, &[n("Nat.add")]).unwrap();
        assert_eq!(
            ProtectedNames::read(&twice),
            Err(ProtectedError::Duplicate(n("Nat.add")))
        );
    }

    #[test]
    fn a_malformed_or_foreign_journal_is_refused_not_read_as_empty() {
        let env = with_axioms(&["Nat.add"]);
        let mut valid = MAGIC.to_vec();
        valid.extend(1_u32.to_le_bytes());
        write_name(&n("Nat.add"), &mut valid).unwrap();
        let zero = [MAGIC, &0_u32.to_le_bytes()].concat();
        let short_count = [MAGIC, &2_u32.to_le_bytes(), &valid[MAGIC.len() + 4..]].concat();
        let trailing = [valid.as_slice(), &[0]].concat();
        let missing = {
            let mut payload = MAGIC.to_vec();
            payload.extend(1_u32.to_le_bytes());
            write_name(&n("Nat.missing"), &mut payload).unwrap();
            payload
        };
        for payload in [
            Vec::new(),
            MAGIC.to_vec(),
            zero,
            short_count,
            trailing,
            missing,
        ] {
            let broken = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&extension_name(), payload)
                .unwrap();
            assert!(ProtectedNames::read(&broken).is_err());
        }
        let good = env
            .register_extension(descriptor())
            .unwrap()
            .push_extension_entry(&extension_name(), valid)
            .unwrap();
        assert!(ProtectedNames::read(&good).unwrap().contains(&n("Nat.add")));
        let mut foreign = descriptor();
        foreign.provenance = PayloadProvenance::Opaque;
        let env = env.register_extension(foreign).unwrap();
        assert_eq!(ProtectedNames::read(&env), Err(ProtectedError::Malformed));
    }
}
