//! Imported `export` aliases: the pin's `aliasExtension` (vendored
//! `src/Lean/ResolveName.lean`). `export A (x)` in namespace `B` records the
//! alias `B.x ~> A.x`; global name resolution consults aliases beside real
//! declarations. They are activated from imported modules like the instance
//! journals, and grant no declaration authority: an alias names only a
//! declaration the environment already holds.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeMap;

const MAGIC: &[u8] = b"FLNALIAS\x01";
const MAX_ROWS: usize = 65_536;
const MAX_ENTRY_BYTES: usize = 65_536;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AliasError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
}

impl std::fmt::Display for AliasError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native source alias journal"),
            Self::Limit => f.write_str("native source alias journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "an alias names {}, which is not admitted",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for AliasError {}

fn codec(error: InstanceRegistryError) -> AliasError {
    match error {
        InstanceRegistryError::Limit => AliasError::Limit,
        _ => AliasError::Malformed,
    }
}

fn extension_name() -> Name {
    Name::from_components(["FrankenLean", "sourceAliases", "v1"])
}
fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: extension_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// The alias journal's content identity, if it exists: what a reader keyed on
/// it can cache.
pub fn journal_digest(env: &Environment) -> Option<[u8; 32]> {
    env.extension(&extension_name())
        .map(|extension| extension.content_digest().0)
}

/// Record `alias ~> declaration`, as the pin's `addAlias env a e` records
/// `(a, e)`. The declaration must be admitted. A pair already recorded is not
/// recorded again (the pin's `addAliasEntry` keeps each target once).
pub fn register(
    env: &Environment,
    alias: &Name,
    declaration: &Name,
) -> Result<Environment, AliasError> {
    if !env.contains(declaration) {
        return Err(AliasError::UnknownDeclaration(declaration.clone()));
    }
    if alias.is_anonymous() {
        return Err(AliasError::Malformed);
    }
    if AliasTable::read(env)?.targets(alias).contains(declaration) {
        return Ok(env.clone());
    }
    let mut payload = MAGIC.to_vec();
    write_name(alias, &mut payload).map_err(codec)?;
    write_name(declaration, &mut payload).map_err(codec)?;
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(AliasError::Limit);
    }
    let env = if env.extension(&extension_name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| AliasError::Malformed)?
    } else {
        env.clone()
    };
    if env
        .extension(&extension_name())
        .is_some_and(|state| state.len() >= MAX_ROWS)
    {
        return Err(AliasError::Limit);
    }
    env.push_extension_entry(&extension_name(), payload)
        .map_err(|_| AliasError::Malformed)
}

/// Every alias with its targets, each target once, in journal order.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct AliasTable {
    targets: BTreeMap<Name, Vec<Name>>,
}

impl AliasTable {
    /// The table the journal records. A row naming a declaration the
    /// environment does not hold is refused, never kept as a dangling alias.
    pub fn read(env: &Environment) -> Result<Self, AliasError> {
        let Some(extension) = env.extension(&extension_name()) else {
            return Ok(Self::default());
        };
        if extension.descriptor != descriptor() {
            return Err(AliasError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(AliasError::Limit);
        }
        let mut table = Self::default();
        for entry in extension.entries() {
            if entry.payload.len() > MAX_ENTRY_BYTES {
                return Err(AliasError::Limit);
            }
            let mut bytes: &[u8] = &entry.payload;
            if bytes.len() < MAGIC.len() || &bytes[..MAGIC.len()] != MAGIC {
                return Err(AliasError::Malformed);
            }
            bytes = &bytes[MAGIC.len()..];
            let alias = read_name(&mut bytes).map_err(codec)?;
            let declaration = read_name(&mut bytes).map_err(codec)?;
            if !bytes.is_empty() {
                return Err(AliasError::Malformed);
            }
            if !env.contains(&declaration) {
                return Err(AliasError::UnknownDeclaration(declaration));
            }
            let targets = table.targets.entry(alias).or_default();
            if !targets.contains(&declaration) {
                targets.push(declaration);
            }
        }
        Ok(table)
    }

    /// The declarations `alias` names, in journal order; empty if none.
    pub fn targets(&self, alias: &Name) -> &[Name] {
        self.targets.get(alias).map_or(&[], Vec::as_slice)
    }

    pub fn is_empty(&self) -> bool {
        self.targets.is_empty()
    }
}

/// One elaboration's alias table, re-read only when what [`AliasTable::read`]
/// reads can have changed: the alias journal, or the constants it validates
/// against (by count). A failed read is never kept.
#[derive(Clone, Default)]
pub(crate) struct AliasCache {
    last: std::cell::RefCell<Option<(CacheKey, std::sync::Arc<AliasTable>)>>,
}

/// The alias journal's digest (if any) and the environment's constant count.
type CacheKey = (Option<[u8; 32]>, usize);

impl AliasCache {
    pub(crate) fn read(&self, env: &Environment) -> Result<std::sync::Arc<AliasTable>, AliasError> {
        let key = (journal_digest(env), env.len());
        if let Some((cached, table)) = self.last.borrow().as_ref()
            && *cached == key
        {
            return Ok(std::sync::Arc::clone(table));
        }
        let table = std::sync::Arc::new(AliasTable::read(env)?);
        *self.last.borrow_mut() = Some((key, std::sync::Arc::clone(&table)));
        Ok(table)
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

    fn with_axiom(env: &Environment, name: &str) -> Environment {
        env.add_decl(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: n(name),
                level_params: Vec::new(),
                type_: Expr::sort(Level::one()),
            },
            is_unsafe: false,
        }))
        .unwrap()
    }

    #[test]
    fn an_alias_names_its_declarations_once_each_in_journal_order() {
        let env = with_axiom(&with_axiom(&Environment::new(), "A.x"), "C.x");
        assert!(AliasTable::read(&env).unwrap().is_empty());
        let env = register(&env, &n("x"), &n("A.x")).unwrap();
        let env = register(&env, &n("x"), &n("C.x")).unwrap();
        let again = register(&env, &n("x"), &n("A.x")).unwrap();
        assert_eq!(again, env, "a recorded pair is not recorded twice");
        let table = AliasTable::read(&env).unwrap();
        assert_eq!(table.targets(&n("x")), [n("A.x"), n("C.x")]);
        assert!(table.targets(&n("y")).is_empty());
    }

    #[test]
    fn an_alias_cannot_name_what_the_environment_does_not_hold() {
        let env = with_axiom(&Environment::new(), "A.x");
        assert_eq!(
            register(&env, &n("x"), &n("A.missing")),
            Err(AliasError::UnknownDeclaration(n("A.missing")))
        );
        assert_eq!(
            register(&env, &Name::anonymous(), &n("A.x")),
            Err(AliasError::Malformed)
        );
    }

    #[test]
    fn a_malformed_or_foreign_journal_is_refused_not_read_as_empty() {
        let env = with_axiom(&Environment::new(), "A.x");
        for payload in [Vec::new(), MAGIC.to_vec(), [MAGIC, &[9]].concat()] {
            let broken = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&extension_name(), payload)
                .unwrap();
            assert!(AliasTable::read(&broken).is_err());
        }
        let mut foreign = descriptor();
        foreign.provenance = PayloadProvenance::Opaque;
        let env = env.register_extension(foreign).unwrap();
        assert_eq!(AliasTable::read(&env), Err(AliasError::Malformed));
    }
}
