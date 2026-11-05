//! Reducibility status: the pin's `reducibilityCore` extension (vendored
//! `src/Lean/ReducibilityAttrs.lean`). A definition's status decides which
//! transparency modes may unfold it. At `instances` transparency the pin unfolds
//! `reducible` and `implicitReducible` definitions (`canUnfoldDefault`, vendored
//! `src/Lean/Meta/GetUnfoldableConst.lean`); instances carry `implicitReducible`,
//! and instance selection runs at that mode (bead fln-gkhu).
//!
//! Statuses are activated from imported modules like the instance journals. They
//! grant no declaration authority: a status names only a declaration the
//! environment already holds, and only changes what elaboration may unfold, never
//! what the kernel accepts.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

pub mod export;

const MAGIC: &[u8] = b"FLNREDUC\x01";
const MAX_ROWS: usize = 1 << 20;
const MAX_ENTRY_BYTES: usize = 65_536;

/// The pin's `ReducibilityStatus`, in its declaration order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Reducibility {
    Reducible,
    Semireducible,
    Irreducible,
    ImplicitReducible,
}

impl Reducibility {
    fn tag(self) -> u8 {
        match self {
            Self::Reducible => 0,
            Self::Semireducible => 1,
            Self::Irreducible => 2,
            Self::ImplicitReducible => 3,
        }
    }
    fn from_tag(tag: u8) -> Option<Self> {
        Some(match tag {
            0 => Self::Reducible,
            1 => Self::Semireducible,
            2 => Self::Irreducible,
            3 => Self::ImplicitReducible,
            _ => return None,
        })
    }
    /// Whether the pin's `instances` transparency may unfold a definition with
    /// this status.
    pub fn unfolds_at_instances(self) -> bool {
        matches!(self, Self::Reducible | Self::ImplicitReducible)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ReducibilityError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    /// The instance registry the native-instance default reads could not be read.
    Instances(InstanceRegistryError),
}

impl std::fmt::Display for ReducibilityError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native reducibility journal"),
            Self::Limit => f.write_str("native reducibility journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "a reducibility status names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::Instances(error) => write!(f, "{error}"),
        }
    }
}
impl std::error::Error for ReducibilityError {}

fn codec(error: InstanceRegistryError) -> ReducibilityError {
    match error {
        InstanceRegistryError::Limit => ReducibilityError::Limit,
        _ => ReducibilityError::Malformed,
    }
}

fn extension_name() -> Name {
    Name::from_components(["FrankenLean", "sourceReducibility", "v1"])
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

/// Record `declaration`'s status. The declaration must be admitted. A later
/// entry for the same declaration replaces an earlier one, as the pin's
/// `NameMap.insert` does; appending never re-reads the journal.
pub fn register(
    env: &Environment,
    declaration: &Name,
    status: Reducibility,
) -> Result<Environment, ReducibilityError> {
    if !env.contains(declaration) {
        return Err(ReducibilityError::UnknownDeclaration(declaration.clone()));
    }
    let mut payload = MAGIC.to_vec();
    write_name(declaration, &mut payload).map_err(codec)?;
    payload.push(status.tag());
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(ReducibilityError::Limit);
    }
    let env = if env.extension(&extension_name()).is_none() {
        env.register_extension(descriptor())
            .map_err(|_| ReducibilityError::Malformed)?
    } else {
        env.clone()
    };
    if env
        .extension(&extension_name())
        .is_some_and(|state| state.len() >= MAX_ROWS)
    {
        return Err(ReducibilityError::Limit);
    }
    env.push_extension_entry(&extension_name(), payload)
        .map_err(|_| ReducibilityError::Malformed)
}

/// Lexical transparency overrides. They live in a source scope, never in the
/// admitted environment's journal or a module's exported extension suffix.
/// An elaboration receives a temporary environment with these statuses, so
/// unification, instance selection and simplification read one coherent table.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct LocalReducibility {
    statuses: BTreeMap<Name, Reducibility>,
}

impl LocalReducibility {
    const MAX_DECLARATIONS: usize = 4096;

    /// Stage one already resolved definition. Validation of the requested
    /// transition belongs to the source attribute handler; this boundary also
    /// validates embedders' names, declaration kinds and retained-state bounds.
    pub fn with_status(
        &self,
        env: &Environment,
        declaration: &Name,
        status: Reducibility,
    ) -> Result<Self, ReducibilityError> {
        match env.find(declaration) {
            Some(fln_env::constants::ConstantInfo::Defn(_)) => {}
            Some(_) => return Err(ReducibilityError::Malformed),
            None => return Err(ReducibilityError::UnknownDeclaration(declaration.clone())),
        }
        if !self.statuses.contains_key(declaration) && self.statuses.len() >= Self::MAX_DECLARATIONS
        {
            return Err(ReducibilityError::Limit);
        }
        // Use the persistent codec's exact name and payload limits, without
        // publishing the validation snapshot.
        register(env, declaration, status)?;
        let mut next = self.clone();
        next.statuses.insert(declaration.clone(), status);
        Ok(next)
    }

    /// The subset meaningful in a public module world. Private declarations
    /// and opaque public interfaces have no unfoldable body in that world.
    pub fn visible_in(&self, env: &Environment) -> Self {
        Self {
            statuses: self
                .statuses
                .iter()
                .filter(|(name, _)| {
                    matches!(
                        env.find(name),
                        Some(fln_env::constants::ConstantInfo::Defn(_))
                    )
                })
                .map(|(name, status)| (name.clone(), *status))
                .collect(),
        }
    }

    /// Apply this scope only to an elaboration snapshot. The caller retains
    /// its original environment for admission and publication. Reapplying the
    /// same scope to a child context does not grow the temporary journal.
    pub fn environment(&self, env: &Environment) -> Result<Environment, ReducibilityError> {
        if self.statuses.is_empty() {
            return Ok(env.clone());
        }
        let current = table(env)?;
        let mut next = env.clone();
        for (name, status) in &self.statuses {
            match env.find(name) {
                Some(fln_env::constants::ConstantInfo::Defn(_)) => {}
                Some(_) => return Err(ReducibilityError::Malformed),
                None => return Err(ReducibilityError::UnknownDeclaration(name.clone())),
            }
            if current.status(name) != *status {
                next = register(&next, name, *status)?;
            }
        }
        Ok(next)
    }
}

/// Every recorded status, the last entry for a declaration winning.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ReducibilityTable {
    statuses: HashMap<Name, Reducibility>,
    opaque_definitions: BTreeSet<Name>,
}

impl ReducibilityTable {
    /// The table the journal records. A row naming a declaration the environment
    /// does not hold is refused, never kept.
    pub fn read(env: &Environment) -> Result<Self, ReducibilityError> {
        let Some(extension) = env.extension(&extension_name()) else {
            return Ok(Self::default());
        };
        if extension.descriptor != descriptor() {
            return Err(ReducibilityError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(ReducibilityError::Limit);
        }
        let mut table = Self::default();
        for (entry, validation) in env.metadata_validation_entries(&extension_name()) {
            if entry.payload.len() > MAX_ENTRY_BYTES {
                return Err(ReducibilityError::Limit);
            }
            let mut bytes: &[u8] = &entry.payload;
            if bytes.len() < MAGIC.len() || &bytes[..MAGIC.len()] != MAGIC {
                return Err(ReducibilityError::Malformed);
            }
            bytes = &bytes[MAGIC.len()..];
            let declaration = read_name(&mut bytes).map_err(codec)?;
            let [tag] = bytes else {
                return Err(ReducibilityError::Malformed);
            };
            let status = Reducibility::from_tag(*tag).ok_or(ReducibilityError::Malformed)?;
            if !validation.contains(&declaration) {
                return Err(ReducibilityError::UnknownDeclaration(declaration));
            }
            if status == Reducibility::Irreducible {
                table.opaque_definitions.insert(declaration.clone());
            } else {
                table.opaque_definitions.remove(&declaration);
            }
            table.statuses.insert(declaration, status);
        }
        table.statuses.retain(|name, _| env.contains(name));
        table.opaque_definitions.retain(|name| env.contains(name));
        Ok(table)
    }

    /// The journal's statuses, plus `ImplicitReducible` for each instance declared
    /// here (not imported) that the journal does not record: the status the pin's
    /// `instance` command gives it.
    pub fn effective(env: &Environment) -> Result<Self, ReducibilityError> {
        let mut table = Self::read(env)?;
        let registry =
            crate::instances::InstanceRegistry::read(env).map_err(ReducibilityError::Instances)?;
        for name in registry.native_instances() {
            table
                .statuses
                .entry(name.clone())
                .or_insert(Reducibility::ImplicitReducible);
        }
        Ok(table)
    }

    /// `declaration`'s status: `Semireducible`, the pin's default, when none is
    /// recorded.
    pub fn status(&self, declaration: &Name) -> Reducibility {
        self.statuses
            .get(declaration)
            .copied()
            .unwrap_or(Reducibility::Semireducible)
    }

    /// `declaration`'s status if one is known: recorded in the journal, or given
    /// to an instance declared here. `None` is "unknown", not "semireducible".
    pub fn get(&self, declaration: &Name) -> Option<Reducibility> {
        self.statuses.get(declaration).copied()
    }

    /// The immutable Default-transparency restriction for kernel equality
    /// queries. Kept with the cached table so each conversion does not rebuild
    /// the journal's set; a later status overrides membership in either direction.
    pub(crate) fn opaque_definitions(&self) -> &BTreeSet<Name> {
        &self.opaque_definitions
    }

    pub fn len(&self) -> usize {
        self.statuses.len()
    }

    pub fn is_empty(&self) -> bool {
        self.statuses.is_empty()
    }
}

thread_local! {
    /// One thread's last table. Unification consults statuses on every unfold,
    /// so the table is re-read only when what it reads can have changed. A failed
    /// read is never kept.
    static LAST: std::cell::RefCell<Option<(Environment, Arc<ReducibilityTable>)>> =
        const { std::cell::RefCell::new(None) };
}

/// The environment's effective table, read once per change of what it reads.
pub fn table(env: &Environment) -> Result<Arc<ReducibilityTable>, ReducibilityError> {
    if let Some(table) = LAST.with(|last| {
        last.borrow()
            .as_ref()
            .filter(|(cached, _)| cached == env)
            .map(|(_, table)| Arc::clone(table))
    }) {
        return Ok(table);
    }
    let table = Arc::new(ReducibilityTable::effective(env)?);
    LAST.with(|last| *last.borrow_mut() = Some((env.clone(), Arc::clone(&table))));
    Ok(table)
}

/// `declaration`'s known reducibility status in `env` (bead fln-gkhu), for
/// readers outside unification such as the instance index's goal keys (bead
/// fln-52qv). `None` means no status is known: an imported declaration absent from
/// its module's `reducibilityCore` is semireducible at the pin, but a declaration
/// elaborated here without a recorded status is not known to be.
pub fn known_status(
    env: &Environment,
    declaration: &Name,
) -> Result<Option<Reducibility>, ReducibilityError> {
    Ok(table(env)?.get(declaration))
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
    fn the_last_status_for_a_declaration_wins_and_absence_is_semireducible() {
        let env = with_axiom(&with_axiom(&Environment::new(), "a"), "b");
        let empty = table(&env).unwrap();
        assert!(empty.is_empty());
        assert_eq!(empty.status(&n("a")), Reducibility::Semireducible);
        let env = register(&env, &n("a"), Reducibility::Reducible).unwrap();
        let env = register(&env, &n("b"), Reducibility::ImplicitReducible).unwrap();
        let env = register(&env, &n("a"), Reducibility::Irreducible).unwrap();
        let read = table(&env).unwrap();
        assert_eq!(
            known_status(&env, &n("a")),
            Ok(Some(Reducibility::Irreducible))
        );
        assert_eq!(known_status(&env, &n("unrecorded")), Ok(None));
        assert_eq!(read.status(&n("a")), Reducibility::Irreducible);
        assert_eq!(read.status(&n("b")), Reducibility::ImplicitReducible);
        assert_eq!(read.len(), 2);
        // The cache answers the new journal, not the empty one it held.
        assert!(!Arc::ptr_eq(&empty, &read));
        assert!(Arc::ptr_eq(&read, &table(&env).unwrap()));
    }

    #[test]
    fn only_reducible_and_implicit_reducible_unfold_at_instances() {
        assert!(Reducibility::Reducible.unfolds_at_instances());
        assert!(Reducibility::ImplicitReducible.unfolds_at_instances());
        assert!(!Reducibility::Semireducible.unfolds_at_instances());
        assert!(!Reducibility::Irreducible.unfolds_at_instances());
    }

    #[test]
    fn a_status_cannot_name_what_the_environment_does_not_hold() {
        let env = with_axiom(&Environment::new(), "a");
        assert_eq!(
            register(&env, &n("missing"), Reducibility::Reducible),
            Err(ReducibilityError::UnknownDeclaration(n("missing")))
        );
    }

    #[test]
    fn a_malformed_or_foreign_journal_is_refused_not_read_as_empty() {
        let env = with_axiom(&Environment::new(), "a");
        let mut good = MAGIC.to_vec();
        write_name(&n("a"), &mut good).unwrap();
        for payload in [
            Vec::new(),
            MAGIC.to_vec(),
            [good.as_slice(), &[4]].concat(),
            [good.as_slice(), &[0, 0]].concat(),
        ] {
            let broken = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&extension_name(), payload)
                .unwrap();
            assert!(ReducibilityTable::read(&broken).is_err());
        }
        let mut foreign = descriptor();
        foreign.provenance = PayloadProvenance::Opaque;
        let env = env.register_extension(foreign).unwrap();
        assert_eq!(
            ReducibilityTable::read(&env),
            Err(ReducibilityError::Malformed)
        );
    }
}
