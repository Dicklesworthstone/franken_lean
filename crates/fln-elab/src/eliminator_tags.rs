//! The pin's `Lean.Elab.Term.elabAsElim` and `Lean.sparseCasesOnExt` tags.
//!
//! These are separate from `Lean.auxRecExt`: an ordinary tagged theorem or
//! definition receives dependent application elaboration, not the auxiliary
//! recursor's reduction or compiler privileges. The sparse tag preserves the
//! identity of admitted generated cases eliminators; it does not assert that
//! the native compiler implements the pin's sparse-cases optimization.
//!
//! Generators register only after normal admission. Importers additionally
//! establish module ownership. Every journal read validates against the exact
//! checked metadata context, then projects the names visible in this world.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::{expr::Expr, name::Name};
use fln_env::constants::ConstantInfo;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

#[cfg(test)]
mod tests;
mod validation;

pub const MAX_ROWS: usize = 65_536;
const MAX_NAMES: usize = 1 << 20;
const MAX_ENTRY_BYTES: usize = 16 << 20;
const MAX_VALIDATION_STEPS: usize = 1_000_000;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TagKind {
    ElabAsElim,
    SparseCasesOn,
}

impl TagKind {
    fn component(self) -> &'static str {
        match self {
            Self::ElabAsElim => "elabAsElim",
            Self::SparseCasesOn => "sparseCasesOn",
        }
    }

    fn magic(self) -> &'static [u8] {
        match self {
            Self::ElabAsElim => b"FLNELABELIM\x01",
            Self::SparseCasesOn => b"FLNSPARSECASE\x01",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EliminatorTagError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    NotDefinition(Name),
    InvalidEliminator(Name),
    /// A retained type needs normalization outside the bounded native header
    /// reader, or a later opacity policy hides its registration-time telescope.
    UnsupportedEliminator(Name),
    Duplicate(Name),
}

impl std::fmt::Display for EliminatorTagError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed native eliminator-tag journal"),
            Self::Limit => f.write_str("native eliminator-tag journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "an eliminator tag names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::NotDefinition(name) => write!(
                f,
                "a generated sparse cases tag requires an admitted definition: {}",
                name.to_display_string()
            ),
            Self::InvalidEliminator(name) => write!(
                f,
                "invalid elab_as_elim telescope for {}",
                name.to_display_string()
            ),
            Self::UnsupportedEliminator(name) => write!(
                f,
                "unsupported elab_as_elim type normalization for {}",
                name.to_display_string()
            ),
            Self::Duplicate(name) => write!(
                f,
                "{} occurs twice in an eliminator-tag journal",
                name.to_display_string()
            ),
        }
    }
}
impl std::error::Error for EliminatorTagError {}

fn codec(error: InstanceRegistryError) -> EliminatorTagError {
    match error {
        InstanceRegistryError::Limit => EliminatorTagError::Limit,
        _ => EliminatorTagError::Malformed,
    }
}

pub fn journal_name(kind: TagKind) -> Name {
    Name::from_components(["FrankenLean", kind.component(), "v1"])
}

fn descriptor(kind: TagKind) -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(kind),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

pub fn supports(kind: TagKind, candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor(kind)
}

fn validate(
    env: &Environment,
    kind: TagKind,
    name: &Name,
    remaining: &mut usize,
) -> Result<Expr, EliminatorTagError> {
    if name.is_anonymous() {
        return Err(EliminatorTagError::Malformed);
    }
    let info = env
        .find(name)
        .ok_or_else(|| EliminatorTagError::UnknownDeclaration(name.clone()))?;
    match kind {
        TagKind::ElabAsElim => validation::eliminator_type(env, info, remaining),
        TagKind::SparseCasesOn if matches!(info, ConstantInfo::Defn(_)) => {
            Ok(info.constant_val().type_.clone())
        }
        TagKind::SparseCasesOn => Err(EliminatorTagError::NotDefinition(name.clone())),
    }
}

/// Append one checked module's names. Ownership is checked by the importer;
/// this layer checks membership and the selected tag's supported semantics.
/// Repeated names within a batch fail now; cross-batch repeats fail on read,
/// without repeatedly traversing all earlier modules during import.
pub fn register_module(
    env: &Environment,
    kind: TagKind,
    names: &[Name],
) -> Result<Environment, EliminatorTagError> {
    if names.is_empty() {
        return Ok(env.clone());
    }
    if names.len() > MAX_NAMES {
        return Err(EliminatorTagError::Limit);
    }
    let mut remaining = MAX_VALIDATION_STEPS;
    let mut seen = BTreeSet::new();
    let mut payload = kind.magic().to_vec();
    payload.extend(
        u32::try_from(names.len())
            .map_err(|_| EliminatorTagError::Limit)?
            .to_le_bytes(),
    );
    for name in names {
        if !seen.insert(name) {
            return Err(EliminatorTagError::Duplicate(name.clone()));
        }
        validate(env, kind, name, &mut remaining)?;
        write_name(name, &mut payload).map_err(codec)?;
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(EliminatorTagError::Limit);
        }
    }
    let env = match env.extension(&journal_name(kind)) {
        Some(state) if !supports(kind, &state.descriptor) => {
            return Err(EliminatorTagError::Malformed);
        }
        Some(state) if state.len() >= MAX_ROWS => return Err(EliminatorTagError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor(kind))
            .map_err(|_| EliminatorTagError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(kind), payload)
        .map_err(|_| EliminatorTagError::Malformed)
}

/// Install both tags for a batch of admitted per-constructor `.elim`
/// definitions. A failure in either journal leaves the caller's world intact.
/// The family-level `ctorElim` and `ctorElimType` are deliberately not tagged.
pub fn register_generated(
    env: &Environment,
    names: &[Name],
) -> Result<Environment, EliminatorTagError> {
    let staged = register_module(env, TagKind::SparseCasesOn, names)?;
    register_module(&staged, TagKind::ElabAsElim, names)
}

fn read_types(
    env: &Environment,
    kind: TagKind,
) -> Result<BTreeMap<Name, Expr>, EliminatorTagError> {
    let Some(extension) = env.extension(&journal_name(kind)) else {
        return Ok(BTreeMap::new());
    };
    if !supports(kind, &extension.descriptor) {
        return Err(EliminatorTagError::Malformed);
    }
    if extension.len() > MAX_ROWS {
        return Err(EliminatorTagError::Limit);
    }
    let mut remaining = MAX_VALIDATION_STEPS;
    let mut names = BTreeMap::new();
    for (entry, validation) in env.metadata_validation_entries(&journal_name(kind)) {
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(EliminatorTagError::Limit);
        }
        let mut bytes = entry
            .payload
            .strip_prefix(kind.magic())
            .ok_or(EliminatorTagError::Malformed)?;
        if bytes.len() < 4 {
            return Err(EliminatorTagError::Malformed);
        }
        let (count, rest) = bytes.split_at(4);
        let count = u32::from_le_bytes(
            count
                .try_into()
                .map_err(|_| EliminatorTagError::Malformed)?,
        );
        let count = usize::try_from(count).map_err(|_| EliminatorTagError::Limit)?;
        if count == 0 {
            return Err(EliminatorTagError::Malformed);
        }
        if names.len().saturating_add(count) > MAX_NAMES {
            return Err(EliminatorTagError::Limit);
        }
        bytes = rest;
        for _ in 0..count {
            let name = read_name(&mut bytes).map_err(codec)?;
            let type_ = validate(validation, kind, &name, &mut remaining)?;
            if names.insert(name.clone(), type_).is_some() {
                return Err(EliminatorTagError::Duplicate(name));
            }
        }
        if !bytes.is_empty() {
            return Err(EliminatorTagError::Malformed);
        }
    }
    names.retain(|name, _| env.contains(name));
    Ok(names)
}

pub fn read(env: &Environment, kind: TagKind) -> Result<BTreeSet<Name>, EliminatorTagError> {
    Ok(read_types(env, kind)?.into_keys().collect())
}

/// Exact environment identity binds both the checked declarations and their
/// effective reducibility/metadata contexts. Equal counts or a tag digest do
/// not identify speculative sibling worlds. Errors are never cached.
#[derive(Clone, Default)]
pub(crate) struct ElabAsElimCache {
    last: std::cell::RefCell<Option<(Environment, Arc<BTreeSet<Name>>)>>,
    types: std::cell::RefCell<Arc<BTreeMap<Name, Expr>>>,
}

impl ElabAsElimCache {
    pub(crate) fn declared_type(
        &self,
        env: &Environment,
        name: &Name,
    ) -> Result<Option<Expr>, EliminatorTagError> {
        let unchanged = self
            .last
            .borrow()
            .as_ref()
            .is_some_and(|(cached, _)| cached == env);
        if !unchanged {
            let names = Arc::new(read(env, TagKind::ElabAsElim)?);
            *self.last.borrow_mut() = Some((env.clone(), names));
            *self.types.borrow_mut() = Arc::default();
        }
        if !self
            .last
            .borrow()
            .as_ref()
            .is_some_and(|(_, names)| names.contains(name))
        {
            return Ok(None);
        }
        if let Some(type_) = self.types.borrow().get(name) {
            return Ok(Some(type_.clone()));
        }
        // Metadata membership can validate using retained hidden definitions.
        // Actual type normalization may use only this visible environment.
        let mut remaining = MAX_VALIDATION_STEPS;
        let type_ = validate(env, TagKind::ElabAsElim, name, &mut remaining)?;
        Arc::make_mut(&mut self.types.borrow_mut()).insert(name.clone(), type_.clone());
        Ok(Some(type_))
    }
}
