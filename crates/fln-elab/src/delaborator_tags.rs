//! The pin's delaborator attributes: declarations tagged
//! `@[pp_using_anonymous_constructor]` (`Lean.ppUsingAnonymousConstructorAttr`), functions
//! tagged `@[pp_nodot]` (`Lean.ppNoDotAttr`), and the constants an `@[app_unexpander]`
//! (`Lean.PrettyPrinter.Delaborator.appUnexpanderAttribute`) is registered for, vendored
//! `src/Lean/PrettyPrinter/Delaborator/{Attributes,Basic}.lean`.
//!
//! The printer reads them. A tagged structure prints as `⟨…⟩`, a tagged function never with
//! field notation, and an application of a key goes through compiled code this door does not
//! run, so it is never printed as a structure instance. An unexpander's own declaration is
//! not recorded: nothing here executes it. Each imported module contributes its own rows in
//! one entry. Source anonymous-constructor tags have a separate owned journal;
//! exporting that journal does not authorize losing unexpander registrations.
//! A malformed journal is refused, not read as empty.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::{BTreeMap, BTreeSet};

pub mod coercions;
pub use coercions::{CoeFnInfo, CoeFnKind};

const MAGIC: &[u8] = b"FLNDLBT\x01";
const MAX_ROWS: usize = 65_536;
const MAX_TAGS: usize = 1 << 20;
const MAX_ENTRY_BYTES: usize = 16 << 20;
const SOURCE_MAGIC: &[u8] = b"FLNPPAC\x01";
pub const MAX_SOURCE_ROWS: usize = 65_536;
const MAX_SOURCE_ENTRY_BYTES: usize = 65_536;

const ANONYMOUS_CONSTRUCTOR: u8 = 0;
const NODOT: u8 = 1;
const UNEXPANDER: u8 = 2;

/// One imported delaborator tag.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum DelaboratorTag {
    /// `@[pp_using_anonymous_constructor]`, a plain tag on any declaration.
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
    Duplicate(Name),
    NoExplicitArgument(Name),
    UnsupportedTelescope(Name),
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
            Self::Duplicate(name) => write!(
                f,
                "{} carries the same delaborator tag twice",
                name.to_display_string()
            ),
            Self::NoExplicitArgument(name) => {
                write!(f, "{} has no explicit arguments", name.to_display_string())
            }
            Self::UnsupportedTelescope(name) => write!(
                f,
                "unsupported coercion telescope for {}",
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
    // The pin's registerTagAttribute has no validator for either plain tag.
    // Structure membership is a separate printer condition, not tag authority.
    if env.contains(name) {
        Ok(())
    } else {
        Err(DelaboratorTagError::UnknownDeclaration(name.clone()))
    }
}

/// Owned source tags, independent of the import-only unexpander/no-dot journal.
pub fn source_journal_name() -> Name {
    Name::from_components(["FrankenLean", "sourceAnonymousConstructor", "v1"])
}

fn source_descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: source_journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

pub fn supports_source(candidate: &ExtensionDescriptor) -> bool {
    *candidate == source_descriptor() || coercions::supports(candidate)
}

/// Source admission checks global scope and module ownership before calling this.
/// Repeated NameSet insertion is idempotent, including an inherited tag.
pub fn register_anonymous_constructor(
    env: &Environment,
    name: &Name,
) -> Result<Environment, DelaboratorTagError> {
    validate(env, &DelaboratorTag::AnonymousConstructor(name.clone()))?;
    if DelaboratorTags::read(env)?.anonymous_constructor(name) {
        return Ok(env.clone());
    }
    let mut payload = SOURCE_MAGIC.to_vec();
    write_name(name, &mut payload).map_err(codec)?;
    if payload.len() > MAX_SOURCE_ENTRY_BYTES {
        return Err(DelaboratorTagError::Limit);
    }
    let env = match env.extension(&source_journal_name()) {
        Some(state) if state.len() >= MAX_SOURCE_ROWS => {
            return Err(DelaboratorTagError::Limit);
        }
        Some(_) => env.clone(),
        None => env
            .register_extension(source_descriptor())
            .map_err(|_| DelaboratorTagError::Malformed)?,
    };
    env.push_extension_entry(&source_journal_name(), payload)
        .map_err(|_| DelaboratorTagError::Malformed)
}

/// Read the exportable source journal against each row's admitted environment.
/// Projection-hidden declarations are validated there, then omitted here.
pub fn source_anonymous_constructors(
    env: &Environment,
) -> Result<BTreeSet<Name>, DelaboratorTagError> {
    let Some(extension) = env.extension(&source_journal_name()) else {
        return Ok(BTreeSet::new());
    };
    if extension.descriptor != source_descriptor() {
        return Err(DelaboratorTagError::Malformed);
    }
    if extension.len() > MAX_SOURCE_ROWS {
        return Err(DelaboratorTagError::Limit);
    }
    let mut names = BTreeSet::new();
    for (entry, validation) in env.metadata_validation_entries(&source_journal_name()) {
        if entry.payload.len() > MAX_SOURCE_ENTRY_BYTES {
            return Err(DelaboratorTagError::Limit);
        }
        let mut bytes = entry
            .payload
            .strip_prefix(SOURCE_MAGIC)
            .ok_or(DelaboratorTagError::Malformed)?;
        let name = read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty() {
            return Err(DelaboratorTagError::Malformed);
        }
        validate(
            validation,
            &DelaboratorTag::AnonymousConstructor(name.clone()),
        )?;
        if !names.insert(name.clone()) {
            return Err(DelaboratorTagError::Duplicate(name));
        }
    }
    names.retain(|name| env.contains(name));
    Ok(names)
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
/// module's own declaration; here every name must be admitted. The pin's plain tags
/// impose no declaration-kind restriction. A tag repeated within the module is refused.
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

/// The imported and source delaborator tags in force.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct DelaboratorTags {
    anonymous_constructor: BTreeSet<Name>,
    nodot: BTreeSet<Name>,
    /// Each constant's `@[app_unexpander]` registrations: `None` for a global one, and the
    /// namespace of a `scoped` one.
    unexpanded: BTreeMap<Name, BTreeSet<Option<Name>>>,
    coercions: BTreeMap<Name, CoeFnInfo>,
}

impl DelaboratorTags {
    /// Validate and read every recorded tag, keeping each unexpander's scope.
    pub fn read(env: &Environment) -> Result<Self, DelaboratorTagError> {
        let source = source_anonymous_constructors(env)?;
        let coercions = coercions::read(env)?.into_iter().collect();
        let Some(extension) = env.extension(&journal_name()) else {
            return Ok(Self {
                anonymous_constructor: source,
                coercions,
                ..Self::default()
            });
        };
        if extension.descriptor != descriptor() {
            return Err(DelaboratorTagError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(DelaboratorTagError::Limit);
        }
        let mut tags = Self {
            coercions,
            ..Self::default()
        };
        let mut total = source.len();
        for (entry, validation) in env.metadata_validation_entries(&journal_name()) {
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
                validate(validation, &tag)?;
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
                    DelaboratorTag::Unexpander { key, scope } => {
                        tags.unexpanded.entry(key).or_default().insert(scope);
                    }
                }
            }
            if !bytes.is_empty() {
                return Err(DelaboratorTagError::Malformed);
            }
        }
        tags.anonymous_constructor.retain(|name| env.contains(name));
        tags.anonymous_constructor.extend(source);
        tags.nodot.retain(|name| env.contains(name));
        tags.unexpanded.retain(|name, _| env.contains(name));
        Ok(tags)
    }

    /// Whether `declaration` is tagged `@[pp_using_anonymous_constructor]`.
    pub fn anonymous_constructor(&self, declaration: &Name) -> bool {
        self.anonymous_constructor.contains(declaration)
    }

    /// The last global coercion registration for this function, including
    /// imported and source rows. This is printer metadata, not a Coe instance.
    pub fn coercion(&self, declaration: &Name) -> Option<&CoeFnInfo> {
        self.coercions.get(declaration)
    }

    /// Whether `function` is tagged `@[pp_nodot]`.
    pub fn nodot(&self, function: &Name) -> bool {
        self.nodot.contains(function)
    }

    /// Whether an `@[app_unexpander]` for applications of `constant` is in force: a global
    /// one always, and a `scoped` one where `active` holds of its namespace (`open N`, or
    /// inside `namespace N`). `Int.negSucc`'s `-[n+1]` is scoped to `Int`, so the pin prints
    /// `Int.negSucc 9` outside it.
    pub fn unexpanded(&self, constant: &Name, active: impl Fn(&Name) -> bool) -> bool {
        self.unexpanded.get(constant).is_some_and(|scopes| {
            scopes
                .iter()
                .any(|scope| scope.as_ref().is_none_or(&active))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::{expr::Expr, level::Level};
    use fln_env::constants::{AxiomVal, ConstantInfo, ConstantVal};

    fn axiom() -> (Environment, Name) {
        let name = Name::from_components(["A"]);
        let env = Environment::new()
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: Vec::new(),
                    type_: Expr::sort(Level::one()),
                },
                is_unsafe: false,
            }))
            .unwrap();
        (env, name)
    }

    #[test]
    fn anonymous_constructor_is_a_plain_idempotent_source_and_imported_tag() {
        let (env, name) = axiom();
        let source = register_anonymous_constructor(&env, &name).unwrap();
        let repeated = register_anonymous_constructor(&source, &name).unwrap();
        assert_eq!(repeated, source);
        assert_eq!(
            source_anonymous_constructors(&source).unwrap(),
            BTreeSet::from([name.clone()])
        );
        assert!(
            DelaboratorTags::read(&source)
                .unwrap()
                .anonymous_constructor(&name)
        );
        assert_eq!(source.extension(&source_journal_name()).unwrap().len(), 1);
        let imported =
            register_module(&env, &[DelaboratorTag::AnonymousConstructor(name.clone())]).unwrap();
        assert_eq!(
            DelaboratorTags::read(&imported).unwrap(),
            DelaboratorTags::read(&source).unwrap()
        );
        assert_eq!(
            register_anonymous_constructor(&imported, &name).unwrap(),
            imported
        );
        assert!(imported.extension(&source_journal_name()).is_none());
    }

    #[test]
    fn malformed_source_tags_are_not_ignored_or_repaired() {
        let (env, name) = axiom();
        for bytes in [Vec::new(), SOURCE_MAGIC.to_vec(), b"broken".to_vec()] {
            let malformed = env
                .register_extension(source_descriptor())
                .unwrap()
                .push_extension_entry(&source_journal_name(), bytes)
                .unwrap();
            assert_eq!(
                DelaboratorTags::read(&malformed),
                Err(DelaboratorTagError::Malformed)
            );
            assert_eq!(
                register_anonymous_constructor(&malformed, &name),
                Err(DelaboratorTagError::Malformed)
            );
        }
        let missing = Name::from_components(["missing"]);
        assert_eq!(
            register_anonymous_constructor(&env, &missing),
            Err(DelaboratorTagError::UnknownDeclaration(missing))
        );
    }

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
