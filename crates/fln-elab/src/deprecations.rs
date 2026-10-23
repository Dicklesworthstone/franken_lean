//! `@[deprecated]` declarations: the pin's `deprecatedAttr` (vendored
//! `src/Lean/Linter/Deprecated.lean`), a parametric attribute whose parameter is a
//! `DeprecationEntry` (`newName?`, `text?`, `since?`).
//!
//! The entries come from two places. Imported modules are activated like the other attribute
//! journals, one journal entry per module. A source declaration carrying `@[deprecated …]` is
//! recorded once the council has admitted it, one entry per declaration, as the pin's
//! `setParam` records it after type checking. The journal grants no declaration authority: a
//! name must be an admitted declaration, is recorded once, and a malformed journal is refused,
//! never read as empty, which would silently drop the pin's warnings.
//!
//! The elaborator records each resolution of a deprecated constant where the pin's
//! `Linter.checkDeprecated` runs ([`DeprecatedUse`]); a front door that reports them installs a
//! [`UseSink`] and drains it after each command.
use crate::instances::{InstanceRegistryError, read_name, write_name};
use fln_core::name::Name;
use fln_env::environment::Environment;
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

const MAGIC: &[u8] = b"FLNDEPR\x01";
const MAX_ROWS: usize = 65_536;
const MAX_ENTRIES: usize = 1 << 20;
const MAX_ENTRY_BYTES: usize = 16 << 20;
const MAX_TEXT_BYTES: usize = 1 << 16;
/// Uses one sink holds before the next drain; the pin has no such bound, so reaching it is a
/// refusal of the elaboration that reports one more, never a dropped warning.
const MAX_USES: usize = 65_536;

const HAS_NEW_NAME: u8 = 1;
const HAS_TEXT: u8 = 2;
const HAS_SINCE: u8 = 4;

/// One `@[deprecated]` declaration and its `DeprecationEntry`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Deprecation {
    pub declaration: Name,
    pub new_name: Option<Name>,
    pub text: Option<String>,
    pub since: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeprecationError {
    Malformed,
    Limit,
    UnknownDeclaration(Name),
    /// A declaration deprecated twice. The pin's `setParam` sets a parameter once.
    Duplicate(Name),
}

impl std::fmt::Display for DeprecationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed => f.write_str("malformed deprecation journal"),
            Self::Limit => f.write_str("deprecation journal resource limit"),
            Self::UnknownDeclaration(name) => write!(
                f,
                "a deprecation names {}, which is not admitted",
                name.to_display_string()
            ),
            Self::Duplicate(name) => {
                write!(f, "{} is deprecated twice", name.to_display_string())
            }
        }
    }
}
impl std::error::Error for DeprecationError {}

fn codec(error: InstanceRegistryError) -> DeprecationError {
    match error {
        InstanceRegistryError::Limit => DeprecationError::Limit,
        _ => DeprecationError::Malformed,
    }
}

/// Native append-only identity, distinct from the pin's serialized extension.
pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "deprecations", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// Whether `descriptor` is this journal's, which a module's `.olean` can carry: its own entries
/// become the pin's `deprecatedAttr` entries.
pub fn supports(descriptor_: &ExtensionDescriptor) -> bool {
    *descriptor_ == descriptor()
}

/// The journal's content identity, if it exists.
pub fn journal_digest(env: &Environment) -> Option<[u8; 32]> {
    env.extension(&journal_name())
        .map(|extension| extension.content_digest().0)
}

fn write_text(text: &str, out: &mut Vec<u8>) -> Result<(), DeprecationError> {
    if text.len() > MAX_TEXT_BYTES {
        return Err(DeprecationError::Limit);
    }
    out.extend(
        u32::try_from(text.len())
            .map_err(|_| DeprecationError::Limit)?
            .to_le_bytes(),
    );
    out.extend(text.as_bytes());
    Ok(())
}

fn take<'a>(bytes: &mut &'a [u8], count: usize) -> Result<&'a [u8], DeprecationError> {
    if bytes.len() < count {
        return Err(DeprecationError::Malformed);
    }
    let (head, rest) = bytes.split_at(count);
    *bytes = rest;
    Ok(head)
}

fn read_text(bytes: &mut &[u8]) -> Result<String, DeprecationError> {
    let length = u32::from_le_bytes(
        take(bytes, 4)?
            .try_into()
            .map_err(|_| DeprecationError::Malformed)?,
    );
    let length = usize::try_from(length).map_err(|_| DeprecationError::Limit)?;
    if length > MAX_TEXT_BYTES {
        return Err(DeprecationError::Limit);
    }
    String::from_utf8(take(bytes, length)?.to_vec()).map_err(|_| DeprecationError::Malformed)
}

fn encode(entry: &Deprecation, out: &mut Vec<u8>) -> Result<(), DeprecationError> {
    write_name(&entry.declaration, out).map_err(codec)?;
    let mut flags = 0;
    if entry.new_name.is_some() {
        flags |= HAS_NEW_NAME;
    }
    if entry.text.is_some() {
        flags |= HAS_TEXT;
    }
    if entry.since.is_some() {
        flags |= HAS_SINCE;
    }
    out.push(flags);
    if let Some(new_name) = &entry.new_name {
        if new_name.is_anonymous() {
            return Err(DeprecationError::Malformed);
        }
        write_name(new_name, out).map_err(codec)?;
    }
    if let Some(text) = &entry.text {
        write_text(text, out)?;
    }
    if let Some(since) = &entry.since {
        write_text(since, out)?;
    }
    Ok(())
}

fn decode(bytes: &mut &[u8]) -> Result<Deprecation, DeprecationError> {
    let declaration = read_name(bytes).map_err(codec)?;
    let flags = take(bytes, 1)?[0];
    if flags & !(HAS_NEW_NAME | HAS_TEXT | HAS_SINCE) != 0 {
        return Err(DeprecationError::Malformed);
    }
    let new_name = if flags & HAS_NEW_NAME != 0 {
        let name = read_name(bytes).map_err(codec)?;
        if name.is_anonymous() {
            return Err(DeprecationError::Malformed);
        }
        Some(name)
    } else {
        None
    };
    let text = (flags & HAS_TEXT != 0)
        .then(|| read_text(bytes))
        .transpose()?;
    let since = (flags & HAS_SINCE != 0)
        .then(|| read_text(bytes))
        .transpose()?;
    Ok(Deprecation {
        declaration,
        new_name,
        text,
        since,
    })
}

/// Record a batch of deprecations as one journal entry: one imported module's, kept together as
/// the pin keeps them, or one admitted source declaration's. Every declaration must be admitted
/// and appear once in `entries`; an empty batch records nothing. A declaration some earlier
/// entry already recorded is refused by [`Deprecations::read`].
pub fn register_module(
    env: &Environment,
    entries: &[Deprecation],
) -> Result<Environment, DeprecationError> {
    if entries.is_empty() {
        return Ok(env.clone());
    }
    if entries.len() > MAX_ENTRIES {
        return Err(DeprecationError::Limit);
    }
    let mut seen = BTreeSet::new();
    let mut payload = MAGIC.to_vec();
    payload.extend(
        u32::try_from(entries.len())
            .map_err(|_| DeprecationError::Limit)?
            .to_le_bytes(),
    );
    for entry in entries {
        if entry.declaration.is_anonymous() {
            return Err(DeprecationError::Malformed);
        }
        if !env.contains(&entry.declaration) {
            return Err(DeprecationError::UnknownDeclaration(
                entry.declaration.clone(),
            ));
        }
        if !seen.insert(&entry.declaration) {
            return Err(DeprecationError::Duplicate(entry.declaration.clone()));
        }
        encode(entry, &mut payload)?;
        if payload.len() > MAX_ENTRY_BYTES {
            return Err(DeprecationError::Limit);
        }
    }
    let env = match env.extension(&journal_name()) {
        Some(state) if state.descriptor != descriptor() => {
            return Err(DeprecationError::Malformed);
        }
        Some(state) if state.len() >= MAX_ROWS => return Err(DeprecationError::Limit),
        Some(_) => env.clone(),
        None => env
            .register_extension(descriptor())
            .map_err(|_| DeprecationError::Malformed)?,
    };
    env.push_extension_entry(&journal_name(), payload)
        .map_err(|_| DeprecationError::Malformed)
}

/// Every deprecation the journal records, by declaration.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Deprecations {
    entries: BTreeMap<Name, Deprecation>,
}

impl Deprecations {
    /// Validate and read every recorded deprecation. A declaration the environment does not
    /// hold, or one recorded twice, is refused, never kept or dropped quietly.
    pub fn read(env: &Environment) -> Result<Self, DeprecationError> {
        let Some(extension) = env.extension(&journal_name()) else {
            return Ok(Self::default());
        };
        if extension.descriptor != descriptor() {
            return Err(DeprecationError::Malformed);
        }
        if extension.len() > MAX_ROWS {
            return Err(DeprecationError::Limit);
        }
        let mut entries = BTreeMap::new();
        for row in extension.entries() {
            if row.payload.len() > MAX_ENTRY_BYTES {
                return Err(DeprecationError::Limit);
            }
            let mut bytes = row
                .payload
                .strip_prefix(MAGIC)
                .ok_or(DeprecationError::Malformed)?;
            let count = u32::from_le_bytes(
                take(&mut bytes, 4)?
                    .try_into()
                    .map_err(|_| DeprecationError::Malformed)?,
            );
            let count = usize::try_from(count).map_err(|_| DeprecationError::Limit)?;
            if count == 0 {
                return Err(DeprecationError::Malformed);
            }
            if entries.len().saturating_add(count) > MAX_ENTRIES {
                return Err(DeprecationError::Limit);
            }
            for _ in 0..count {
                let entry = decode(&mut bytes)?;
                if !env.contains(&entry.declaration) {
                    return Err(DeprecationError::UnknownDeclaration(entry.declaration));
                }
                if entries.contains_key(&entry.declaration) {
                    return Err(DeprecationError::Duplicate(entry.declaration));
                }
                entries.insert(entry.declaration.clone(), entry);
            }
            if !bytes.is_empty() {
                return Err(DeprecationError::Malformed);
            }
        }
        Ok(Self { entries })
    }

    /// `deprecatedAttr.getParam? env declaration`.
    pub fn get(&self, declaration: &Name) -> Option<&Deprecation> {
        self.entries.get(declaration)
    }

    /// Every deprecation, in declaration order.
    pub fn iter(&self) -> impl Iterator<Item = &Deprecation> {
        self.entries.values()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// One elaboration's deprecations, re-read only when the journal or the constants it validates
/// against (by count) can have changed. A failed read is never kept.
#[derive(Clone, Default)]
pub(crate) struct DeprecationCache {
    last: RefCell<Option<(CacheKey, Arc<Deprecations>)>>,
}

/// The journal's digest (if any) and the environment's constant count.
type CacheKey = (Option<[u8; 32]>, usize);

impl DeprecationCache {
    pub(crate) fn read(&self, env: &Environment) -> Result<Arc<Deprecations>, DeprecationError> {
        let key = (journal_digest(env), env.len());
        if let Some((cached, entries)) = self.last.borrow().as_ref()
            && *cached == key
        {
            return Ok(Arc::clone(entries));
        }
        let entries = Arc::new(Deprecations::read(env)?);
        *self.last.borrow_mut() = Some((key, Arc::clone(&entries)));
        Ok(entries)
    }
}

/// One resolution of a deprecated constant where the pin's `Linter.checkDeprecated` runs, at
/// the syntax it reports: byte offsets relative to the source the elaborator read, or `None`
/// for syntax with no position, which a front door must not place by guessing.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DeprecatedUse {
    pub constant: Name,
    pub span: Option<(usize, usize)>,
}

thread_local! {
    /// The installed sink, if a front door asked for the uses: each completed elaboration's
    /// uses, in completion order. Elaboration runs on the thread that entered its command.
    static SINK: RefCell<Option<Publications>> = const { RefCell::new(None) };
}

#[derive(Default)]
struct Publications {
    published: Vec<Vec<DeprecatedUse>>,
    uses: usize,
}

/// A front door's collection of the [`DeprecatedUse`]s its elaborations publish, while it is
/// alive on this thread. Dropping it restores the sink it replaced.
pub struct UseSink {
    previous: Option<Publications>,
}

impl UseSink {
    /// Start collecting on this thread.
    pub fn install() -> Self {
        Self {
            previous: SINK.with(|sink| sink.borrow_mut().replace(Publications::default())),
        }
    }

    /// The uses published since the last call, as the pin logs them for one command. Each
    /// elaboration's own uses are kept as it recorded them, a repeat included (the pin checks a
    /// `match`'s identifier discriminant twice). This engine may elaborate a command's syntax
    /// more than once where the pin elaborates it once (a trial before the admitted run, a
    /// header before its body), so a later elaboration contributes a use only beyond the times
    /// the earlier ones already reported it at that place.
    pub fn take(&self) -> Vec<DeprecatedUse> {
        let publications = SINK.with(|sink| {
            sink.borrow_mut()
                .as_mut()
                .map(std::mem::take)
                .unwrap_or_default()
        });
        let mut merged: Vec<DeprecatedUse> = Vec::new();
        let mut reported: BTreeMap<(Option<(usize, usize)>, Name), usize> = BTreeMap::new();
        for uses in publications.published {
            let mut counted: BTreeMap<(Option<(usize, usize)>, Name), usize> = BTreeMap::new();
            for used in uses {
                let key = (used.span, used.constant.clone());
                let count = counted.entry(key.clone()).or_default();
                *count += 1;
                let already = reported.entry(key).or_default();
                if *count > *already {
                    *already = *count;
                    merged.push(used);
                }
            }
        }
        merged
    }
}

impl Drop for UseSink {
    fn drop(&mut self) {
        let previous = self.previous.take();
        SINK.with(|sink| *sink.borrow_mut() = previous);
    }
}

/// Hand a completed elaboration's uses to the installed sink, if any. `false` when the sink
/// would exceed its bound.
pub(crate) fn publish(uses: &[DeprecatedUse]) -> bool {
    if uses.is_empty() {
        return true;
    }
    SINK.with(|sink| match sink.borrow_mut().as_mut() {
        Some(collected) if collected.uses.saturating_add(uses.len()) > MAX_USES => false,
        Some(collected) => {
            collected.uses += uses.len();
            collected.published.push(uses.to_vec());
            true
        }
        None => true,
    })
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

    fn entry(declaration: &str, new_name: Option<&str>, text: Option<&str>) -> Deprecation {
        Deprecation {
            declaration: n(declaration),
            new_name: new_name.map(n),
            text: text.map(str::to_owned),
            since: Some("2025-01-01".to_owned()),
        }
    }

    #[test]
    fn modules_record_their_entries_and_the_journal_reads_them_all() {
        let env = with_axioms(&["A.old", "A.new", "B.gone"]);
        assert!(Deprecations::read(&env).unwrap().is_empty());
        assert_eq!(register_module(&env, &[]).unwrap(), env);
        let env = register_module(&env, &[entry("A.old", Some("A.new"), None)]).unwrap();
        let env = register_module(&env, &[entry("B.gone", None, Some("use `x`"))]).unwrap();
        let read = Deprecations::read(&env).unwrap();
        assert_eq!(read.len(), 2);
        assert_eq!(
            read.get(&n("A.old")),
            Some(&entry("A.old", Some("A.new"), None))
        );
        assert_eq!(
            read.get(&n("B.gone"))
                .and_then(|entry| entry.text.as_deref()),
            Some("use `x`")
        );
        assert_eq!(read.get(&n("A.new")), None);
    }

    #[test]
    fn an_entry_must_name_one_admitted_declaration_once() {
        let env = with_axioms(&["A.old"]);
        assert_eq!(
            register_module(&env, &[entry("A.missing", None, None)]),
            Err(DeprecationError::UnknownDeclaration(n("A.missing")))
        );
        assert_eq!(
            register_module(
                &env,
                &[entry("A.old", None, None), entry("A.old", None, None)]
            ),
            Err(DeprecationError::Duplicate(n("A.old")))
        );
        let twice = register_module(&env, &[entry("A.old", None, None)]).unwrap();
        let twice = register_module(&twice, &[entry("A.old", None, None)]).unwrap();
        assert_eq!(
            Deprecations::read(&twice),
            Err(DeprecationError::Duplicate(n("A.old")))
        );
    }

    #[test]
    fn a_malformed_journal_is_refused_not_read_as_empty() {
        let env = with_axioms(&["A.old"]);
        let mut valid = MAGIC.to_vec();
        valid.extend(1_u32.to_le_bytes());
        encode(&entry("A.old", None, Some("t")), &mut valid).unwrap();
        let unknown_flag = {
            let mut payload = MAGIC.to_vec();
            payload.extend(1_u32.to_le_bytes());
            write_name(&n("A.old"), &mut payload).unwrap();
            payload.push(8);
            payload
        };
        for payload in [
            Vec::new(),
            MAGIC.to_vec(),
            [MAGIC, &0_u32.to_le_bytes()].concat(),
            [valid.as_slice(), &[0]].concat(),
            valid[..valid.len() - 1].to_vec(),
            unknown_flag,
        ] {
            let broken = env
                .register_extension(descriptor())
                .unwrap()
                .push_extension_entry(&journal_name(), payload)
                .unwrap();
            assert!(Deprecations::read(&broken).is_err());
        }
        let good = env
            .register_extension(descriptor())
            .unwrap()
            .push_extension_entry(&journal_name(), valid)
            .unwrap();
        assert!(
            Deprecations::read(&good)
                .unwrap()
                .get(&n("A.old"))
                .is_some()
        );
    }

    #[test]
    fn a_sink_collects_only_while_installed_and_restores_the_one_it_replaced() {
        let used = |name: &str| DeprecatedUse {
            constant: n(name),
            span: Some((1, 2)),
        };
        assert!(publish(&[used("ignored")]));
        let outer = UseSink::install();
        assert!(publish(&[used("a")]));
        {
            let inner = UseSink::install();
            assert!(publish(&[used("b")]));
            assert_eq!(inner.take(), vec![used("b")]);
        }
        assert!(publish(&[used("c")]));
        assert_eq!(outer.take(), vec![used("a"), used("c")]);
        // One elaboration's repeat is kept; a second elaboration of the same syntax adds only
        // what it reports beyond the first.
        assert!(publish(&[used("a"), used("a"), used("b")]));
        assert!(publish(&[used("a"), used("b"), used("b"), used("c")]));
        assert_eq!(
            outer.take(),
            vec![used("a"), used("a"), used("b"), used("b"), used("c")]
        );
        assert!(outer.take().is_empty());
        drop(outer);
        assert!(publish(&[used("after")]));
        assert!(UseSink::install().take().is_empty());
    }
}
