//! Content-keyed reuse of checked source modules across invocations (bead
//! `franken_lean-z8j.1.1`).
//!
//! A module's [`SourceModuleKey`] covers the checker identity, the options, the
//! session's base logical root, the module's name and source bytes, and the ordered
//! steps that build its imported environment. Each local dependency step carries that
//! dependency's result logical root. So editing a module changes its key and the key
//! of every module whose imported environment changed with it. A dependency whose
//! edit leaves its checked declarations and journals unchanged changes nothing
//! downstream.
//!
//! A record is never an answer by itself. A hit takes the recorded `.olean` artifact
//! and plans its declarations the way `fln check-olean` does. Every unit is then
//! admitted by both engines onto the module's real imported environment, which must
//! have the recorded base root, and the recorded journal rows are replayed. The
//! result must reach the recorded result root, and re-encoding the replayed module
//! must give the recorded artifact byte for byte. Anything else refuses the record
//! and the module is elaborated from source. Disk outputs never take part: the build
//! directory's `.olean` files are neither read nor trusted here.
//!
//! What re-admission cannot show is that the recorded declarations are the ones the
//! source elaborates to. That binding is the record store's: like the import records
//! of `fln-uyuz`, the store is a per-user trust boundary, not a kernel-signed receipt.
use super::reuse::CheckerIdentity;
use super::*;
use crate::{
    ArtifactReadings, OleanCheckLimits, OleanDecodeLimits, ReadingCheck, decode_olean_artifact,
    plan_olean_declarations,
};
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use fln_hash::domain::{Digest, Domain, DomainHasher};
use std::sync::Arc;

const RECORD_MAGIC: &[u8] = b"fln.source-module-record/1\0";
const RECORD_SEAL_PREFIX: &[u8] = b"fln.source-module-record-seal/1\0";
/// More journals than an artifact-mode module can carry today (one); a bound, not a model.
const MAX_RECORDED_EXTENSIONS: usize = 64;

/// The `Domain::CacheKey` digest a source module record is stored and found under.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SourceModuleKey(Digest);

/// One step that builds a module's imported environment, in replay order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum KeyStep {
    /// An external module's metadata, from the session's checked import closure.
    External(Name),
    /// A local dependency, identified by the result root of its checked environment.
    Source(Name, LogicalRoot),
}

fn field(hasher: &mut DomainHasher, bytes: &[u8]) {
    hasher.update(&u64::try_from(bytes.len()).unwrap_or(u64::MAX).to_le_bytes());
    hasher.update(bytes);
}

impl SourceModuleKey {
    /// Every field is length-prefixed or fixed-width, so distinct inputs never share an
    /// encoding. The session base root identifies the external world; the per-module
    /// base root is checked against the record on every hit. A non-default `mode` is a
    /// trailing fixed-width field after the counted steps: frontier admits recursor
    /// code the default refuses (bead `franken_lean-z8j.1.6.6`), so its records must
    /// never answer a default lookup, while every default key stays what it was.
    pub(super) fn compute(
        checker: CheckerIdentity,
        mode: fln_core::mode::Mode,
        options: &KVMap,
        session_base: LogicalRoot,
        name: &Name,
        source: &[u8],
        steps: &[KeyStep],
    ) -> Self {
        let mut hasher = DomainHasher::new(Domain::CacheKey);
        hasher.update(b"fln.source-module-key/1\0");
        hasher.update(&checker.digest().0);
        field(&mut hasher, &options.to_canonical_bytes());
        hasher.update(&session_base.0.0);
        field(&mut hasher, &name.to_canonical_bytes());
        field(&mut hasher, source);
        hasher.update(&u64::try_from(steps.len()).unwrap_or(u64::MAX).to_le_bytes());
        for step in steps {
            match step {
                KeyStep::External(name) => {
                    hasher.update(&[0]);
                    field(&mut hasher, &name.to_canonical_bytes());
                }
                KeyStep::Source(name, root) => {
                    hasher.update(&[1]);
                    field(&mut hasher, &name.to_canonical_bytes());
                    hasher.update(&root.0.0);
                }
            }
        }
        if mode != fln_core::mode::Mode::DEFAULT {
            hasher.update(b"mode\0");
            hasher.update(&[mode.tag()]);
        }
        SourceModuleKey(hasher.finalize())
    }

    pub fn digest(self) -> Digest {
        self.0
    }

    pub fn to_hex(self) -> String {
        self.0.to_hex()
    }
}

/// Bytes keyed by [`SourceModuleKey`]. The store holds no trust of its own: whatever
/// it returns is parsed strictly, bound to the key, checker and module, and re-admitted.
pub trait SourceModuleStore {
    /// The bytes stored under `key`, `Ok(None)` when there are none.
    fn load(&self, key: SourceModuleKey) -> std::result::Result<Option<Vec<u8>>, String>;
    /// Store `bytes` under `key`, replacing what was there.
    fn save(&self, key: SourceModuleKey, bytes: &[u8]) -> std::result::Result<(), String>;
}

/// Who is checking, and where module records live. Without it a build consults and
/// writes no record.
#[derive(Clone, Copy)]
pub struct PersistedModules<'a> {
    pub checker: CheckerIdentity,
    pub store: &'a dyn SourceModuleStore,
}

/// Why a record was not used. Each refusal leaves the module to be elaborated from
/// source; none is a verdict about the module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleRecordRefusal {
    /// The bytes are not a well-formed record: the reason names the first violation.
    Malformed(&'static str),
    /// The body does not match its seal.
    Seal,
    /// The record was stored under another key.
    Key,
    /// The record was made by another checker identity.
    CheckerIdentity,
    /// The record is for another module.
    Module,
    /// The module's imported environment is not the one the record was made over.
    BaseRoot,
    /// The recorded artifact does not decode.
    Decode,
    /// The recorded declarations cannot be planned as new declarations over the base.
    Plan,
    /// A recorded declaration was refused, or did not finish, under admission.
    Admission,
    /// A recorded journal row cannot be replayed, or is not an artifact journal.
    Extension,
    /// The replayed environment does not reach the recorded result root.
    ResultRoot,
    /// Re-encoding the replayed module does not give the recorded artifact.
    Artifact,
}

impl ModuleRecordRefusal {
    /// The stable code reports carry, as `refused:<code>`.
    pub fn code(&self) -> &'static str {
        match self {
            Self::Malformed(_) => "malformed",
            Self::Seal => "seal",
            Self::Key => "key",
            Self::CheckerIdentity => "checker-identity",
            Self::Module => "module",
            Self::BaseRoot => "base-root",
            Self::Decode => "decode",
            Self::Plan => "plan",
            Self::Admission => "admission",
            Self::Extension => "extension",
            Self::ResultRoot => "result-root",
            Self::Artifact => "artifact",
        }
    }
}

impl std::fmt::Display for ModuleRecordRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Malformed(reason) => write!(f, "malformed record: {reason}"),
            other => f.write_str(other.code()),
        }
    }
}

/// One journal's rows that a module appended, as the artifact-mode export carries them.
#[derive(Debug, Clone, PartialEq, Eq)]
struct RecordedExtension {
    descriptor: ExtensionDescriptor,
    entries: Vec<Vec<u8>>,
}

/// What a successful elaboration leaves for a later invocation: the artifact, the
/// journal rows the module appended, its roots, and the counts a hit must charge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceModuleRecord {
    key: SourceModuleKey,
    checker: Digest,
    name: Vec<u8>,
    base_root: Digest,
    result_root: Digest,
    commands: u64,
    theorems: u64,
    work: u64,
    bytes: u64,
    extensions: Vec<RecordedExtension>,
    artifact: Vec<u8>,
}

fn seal(body: &[u8]) -> Digest {
    let mut hasher = DomainHasher::new(Domain::CacheKey);
    hasher.update(RECORD_SEAL_PREFIX);
    hasher.update(body);
    hasher.finalize()
}

fn merge_code(merge: MergeSemantics) -> u8 {
    match merge {
        MergeSemantics::AppendOrdered => 0,
        MergeSemantics::SetUnion => 1,
        MergeSemantics::ConflictsRequireReview => 2,
    }
}
fn checkpoint_code(checkpoint: CheckpointSemantics) -> u8 {
    match checkpoint {
        CheckpointSemantics::JournalSuffix => 0,
        CheckpointSemantics::FullJournal => 1,
    }
}
fn provenance_code(provenance: PayloadProvenance) -> u8 {
    match provenance {
        PayloadProvenance::Understood => 0,
        PayloadProvenance::Opaque => 1,
    }
}

/// A strict reader: every read is bounded by the bytes that remain.
struct Reader<'a>(&'a [u8]);
impl<'a> Reader<'a> {
    fn take(&mut self, n: usize) -> std::result::Result<&'a [u8], ModuleRecordRefusal> {
        if n > self.0.len() {
            return Err(ModuleRecordRefusal::Malformed("truncated"));
        }
        let (head, tail) = self.0.split_at(n);
        self.0 = tail;
        Ok(head)
    }
    fn u8(&mut self) -> std::result::Result<u8, ModuleRecordRefusal> {
        Ok(self.take(1)?[0])
    }
    fn u32(&mut self) -> std::result::Result<u32, ModuleRecordRefusal> {
        let bytes: [u8; 4] = self.take(4)?.try_into().unwrap_or([0; 4]);
        Ok(u32::from_le_bytes(bytes))
    }
    fn u64(&mut self) -> std::result::Result<u64, ModuleRecordRefusal> {
        let bytes: [u8; 8] = self.take(8)?.try_into().unwrap_or([0; 8]);
        Ok(u64::from_le_bytes(bytes))
    }
    fn digest(&mut self) -> std::result::Result<Digest, ModuleRecordRefusal> {
        let bytes: [u8; 32] = self.take(32)?.try_into().unwrap_or([0; 32]);
        Ok(Digest(bytes))
    }
    fn bytes32(&mut self) -> std::result::Result<&'a [u8], ModuleRecordRefusal> {
        let length =
            usize::try_from(self.u32()?).map_err(|_| ModuleRecordRefusal::Malformed("length"))?;
        self.take(length)
    }
    fn bytes64(&mut self) -> std::result::Result<&'a [u8], ModuleRecordRefusal> {
        let length =
            usize::try_from(self.u64()?).map_err(|_| ModuleRecordRefusal::Malformed("length"))?;
        self.take(length)
    }
}

fn put32(out: &mut Vec<u8>, bytes: &[u8]) {
    out.extend(u32::try_from(bytes.len()).unwrap_or(u32::MAX).to_le_bytes());
    out.extend(bytes);
}

impl SourceModuleRecord {
    pub fn key(&self) -> SourceModuleKey {
        self.key
    }

    /// The sealed byte form: a magic line, fixed-width digests and counts,
    /// length-prefixed fields, then the seal over everything before it.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = RECORD_MAGIC.to_vec();
        out.extend(self.key.0.0);
        out.extend(self.checker.0);
        out.extend(self.base_root.0);
        out.extend(self.result_root.0);
        put32(&mut out, &self.name);
        for count in [self.commands, self.theorems, self.work, self.bytes] {
            out.extend(count.to_le_bytes());
        }
        out.extend(
            u32::try_from(self.extensions.len())
                .unwrap_or(u32::MAX)
                .to_le_bytes(),
        );
        for extension in &self.extensions {
            put32(&mut out, &extension.descriptor.name.to_canonical_bytes());
            out.push(merge_code(extension.descriptor.merge));
            out.push(checkpoint_code(extension.descriptor.checkpoint));
            out.push(provenance_code(extension.descriptor.provenance));
            out.extend(
                u32::try_from(extension.entries.len())
                    .unwrap_or(u32::MAX)
                    .to_le_bytes(),
            );
            for entry in &extension.entries {
                put32(&mut out, entry);
            }
        }
        out.extend(
            u64::try_from(self.artifact.len())
                .unwrap_or(u64::MAX)
                .to_le_bytes(),
        );
        out.extend(&self.artifact);
        let sealed = seal(&out);
        out.extend(sealed.0);
        out
    }

    /// Parse `bytes` as the record stored under `key` for `module` by `checker`.
    /// Never panics; every malformation is a typed refusal.
    pub fn parse(
        bytes: &[u8],
        key: SourceModuleKey,
        checker: CheckerIdentity,
        module: &Name,
    ) -> std::result::Result<Self, ModuleRecordRefusal> {
        let Some(body_length) = bytes.len().checked_sub(32) else {
            return Err(ModuleRecordRefusal::Malformed("truncated"));
        };
        let (body, sealed) = bytes.split_at(body_length);
        let mut reader = Reader(body);
        if reader.take(RECORD_MAGIC.len())? != RECORD_MAGIC {
            return Err(ModuleRecordRefusal::Malformed("schema"));
        }
        if seal(body).0 != sealed {
            return Err(ModuleRecordRefusal::Seal);
        }
        let recorded_key = SourceModuleKey(reader.digest()?);
        let recorded_checker = reader.digest()?;
        let base_root = reader.digest()?;
        let result_root = reader.digest()?;
        let name = reader.bytes32()?.to_vec();
        let commands = reader.u64()?;
        let theorems = reader.u64()?;
        let work = reader.u64()?;
        let recorded_bytes = reader.u64()?;
        let count = usize::try_from(reader.u32()?)
            .map_err(|_| ModuleRecordRefusal::Malformed("extension count"))?;
        if count > MAX_RECORDED_EXTENSIONS {
            return Err(ModuleRecordRefusal::Malformed("extension count"));
        }
        let journal = fln_elab::instances::export::journal_name().to_canonical_bytes();
        let mut extensions = Vec::with_capacity(count);
        for _ in 0..count {
            // An artifact-mode module can append only the journals its writer can
            // serialize; the name is checked here and the descriptor below.
            if reader.bytes32()? != journal.as_slice() {
                return Err(ModuleRecordRefusal::Extension);
            }
            let merge = match reader.u8()? {
                0 => MergeSemantics::AppendOrdered,
                1 => MergeSemantics::SetUnion,
                2 => MergeSemantics::ConflictsRequireReview,
                _ => return Err(ModuleRecordRefusal::Malformed("merge")),
            };
            let checkpoint = match reader.u8()? {
                0 => CheckpointSemantics::JournalSuffix,
                1 => CheckpointSemantics::FullJournal,
                _ => return Err(ModuleRecordRefusal::Malformed("checkpoint")),
            };
            let provenance = match reader.u8()? {
                0 => PayloadProvenance::Understood,
                1 => PayloadProvenance::Opaque,
                _ => return Err(ModuleRecordRefusal::Malformed("provenance")),
            };
            let descriptor = ExtensionDescriptor {
                name: fln_elab::instances::export::journal_name(),
                merge,
                checkpoint,
                provenance,
            };
            if !fln_elab::instances::export::supports(&descriptor) {
                return Err(ModuleRecordRefusal::Extension);
            }
            let rows = usize::try_from(reader.u32()?)
                .map_err(|_| ModuleRecordRefusal::Malformed("row count"))?;
            // Every row costs at least its four length bytes.
            if rows > reader.0.len() / 4 {
                return Err(ModuleRecordRefusal::Malformed("row count"));
            }
            let mut entries = Vec::with_capacity(rows);
            for _ in 0..rows {
                entries.push(reader.bytes32()?.to_vec());
            }
            extensions.push(RecordedExtension {
                descriptor,
                entries,
            });
        }
        let artifact = reader.bytes64()?.to_vec();
        if !reader.0.is_empty() {
            return Err(ModuleRecordRefusal::Malformed("trailing bytes"));
        }
        if recorded_key != key {
            return Err(ModuleRecordRefusal::Key);
        }
        if recorded_checker != checker.digest() {
            return Err(ModuleRecordRefusal::CheckerIdentity);
        }
        if name != module.to_canonical_bytes() {
            return Err(ModuleRecordRefusal::Module);
        }
        Ok(Self {
            key,
            checker: recorded_checker,
            name,
            base_root,
            result_root,
            commands,
            theorems,
            work,
            bytes: recorded_bytes,
            extensions,
            artifact,
        })
    }
}

/// An elaborated module awaiting its record: everything but the encoded artifact,
/// which exists only after the build's encodings succeed.
pub(super) struct PendingRecord {
    pub(super) name: Name,
    pub(super) key: SourceModuleKey,
    pub(super) export: Arc<replay::Export>,
    pub(super) base_root: LogicalRoot,
    pub(super) result_root: LogicalRoot,
    pub(super) commands: usize,
    pub(super) theorems: usize,
    pub(super) work: usize,
    pub(super) bytes: usize,
}

impl PendingRecord {
    pub(super) fn record(&self, checker: CheckerIdentity, artifact: &[u8]) -> SourceModuleRecord {
        let count = |n: usize| u64::try_from(n).unwrap_or(u64::MAX);
        SourceModuleRecord {
            key: self.key,
            checker: checker.digest(),
            name: self.name.to_canonical_bytes(),
            base_root: self.base_root.0,
            result_root: self.result_root.0,
            commands: count(self.commands),
            theorems: count(self.theorems),
            work: count(self.work),
            bytes: count(self.bytes),
            extensions: self
                .export
                .journal_suffixes()
                .map(|(descriptor, entries)| RecordedExtension {
                    descriptor: descriptor.clone(),
                    entries: entries.iter().map(|entry| entry.to_vec()).collect(),
                })
                .collect(),
            artifact: artifact.to_vec(),
        }
    }
}

/// A record re-admitted over its module's imported environment.
pub(super) struct RecordHit {
    pub(super) engine: Engine,
    pub(super) export: Arc<replay::Export>,
    pub(super) artifact: Arc<artifacts::PendingArtifact>,
    pub(super) base_root: LogicalRoot,
    pub(super) result_root: LogicalRoot,
    pub(super) commands: usize,
    pub(super) theorems: usize,
    pub(super) work: usize,
    pub(super) bytes: usize,
}

type Verdict = std::result::Result<RecordHit, ModuleRecordRefusal>;

/// Re-admit `record` for `module` over `imported`, the environment its own steps just
/// built. `Ok(Complete(Err(_)))` is a refused record; cancellation and internal faults
/// keep their typed forms, and a resource stop in the meter is the caller's error.
#[allow(clippy::too_many_arguments)]
pub(super) fn readmit(
    record: &SourceModuleRecord,
    module: &Name,
    header: &SourceHeader,
    imported: &Engine,
    options: &KVMap,
    write_budget: OleanWriteBudget,
    meter: &mut Meter,
    cancellation: Option<&dyn CancellationProbe>,
) -> std::result::Result<Outcome<Verdict>, SourceModuleCheckError> {
    let refuse = |refusal| Ok(Outcome::Complete(Err(refusal)));
    let base_root = imported.logical_root(options);
    if base_root.0 != record.base_root {
        return refuse(ModuleRecordRefusal::BaseRoot);
    }
    let max_bytes = record.artifact.len().max(1);
    let limits = OleanCheckLimits::new(max_bytes, meter.limits.source.admission.kernel);
    let Ok(decoded) = decode_olean_artifact(&record.artifact, OleanDecodeLimits::new(max_bytes))
    else {
        return refuse(ModuleRecordRefusal::Decode);
    };
    let Ok(plan) = plan_olean_declarations(imported.environment(), &decoded.constants, limits)
    else {
        return refuse(ModuleRecordRefusal::Plan);
    };
    // A module's artifact holds only its own new declarations.
    if !plan.already_present.is_empty() || !plan.subsumed.is_empty() {
        return refuse(ModuleRecordRefusal::Plan);
    }
    // The checker seat judges each declaration as it reads the artifact itself
    // (bead `franken_lean-z8j.1.14`); a record it cannot read is not reused.
    let Ok(readings) = ArtifactReadings::new(&decoded.independent) else {
        return refuse(ModuleRecordRefusal::Decode);
    };
    let mut engine = imported.clone();
    let mut declarations = Vec::with_capacity(plan.order.len());
    for &unit in &plan.order {
        meter.work(1)?;
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-modules/record-declaration",
            )));
        }
        let Some(unit) = plan.units.get(unit) else {
            return Ok(Outcome::InternalFault(InternalFault::new(
                "source module records",
                "a planned unit index left its plan",
            )));
        };
        match engine.admit_declaration_unrooted(
            unit.declaration.clone(),
            options,
            meter.limits.source.admission,
            ReadingCheck::Artifact(&readings),
        ) {
            Ok(Outcome::Complete(admitted)) => {
                engine = admitted.engine;
                declarations.push(admitted.declaration);
            }
            Ok(Outcome::InternalFault(fault)) => return Ok(Outcome::InternalFault(fault)),
            // A refusal or a resource stop says nothing about the module: elaborating
            // it from source gives that verdict, with its own position.
            Ok(Outcome::Inconclusive(_)) | Err(_) => {
                return refuse(ModuleRecordRefusal::Admission);
            }
        }
    }
    for extension in &record.extensions {
        meter.work(1)?;
        let name = &extension.descriptor.name;
        let registered = match engine.environment.extension(name) {
            Some(existing) if existing.descriptor != extension.descriptor => {
                return refuse(ModuleRecordRefusal::Extension);
            }
            Some(_) => Ok(engine.environment.clone()),
            None => engine
                .environment
                .register_extension(extension.descriptor.clone()),
        };
        let Ok(mut environment) = registered else {
            return refuse(ModuleRecordRefusal::Extension);
        };
        for entry in &extension.entries {
            meter.work(1)?;
            meter.bytes(entry.len())?;
            match environment.push_extension_entry(name, Arc::<[u8]>::from(entry.as_slice())) {
                Ok(next) => environment = next,
                Err(_) => return refuse(ModuleRecordRefusal::Extension),
            }
        }
        engine.environment = environment;
    }
    let result_root = engine.environment.logical_root(options);
    if result_root.0 != record.result_root {
        return refuse(ModuleRecordRefusal::ResultRoot);
    }
    let Ok(export) = replay::Export::capture(
        module,
        imported.environment(),
        engine.environment(),
        declarations,
        meter,
    ) else {
        return refuse(ModuleRecordRefusal::Extension);
    };
    if export.require_artifact_support(module).is_err() {
        return refuse(ModuleRecordRefusal::Extension);
    }
    let Ok(artifact) = artifacts::PendingArtifact::capture(
        module,
        header,
        imported.environment(),
        engine.environment(),
        meter,
    ) else {
        return refuse(ModuleRecordRefusal::Artifact);
    };
    match artifact.encode(write_budget) {
        Ok(encoded) if encoded.bytes == record.artifact => {}
        _ => return refuse(ModuleRecordRefusal::Artifact),
    }
    let count = |n: u64| usize::try_from(n).unwrap_or(usize::MAX);
    Ok(Outcome::Complete(Ok(RecordHit {
        engine,
        export: Arc::new(export),
        artifact: Arc::new(artifact),
        base_root,
        result_root,
        commands: count(record.commands),
        theorems: count(record.theorems),
        work: count(record.work),
        bytes: count(record.bytes),
    })))
}

/// How one module of a build was obtained.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleDecision {
    /// Elaborated from source in this invocation.
    Elaborated,
    /// Reused from an earlier target of this same invocation.
    ReusedInSession,
    /// Re-admitted from a persisted record.
    Cached,
}

impl ModuleDecision {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Elaborated => "elaborated",
            Self::ReusedInSession => "reused-in-session",
            Self::Cached => "cached",
        }
    }
}

/// What the record store said for one module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleRecordLookup {
    /// No store was configured, or the module was reused within this invocation.
    NotConsulted,
    Absent,
    Hit,
    Refused(ModuleRecordRefusal),
    /// The store could not be read; the reason is the store's.
    Unavailable(String),
}

impl ModuleRecordLookup {
    pub fn code(&self) -> Option<String> {
        match self {
            Self::NotConsulted => None,
            Self::Absent => Some("absent".to_owned()),
            Self::Hit => Some("hit".to_owned()),
            Self::Refused(refusal) => Some(format!("refused:{}", refusal.code())),
            Self::Unavailable(_) => Some("unavailable".to_owned()),
        }
    }
}

/// Whether a record was written for an elaborated module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleRecordWrite {
    NotAttempted,
    Stored,
    Failed(String),
}

impl ModuleRecordWrite {
    pub fn code(&self) -> Option<&'static str> {
        match self {
            Self::NotAttempted => None,
            Self::Stored => Some("stored"),
            Self::Failed(_) => Some("failed"),
        }
    }
}

/// One module's provenance in a build, in the build's module order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleProvenance {
    pub name: Name,
    pub decision: ModuleDecision,
    /// Present whenever a record store was configured and consulted.
    pub key: Option<SourceModuleKey>,
    pub record: ModuleRecordLookup,
    pub record_write: ModuleRecordWrite,
    pub result_root: LogicalRoot,
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::RefCell;

    /// Records in memory, so a test can read, forge and re-file them.
    #[derive(Default)]
    struct Memory(RefCell<BTreeMap<SourceModuleKey, Vec<u8>>>);
    impl SourceModuleStore for Memory {
        fn load(&self, key: SourceModuleKey) -> std::result::Result<Option<Vec<u8>>, String> {
            Ok(self.0.borrow().get(&key).cloned())
        }
        fn save(&self, key: SourceModuleKey, bytes: &[u8]) -> std::result::Result<(), String> {
            self.0.borrow_mut().insert(key, bytes.to_vec());
            Ok(())
        }
    }

    fn n(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    const GRAPH: [(&str, &str); 4] = [
        ("Base", "prelude\ndef base (P : Prop) (h : P) : P := h\n"),
        (
            "Left",
            "prelude\nimport Base\ndef left (P : Prop) (h : P) : P := base P h\n",
        ),
        (
            "Right",
            "prelude\nimport Base\ndef right (P : Prop) (h : P) : P := base P h\n",
        ),
        (
            "Main",
            "prelude\nimport Left\nimport Right\ntheorem use (P : Prop) (h : P) : P := left P (right P h)\n",
        ),
    ];

    /// One whole invocation: a fresh session, as a new process would have.
    fn build(store: &Memory, checker: CheckerIdentity) -> SourceModuleBuild {
        compile(store, checker, fln_core::mode::Mode::DEFAULT, &GRAPH)
            .unwrap()
            .into_complete()
            .unwrap()
    }

    /// [`build`] of any graph whose entry is `Main`, by an engine in `mode`.
    fn compile(
        store: &Memory,
        checker: CheckerIdentity,
        mode: fln_core::mode::Mode,
        graph: &[(&str, &str)],
    ) -> std::result::Result<Outcome<SourceModuleBuild>, SourceModuleBuildError> {
        let names: Vec<_> = graph.iter().map(|(name, _)| n(name)).collect();
        let inputs: Vec<_> = graph
            .iter()
            .zip(&names)
            .map(|((_, source), name)| SourceModuleInput {
                name,
                source: source.as_bytes(),
            })
            .collect();
        let limits = SourceModuleCheckLimits::new(SourceCheckLimits::new(
            EngineAdmissionLimits::new(Budget::for_stack_bytes(2 * 1024 * 1024)),
        ));
        let mut session = SourceModuleSession::new(
            Engine::builder().mode(mode).build_empty(),
            KVMap::new(),
            limits,
            SourceModuleCacheLimits::default(),
        );
        session.compile_with_records(
            &inputs,
            &n("Main"),
            OleanWriteBudget::default(),
            Some(PersistedModules { checker, store }),
            None,
        )
    }

    fn rows(build: &SourceModuleBuild) -> Vec<(String, ModuleDecision, Option<String>)> {
        build
            .modules
            .iter()
            .map(|row| {
                (
                    row.name.to_display_string(),
                    row.decision,
                    row.record.code(),
                )
            })
            .collect()
    }

    fn products(build: &SourceModuleBuild) -> Vec<(Name, Vec<u8>)> {
        build
            .artifacts
            .iter()
            .map(|artifact| (artifact.name.clone(), artifact.bytes.clone()))
            .collect()
    }

    fn key_of(build: &SourceModuleBuild, module: &str) -> SourceModuleKey {
        build
            .modules
            .iter()
            .find(|row| row.name == n(module))
            .and_then(|row| row.key)
            .unwrap()
    }

    fn checker(label: &[u8]) -> CheckerIdentity {
        CheckerIdentity::of_executable(label)
    }

    /// A record a frontier session wrote never answers a default lookup: frontier admits
    /// recursor code the default refuses (bead `franken_lean-z8j.1.6.6`), and re-admission
    /// does not elaborate, so the mode is part of the key. The default session misses,
    /// elaborates, and refuses as the pin does.
    #[test]
    fn a_frontier_record_never_answers_a_default_lookup() {
        let graph = [(
            "Main",
            "prelude\ninductive T where | a | b (x : T)\ndef f (t : T) : T := T.rec (motive := fun _ => T) T.a (fun _ ih => T.b ih) t\n",
        )];
        let store = Memory::default();
        let identity = checker(b"one");
        let frontier = compile(&store, identity, fln_core::mode::Mode::Frontier, &graph)
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(frontier.modules[0].record_write, ModuleRecordWrite::Stored);
        let again = compile(&store, identity, fln_core::mode::Mode::Frontier, &graph)
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(again.modules[0].record, ModuleRecordLookup::Hit);
        let refusal = compile(&store, identity, fln_core::mode::Mode::DEFAULT, &graph)
            .expect_err("the default session elaborates the module and refuses it");
        assert!(
            format!("{refusal:?}").contains("UnsupportedRecursor"),
            "{refusal:?}"
        );
    }

    #[test]
    fn a_new_session_re_admits_every_recorded_module_and_reproduces_the_build() {
        let store = Memory::default();
        let cold = build(&store, checker(b"one"));
        assert_eq!((cold.elaborated_modules, cold.persisted_modules), (4, 0));
        assert!(
            cold.modules
                .iter()
                .all(|row| row.record_write == ModuleRecordWrite::Stored)
        );
        let warm = build(&store, checker(b"one"));
        assert_eq!((warm.elaborated_modules, warm.persisted_modules), (0, 4));
        assert!(
            warm.modules
                .iter()
                .all(|row| row.decision == ModuleDecision::Cached
                    && row.record == ModuleRecordLookup::Hit)
        );
        assert_eq!(products(&warm), products(&cold));
        assert_eq!(
            warm.checked.checked.result_logical_root,
            cold.checked.checked.result_logical_root
        );
        assert_eq!(
            warm.checked.checked.base_logical_root,
            cold.checked.checked.base_logical_root
        );
    }

    /// Records whose seals are valid but whose contents were changed. Re-admission must
    /// refuse each one, the module must be elaborated, and the build must equal a cold
    /// one. The last forgery is the old placeholder writer's 24-byte "artifact" (bead
    /// `franken_lean-z8j.1.1`): it cannot come back through a record.
    #[test]
    fn seal_valid_forgeries_are_refused_by_re_admission() {
        let store = Memory::default();
        let identity = checker(b"one");
        let cold = build(&store, identity);
        let base_key = key_of(&cold, "Base");
        let stored = |key| store.0.borrow().get(&key).cloned().unwrap();
        let original =
            SourceModuleRecord::parse(&stored(base_key), base_key, identity, &n("Base")).unwrap();
        let left = SourceModuleRecord::parse(
            &stored(key_of(&cold, "Left")),
            key_of(&cold, "Left"),
            identity,
            &n("Left"),
        )
        .unwrap();
        let journal = ExtensionDescriptor {
            name: fln_elab::instances::export::journal_name(),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::FullJournal,
            provenance: PayloadProvenance::Understood,
        };
        assert!(fln_elab::instances::export::supports(&journal));
        let flip = |digest: Digest| {
            let mut bytes = digest.0;
            bytes[0] ^= 1;
            Digest(bytes)
        };
        let forgeries: Vec<(&str, SourceModuleRecord)> = vec![
            (
                "result-root",
                SourceModuleRecord {
                    result_root: flip(original.result_root),
                    ..original.clone()
                },
            ),
            (
                "base-root",
                SourceModuleRecord {
                    base_root: flip(original.base_root),
                    ..original.clone()
                },
            ),
            // Left's declarations name `base`, which Base's imported world lacks.
            (
                "plan",
                SourceModuleRecord {
                    artifact: left.artifact.clone(),
                    ..original.clone()
                },
            ),
            (
                "result-root",
                SourceModuleRecord {
                    extensions: vec![RecordedExtension {
                        descriptor: journal,
                        entries: vec![b"a row the module never appended".to_vec()],
                    }],
                    ..original.clone()
                },
            ),
            (
                "decode",
                SourceModuleRecord {
                    artifact: b"fln-olean-artifact:Base".to_vec(),
                    ..original.clone()
                },
            ),
        ];
        for (code, forged) in forgeries {
            store.save(base_key, &forged.to_bytes()).unwrap();
            let rebuilt = build(&store, identity);
            assert_eq!(
                rows(&rebuilt)[0],
                (
                    "Base".to_owned(),
                    ModuleDecision::Elaborated,
                    Some(format!("refused:{code}"))
                ),
                "{code}"
            );
            assert_eq!(rebuilt.modules[0].record_write, ModuleRecordWrite::Stored);
            // Base's elaboration reaches the same root, so its dependents still hit.
            assert_eq!(rebuilt.persisted_modules, 3, "{code}");
            assert_eq!(products(&rebuilt), products(&cold), "{code}");
            assert_eq!(
                stored(base_key),
                original.to_bytes(),
                "{code}: not rewritten"
            );
        }
    }

    #[test]
    fn records_from_another_checker_or_filed_under_another_key_are_refused() {
        let store = Memory::default();
        let one = checker(b"one");
        let two = checker(b"two");
        let first = build(&store, one);
        // Another identity has other keys: nothing of the first build's is consulted.
        let second = build(&store, two);
        assert_eq!(second.elaborated_modules, 4);
        assert!(
            second
                .modules
                .iter()
                .all(|row| row.record == ModuleRecordLookup::Absent)
        );
        let base_one = key_of(&first, "Base");
        let base_two = key_of(&second, "Base");
        assert_ne!(base_one, base_two);
        let record =
            SourceModuleRecord::parse(&store.0.borrow()[&base_one], base_one, one, &n("Base"))
                .unwrap();
        // The first identity's record, re-keyed and re-sealed for the second key.
        let rekeyed = SourceModuleRecord {
            key: base_two,
            ..record.clone()
        };
        store.save(base_two, &rekeyed.to_bytes()).unwrap();
        let refused = build(&store, two);
        assert_eq!(
            refused.modules[0].record,
            ModuleRecordLookup::Refused(ModuleRecordRefusal::CheckerIdentity)
        );
        // The first identity's bytes as they are, filed under the second key.
        store.save(base_two, &record.to_bytes()).unwrap();
        let misfiled = build(&store, two);
        assert_eq!(
            misfiled.modules[0].record,
            ModuleRecordLookup::Refused(ModuleRecordRefusal::Key)
        );
        assert_eq!(products(&misfiled), products(&first));
    }

    #[test]
    fn every_damaged_record_byte_is_refused_without_panicking() {
        let store = Memory::default();
        let identity = checker(b"one");
        let cold = build(&store, identity);
        let key = key_of(&cold, "Main");
        let bytes = store.0.borrow()[&key].clone();
        assert!(SourceModuleRecord::parse(&bytes, key, identity, &n("Main")).is_ok());
        assert_eq!(
            SourceModuleRecord::parse(&bytes, key, identity, &n("Base")),
            Err(ModuleRecordRefusal::Module)
        );
        for index in 0..bytes.len() {
            let mut damaged = bytes.clone();
            damaged[index] ^= 0x40;
            assert!(
                SourceModuleRecord::parse(&damaged, key, identity, &n("Main")).is_err(),
                "byte {index}"
            );
        }
        for length in 0..bytes.len() {
            assert!(
                SourceModuleRecord::parse(&bytes[..length], key, identity, &n("Main")).is_err(),
                "length {length}"
            );
        }
    }
}
