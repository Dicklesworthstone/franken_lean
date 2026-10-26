//! Sealed, self-contained `.olean` declaration verification by full recomputation.
//!
//! A receipt binds a closed, named module graph, every public/server/private byte
//! stream, the exact ordered options, the compiler pin, and the expected roots.
//! Those bindings are claims, not proof: verification starts with an empty engine
//! and sends the complete graph through both ordinary `.olean` readers and checker
//! seats. Certificates and warm caches cannot authorize any declaration here.
//!
//! Success checks declarations relative to the explicitly supplied axioms. It does
//! not establish those axioms, execute persisted extensions, or claim the unfinished
//! certificate replay fast path. Legacy cartridges are identified separately and
//! must use their existing transport-integrity verifier.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::outcome::ResourceUsage;
use fln_hash::canon::{CanonError, CanonReader, CanonWriter, Canonical, DecodeBudget, SchemaId};
use fln_hash::cartridge::{
    CartridgeArchiveV1, CartridgeBuilderV1, CartridgeDecodeBudgetsV1, CartridgeObjectIdV1,
    CartridgeObjectKindV1, CartridgeObjectV1, CartridgeRefusalV1, CartridgeTransportStateV1,
    ObjectPortabilityV1, ObjectRequirementV1, cartridge_object_id,
};
use fln_hash::domain::{Digest, Domain, hash};

use crate::{
    Budget, CheckedOleanSet, ContentRoot, Engine, EpochId, Inconclusive, KVMap, LogicalRoot, Mode,
    Name, OLEAN_PIN_COMMIT, OLEAN_PIN_TAG, OleanCheckError, OleanCheckLimits, OleanModuleInput,
    Outcome, ReproducibilityProfile,
};

/// The numeric epoch used by the pinned v4.32.0 toolchain's public artifacts.
pub const PINNED_EPOCH: EpochId = EpochId::new(4_032_000);

/// Full-recomputation capsule receipt; changing its encoding requires a new version.
pub const SCHEMA_OLEAN_CAPSULE: SchemaId = SchemaId {
    name: "fln.capsule.olean-replay",
    version: 1,
};

/// Independent transport, structural, expanded-input and checking ceilings.
#[derive(Debug, Clone, Copy)]
pub struct CapsuleLimits {
    pub check: OleanCheckLimits,
    pub max_archive_bytes: usize,
    pub max_profile_bytes: usize,
    /// Aggregate declared object bytes, including repeated chunks, before assembly.
    pub max_expanded_bytes: usize,
    /// Separate allowance for each outer archive, manifest and profile decoder.
    pub max_decode_nodes: u64,
}

impl CapsuleLimits {
    /// Defaults to an 8 MiB profile ceiling and four million structural nodes per
    /// decoder. The caller supplies the artifact allowance and calibrated kernel
    /// stack budget, just as for `Engine::check_olean_modules`.
    pub fn new(max_bytes: usize, kernel: Budget) -> Self {
        Self {
            check: OleanCheckLimits::new(max_bytes, kernel),
            max_archive_bytes: max_bytes,
            max_profile_bytes: max_bytes.min(8 * 1024 * 1024),
            max_expanded_bytes: max_bytes,
            max_decode_nodes: 4 * 1024 * 1024,
        }
    }
}

/// Evidence produced only after both checker seats completed for every module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SemanticCapsuleReport {
    pub manifest_root: Digest,
    pub archive_digest: Digest,
    pub base_logical_root: LogicalRoot,
    pub result_logical_root: LogicalRoot,
    pub modules: usize,
    pub declarations: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SealedOleanCapsule {
    pub bytes: Vec<u8>,
    pub report: SemanticCapsuleReport,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapsuleVerification {
    Semantic(SemanticCapsuleReport),
    /// No supported semantic-profile marker was present. This is not a semantic
    /// result or a replacement for the legacy object-integrity verifier.
    Legacy,
}

/// A completed refusal about the transport, profile or a checked declaration.
/// Resource exhaustion from this layer is returned as `Outcome::Inconclusive`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CapsuleError {
    Transport(CartridgeRefusalV1),
    IncompleteTransport,
    MalformedProfile(&'static str),
    ProfileCodec(CanonError),
    UnsupportedProfileVersion { seen: u16 },
    UnsupportedEpoch { seen: EpochId },
    RootMismatch { subject: &'static str },
    Check(Box<OleanCheckError>),
}

impl CapsuleError {
    /// Existing product diagnostic classes, authority bit and exit code. A
    /// checksum/profile failure is never projected as a rejected theorem.
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::Check(error) => match error.as_ref() {
                OleanCheckError::Admission(error) => {
                    crate::source_check::classify(&error.clone().into())
                }
                OleanCheckError::Decode(error) | OleanCheckError::ModuleDecode { error, .. }
                    if error.is_resource_exhaustion() =>
                {
                    ("resource", false, 3)
                }
                OleanCheckError::ModuleLimit { .. }
                | OleanCheckError::TotalBytesLimit { .. }
                | OleanCheckError::DeclarationLimit { .. }
                | OleanCheckError::DependencyPresentationLimit { .. }
                | OleanCheckError::AllocationFailure { .. }
                | OleanCheckError::HostMemory { .. } => ("resource", false, 3),
                OleanCheckError::InternalInvariant { .. } => ("internal-fault", false, 4),
                OleanCheckError::IndependentReadingDiffers { .. } => ("inconclusive", false, 3),
                OleanCheckError::MissingModuleImports { .. }
                | OleanCheckError::ImportsRequireResolver { .. } => {
                    ("unresolved-imports", false, 1)
                }
                OleanCheckError::UnsupportedDeclaration { .. }
                | OleanCheckError::MutualEnvelopeUnsupported { .. }
                | OleanCheckError::InductiveEnvelopeUnsupported { .. }
                | OleanCheckError::QuotientEnvelopeUnsupported { .. } => {
                    ("unsupported-declaration-unit", false, 1)
                }
                OleanCheckError::DuplicateModule { .. }
                | OleanCheckError::ModuleImportCycle { .. } => ("module-graph", false, 1),
                OleanCheckError::DuplicateDeclaration { .. }
                | OleanCheckError::ConflictingModuleDeclaration { .. }
                | OleanCheckError::MissingConstants { .. }
                | OleanCheckError::DependencyCycle { .. } => ("declaration-closure", false, 1),
                OleanCheckError::Decode(_) | OleanCheckError::ModuleDecode { .. } => {
                    ("decode", false, 1)
                }
                OleanCheckError::EmptyModuleSet | OleanCheckError::MissingCompanionParts { .. } => {
                    ("input", false, 1)
                }
            },
            Self::UnsupportedProfileVersion { .. } | Self::UnsupportedEpoch { .. } => {
                ("unsupported-profile", false, 1)
            }
            Self::Transport(_) | Self::IncompleteTransport => ("transport", false, 1),
            Self::MalformedProfile(_) | Self::ProfileCodec(_) | Self::RootMismatch { .. } => {
                ("semantic-profile", false, 1)
            }
        }
    }
}

impl fmt::Display for CapsuleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Transport(error) => write!(f, "capsule transport: {error:?}"),
            Self::IncompleteTransport => f.write_str("capsule is missing required object frames"),
            Self::MalformedProfile(detail) => write!(f, "capsule semantic profile: {detail}"),
            Self::ProfileCodec(error) => write!(f, "capsule semantic profile: {error}"),
            Self::UnsupportedProfileVersion { seen } => {
                write!(f, "unsupported capsule semantic profile version {seen}")
            }
            Self::UnsupportedEpoch { seen } => {
                write!(
                    f,
                    "unsupported capsule epoch {}; expected {}",
                    seen.get(),
                    PINNED_EPOCH.get()
                )
            }
            Self::RootMismatch { subject } => {
                write!(f, "capsule {subject} root mismatch after recomputation")
            }
            Self::Check(error) => write!(f, "capsule declaration checking: {error}"),
        }
    }
}

impl std::error::Error for CapsuleError {}

impl From<CartridgeRefusalV1> for CapsuleError {
    fn from(error: CartridgeRefusalV1) -> Self {
        Self::Transport(error)
    }
}

impl From<OleanCheckError> for CapsuleError {
    fn from(error: OleanCheckError) -> Self {
        Self::Check(Box::new(error))
    }
}

macro_rules! completed {
    ($value:expr) => {
        match $value {
            Outcome::Complete(value) => value,
            Outcome::Inconclusive(stop) => return Ok(Outcome::Inconclusive(stop)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        }
    };
}

fn limit<T>(
    resource: &'static str,
    allowed: u64,
    observed: u64,
    unit: StructuralUnit,
) -> Outcome<T> {
    Outcome::Inconclusive(
        Inconclusive::resource(ResourceUsage {
            reason: ResourceReason::StructuralBudget { unit },
            allowed,
            observed,
        })
        .with_progress(resource),
    )
}

fn engine(options: &KVMap) -> Engine {
    Engine::builder()
        .mode(Mode::Sound)
        .reproducibility(ReproducibilityProfile::Standard)
        .options(options.clone())
        .build_empty()
}

#[derive(Debug)]
struct ModuleRow {
    name: Name,
    public: CartridgeObjectIdV1,
    companions: Option<(CartridgeObjectIdV1, CartridgeObjectIdV1)>,
    base: LogicalRoot,
    result: LogicalRoot,
    declarations: u64,
}

impl ModuleRow {
    fn objects(&self) -> impl Iterator<Item = CartridgeObjectIdV1> {
        std::iter::once(self.public).chain(
            self.companions
                .into_iter()
                .flat_map(|(server, private)| [server, private]),
        )
    }
}

#[derive(Debug)]
struct Profile {
    options: KVMap,
    base: LogicalRoot,
    result: LogicalRoot,
    modules: Vec<ModuleRow>,
}

impl Profile {
    fn encode(&self, byte_limit: usize) -> Outcome<Vec<u8>> {
        let mut writer = CanonWriter::with_limit(byte_limit);
        writer.schema(SCHEMA_OLEAN_CAPSULE);
        writer.u64(PINNED_EPOCH.get() as u64);
        writer.u64((PINNED_EPOCH.get() >> 64) as u64);
        writer.u8(Mode::Sound.tag());
        writer.u8(ReproducibilityProfile::Standard.tag());
        writer.str(OLEAN_PIN_TAG);
        writer.str(OLEAN_PIN_COMMIT);
        self.options.write_body(&mut writer);
        writer.digest(&self.base.0);
        writer.digest(&self.result.0);
        writer.u64(self.modules.len() as u64);
        for row in &self.modules {
            row.name.write_body(&mut writer);
            writer.digest(&row.public.digest());
            writer.bool(row.companions.is_some());
            if let Some((server, private)) = row.companions {
                writer.digest(&server.digest());
                writer.digest(&private.digest());
            }
            writer.digest(&row.base.0);
            writer.digest(&row.result.0);
            writer.u64(row.declarations);
        }
        if writer.overflowed() {
            limit(
                "capsule profile bytes",
                byte_limit as u64,
                (byte_limit as u64).saturating_add(1),
                StructuralUnit::InputBytes,
            )
        } else {
            Outcome::Complete(writer.into_bytes())
        }
    }

    fn decode(bytes: &[u8], limits: CapsuleLimits) -> Result<Outcome<Self>, CapsuleError> {
        let mut reader = CanonReader::with_budget(
            bytes,
            DecodeBudget::new(limits.max_profile_bytes as u64, limits.max_decode_nodes),
        );
        macro_rules! read {
            ($value:expr) => {
                match $value {
                    Ok(value) => value,
                    Err(error) => {
                        return match reader.exhausted() {
                            Some(stop) => Ok(Outcome::Inconclusive(stop.into_inconclusive())),
                            None => Err(CapsuleError::ProfileCodec(error)),
                        }
                    }
                }
            };
        }
        if read!(reader.str()) != SCHEMA_OLEAN_CAPSULE.name {
            return Err(CapsuleError::MalformedProfile("schema name mismatch"));
        }
        let version = read!(reader.u16());
        if version != SCHEMA_OLEAN_CAPSULE.version {
            return Err(CapsuleError::UnsupportedProfileVersion { seen: version });
        }
        let low = read!(reader.u64()) as u128;
        let high = read!(reader.u64()) as u128;
        let epoch = EpochId::new(low | (high << 64));
        if epoch != PINNED_EPOCH {
            return Err(CapsuleError::UnsupportedEpoch { seen: epoch });
        }
        if read!(reader.u8()) != Mode::Sound.tag()
            || read!(reader.u8()) != ReproducibilityProfile::Standard.tag()
        {
            return Err(CapsuleError::MalformedProfile(
                "unsupported mode or reproducibility profile",
            ));
        }
        if read!(reader.str()) != OLEAN_PIN_TAG || read!(reader.str()) != OLEAN_PIN_COMMIT {
            return Err(CapsuleError::MalformedProfile("compiler pin mismatch"));
        }
        let options = read!(KVMap::read_body(&mut reader));
        let base = LogicalRoot(read!(read_digest(&mut reader)));
        let result = LogicalRoot(read!(read_digest(&mut reader)));
        let count = read!(reader.u64());
        let count_limit = (limits.check.max_modules as u64).min(limits.max_decode_nodes);
        if count > count_limit {
            return Ok(limit(
                "capsule module rows",
                count_limit,
                count,
                StructuralUnit::ProducedNodes,
            ));
        }
        // Even an anonymous name with no companions needs 113 bytes. Refuse an
        // impossible count before reserving memory from an attacker-owned u64.
        if count == 0 || count > (bytes.len() / 113) as u64 {
            return Err(CapsuleError::MalformedProfile(
                "empty or impossible module count",
            ));
        }
        let mut modules: Vec<ModuleRow> = Vec::new();
        if modules.try_reserve_exact(count as usize).is_err() {
            return Ok(limit(
                "capsule module allocation",
                count,
                count,
                StructuralUnit::ProducedNodes,
            ));
        }
        for _ in 0..count {
            let name = read!(Name::read_body(&mut reader));
            if name.is_anonymous() || modules.last().is_some_and(|row| row.name >= name) {
                return Err(CapsuleError::MalformedProfile(
                    "module names must be nonempty, unique and sorted",
                ));
            }
            let public = CartridgeObjectIdV1::new(read!(read_digest(&mut reader)));
            let companions = if read!(reader.bool()) {
                Some((
                    CartridgeObjectIdV1::new(read!(read_digest(&mut reader))),
                    CartridgeObjectIdV1::new(read!(read_digest(&mut reader))),
                ))
            } else {
                None
            };
            modules.push(ModuleRow {
                name,
                public,
                companions,
                base: LogicalRoot(read!(read_digest(&mut reader))),
                result: LogicalRoot(read!(read_digest(&mut reader))),
                declarations: read!(reader.u64()),
            });
        }
        let exhausted = reader.exhausted();
        if let Err(error) = reader.finish() {
            return match exhausted {
                Some(stop) => Ok(Outcome::Inconclusive(stop.into_inconclusive())),
                None => Err(CapsuleError::ProfileCodec(error)),
            };
        }
        Ok(Outcome::Complete(Self {
            options,
            base,
            result,
            modules,
        }))
    }
}

fn read_digest(reader: &mut CanonReader<'_>) -> Result<Digest, CanonError> {
    let mut bytes = [0; 32];
    for byte in &mut bytes {
        *byte = reader.u8()?;
    }
    Ok(Digest(bytes))
}

/// Check a complete named module set, then seal its checked byte streams and
/// claimed roots. No bytes are returned if either checker stops or refuses.
pub fn seal_olean_capsule(
    modules: &[OleanModuleInput<'_>],
    options: &KVMap,
    epoch: EpochId,
    limits: CapsuleLimits,
) -> Result<Outcome<SealedOleanCapsule>, CapsuleError> {
    if epoch != PINNED_EPOCH {
        return Err(CapsuleError::UnsupportedEpoch { seen: epoch });
    }
    if modules.iter().any(|module| module.name.is_anonymous()) {
        return Err(CapsuleError::MalformedProfile(
            "module names must be nonempty",
        ));
    }
    // Borrow and charge unique payloads before the builder copies any artifact.
    // Shared bytes occupy one object; the ordinary checking limit separately
    // charges every named module presentation.
    let payloads = completed!(payloads_within(modules, limits));
    let payload_bytes: usize = payloads.values().map(|bytes| bytes.len()).sum();
    let checked =
        completed!(engine(options).check_olean_modules(modules, options, limits.check)?);
    let input: BTreeMap<_, _> = modules.iter().map(|module| (module.name, module)).collect();
    let mut rows = Vec::with_capacity(checked.modules.len());
    for module in &checked.modules {
        let source = input
            .get(&module.name)
            .ok_or(CapsuleError::MalformedProfile(
                "checked module has no source artifact",
            ))?;
        let identify =
            |bytes: &[u8]| cartridge_object_id(CartridgeObjectKindV1::Declaration, bytes);
        let public = identify(source.artifact);
        let companions = match (source.server_artifact, source.private_artifact) {
            (Some(server), Some(private)) => Some((identify(server), identify(private))),
            (None, None) => None,
            _ => {
                return Err(CapsuleError::MalformedProfile(
                    "incomplete module companion pair",
                ));
            }
        };
        rows.push(ModuleRow {
            name: module.name.clone(),
            public,
            companions,
            base: module.base_logical_root,
            result: module.result_logical_root,
            declarations: module.declarations.len() as u64,
        });
    }
    rows.sort_by(|left, right| left.name.cmp(&right.name));
    let profile = Profile {
        options: options.clone(),
        base: checked.base_logical_root,
        result: checked.result_logical_root,
        modules: rows,
    };
    let profile_bytes = completed!(
        profile.encode(
            limits
                .max_profile_bytes
                .min(limits.max_expanded_bytes - payload_bytes),
        )
    );
    let mut builder =
        CartridgeBuilderV1::new(epoch, ContentRoot::new(checked.result_logical_root.0.0));
    for bytes in payloads.into_values() {
        builder.add_object(
            CartridgeObjectKindV1::Declaration,
            ObjectRequirementV1::Required,
            ObjectPortabilityV1::EpochBound,
            bytes,
        );
    }
    let receipt = builder.add_object(
        CartridgeObjectKindV1::Receipt,
        ObjectRequirementV1::Required,
        ObjectPortabilityV1::EpochBound,
        profile_bytes,
    );
    builder.add_root_receipt(receipt);
    let archive = builder.build()?;
    completed!(expanded_limit(&archive, limits));
    let Some(bytes) = archive.to_canonical_bytes_within(limits.max_archive_bytes)? else {
        return Ok(limit(
            "capsule archive bytes",
            limits.max_archive_bytes as u64,
            (limits.max_archive_bytes as u64).saturating_add(1),
            StructuralUnit::InputBytes,
        ));
    };
    let report = report(&archive, &bytes, &checked)?;
    Ok(Outcome::Complete(SealedOleanCapsule { bytes, report }))
}

fn payloads_within<'a>(
    modules: &[OleanModuleInput<'a>],
    limits: CapsuleLimits,
) -> Outcome<BTreeMap<CartridgeObjectIdV1, &'a [u8]>> {
    if modules.len() > limits.check.max_modules {
        return limit(
            "capsule input modules",
            limits.check.max_modules as u64,
            modules.len() as u64,
            StructuralUnit::ProducedNodes,
        );
    }
    let mut payloads = BTreeMap::new();
    let mut expanded = 0u64;
    let mut presented = 0u64;
    for module in modules {
        for bytes in std::iter::once(module.artifact)
            .chain(module.server_artifact)
            .chain(module.private_artifact)
        {
            presented = presented.saturating_add(bytes.len() as u64);
            if presented > limits.check.max_total_bytes as u64 {
                return limit(
                    "capsule module input bytes",
                    limits.check.max_total_bytes as u64,
                    presented,
                    StructuralUnit::InputBytes,
                );
            }
            if bytes.len() > limits.max_expanded_bytes {
                return limit(
                    "capsule expanded object bytes",
                    limits.max_expanded_bytes as u64,
                    bytes.len() as u64,
                    StructuralUnit::ExpandedWeight,
                );
            }
            let id = cartridge_object_id(CartridgeObjectKindV1::Declaration, bytes);
            if let std::collections::btree_map::Entry::Vacant(entry) = payloads.entry(id) {
                expanded = expanded.saturating_add(bytes.len() as u64);
                if expanded > limits.max_expanded_bytes as u64 {
                    return limit(
                        "capsule expanded object bytes",
                        limits.max_expanded_bytes as u64,
                        expanded,
                        StructuralUnit::ExpandedWeight,
                    );
                }
                entry.insert(bytes);
            }
        }
    }
    Outcome::Complete(payloads)
}

/// Recompute a semantic capsule's complete declaration closure from an empty
/// engine. Unknown versions of this profile are refused even when a caller would
/// otherwise allow legacy integrity-only archives.
pub fn verify_olean_capsule(
    bytes: &[u8],
    limits: CapsuleLimits,
) -> Result<Outcome<CapsuleVerification>, CapsuleError> {
    if bytes.len() > limits.max_archive_bytes {
        return Ok(limit(
            "capsule archive bytes",
            limits.max_archive_bytes as u64,
            bytes.len() as u64,
            StructuralUnit::InputBytes,
        ));
    }
    let decode_budget = DecodeBudget::new(limits.max_archive_bytes as u64, limits.max_decode_nodes);
    let archive = completed!(CartridgeArchiveV1::from_canonical_bytes_budgeted(
        bytes,
        CartridgeDecodeBudgetsV1 {
            archive: decode_budget,
            manifest: decode_budget,
        }
    ))?;
    if !matches!(
        archive.transport_state(),
        CartridgeTransportStateV1::Complete | CartridgeTransportStateV1::Sealed { .. }
    ) {
        return Err(CapsuleError::IncompleteTransport);
    }
    // Charge the full expansion before even probing receipts. Reusing small
    // frames across many objects cannot turn a compact archive into free work.
    completed!(expanded_limit(&archive, limits));
    let mut marker = CanonWriter::new();
    marker.str(SCHEMA_OLEAN_CAPSULE.name);
    let marker = marker.into_bytes();
    let mut candidate = None;
    for object in &archive.manifest.objects {
        // The schema prefix is reserved irrespective of the outer kind. Moving
        // a recognizable profile to a Declaration/Fixture cannot downgrade it
        // to an opaque legacy receipt; the required Receipt role is checked below.
        if object_starts_with(&archive, object, &marker) && candidate.replace(object.id).is_some() {
            return Err(CapsuleError::MalformedProfile("multiple semantic receipts"));
        }
    }
    let Some(receipt) = candidate else {
        return Ok(Outcome::Complete(CapsuleVerification::Legacy));
    };
    // Decode before root-role checks so a recognizable future version never
    // falls back to an interpretation with weaker guarantees.
    let profile_bytes =
        completed!(archive.assemble_object(receipt, limits.max_profile_bytes as u64))?
            .ok_or(CapsuleError::IncompleteTransport)?;
    let profile = completed!(Profile::decode(&profile_bytes, limits)?);
    if archive.manifest.epoch != PINNED_EPOCH {
        return Err(CapsuleError::UnsupportedEpoch {
            seen: archive.manifest.epoch,
        });
    }
    if archive.manifest.root_receipts.as_slice() != [receipt] {
        return Err(CapsuleError::MalformedProfile(
            "semantic receipt must be the unique root receipt",
        ));
    }
    require_object(&archive, receipt, CartridgeObjectKindV1::Receipt)?;
    let mut bound = BTreeSet::from([receipt]);
    let mut module_bytes = 0u64;
    for row in &profile.modules {
        for id in row.objects() {
            let object = require_object(&archive, id, CartridgeObjectKindV1::Declaration)?;
            module_bytes = module_bytes.saturating_add(object.len);
            if module_bytes > limits.check.max_total_bytes as u64 {
                return Ok(limit(
                    "capsule module input bytes",
                    limits.check.max_total_bytes as u64,
                    module_bytes,
                    StructuralUnit::InputBytes,
                ));
            }
            bound.insert(id);
        }
    }
    let mut objects = BTreeMap::new();
    for object in &archive.manifest.objects {
        if !bound.contains(&object.id)
            && (object.requirement == ObjectRequirementV1::Required
                || matches!(
                    object.kind,
                    CartridgeObjectKindV1::Declaration
                        | CartridgeObjectKindV1::Dependency
                        | CartridgeObjectKindV1::Receipt
                ))
        {
            return Err(CapsuleError::MalformedProfile(
                "unbound semantic or required object",
            ));
        }
        if object.id == receipt {
            continue;
        }
        // Optional advisory bytes receive ordinary object-integrity checking,
        // but their internal certificate/cache claims never enter the checker.
        let assembled =
            completed!(archive.assemble_object(object.id, limits.max_expanded_bytes as u64))?;
        if bound.contains(&object.id) {
            objects.insert(
                object.id,
                assembled.ok_or(CapsuleError::IncompleteTransport)?,
            );
        }
    }
    let get = |id| {
        objects
            .get(&id)
            .map(Vec::as_slice)
            .ok_or(CapsuleError::IncompleteTransport)
    };
    let inputs = profile
        .modules
        .iter()
        .map(|row| {
            let (server_artifact, private_artifact) = match row.companions {
                Some((server, private)) => (Some(get(server)?), Some(get(private)?)),
                None => (None, None),
            };
            Ok(OleanModuleInput {
                name: &row.name,
                artifact: get(row.public)?,
                server_artifact,
                private_artifact,
            })
        })
        .collect::<Result<Vec<_>, CapsuleError>>()?;
    let checked = completed!(engine(&profile.options).check_olean_modules(
        &inputs,
        &profile.options,
        limits.check
    )?);
    compare_roots(&archive, &profile, &checked)?;
    Ok(Outcome::Complete(CapsuleVerification::Semantic(report(
        &archive, bytes, &checked,
    )?)))
}

fn expanded_limit(archive: &CartridgeArchiveV1, limits: CapsuleLimits) -> Outcome<()> {
    let expanded = archive
        .manifest
        .objects
        .iter()
        .fold(0u64, |sum, object| sum.saturating_add(object.len));
    if expanded > limits.max_expanded_bytes as u64 {
        limit(
            "capsule expanded object bytes",
            limits.max_expanded_bytes as u64,
            expanded,
            StructuralUnit::ExpandedWeight,
        )
    } else {
        Outcome::Complete(())
    }
}

fn object_starts_with(
    archive: &CartridgeArchiveV1,
    object: &CartridgeObjectV1,
    marker: &[u8],
) -> bool {
    let mut consumed = 0;
    for chunk in &object.chunks {
        let Some(frame) = archive.frame(chunk.id) else {
            return false;
        };
        let take = frame.bytes.len().min(marker.len() - consumed);
        if frame.bytes[..take] != marker[consumed..consumed + take] {
            return false;
        }
        consumed += take;
        if consumed == marker.len() {
            return true;
        }
    }
    false
}

fn require_object(
    archive: &CartridgeArchiveV1,
    id: CartridgeObjectIdV1,
    kind: CartridgeObjectKindV1,
) -> Result<&CartridgeObjectV1, CapsuleError> {
    let object = archive
        .manifest
        .object(id)
        .ok_or(CapsuleError::MalformedProfile(
            "bound module object is absent",
        ))?;
    if object.kind != kind
        || object.requirement != ObjectRequirementV1::Required
        || object.portability != ObjectPortabilityV1::EpochBound
    {
        return Err(CapsuleError::MalformedProfile(
            "bound object has incorrect kind, requirement or portability",
        ));
    }
    Ok(object)
}

fn compare_roots(
    archive: &CartridgeArchiveV1,
    profile: &Profile,
    checked: &CheckedOleanSet,
) -> Result<(), CapsuleError> {
    if profile.base != checked.base_logical_root {
        return Err(CapsuleError::RootMismatch {
            subject: "base environment",
        });
    }
    if profile.result != checked.result_logical_root
        || archive.manifest.environment_root.bytes() != checked.result_logical_root.0.0
    {
        return Err(CapsuleError::RootMismatch {
            subject: "result environment",
        });
    }
    for module in &checked.modules {
        let row = profile
            .modules
            .binary_search_by(|row| row.name.cmp(&module.name))
            .ok()
            .map(|index| &profile.modules[index])
            .ok_or(CapsuleError::MalformedProfile(
                "recomputed module is absent from profile",
            ))?;
        if row.base != module.base_logical_root || row.result != module.result_logical_root {
            return Err(CapsuleError::RootMismatch {
                subject: "module environment",
            });
        }
        if row.declarations != module.declarations.len() as u64 {
            return Err(CapsuleError::MalformedProfile(
                "recomputed declaration count differs",
            ));
        }
    }
    Ok(())
}

fn report(
    archive: &CartridgeArchiveV1,
    bytes: &[u8],
    checked: &CheckedOleanSet,
) -> Result<SemanticCapsuleReport, CapsuleError> {
    Ok(SemanticCapsuleReport {
        manifest_root: archive.manifest_root()?,
        archive_digest: hash(Domain::Receipt, bytes),
        base_logical_root: checked.base_logical_root,
        result_logical_root: checked.result_logical_root,
        modules: checked.modules.len(),
        declarations: checked
            .modules
            .iter()
            .map(|module| module.declarations.len())
            .sum(),
    })
}
