//! Canonical certificate-cartridge transport (plan §§7.4, 8.6; OQ-13;
//! bead `franken_lean-eikp`).
//!
//! A cartridge has one logical manifest identity whether its transport is thin,
//! partially downloaded, sealed for air-gapped verification, or fully populated with
//! optional material. Frames are content-addressed and independently checkable;
//! staging validates a frame before mutating state; canonical archives sort frames by
//! identity; and a derived index gives deterministic random access without trusting
//! offsets supplied by the producer.
//!
//! OQ-13 is resolved narrowly. A warm definitional-equality cache is an optional,
//! advisory attachment to exactly one receipt and its certificate. It binds epoch,
//! mode, environment, producer builds, policy, and fuel. Missing, stale, malformed, or
//! replay-failing hints select ordinary verification without the cache. No type in
//! this module can admit or reject a declaration.

use std::collections::{BTreeMap, BTreeSet};

use fln_core::diag::ResourceReason;
use fln_core::mode::{ContentRoot, EpochId, Mode};
use fln_core::outcome::{Inconclusive, InconclusiveCause, InternalFault, Outcome, ResourceUsage};

use crate::canon::{
    CanonError, CanonReader, CanonWriter, DecodeBudget, SCHEMA_CARTRIDGE_ARCHIVE,
    SCHEMA_CARTRIDGE_MANIFEST, SCHEMA_WARM_DEFEQ_CACHE,
};
use crate::domain::{Digest, Domain, hash};

/// Hard structural ceilings checked before allocation even under an unlimited caller
/// budget. These are format limits, not claims about a particular host.
pub const MAX_CARTRIDGE_OBJECTS_V1: usize = 1_048_576;
pub const MAX_CARTRIDGE_CHUNKS_V1: usize = 1_048_576;
pub const MAX_OBJECT_CHUNKS_V1: usize = 1_048_576;
pub const MAX_ATTACHMENTS_V1: usize = 1_048_576;
pub const MAX_WARM_DEFEQ_ENTRIES_V1: usize = 1_048_576;
pub const MAX_REDUCTION_TRACE_ROOTS_V1: usize = 1_048_576;
pub const MAX_EXTENSIONS_V1: usize = 65_536;
pub const MAX_EXTENSION_PAYLOAD_V1: usize = 16 * 1024 * 1024;

/// Identity of one logical cartridge object. The object kind is inside the hash
/// preimage, so identical bytes used as a receipt and as a fixture are distinct.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CartridgeObjectIdV1(Digest);

impl CartridgeObjectIdV1 {
    pub const fn new(digest: Digest) -> CartridgeObjectIdV1 {
        CartridgeObjectIdV1(digest)
    }

    pub const fn digest(self) -> Digest {
        self.0
    }
}

/// Identity of one transport frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CartridgeChunkIdV1(Digest);

impl CartridgeChunkIdV1 {
    pub const fn new(digest: Digest) -> CartridgeChunkIdV1 {
        CartridgeChunkIdV1(digest)
    }

    pub const fn digest(self) -> Digest {
        self.0
    }
}

/// Every object class a v1 manifest may carry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CartridgeObjectKindV1 {
    Declaration,
    Dependency,
    Receipt,
    Certificate,
    Fixture,
    Schema,
    ResourceContract,
    Witness,
    WarmDefeqCache,
}

impl CartridgeObjectKindV1 {
    pub const ALL: [CartridgeObjectKindV1; 9] = [
        CartridgeObjectKindV1::Declaration,
        CartridgeObjectKindV1::Dependency,
        CartridgeObjectKindV1::Receipt,
        CartridgeObjectKindV1::Certificate,
        CartridgeObjectKindV1::Fixture,
        CartridgeObjectKindV1::Schema,
        CartridgeObjectKindV1::ResourceContract,
        CartridgeObjectKindV1::Witness,
        CartridgeObjectKindV1::WarmDefeqCache,
    ];

    const fn tag(self) -> u8 {
        match self {
            CartridgeObjectKindV1::Declaration => 0,
            CartridgeObjectKindV1::Dependency => 1,
            CartridgeObjectKindV1::Receipt => 2,
            CartridgeObjectKindV1::Certificate => 3,
            CartridgeObjectKindV1::Fixture => 4,
            CartridgeObjectKindV1::Schema => 5,
            CartridgeObjectKindV1::ResourceContract => 6,
            CartridgeObjectKindV1::Witness => 7,
            CartridgeObjectKindV1::WarmDefeqCache => 8,
        }
    }

    const fn requires_epoch_binding(self) -> bool {
        matches!(
            self,
            CartridgeObjectKindV1::Declaration
                | CartridgeObjectKindV1::Dependency
                | CartridgeObjectKindV1::Receipt
                | CartridgeObjectKindV1::Certificate
                | CartridgeObjectKindV1::WarmDefeqCache
        )
    }
}

/// Whether the object belongs to the air-gapped verification closure.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ObjectRequirementV1 {
    Required,
    Optional,
}

/// Portability declared for one object. A declaration of portability is validated
/// against the object kind before it can enter a manifest.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ObjectPortabilityV1 {
    /// Schema, fixture, resource-contract, or witness data whose own codec is
    /// epoch-neutral.
    Portable,
    /// Reusable only at the manifest epoch, but independent of target platform.
    EpochBound,
    /// Reusable only at the manifest epoch and exact target identifier.
    PlatformBound { target: String },
}

/// Receipt attachment roles. Role and object kind are joined in both directions by
/// manifest validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AttachmentRoleV1 {
    Certificate,
    Dependency,
    Fixture,
    Schema,
    ResourceContract,
    Witness,
    WarmDefeqCache,
}

impl AttachmentRoleV1 {
    pub const ALL: [AttachmentRoleV1; 7] = [
        AttachmentRoleV1::Certificate,
        AttachmentRoleV1::Dependency,
        AttachmentRoleV1::Fixture,
        AttachmentRoleV1::Schema,
        AttachmentRoleV1::ResourceContract,
        AttachmentRoleV1::Witness,
        AttachmentRoleV1::WarmDefeqCache,
    ];

    const fn tag(self) -> u8 {
        match self {
            AttachmentRoleV1::Certificate => 0,
            AttachmentRoleV1::Dependency => 1,
            AttachmentRoleV1::Fixture => 2,
            AttachmentRoleV1::Schema => 3,
            AttachmentRoleV1::ResourceContract => 4,
            AttachmentRoleV1::Witness => 5,
            AttachmentRoleV1::WarmDefeqCache => 6,
        }
    }

    const fn expected_kind(self) -> CartridgeObjectKindV1 {
        match self {
            AttachmentRoleV1::Certificate => CartridgeObjectKindV1::Certificate,
            AttachmentRoleV1::Dependency => CartridgeObjectKindV1::Dependency,
            AttachmentRoleV1::Fixture => CartridgeObjectKindV1::Fixture,
            AttachmentRoleV1::Schema => CartridgeObjectKindV1::Schema,
            AttachmentRoleV1::ResourceContract => CartridgeObjectKindV1::ResourceContract,
            AttachmentRoleV1::Witness => CartridgeObjectKindV1::Witness,
            AttachmentRoleV1::WarmDefeqCache => CartridgeObjectKindV1::WarmDefeqCache,
        }
    }
}

/// Unknown advisory extensions survive byte-for-byte. Schema v1 registers no
/// critical extension, so every critical row is a typed refusal.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct CartridgeExtensionV1 {
    pub id: u32,
    pub critical: bool,
    pub payload: Vec<u8>,
}

impl CartridgeExtensionV1 {
    pub fn advisory(id: u32, payload: impl Into<Vec<u8>>) -> CartridgeExtensionV1 {
        CartridgeExtensionV1 {
            id,
            critical: false,
            payload: payload.into(),
        }
    }
}

/// Transparency mode of one cached defeq query.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DefeqTransparencyV1 {
    Reducible,
    Instances,
    Semireducible,
    All,
}

impl DefeqTransparencyV1 {
    pub const ALL: [DefeqTransparencyV1; 4] = [
        DefeqTransparencyV1::Reducible,
        DefeqTransparencyV1::Instances,
        DefeqTransparencyV1::Semireducible,
        DefeqTransparencyV1::All,
    ];

    const fn tag(self) -> u8 {
        match self {
            DefeqTransparencyV1::Reducible => 0,
            DefeqTransparencyV1::Instances => 1,
            DefeqTransparencyV1::Semireducible => 2,
            DefeqTransparencyV1::All => 3,
        }
    }
}

/// Complete query key for one memoized defeq replay.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WarmDefeqQueryV1 {
    pub left_term_root: ContentRoot,
    pub right_term_root: ContentRoot,
    pub expected_type_root: Option<ContentRoot>,
    pub transparency: DefeqTransparencyV1,
}

/// Replay hints for a query that reached one common normal-form root. The traces are
/// root chains only; the checker still replays reductions against certificate terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WarmDefeqEntryV1 {
    pub query: WarmDefeqQueryV1,
    pub normal_form_root: ContentRoot,
    pub left_trace: Vec<ContentRoot>,
    pub right_trace: Vec<ContentRoot>,
}

/// Every semantic coordinate that makes a warm cache reusable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WarmDefeqBindingV1 {
    pub receipt_object: CartridgeObjectIdV1,
    pub certificate_object: CartridgeObjectIdV1,
    pub epoch: EpochId,
    pub mode: Mode,
    pub environment_root: ContentRoot,
    pub kernel_build_root: ContentRoot,
    pub checker_build_root: ContentRoot,
    pub policy_root: ContentRoot,
    pub fuel_profile_root: ContentRoot,
}

/// Consumer-owned coordinates required before a warm cache can supply replay hints.
///
/// Receipt and certificate identities come from the attachment being classified.
/// Everything in this type comes from the verifying process, never from the cache
/// being judged; deriving it from the cache would make the comparison tautological.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WarmDefeqContextV1 {
    pub epoch: EpochId,
    pub mode: Mode,
    pub environment_root: ContentRoot,
    pub kernel_build_root: ContentRoot,
    pub checker_build_root: ContentRoot,
    pub policy_root: ContentRoot,
    pub fuel_profile_root: ContentRoot,
}

impl WarmDefeqBindingV1 {
    /// Classify all nine binding coordinates as one indivisible replay-hint key.
    pub fn classify_against(&self, expected: &WarmDefeqBindingV1) -> WarmCacheStateV1 {
        if self == expected {
            WarmCacheStateV1::CurrentAndBound
        } else {
            WarmCacheStateV1::BindingMismatch
        }
    }
}

/// OQ-13 v1 warm-cache payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WarmDefeqCacheV1 {
    pub binding: WarmDefeqBindingV1,
    pub entries: Vec<WarmDefeqEntryV1>,
    pub extensions: Vec<CartridgeExtensionV1>,
}

/// Exact structural law violated by a parseable warm cache or cartridge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CartridgeRuleV1 {
    TooManyObjects,
    TooManyChunks,
    TooManyObjectChunks,
    TooManyAttachments,
    TooManyRootReceipts,
    TooManyWarmEntries,
    TooManyTraceRoots,
    TooManyExtensions,
    EmptyRootReceipts,
    RootReceiptsNotStrictlySorted,
    ObjectsNotStrictlySorted,
    ChunksNotStrictlySorted,
    AttachmentsNotStrictlySorted,
    ExtensionsNotStrictlySorted,
    WarmEntriesNotStrictlySorted,
    UnknownCriticalExtension,
    OversizeExtension,
    InvalidPlatformTarget,
    EpochBoundKindDeclaredPortable,
    OptionalOnlyKindDeclaredRequired,
    EmptyObjectChunkList,
    ObjectChunkOffsetsNotContiguous,
    ObjectLengthMismatch,
    MissingChunkDescriptor,
    ChunkLengthMismatch,
    UnreferencedChunkDescriptor,
    MissingRootReceipt,
    RootReceiptWrongKind,
    RootReceiptOptional,
    MissingAttachmentReceipt,
    AttachmentReceiptWrongKind,
    AttachmentReceiptNotRoot,
    MissingAttachedObject,
    AttachmentRoleKindMismatch,
    WarmCacheAttachmentCount,
    WarmCacheAttachmentRequired,
    WarmCacheMissingCertificateAttachment,
    WarmTraceEmpty,
    WarmTraceWrongStart,
    WarmTraceWrongEnd,
    FramesNotStrictlySorted,
    FrameUndeclared,
    FrameLengthMismatch,
    FrameDigestMismatch,
    ObjectDigestMismatch,
    RequiredFramesMissing,
    ArchiveManifestMismatch,
    InvalidChunkSize,
}

/// Typed refusal at a cartridge boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CartridgeRefusalV1 {
    SchemaNameMismatch { expected: &'static str },
    UnsupportedVersion { schema: &'static str, seen: u16 },
    Malformed(CanonError),
    InvalidStructure { rule: CartridgeRuleV1, index: u64 },
    PortabilityMismatch { object: CartridgeObjectIdV1 },
    MissingObject { object: CartridgeObjectIdV1 },
    MissingChunk { chunk: CartridgeChunkIdV1 },
    DuplicateFrame { chunk: CartridgeChunkIdV1 },
    ConflictingObjectDeclaration { object: CartridgeObjectIdV1 },
}

pub type WarmDefeqDecodeOutcomeV1 = Outcome<Result<WarmDefeqCacheV1, CartridgeRefusalV1>>;

impl WarmDefeqCacheV1 {
    pub fn new(
        binding: WarmDefeqBindingV1,
        entries: Vec<WarmDefeqEntryV1>,
        extensions: Vec<CartridgeExtensionV1>,
    ) -> Result<WarmDefeqCacheV1, CartridgeRefusalV1> {
        let cache = WarmDefeqCacheV1 {
            binding,
            entries,
            extensions,
        };
        cache.validate()?;
        Ok(cache)
    }

    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>, CartridgeRefusalV1> {
        self.validate()?;
        let mut writer = CanonWriter::new();
        writer.schema(SCHEMA_WARM_DEFEQ_CACHE);
        write_warm_binding(&mut writer, &self.binding);
        writer.u64(self.entries.len() as u64);
        for entry in &self.entries {
            write_warm_entry(&mut writer, entry);
        }
        write_extensions(&mut writer, &self.extensions);
        Ok(writer.into_bytes())
    }

    pub fn digest(&self) -> Result<Digest, CartridgeRefusalV1> {
        Ok(hash(Domain::Receipt, &self.to_canonical_bytes()?))
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> WarmDefeqDecodeOutcomeV1 {
        Self::from_canonical_bytes_budgeted(bytes, DecodeBudget::unlimited())
    }

    pub fn from_canonical_bytes_budgeted(
        bytes: &[u8],
        budget: DecodeBudget,
    ) -> WarmDefeqDecodeOutcomeV1 {
        let mut reader = CanonReader::with_budget(bytes, budget);
        macro_rules! read {
            ($expression:expr) => {
                match $expression {
                    Ok(value) => value,
                    Err(error) => return decode_error(&reader, error),
                }
            };
        }

        let schema_name = read!(reader.str());
        if schema_name != SCHEMA_WARM_DEFEQ_CACHE.name {
            return Outcome::Complete(Err(CartridgeRefusalV1::SchemaNameMismatch {
                expected: SCHEMA_WARM_DEFEQ_CACHE.name,
            }));
        }
        let version = read!(reader.u16());
        if version != SCHEMA_WARM_DEFEQ_CACHE.version {
            return Outcome::Complete(Err(CartridgeRefusalV1::UnsupportedVersion {
                schema: SCHEMA_WARM_DEFEQ_CACHE.name,
                seen: version,
            }));
        }

        let binding = read!(read_warm_binding(&mut reader));
        let entry_count = read!(read_count(
            &mut reader,
            MAX_WARM_DEFEQ_ENTRIES_V1,
            "too many warm defeq entries",
        ));
        let mut entries = Vec::with_capacity(entry_count);
        for _ in 0..entry_count {
            read!(reader.charge_node());
            entries.push(read!(read_warm_entry(&mut reader)));
        }
        let extensions = read!(read_extensions(&mut reader));
        let cache = WarmDefeqCacheV1 {
            binding,
            entries,
            extensions,
        };
        finish_decoded(reader, cache, WarmDefeqCacheV1::validate)
    }

    fn validate(&self) -> Result<(), CartridgeRefusalV1> {
        if self.entries.len() > MAX_WARM_DEFEQ_ENTRIES_V1 {
            return invalid(CartridgeRuleV1::TooManyWarmEntries, self.entries.len());
        }
        if !self
            .entries
            .windows(2)
            .all(|pair| pair[0].query < pair[1].query)
        {
            return invalid(CartridgeRuleV1::WarmEntriesNotStrictlySorted, 0);
        }
        for (index, entry) in self.entries.iter().enumerate() {
            validate_trace(
                &entry.left_trace,
                entry.query.left_term_root,
                entry.normal_form_root,
                index,
            )?;
            validate_trace(
                &entry.right_trace,
                entry.query.right_term_root,
                entry.normal_form_root,
                index,
            )?;
        }
        validate_extensions(&self.extensions)
    }
}

fn validate_trace(
    trace: &[ContentRoot],
    start: ContentRoot,
    end: ContentRoot,
    index: usize,
) -> Result<(), CartridgeRefusalV1> {
    if trace.is_empty() {
        return invalid(CartridgeRuleV1::WarmTraceEmpty, index);
    }
    if trace.len() > MAX_REDUCTION_TRACE_ROOTS_V1 {
        return invalid(CartridgeRuleV1::TooManyTraceRoots, index);
    }
    if trace.first().copied() != Some(start) {
        return invalid(CartridgeRuleV1::WarmTraceWrongStart, index);
    }
    if trace.last().copied() != Some(end) {
        return invalid(CartridgeRuleV1::WarmTraceWrongEnd, index);
    }
    Ok(())
}

/// The only v1 receipt-attachment policy. The cache is never required for verification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Oq13AttachmentPolicyV1 {
    OptionalAdvisoryReceiptAttachment,
}

pub const fn oq13_attachment_policy() -> Oq13AttachmentPolicyV1 {
    Oq13AttachmentPolicyV1::OptionalAdvisoryReceiptAttachment
}

/// Every cache boundary state has one deterministic non-authoritative action.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WarmCacheStateV1 {
    CurrentAndBound,
    Absent,
    UnsupportedVersion,
    Malformed,
    ResourceLimited,
    Cancelled,
    BindingMismatch,
    ReplayFailed,
    UnknownCriticalExtension,
    InternalFault,
}

impl WarmCacheStateV1 {
    pub const ALL: [WarmCacheStateV1; 10] = [
        WarmCacheStateV1::CurrentAndBound,
        WarmCacheStateV1::Absent,
        WarmCacheStateV1::UnsupportedVersion,
        WarmCacheStateV1::Malformed,
        WarmCacheStateV1::ResourceLimited,
        WarmCacheStateV1::Cancelled,
        WarmCacheStateV1::BindingMismatch,
        WarmCacheStateV1::ReplayFailed,
        WarmCacheStateV1::UnknownCriticalExtension,
        WarmCacheStateV1::InternalFault,
    ];
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WarmCacheActionV1 {
    ReplayHints,
    VerifyWithoutCache,
    QuarantineAndVerifyIndependently,
}

pub const fn warm_cache_action(state: WarmCacheStateV1) -> WarmCacheActionV1 {
    match state {
        WarmCacheStateV1::CurrentAndBound => WarmCacheActionV1::ReplayHints,
        WarmCacheStateV1::Absent
        | WarmCacheStateV1::UnsupportedVersion
        | WarmCacheStateV1::Malformed
        | WarmCacheStateV1::ResourceLimited
        | WarmCacheStateV1::Cancelled
        | WarmCacheStateV1::BindingMismatch
        | WarmCacheStateV1::ReplayFailed
        | WarmCacheStateV1::UnknownCriticalExtension => WarmCacheActionV1::VerifyWithoutCache,
        WarmCacheStateV1::InternalFault => WarmCacheActionV1::QuarantineAndVerifyIndependently,
    }
}

/// One typed, non-authoritative decision about an optional warm-cache attachment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WarmCacheDecisionV1 {
    pub cache_object: CartridgeObjectIdV1,
    pub state: WarmCacheStateV1,
    pub action: WarmCacheActionV1,
}

/// Decisions remain diagnostic data; callers may use only entries whose action is
/// [`WarmCacheActionV1::ReplayHints`], and must still replay those hints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WarmCacheAttachmentReportV1 {
    pub decisions: Vec<WarmCacheDecisionV1>,
}

impl WarmCacheAttachmentReportV1 {
    pub fn replayable(&self) -> usize {
        self.decisions
            .iter()
            .filter(|decision| decision.action == WarmCacheActionV1::ReplayHints)
            .count()
    }

    pub fn missing(&self) -> usize {
        self.decisions
            .iter()
            .filter(|decision| decision.state == WarmCacheStateV1::Absent)
            .count()
    }

    pub fn bypassed(&self) -> usize {
        self.decisions
            .iter()
            .filter(|decision| decision.action == WarmCacheActionV1::VerifyWithoutCache)
            .count()
    }

    pub fn quarantined(&self) -> usize {
        self.decisions
            .iter()
            .filter(|decision| {
                decision.action == WarmCacheActionV1::QuarantineAndVerifyIndependently
            })
            .count()
    }
}

/// Internal OQ-13 fields and their non-dropping transport projection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Oq13FieldV1 {
    ReceiptBinding,
    CertificateBinding,
    Epoch,
    Mode,
    Environment,
    KernelBuild,
    CheckerBuild,
    Policy,
    Fuel,
    Query,
    ReductionTrace,
    Extensions,
}

impl Oq13FieldV1 {
    pub const ALL: [Oq13FieldV1; 12] = [
        Oq13FieldV1::ReceiptBinding,
        Oq13FieldV1::CertificateBinding,
        Oq13FieldV1::Epoch,
        Oq13FieldV1::Mode,
        Oq13FieldV1::Environment,
        Oq13FieldV1::KernelBuild,
        Oq13FieldV1::CheckerBuild,
        Oq13FieldV1::Policy,
        Oq13FieldV1::Fuel,
        Oq13FieldV1::Query,
        Oq13FieldV1::ReductionTrace,
        Oq13FieldV1::Extensions,
    ];
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Oq13ProjectionV1 {
    ReceiptAttachedAdvisory,
    ReplayCheckedSemanticField,
    RefuseWithoutRegisteredMapping,
}

pub const fn oq13_projection(field: Oq13FieldV1) -> Oq13ProjectionV1 {
    match field {
        Oq13FieldV1::ReceiptBinding
        | Oq13FieldV1::CertificateBinding
        | Oq13FieldV1::Epoch
        | Oq13FieldV1::Mode
        | Oq13FieldV1::Environment
        | Oq13FieldV1::KernelBuild
        | Oq13FieldV1::CheckerBuild
        | Oq13FieldV1::Policy
        | Oq13FieldV1::Fuel => Oq13ProjectionV1::ReceiptAttachedAdvisory,
        Oq13FieldV1::Query | Oq13FieldV1::ReductionTrace => {
            Oq13ProjectionV1::ReplayCheckedSemanticField
        }
        Oq13FieldV1::Extensions => Oq13ProjectionV1::RefuseWithoutRegisteredMapping,
    }
}

/// One content-addressed frame declared by the manifest.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChunkDescriptorV1 {
    pub id: CartridgeChunkIdV1,
    pub len: u64,
}

/// One frame occurrence inside a logical object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ObjectChunkRefV1 {
    pub id: CartridgeChunkIdV1,
    pub offset: u64,
    pub len: u64,
}

/// One logical object row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CartridgeObjectV1 {
    pub id: CartridgeObjectIdV1,
    pub kind: CartridgeObjectKindV1,
    pub requirement: ObjectRequirementV1,
    pub portability: ObjectPortabilityV1,
    pub len: u64,
    pub chunks: Vec<ObjectChunkRefV1>,
}

/// One receipt-to-object attachment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ReceiptAttachmentV1 {
    pub receipt: CartridgeObjectIdV1,
    pub role: AttachmentRoleV1,
    pub object: CartridgeObjectIdV1,
}

/// Transport-independent logical identity of one cartridge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CartridgeManifestV1 {
    pub epoch: EpochId,
    pub environment_root: ContentRoot,
    pub root_receipts: Vec<CartridgeObjectIdV1>,
    pub objects: Vec<CartridgeObjectV1>,
    pub chunks: Vec<ChunkDescriptorV1>,
    pub attachments: Vec<ReceiptAttachmentV1>,
    pub extensions: Vec<CartridgeExtensionV1>,
}

pub type CartridgeManifestDecodeOutcomeV1 =
    Outcome<Result<CartridgeManifestV1, CartridgeRefusalV1>>;

impl CartridgeManifestV1 {
    pub fn new(
        epoch: EpochId,
        environment_root: ContentRoot,
        root_receipts: Vec<CartridgeObjectIdV1>,
        objects: Vec<CartridgeObjectV1>,
        chunks: Vec<ChunkDescriptorV1>,
        attachments: Vec<ReceiptAttachmentV1>,
        extensions: Vec<CartridgeExtensionV1>,
    ) -> Result<CartridgeManifestV1, CartridgeRefusalV1> {
        let manifest = CartridgeManifestV1 {
            epoch,
            environment_root,
            root_receipts,
            objects,
            chunks,
            attachments,
            extensions,
        };
        manifest.validate()?;
        Ok(manifest)
    }

    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>, CartridgeRefusalV1> {
        self.validate()?;
        let mut writer = CanonWriter::new();
        writer.schema(SCHEMA_CARTRIDGE_MANIFEST);
        write_manifest_body(&mut writer, self);
        Ok(writer.into_bytes())
    }

    /// Logical cartridge identity. Thin and sealed transports share this root.
    pub fn manifest_root(&self) -> Result<Digest, CartridgeRefusalV1> {
        Ok(hash(Domain::Receipt, &self.to_canonical_bytes()?))
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> CartridgeManifestDecodeOutcomeV1 {
        Self::from_canonical_bytes_budgeted(bytes, DecodeBudget::unlimited())
    }

    pub fn from_canonical_bytes_budgeted(
        bytes: &[u8],
        budget: DecodeBudget,
    ) -> CartridgeManifestDecodeOutcomeV1 {
        let mut reader = CanonReader::with_budget(bytes, budget);
        macro_rules! read {
            ($expression:expr) => {
                match $expression {
                    Ok(value) => value,
                    Err(error) => return decode_error(&reader, error),
                }
            };
        }

        let schema_name = read!(reader.str());
        if schema_name != SCHEMA_CARTRIDGE_MANIFEST.name {
            return Outcome::Complete(Err(CartridgeRefusalV1::SchemaNameMismatch {
                expected: SCHEMA_CARTRIDGE_MANIFEST.name,
            }));
        }
        let version = read!(reader.u16());
        if version != SCHEMA_CARTRIDGE_MANIFEST.version {
            return Outcome::Complete(Err(CartridgeRefusalV1::UnsupportedVersion {
                schema: SCHEMA_CARTRIDGE_MANIFEST.name,
                seen: version,
            }));
        }
        let manifest = read!(read_manifest_body(&mut reader));
        finish_decoded(reader, manifest, CartridgeManifestV1::validate)
    }

    pub fn object(&self, id: CartridgeObjectIdV1) -> Option<&CartridgeObjectV1> {
        self.objects
            .binary_search_by_key(&id, |object| object.id)
            .ok()
            .map(|index| &self.objects[index])
    }

    pub fn chunk(&self, id: CartridgeChunkIdV1) -> Option<&ChunkDescriptorV1> {
        self.chunks
            .binary_search_by_key(&id, |chunk| chunk.id)
            .ok()
            .map(|index| &self.chunks[index])
    }

    pub fn required_chunk_ids(&self) -> BTreeSet<CartridgeChunkIdV1> {
        self.objects
            .iter()
            .filter(|object| object.requirement == ObjectRequirementV1::Required)
            .flat_map(|object| object.chunks.iter().map(|chunk| chunk.id))
            .collect()
    }

    pub fn optional_chunk_ids(&self) -> BTreeSet<CartridgeChunkIdV1> {
        let required = self.required_chunk_ids();
        self.objects
            .iter()
            .filter(|object| object.requirement == ObjectRequirementV1::Optional)
            .flat_map(|object| object.chunks.iter().map(|chunk| chunk.id))
            .filter(|id| !required.contains(id))
            .collect()
    }

    /// Validate declared reuse against a destination. Portable objects may cross an
    /// epoch; every logical artifact and cache stays epoch-bound.
    pub fn portable_to(
        &self,
        destination_epoch: EpochId,
        destination_target: &str,
    ) -> Result<(), CartridgeRefusalV1> {
        for object in &self.objects {
            let usable = match &object.portability {
                ObjectPortabilityV1::Portable => true,
                ObjectPortabilityV1::EpochBound => destination_epoch == self.epoch,
                ObjectPortabilityV1::PlatformBound { target } => {
                    destination_epoch == self.epoch && destination_target == target
                }
            };
            if !usable {
                return Err(CartridgeRefusalV1::PortabilityMismatch { object: object.id });
            }
        }
        Ok(())
    }

    fn validate(&self) -> Result<(), CartridgeRefusalV1> {
        if self.objects.len() > MAX_CARTRIDGE_OBJECTS_V1 {
            return invalid(CartridgeRuleV1::TooManyObjects, self.objects.len());
        }
        if self.chunks.len() > MAX_CARTRIDGE_CHUNKS_V1 {
            return invalid(CartridgeRuleV1::TooManyChunks, self.chunks.len());
        }
        if self.attachments.len() > MAX_ATTACHMENTS_V1 {
            return invalid(CartridgeRuleV1::TooManyAttachments, self.attachments.len());
        }
        if self.root_receipts.len() > MAX_CARTRIDGE_OBJECTS_V1 {
            return invalid(
                CartridgeRuleV1::TooManyRootReceipts,
                self.root_receipts.len(),
            );
        }
        if self.root_receipts.is_empty() {
            return invalid(CartridgeRuleV1::EmptyRootReceipts, 0);
        }
        if !strictly_sorted(&self.root_receipts) {
            return invalid(CartridgeRuleV1::RootReceiptsNotStrictlySorted, 0);
        }
        if !self.objects.windows(2).all(|pair| pair[0].id < pair[1].id) {
            return invalid(CartridgeRuleV1::ObjectsNotStrictlySorted, 0);
        }
        if !self.chunks.windows(2).all(|pair| pair[0].id < pair[1].id) {
            return invalid(CartridgeRuleV1::ChunksNotStrictlySorted, 0);
        }
        if !strictly_sorted(&self.attachments) {
            return invalid(CartridgeRuleV1::AttachmentsNotStrictlySorted, 0);
        }

        let mut referenced_chunks = BTreeSet::new();
        for (index, object) in self.objects.iter().enumerate() {
            validate_object_declaration(self, object, index, &mut referenced_chunks)?;
        }
        for (index, descriptor) in self.chunks.iter().enumerate() {
            if !referenced_chunks.contains(&descriptor.id) {
                return invalid(CartridgeRuleV1::UnreferencedChunkDescriptor, index);
            }
        }

        for (index, receipt) in self.root_receipts.iter().enumerate() {
            let Some(object) = self.object(*receipt) else {
                return invalid(CartridgeRuleV1::MissingRootReceipt, index);
            };
            if object.kind != CartridgeObjectKindV1::Receipt {
                return invalid(CartridgeRuleV1::RootReceiptWrongKind, index);
            }
            if object.requirement != ObjectRequirementV1::Required {
                return invalid(CartridgeRuleV1::RootReceiptOptional, index);
            }
        }

        for (index, attachment) in self.attachments.iter().enumerate() {
            let Some(receipt) = self.object(attachment.receipt) else {
                return invalid(CartridgeRuleV1::MissingAttachmentReceipt, index);
            };
            if receipt.kind != CartridgeObjectKindV1::Receipt {
                return invalid(CartridgeRuleV1::AttachmentReceiptWrongKind, index);
            }
            if self
                .root_receipts
                .binary_search(&attachment.receipt)
                .is_err()
            {
                return invalid(CartridgeRuleV1::AttachmentReceiptNotRoot, index);
            }
            let Some(object) = self.object(attachment.object) else {
                return invalid(CartridgeRuleV1::MissingAttachedObject, index);
            };
            if object.kind != attachment.role.expected_kind() {
                return invalid(CartridgeRuleV1::AttachmentRoleKindMismatch, index);
            }
        }

        for object in self
            .objects
            .iter()
            .filter(|object| object.kind == CartridgeObjectKindV1::WarmDefeqCache)
        {
            if object.requirement != ObjectRequirementV1::Optional {
                return invalid(CartridgeRuleV1::WarmCacheAttachmentRequired, 0);
            }
            let attached: Vec<_> = self
                .attachments
                .iter()
                .filter(|attachment| {
                    attachment.object == object.id
                        && attachment.role == AttachmentRoleV1::WarmDefeqCache
                })
                .collect();
            if attached.len() != 1 {
                return invalid(CartridgeRuleV1::WarmCacheAttachmentCount, attached.len());
            }
            let receipt = attached[0].receipt;
            if !self.attachments.iter().any(|attachment| {
                attachment.receipt == receipt && attachment.role == AttachmentRoleV1::Certificate
            }) {
                return invalid(CartridgeRuleV1::WarmCacheMissingCertificateAttachment, 0);
            }
        }
        validate_extensions(&self.extensions)
    }
}

fn validate_object_declaration(
    manifest: &CartridgeManifestV1,
    object: &CartridgeObjectV1,
    index: usize,
    referenced_chunks: &mut BTreeSet<CartridgeChunkIdV1>,
) -> Result<(), CartridgeRefusalV1> {
    if object.kind.requires_epoch_binding() && object.portability == ObjectPortabilityV1::Portable {
        return invalid(CartridgeRuleV1::EpochBoundKindDeclaredPortable, index);
    }
    if matches!(
        object.kind,
        CartridgeObjectKindV1::Witness | CartridgeObjectKindV1::WarmDefeqCache
    ) && object.requirement != ObjectRequirementV1::Optional
    {
        return invalid(CartridgeRuleV1::OptionalOnlyKindDeclaredRequired, index);
    }
    if let ObjectPortabilityV1::PlatformBound { target } = &object.portability
        && (target.is_empty()
            || target.len() > 128
            || !target
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || matches!(byte, b'.' | b'-' | b'_')))
    {
        return invalid(CartridgeRuleV1::InvalidPlatformTarget, index);
    }
    if object.chunks.is_empty() {
        return invalid(CartridgeRuleV1::EmptyObjectChunkList, index);
    }
    if object.chunks.len() > MAX_OBJECT_CHUNKS_V1 {
        return invalid(CartridgeRuleV1::TooManyObjectChunks, index);
    }
    let mut next_offset = 0u64;
    for chunk_ref in &object.chunks {
        if chunk_ref.offset != next_offset {
            return invalid(CartridgeRuleV1::ObjectChunkOffsetsNotContiguous, index);
        }
        let Some(descriptor) = manifest.chunk(chunk_ref.id) else {
            return invalid(CartridgeRuleV1::MissingChunkDescriptor, index);
        };
        if descriptor.len != chunk_ref.len {
            return invalid(CartridgeRuleV1::ChunkLengthMismatch, index);
        }
        next_offset = next_offset.checked_add(chunk_ref.len).ok_or({
            CartridgeRefusalV1::InvalidStructure {
                rule: CartridgeRuleV1::ObjectLengthMismatch,
                index: index as u64,
            }
        })?;
        referenced_chunks.insert(chunk_ref.id);
    }
    if next_offset != object.len {
        return invalid(CartridgeRuleV1::ObjectLengthMismatch, index);
    }
    Ok(())
}

/// Content-addressed bytes carried by a transport.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CartridgeFrameV1 {
    pub id: CartridgeChunkIdV1,
    pub bytes: Vec<u8>,
}

impl CartridgeFrameV1 {
    pub fn new(bytes: impl Into<Vec<u8>>) -> CartridgeFrameV1 {
        let bytes = bytes.into();
        let id = cartridge_chunk_id(&bytes);
        CartridgeFrameV1 { id, bytes }
    }
}

/// Transport completeness is a completed fact about a valid archive, not an
/// outcome-level non-answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CartridgeTransportStateV1 {
    Thin,
    Partial {
        missing_required: Vec<CartridgeChunkIdV1>,
    },
    /// All proof-relevant frames are present; optional witness/cache frames may be
    /// absent.
    Sealed {
        missing_optional: Vec<CartridgeChunkIdV1>,
    },
    Complete,
}

fn transport_state(
    manifest: &CartridgeManifestV1,
    present: &BTreeSet<CartridgeChunkIdV1>,
) -> CartridgeTransportStateV1 {
    if present.is_empty() {
        return CartridgeTransportStateV1::Thin;
    }
    let missing_required: Vec<_> = manifest
        .required_chunk_ids()
        .into_iter()
        .filter(|id| !present.contains(id))
        .collect();
    if !missing_required.is_empty() {
        return CartridgeTransportStateV1::Partial { missing_required };
    }
    let missing_optional: Vec<_> = manifest
        .optional_chunk_ids()
        .into_iter()
        .filter(|id| !present.contains(id))
        .collect();
    if missing_optional.is_empty() {
        CartridgeTransportStateV1::Complete
    } else {
        CartridgeTransportStateV1::Sealed { missing_optional }
    }
}

/// Separate structural budgets for the outer transport and nested manifest. Keeping
/// them explicit avoids pretending two decoders share one counter.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CartridgeDecodeBudgetsV1 {
    pub archive: DecodeBudget,
    pub manifest: DecodeBudget,
}

impl CartridgeDecodeBudgetsV1 {
    pub const fn unlimited() -> CartridgeDecodeBudgetsV1 {
        CartridgeDecodeBudgetsV1 {
            archive: DecodeBudget::unlimited(),
            manifest: DecodeBudget::unlimited(),
        }
    }
}

/// A canonical transport carrying a manifest and a sorted subset of declared frames.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CartridgeArchiveV1 {
    pub manifest: CartridgeManifestV1,
    pub frames: Vec<CartridgeFrameV1>,
}

pub type CartridgeArchiveDecodeOutcomeV1 = Outcome<Result<CartridgeArchiveV1, CartridgeRefusalV1>>;

impl CartridgeArchiveV1 {
    pub fn new(
        manifest: CartridgeManifestV1,
        frames: Vec<CartridgeFrameV1>,
    ) -> Result<CartridgeArchiveV1, CartridgeRefusalV1> {
        let archive = CartridgeArchiveV1 { manifest, frames };
        archive.validate()?;
        Ok(archive)
    }

    pub fn thin(manifest: CartridgeManifestV1) -> Result<CartridgeArchiveV1, CartridgeRefusalV1> {
        CartridgeArchiveV1::new(manifest, Vec::new())
    }

    pub fn transport_state(&self) -> CartridgeTransportStateV1 {
        let present = self.frames.iter().map(|frame| frame.id).collect();
        transport_state(&self.manifest, &present)
    }

    pub fn manifest_root(&self) -> Result<Digest, CartridgeRefusalV1> {
        self.manifest.manifest_root()
    }

    pub fn to_canonical_bytes(&self) -> Result<Vec<u8>, CartridgeRefusalV1> {
        self.validate()?;
        let manifest_bytes = self.manifest.to_canonical_bytes()?;
        let mut writer = CanonWriter::new();
        writer.schema(SCHEMA_CARTRIDGE_ARCHIVE);
        writer.bytes(&manifest_bytes);
        writer.u64(self.frames.len() as u64);
        for frame in &self.frames {
            write_chunk_id(&mut writer, frame.id);
            writer.bytes(&frame.bytes);
        }
        Ok(writer.into_bytes())
    }

    /// Byte identity of this exact transport population. The logical cartridge
    /// identity remains [`CartridgeArchiveV1::manifest_root`].
    pub fn archive_digest(&self) -> Result<Digest, CartridgeRefusalV1> {
        Ok(hash(Domain::Receipt, &self.to_canonical_bytes()?))
    }

    pub fn from_canonical_bytes(bytes: &[u8]) -> CartridgeArchiveDecodeOutcomeV1 {
        Self::from_canonical_bytes_budgeted(bytes, CartridgeDecodeBudgetsV1::unlimited())
    }

    pub fn from_canonical_bytes_budgeted(
        bytes: &[u8],
        budgets: CartridgeDecodeBudgetsV1,
    ) -> CartridgeArchiveDecodeOutcomeV1 {
        let mut reader = CanonReader::with_budget(bytes, budgets.archive);
        macro_rules! read {
            ($expression:expr) => {
                match $expression {
                    Ok(value) => value,
                    Err(error) => return decode_error(&reader, error),
                }
            };
        }

        let schema_name = read!(reader.str());
        if schema_name != SCHEMA_CARTRIDGE_ARCHIVE.name {
            return Outcome::Complete(Err(CartridgeRefusalV1::SchemaNameMismatch {
                expected: SCHEMA_CARTRIDGE_ARCHIVE.name,
            }));
        }
        let version = read!(reader.u16());
        if version != SCHEMA_CARTRIDGE_ARCHIVE.version {
            return Outcome::Complete(Err(CartridgeRefusalV1::UnsupportedVersion {
                schema: SCHEMA_CARTRIDGE_ARCHIVE.name,
                seen: version,
            }));
        }
        let manifest_bytes = read!(reader.bytes()).to_vec();
        read!(reader.charge_node());
        let frame_count = read!(read_count(
            &mut reader,
            MAX_CARTRIDGE_CHUNKS_V1,
            "too many cartridge frames",
        ));
        let mut frames = Vec::with_capacity(frame_count);
        for _ in 0..frame_count {
            read!(reader.charge_node());
            frames.push(CartridgeFrameV1 {
                id: read!(read_chunk_id(&mut reader)),
                bytes: read!(reader.bytes()).to_vec(),
            });
        }
        let exhausted = reader.exhausted();
        if let Err(error) = reader.finish() {
            return match exhausted {
                Some(stop) => Outcome::Inconclusive(stop.into_inconclusive()),
                None => Outcome::Complete(Err(CartridgeRefusalV1::Malformed(error))),
            };
        }
        if exhausted.is_some() {
            return Outcome::InternalFault(
                InternalFault::new(
                    "FL-INV-07",
                    "cartridge archive decode completed after recording a budget stop",
                )
                .with_evidence("fln_hash::cartridge::CartridgeArchiveV1"),
            );
        }
        let manifest = match CartridgeManifestV1::from_canonical_bytes_budgeted(
            &manifest_bytes,
            budgets.manifest,
        ) {
            Outcome::Complete(Ok(manifest)) => manifest,
            Outcome::Complete(Err(refusal)) => return Outcome::Complete(Err(refusal)),
            Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };
        Outcome::Complete(CartridgeArchiveV1::new(manifest, frames))
    }

    pub fn frame(&self, id: CartridgeChunkIdV1) -> Option<&CartridgeFrameV1> {
        self.frames
            .binary_search_by_key(&id, |frame| frame.id)
            .ok()
            .map(|index| &self.frames[index])
    }

    /// Reassemble one object after checking every frame and the whole-object identity.
    ///
    /// Missing frames are a completed partial-transport fact (`Complete(Ok(None))`).
    /// The declared logical length is checked against the caller's memory allowance
    /// before allocation, so repeated references to one small shared frame cannot
    /// expand into an unbounded object behind a compact archive.
    pub fn assemble_object(
        &self,
        id: CartridgeObjectIdV1,
        max_object_bytes: u64,
    ) -> Outcome<Result<Option<Vec<u8>>, CartridgeRefusalV1>> {
        let Some(object) = self.manifest.object(id) else {
            return Outcome::Complete(Err(CartridgeRefusalV1::MissingObject { object: id }));
        };
        let allowed = max_object_bytes.min(isize::MAX as u64);
        if object.len > allowed {
            return Outcome::Inconclusive(
                Inconclusive::resource(ResourceUsage {
                    reason: ResourceReason::Memory {
                        limit_bytes: allowed,
                    },
                    allowed,
                    observed: object.len,
                })
                .with_progress(format!("assemble cartridge object {}", object.id.digest())),
            );
        }
        let capacity = match usize::try_from(object.len) {
            Ok(capacity) => capacity,
            Err(_) => {
                return Outcome::InternalFault(
                    InternalFault::new(
                        "FL-INV-07",
                        "a cartridge object within the address-space limit did not fit usize",
                    )
                    .with_evidence("fln_hash::cartridge::CartridgeArchiveV1::assemble_object"),
                );
            }
        };
        let mut bytes = Vec::with_capacity(capacity);
        for chunk_ref in &object.chunks {
            let Some(frame) = self.frame(chunk_ref.id) else {
                return Outcome::Complete(Ok(None));
            };
            bytes.extend_from_slice(&frame.bytes);
        }
        if cartridge_object_id(object.kind, &bytes) != object.id {
            return Outcome::Complete(invalid(CartridgeRuleV1::ObjectDigestMismatch, 0));
        }
        Outcome::Complete(Ok(Some(bytes)))
    }

    /// Classify every optional OQ-13 cache against consumer-owned coordinates.
    ///
    /// A stale, malformed, unsupported, cancelled, or resource-limited cache is a
    /// decision to verify without hints, not a cartridge rejection. Only a failure
    /// of the outer content-addressed object graph remains a transport refusal.
    pub fn classify_present_warm_caches(
        &self,
        context: &WarmDefeqContextV1,
        budget: DecodeBudget,
        max_cache_bytes: u64,
    ) -> Result<WarmCacheAttachmentReportV1, CartridgeRefusalV1> {
        let mut report = WarmCacheAttachmentReportV1 {
            decisions: Vec::new(),
        };
        for attachment in self
            .manifest
            .attachments
            .iter()
            .filter(|attachment| attachment.role == AttachmentRoleV1::WarmDefeqCache)
        {
            let assembled = self.assemble_object(attachment.object, max_cache_bytes);
            let state = match assembled {
                Outcome::Complete(Ok(Some(bytes))) => {
                    match WarmDefeqCacheV1::from_canonical_bytes_budgeted(&bytes, budget) {
                        Outcome::Complete(Ok(cache)) => {
                            let certificate_is_attached =
                                self.manifest.attachments.iter().any(|candidate| {
                                    candidate.receipt == attachment.receipt
                                        && candidate.role == AttachmentRoleV1::Certificate
                                        && candidate.object == cache.binding.certificate_object
                                });
                            let expected = WarmDefeqBindingV1 {
                                receipt_object: attachment.receipt,
                                certificate_object: cache.binding.certificate_object,
                                epoch: context.epoch,
                                mode: context.mode,
                                environment_root: context.environment_root,
                                kernel_build_root: context.kernel_build_root,
                                checker_build_root: context.checker_build_root,
                                policy_root: context.policy_root,
                                fuel_profile_root: context.fuel_profile_root,
                            };
                            if !certificate_is_attached
                                || context.epoch != self.manifest.epoch
                                || context.environment_root != self.manifest.environment_root
                            {
                                WarmCacheStateV1::BindingMismatch
                            } else {
                                cache.binding.classify_against(&expected)
                            }
                        }
                        Outcome::Complete(Err(refusal)) => warm_cache_refusal_state(&refusal),
                        Outcome::Inconclusive(stop) => match stop.cause {
                            InconclusiveCause::Cancelled { .. } => WarmCacheStateV1::Cancelled,
                            InconclusiveCause::ResourceExhausted { .. } => {
                                WarmCacheStateV1::ResourceLimited
                            }
                            InconclusiveCause::DependencyUnavailable { .. }
                            | InconclusiveCause::AuthorityIncomplete { .. } => {
                                WarmCacheStateV1::InternalFault
                            }
                        },
                        Outcome::InternalFault(_) => WarmCacheStateV1::InternalFault,
                    }
                }
                Outcome::Complete(Ok(None)) => WarmCacheStateV1::Absent,
                Outcome::Complete(Err(refusal)) => return Err(refusal),
                Outcome::Inconclusive(stop) => match stop.cause {
                    InconclusiveCause::Cancelled { .. } => WarmCacheStateV1::Cancelled,
                    InconclusiveCause::ResourceExhausted { .. } => {
                        WarmCacheStateV1::ResourceLimited
                    }
                    InconclusiveCause::DependencyUnavailable { .. }
                    | InconclusiveCause::AuthorityIncomplete { .. } => {
                        WarmCacheStateV1::InternalFault
                    }
                },
                Outcome::InternalFault(_) => WarmCacheStateV1::InternalFault,
            };
            report.decisions.push(WarmCacheDecisionV1 {
                cache_object: attachment.object,
                state,
                action: warm_cache_action(state),
            });
        }
        Ok(report)
    }

    fn validate(&self) -> Result<(), CartridgeRefusalV1> {
        self.manifest.validate()?;
        if !self.frames.windows(2).all(|pair| pair[0].id < pair[1].id) {
            return invalid(CartridgeRuleV1::FramesNotStrictlySorted, 0);
        }
        for (index, frame) in self.frames.iter().enumerate() {
            validate_frame(&self.manifest, frame, index)?;
        }
        Ok(())
    }
}

fn warm_cache_refusal_state(refusal: &CartridgeRefusalV1) -> WarmCacheStateV1 {
    match refusal {
        CartridgeRefusalV1::UnsupportedVersion { .. } => WarmCacheStateV1::UnsupportedVersion,
        CartridgeRefusalV1::InvalidStructure {
            rule: CartridgeRuleV1::UnknownCriticalExtension,
            ..
        } => WarmCacheStateV1::UnknownCriticalExtension,
        CartridgeRefusalV1::SchemaNameMismatch { .. }
        | CartridgeRefusalV1::Malformed(_)
        | CartridgeRefusalV1::InvalidStructure { .. }
        | CartridgeRefusalV1::PortabilityMismatch { .. }
        | CartridgeRefusalV1::MissingObject { .. }
        | CartridgeRefusalV1::MissingChunk { .. }
        | CartridgeRefusalV1::DuplicateFrame { .. }
        | CartridgeRefusalV1::ConflictingObjectDeclaration { .. } => WarmCacheStateV1::Malformed,
    }
}

fn validate_frame(
    manifest: &CartridgeManifestV1,
    frame: &CartridgeFrameV1,
    index: usize,
) -> Result<(), CartridgeRefusalV1> {
    let Some(descriptor) = manifest.chunk(frame.id) else {
        return invalid(CartridgeRuleV1::FrameUndeclared, index);
    };
    if descriptor.len != frame.bytes.len() as u64 {
        return invalid(CartridgeRuleV1::FrameLengthMismatch, index);
    }
    if cartridge_chunk_id(&frame.bytes) != frame.id {
        return invalid(CartridgeRuleV1::FrameDigestMismatch, index);
    }
    Ok(())
}

/// Failure-atomic mutable staging area. A frame is fully checked before insertion.
#[derive(Debug, Clone)]
pub struct CartridgeStagerV1 {
    manifest: CartridgeManifestV1,
    frames: BTreeMap<CartridgeChunkIdV1, Vec<u8>>,
}

impl CartridgeStagerV1 {
    pub fn new(manifest: CartridgeManifestV1) -> Result<CartridgeStagerV1, CartridgeRefusalV1> {
        manifest.validate()?;
        Ok(CartridgeStagerV1 {
            manifest,
            frames: BTreeMap::new(),
        })
    }

    pub fn manifest(&self) -> &CartridgeManifestV1 {
        &self.manifest
    }

    pub fn staged_frames(&self) -> usize {
        self.frames.len()
    }

    pub fn stage(&mut self, frame: CartridgeFrameV1) -> Result<(), CartridgeRefusalV1> {
        if self.frames.contains_key(&frame.id) {
            return Err(CartridgeRefusalV1::DuplicateFrame { chunk: frame.id });
        }
        validate_frame(&self.manifest, &frame, self.frames.len())?;
        self.frames.insert(frame.id, frame.bytes);
        Ok(())
    }

    pub fn transport_state(&self) -> CartridgeTransportStateV1 {
        transport_state(&self.manifest, &self.frames.keys().copied().collect())
    }

    pub fn snapshot(&self) -> Result<CartridgeArchiveV1, CartridgeRefusalV1> {
        CartridgeArchiveV1::new(
            self.manifest.clone(),
            self.frames
                .iter()
                .map(|(id, bytes)| CartridgeFrameV1 {
                    id: *id,
                    bytes: bytes.clone(),
                })
                .collect(),
        )
    }

    pub fn finalize_sealed(self) -> Result<CartridgeArchiveV1, CartridgeRefusalV1> {
        let archive = self.snapshot()?;
        if matches!(
            archive.transport_state(),
            CartridgeTransportStateV1::Thin | CartridgeTransportStateV1::Partial { .. }
        ) {
            return invalid(CartridgeRuleV1::RequiredFramesMissing, 0);
        }
        Ok(archive)
    }
}

/// Incremental boundary adapter. It never publishes a partial archive; callers can
/// retain the buffer for diagnosis, while authority remains on `finish`.
#[derive(Debug, Clone)]
pub struct CartridgeStreamDecoderV1 {
    bytes: Vec<u8>,
    max_buffered_bytes: u64,
    cancelled: bool,
}

impl CartridgeStreamDecoderV1 {
    pub fn new(max_buffered_bytes: u64) -> CartridgeStreamDecoderV1 {
        CartridgeStreamDecoderV1 {
            bytes: Vec::new(),
            max_buffered_bytes,
            cancelled: false,
        }
    }

    pub fn buffered_bytes(&self) -> usize {
        self.bytes.len()
    }

    pub fn cancel(&mut self) {
        self.cancelled = true;
    }

    pub fn push(&mut self, bytes: &[u8]) -> Outcome<Result<(), CartridgeRefusalV1>> {
        if self.cancelled {
            return Outcome::Inconclusive(Inconclusive::cancelled("cartridge stream"));
        }
        let observed = (self.bytes.len() as u64).saturating_add(bytes.len() as u64);
        if observed > self.max_buffered_bytes {
            return Outcome::Inconclusive(
                Inconclusive::resource(ResourceUsage {
                    reason: ResourceReason::Memory {
                        limit_bytes: self.max_buffered_bytes,
                    },
                    allowed: self.max_buffered_bytes,
                    observed,
                })
                .with_progress(format!("{} buffered bytes", self.bytes.len())),
            );
        }
        self.bytes.extend_from_slice(bytes);
        Outcome::Complete(Ok(()))
    }

    pub fn finish(self, budgets: CartridgeDecodeBudgetsV1) -> CartridgeArchiveDecodeOutcomeV1 {
        if self.cancelled {
            return Outcome::Inconclusive(Inconclusive::cancelled("cartridge stream"));
        }
        CartridgeArchiveV1::from_canonical_bytes_budgeted(&self.bytes, budgets)
    }
}

/// Derived byte locator for one frame.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChunkLocatorV1 {
    pub id: CartridgeChunkIdV1,
    pub payload_offset: usize,
    pub len: usize,
}

/// Random-access index derived from validated archive bytes. No producer offset enters
/// this type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CartridgeIndexV1 {
    pub manifest_root: Digest,
    pub transport_state: CartridgeTransportStateV1,
    pub chunks: Vec<ChunkLocatorV1>,
}

impl CartridgeIndexV1 {
    pub fn from_canonical_bytes(
        bytes: &[u8],
        budgets: CartridgeDecodeBudgetsV1,
    ) -> Outcome<Result<CartridgeIndexV1, CartridgeRefusalV1>> {
        let archive = match CartridgeArchiveV1::from_canonical_bytes_budgeted(bytes, budgets) {
            Outcome::Complete(Ok(archive)) => archive,
            Outcome::Complete(Err(refusal)) => return Outcome::Complete(Err(refusal)),
            Outcome::Inconclusive(stop) => return Outcome::Inconclusive(stop),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };
        let chunks = match locate_frames(bytes) {
            Ok(chunks) => chunks,
            Err(refusal) => return Outcome::Complete(Err(refusal)),
        };
        Outcome::Complete(Ok(CartridgeIndexV1 {
            manifest_root: match archive.manifest_root() {
                Ok(root) => root,
                Err(refusal) => return Outcome::Complete(Err(refusal)),
            },
            transport_state: archive.transport_state(),
            chunks,
        }))
    }

    pub fn read_chunk<'a>(
        &self,
        archive_bytes: &'a [u8],
        id: CartridgeChunkIdV1,
    ) -> Result<&'a [u8], CartridgeRefusalV1> {
        let locator = self
            .chunks
            .binary_search_by_key(&id, |locator| locator.id)
            .ok()
            .map(|index| self.chunks[index])
            .ok_or(CartridgeRefusalV1::MissingChunk { chunk: id })?;
        let end = locator
            .payload_offset
            .checked_add(locator.len)
            .filter(|end| *end <= archive_bytes.len())
            .ok_or(CartridgeRefusalV1::InvalidStructure {
                rule: CartridgeRuleV1::FrameLengthMismatch,
                index: 0,
            })?;
        let payload = &archive_bytes[locator.payload_offset..end];
        if cartridge_chunk_id(payload) != id {
            return invalid(CartridgeRuleV1::FrameDigestMismatch, 0);
        }
        Ok(payload)
    }
}

fn locate_frames(bytes: &[u8]) -> Result<Vec<ChunkLocatorV1>, CartridgeRefusalV1> {
    let mut reader = CanonReader::new(bytes);
    reader
        .expect_schema(SCHEMA_CARTRIDGE_ARCHIVE)
        .map_err(CartridgeRefusalV1::Malformed)?;
    let _manifest = reader.bytes().map_err(CartridgeRefusalV1::Malformed)?;
    let count = read_count(
        &mut reader,
        MAX_CARTRIDGE_CHUNKS_V1,
        "too many cartridge frames",
    )
    .map_err(CartridgeRefusalV1::Malformed)?;
    let mut chunks = Vec::with_capacity(count);
    for _ in 0..count {
        let id = read_chunk_id(&mut reader).map_err(CartridgeRefusalV1::Malformed)?;
        let payload = reader.bytes().map_err(CartridgeRefusalV1::Malformed)?;
        chunks.push(ChunkLocatorV1 {
            id,
            payload_offset: reader.offset().saturating_sub(payload.len()),
            len: payload.len(),
        });
    }
    reader.finish().map_err(CartridgeRefusalV1::Malformed)?;
    Ok(chunks)
}

#[derive(Debug, Clone)]
struct BuilderObjectV1 {
    kind: CartridgeObjectKindV1,
    requirement: ObjectRequirementV1,
    portability: ObjectPortabilityV1,
    bytes: Vec<u8>,
}

/// Deterministic constructor for real cartridge handoff paths.
#[derive(Debug, Clone)]
pub struct CartridgeBuilderV1 {
    epoch: EpochId,
    environment_root: ContentRoot,
    chunk_size: usize,
    objects: BTreeMap<CartridgeObjectIdV1, BuilderObjectV1>,
    conflicting_objects: BTreeSet<CartridgeObjectIdV1>,
    root_receipts: BTreeSet<CartridgeObjectIdV1>,
    attachments: BTreeSet<ReceiptAttachmentV1>,
    extensions: Vec<CartridgeExtensionV1>,
}

impl CartridgeBuilderV1 {
    pub fn new(epoch: EpochId, environment_root: ContentRoot) -> CartridgeBuilderV1 {
        CartridgeBuilderV1 {
            epoch,
            environment_root,
            chunk_size: 64 * 1024,
            objects: BTreeMap::new(),
            conflicting_objects: BTreeSet::new(),
            root_receipts: BTreeSet::new(),
            attachments: BTreeSet::new(),
            extensions: Vec::new(),
        }
    }

    pub fn with_chunk_size(
        mut self,
        chunk_size: usize,
    ) -> Result<CartridgeBuilderV1, CartridgeRefusalV1> {
        if chunk_size == 0 {
            return invalid(CartridgeRuleV1::InvalidChunkSize, 0);
        }
        self.chunk_size = chunk_size;
        Ok(self)
    }

    pub fn add_object(
        &mut self,
        kind: CartridgeObjectKindV1,
        requirement: ObjectRequirementV1,
        portability: ObjectPortabilityV1,
        bytes: impl Into<Vec<u8>>,
    ) -> CartridgeObjectIdV1 {
        let bytes = bytes.into();
        let id = cartridge_object_id(kind, &bytes);
        if let Some(existing) = self.objects.get_mut(&id) {
            if existing.kind != kind || existing.bytes != bytes {
                self.conflicting_objects.insert(id);
                return id;
            }
            if requirement == ObjectRequirementV1::Required {
                existing.requirement = ObjectRequirementV1::Required;
            }
            match merge_portability(&existing.portability, &portability) {
                Some(merged) => existing.portability = merged,
                None => {
                    self.conflicting_objects.insert(id);
                }
            }
        } else {
            self.objects.insert(
                id,
                BuilderObjectV1 {
                    kind,
                    requirement,
                    portability,
                    bytes,
                },
            );
        }
        id
    }

    pub fn add_root_receipt(&mut self, receipt: CartridgeObjectIdV1) {
        self.root_receipts.insert(receipt);
    }

    pub fn attach(
        &mut self,
        receipt: CartridgeObjectIdV1,
        role: AttachmentRoleV1,
        object: CartridgeObjectIdV1,
    ) {
        self.attachments.insert(ReceiptAttachmentV1 {
            receipt,
            role,
            object,
        });
    }

    pub fn add_extension(&mut self, extension: CartridgeExtensionV1) {
        self.extensions.push(extension);
        self.extensions.sort_by_key(|extension| extension.id);
    }

    pub fn build(self) -> Result<CartridgeArchiveV1, CartridgeRefusalV1> {
        if self.chunk_size == 0 {
            return invalid(CartridgeRuleV1::InvalidChunkSize, 0);
        }
        if let Some(object) = self.conflicting_objects.first() {
            return Err(CartridgeRefusalV1::ConflictingObjectDeclaration { object: *object });
        }
        let mut frames: BTreeMap<CartridgeChunkIdV1, Vec<u8>> = BTreeMap::new();
        let mut objects = Vec::with_capacity(self.objects.len());
        for (id, object) in self.objects {
            let mut refs = Vec::new();
            let mut offset = 0u64;
            if object.bytes.is_empty() {
                let frame = CartridgeFrameV1::new(Vec::new());
                refs.push(ObjectChunkRefV1 {
                    id: frame.id,
                    offset: 0,
                    len: 0,
                });
                frames.entry(frame.id).or_insert(frame.bytes);
            } else {
                for bytes in object.bytes.chunks(self.chunk_size) {
                    let frame = CartridgeFrameV1::new(bytes.to_vec());
                    refs.push(ObjectChunkRefV1 {
                        id: frame.id,
                        offset,
                        len: frame.bytes.len() as u64,
                    });
                    offset += frame.bytes.len() as u64;
                    frames.entry(frame.id).or_insert(frame.bytes);
                }
            }
            objects.push(CartridgeObjectV1 {
                id,
                kind: object.kind,
                requirement: object.requirement,
                portability: object.portability,
                len: object.bytes.len() as u64,
                chunks: refs,
            });
        }
        let chunks = frames
            .iter()
            .map(|(id, bytes)| ChunkDescriptorV1 {
                id: *id,
                len: bytes.len() as u64,
            })
            .collect();
        let manifest = CartridgeManifestV1::new(
            self.epoch,
            self.environment_root,
            self.root_receipts.into_iter().collect(),
            objects,
            chunks,
            self.attachments.into_iter().collect(),
            self.extensions,
        )?;
        CartridgeArchiveV1::new(
            manifest,
            frames
                .into_iter()
                .map(|(id, bytes)| CartridgeFrameV1 { id, bytes })
                .collect(),
        )
    }
}

fn merge_portability(
    left: &ObjectPortabilityV1,
    right: &ObjectPortabilityV1,
) -> Option<ObjectPortabilityV1> {
    match (left, right) {
        (ObjectPortabilityV1::Portable, other) | (other, ObjectPortabilityV1::Portable) => {
            Some(other.clone())
        }
        (ObjectPortabilityV1::EpochBound, ObjectPortabilityV1::EpochBound) => {
            Some(ObjectPortabilityV1::EpochBound)
        }
        (ObjectPortabilityV1::EpochBound, platform @ ObjectPortabilityV1::PlatformBound { .. })
        | (platform @ ObjectPortabilityV1::PlatformBound { .. }, ObjectPortabilityV1::EpochBound) => {
            Some(platform.clone())
        }
        (
            ObjectPortabilityV1::PlatformBound { target: left },
            ObjectPortabilityV1::PlatformBound { target: right },
        ) if left == right => Some(ObjectPortabilityV1::PlatformBound {
            target: left.clone(),
        }),
        (ObjectPortabilityV1::PlatformBound { .. }, ObjectPortabilityV1::PlatformBound { .. }) => {
            None
        }
    }
}

/// Content identity of one frame.
pub fn cartridge_chunk_id(bytes: &[u8]) -> CartridgeChunkIdV1 {
    let mut writer = CanonWriter::new();
    writer.str("fln.cartridge.chunk/1");
    writer.bytes(bytes);
    CartridgeChunkIdV1::new(hash(Domain::Receipt, &writer.into_bytes()))
}

/// Content identity of one typed logical object.
pub fn cartridge_object_id(kind: CartridgeObjectKindV1, bytes: &[u8]) -> CartridgeObjectIdV1 {
    let mut writer = CanonWriter::new();
    writer.str("fln.cartridge.object/1");
    writer.u8(kind.tag());
    writer.bytes(bytes);
    CartridgeObjectIdV1::new(hash(Domain::Receipt, &writer.into_bytes()))
}

fn invalid<T>(rule: CartridgeRuleV1, index: usize) -> Result<T, CartridgeRefusalV1> {
    Err(CartridgeRefusalV1::InvalidStructure {
        rule,
        index: index as u64,
    })
}

fn strictly_sorted<T: Ord>(values: &[T]) -> bool {
    values.windows(2).all(|pair| pair[0] < pair[1])
}

fn validate_extensions(extensions: &[CartridgeExtensionV1]) -> Result<(), CartridgeRefusalV1> {
    if extensions.len() > MAX_EXTENSIONS_V1 {
        return invalid(CartridgeRuleV1::TooManyExtensions, extensions.len());
    }
    if !extensions.windows(2).all(|pair| pair[0].id < pair[1].id) {
        return invalid(CartridgeRuleV1::ExtensionsNotStrictlySorted, 0);
    }
    for (index, extension) in extensions.iter().enumerate() {
        if extension.payload.len() > MAX_EXTENSION_PAYLOAD_V1 {
            return invalid(CartridgeRuleV1::OversizeExtension, index);
        }
        if extension.critical {
            return invalid(CartridgeRuleV1::UnknownCriticalExtension, index);
        }
    }
    Ok(())
}

fn decode_error<T>(
    reader: &CanonReader<'_>,
    error: CanonError,
) -> Outcome<Result<T, CartridgeRefusalV1>> {
    match reader.exhausted() {
        Some(stop) => Outcome::Inconclusive(stop.into_inconclusive()),
        None => Outcome::Complete(Err(CartridgeRefusalV1::Malformed(error))),
    }
}

fn finish_decoded<T>(
    reader: CanonReader<'_>,
    value: T,
    validate: fn(&T) -> Result<(), CartridgeRefusalV1>,
) -> Outcome<Result<T, CartridgeRefusalV1>> {
    let exhausted = reader.exhausted();
    match reader.finish() {
        Ok(()) => match exhausted {
            None => Outcome::Complete(validate(&value).map(|()| value)),
            Some(_) => Outcome::InternalFault(
                InternalFault::new(
                    "FL-INV-07",
                    "cartridge decode completed after recording a budget stop",
                )
                .with_evidence("fln_hash::cartridge::finish_decoded"),
            ),
        },
        Err(error) => match exhausted {
            Some(stop) => Outcome::Inconclusive(stop.into_inconclusive()),
            None => Outcome::Complete(Err(CartridgeRefusalV1::Malformed(error))),
        },
    }
}

fn read_count(
    reader: &mut CanonReader<'_>,
    maximum: usize,
    what: &'static str,
) -> Result<usize, CanonError> {
    let count = reader.u64()?;
    let count = usize::try_from(count).map_err(|_| reader.reject(what))?;
    if count > maximum {
        return Err(reader.reject(what));
    }
    Ok(count)
}

fn write_u128(writer: &mut CanonWriter, value: u128) {
    writer.u64(value as u64);
    writer.u64((value >> 64) as u64);
}

fn read_u128(reader: &mut CanonReader<'_>) -> Result<u128, CanonError> {
    let low = u128::from(reader.u64()?);
    let high = u128::from(reader.u64()?);
    Ok(low | (high << 64))
}

fn write_digest(writer: &mut CanonWriter, digest: Digest) {
    writer.bytes(&digest.0);
}

fn read_digest(reader: &mut CanonReader<'_>) -> Result<Digest, CanonError> {
    let raw = reader.bytes()?;
    let bytes: [u8; 32] = raw
        .try_into()
        .map_err(|_| reader.reject("digest must contain exactly 32 bytes"))?;
    reader.charge_node()?;
    Ok(Digest(bytes))
}

fn write_root(writer: &mut CanonWriter, root: ContentRoot) {
    writer.bytes(&root.bytes());
}

fn read_root(reader: &mut CanonReader<'_>) -> Result<ContentRoot, CanonError> {
    Ok(ContentRoot::new(read_digest(reader)?.0))
}

fn write_object_id(writer: &mut CanonWriter, id: CartridgeObjectIdV1) {
    write_digest(writer, id.digest());
}

fn read_object_id(reader: &mut CanonReader<'_>) -> Result<CartridgeObjectIdV1, CanonError> {
    Ok(CartridgeObjectIdV1::new(read_digest(reader)?))
}

fn write_chunk_id(writer: &mut CanonWriter, id: CartridgeChunkIdV1) {
    write_digest(writer, id.digest());
}

fn read_chunk_id(reader: &mut CanonReader<'_>) -> Result<CartridgeChunkIdV1, CanonError> {
    Ok(CartridgeChunkIdV1::new(read_digest(reader)?))
}

fn write_optional_root(writer: &mut CanonWriter, root: Option<ContentRoot>) {
    writer.bool(root.is_some());
    if let Some(root) = root {
        write_root(writer, root);
    }
}

fn read_optional_root(reader: &mut CanonReader<'_>) -> Result<Option<ContentRoot>, CanonError> {
    if reader.bool()? {
        Ok(Some(read_root(reader)?))
    } else {
        Ok(None)
    }
}

fn write_roots(writer: &mut CanonWriter, roots: &[ContentRoot]) {
    writer.u64(roots.len() as u64);
    for root in roots {
        write_root(writer, *root);
    }
}

fn read_roots(
    reader: &mut CanonReader<'_>,
    maximum: usize,
    what: &'static str,
) -> Result<Vec<ContentRoot>, CanonError> {
    let count = read_count(reader, maximum, what)?;
    let mut roots = Vec::with_capacity(count);
    for _ in 0..count {
        roots.push(read_root(reader)?);
    }
    Ok(roots)
}

fn write_warm_binding(writer: &mut CanonWriter, binding: &WarmDefeqBindingV1) {
    write_object_id(writer, binding.receipt_object);
    write_object_id(writer, binding.certificate_object);
    write_u128(writer, binding.epoch.get());
    writer.u8(binding.mode.tag());
    write_root(writer, binding.environment_root);
    write_root(writer, binding.kernel_build_root);
    write_root(writer, binding.checker_build_root);
    write_root(writer, binding.policy_root);
    write_root(writer, binding.fuel_profile_root);
}

fn read_warm_binding(reader: &mut CanonReader<'_>) -> Result<WarmDefeqBindingV1, CanonError> {
    Ok(WarmDefeqBindingV1 {
        receipt_object: read_object_id(reader)?,
        certificate_object: read_object_id(reader)?,
        epoch: EpochId::new(read_u128(reader)?),
        mode: Mode::from_tag(Some(reader.u8()?))
            .map_err(|_| reader.reject("unknown warm-cache mode"))?,
        environment_root: read_root(reader)?,
        kernel_build_root: read_root(reader)?,
        checker_build_root: read_root(reader)?,
        policy_root: read_root(reader)?,
        fuel_profile_root: read_root(reader)?,
    })
}

fn write_warm_query(writer: &mut CanonWriter, query: &WarmDefeqQueryV1) {
    write_root(writer, query.left_term_root);
    write_root(writer, query.right_term_root);
    write_optional_root(writer, query.expected_type_root);
    writer.u8(query.transparency.tag());
}

fn read_warm_query(reader: &mut CanonReader<'_>) -> Result<WarmDefeqQueryV1, CanonError> {
    Ok(WarmDefeqQueryV1 {
        left_term_root: read_root(reader)?,
        right_term_root: read_root(reader)?,
        expected_type_root: read_optional_root(reader)?,
        transparency: read_transparency(reader)?,
    })
}

fn write_warm_entry(writer: &mut CanonWriter, entry: &WarmDefeqEntryV1) {
    write_warm_query(writer, &entry.query);
    write_root(writer, entry.normal_form_root);
    write_roots(writer, &entry.left_trace);
    write_roots(writer, &entry.right_trace);
}

fn read_warm_entry(reader: &mut CanonReader<'_>) -> Result<WarmDefeqEntryV1, CanonError> {
    Ok(WarmDefeqEntryV1 {
        query: read_warm_query(reader)?,
        normal_form_root: read_root(reader)?,
        left_trace: read_roots(
            reader,
            MAX_REDUCTION_TRACE_ROOTS_V1,
            "too many left reduction trace roots",
        )?,
        right_trace: read_roots(
            reader,
            MAX_REDUCTION_TRACE_ROOTS_V1,
            "too many right reduction trace roots",
        )?,
    })
}

fn read_transparency(reader: &mut CanonReader<'_>) -> Result<DefeqTransparencyV1, CanonError> {
    match reader.u8()? {
        0 => Ok(DefeqTransparencyV1::Reducible),
        1 => Ok(DefeqTransparencyV1::Instances),
        2 => Ok(DefeqTransparencyV1::Semireducible),
        3 => Ok(DefeqTransparencyV1::All),
        _ => Err(reader.reject("unknown warm-cache transparency tag")),
    }
}

fn write_extensions(writer: &mut CanonWriter, extensions: &[CartridgeExtensionV1]) {
    writer.u64(extensions.len() as u64);
    for extension in extensions {
        writer.u32(extension.id);
        writer.bool(extension.critical);
        writer.bytes(&extension.payload);
    }
}

fn read_extensions(reader: &mut CanonReader<'_>) -> Result<Vec<CartridgeExtensionV1>, CanonError> {
    let count = read_count(reader, MAX_EXTENSIONS_V1, "too many cartridge extensions")?;
    let mut extensions = Vec::with_capacity(count);
    for _ in 0..count {
        reader.charge_node()?;
        let id = reader.u32()?;
        let critical = reader.bool()?;
        let payload = reader.bytes()?;
        if payload.len() > MAX_EXTENSION_PAYLOAD_V1 {
            return Err(reader.reject("cartridge extension payload exceeds v1 limit"));
        }
        extensions.push(CartridgeExtensionV1 {
            id,
            critical,
            payload: payload.to_vec(),
        });
    }
    Ok(extensions)
}

fn write_manifest_body(writer: &mut CanonWriter, manifest: &CartridgeManifestV1) {
    write_u128(writer, manifest.epoch.get());
    write_root(writer, manifest.environment_root);
    writer.u64(manifest.root_receipts.len() as u64);
    for receipt in &manifest.root_receipts {
        write_object_id(writer, *receipt);
    }
    writer.u64(manifest.objects.len() as u64);
    for object in &manifest.objects {
        write_object(writer, object);
    }
    writer.u64(manifest.chunks.len() as u64);
    for chunk in &manifest.chunks {
        write_chunk_id(writer, chunk.id);
        writer.u64(chunk.len);
    }
    writer.u64(manifest.attachments.len() as u64);
    for attachment in &manifest.attachments {
        write_object_id(writer, attachment.receipt);
        writer.u8(attachment.role.tag());
        write_object_id(writer, attachment.object);
    }
    write_extensions(writer, &manifest.extensions);
}

fn read_manifest_body(reader: &mut CanonReader<'_>) -> Result<CartridgeManifestV1, CanonError> {
    let epoch = EpochId::new(read_u128(reader)?);
    let environment_root = read_root(reader)?;
    let receipt_count = read_count(reader, MAX_CARTRIDGE_OBJECTS_V1, "too many root receipts")?;
    let mut root_receipts = Vec::with_capacity(receipt_count);
    for _ in 0..receipt_count {
        root_receipts.push(read_object_id(reader)?);
    }
    let object_count = read_count(
        reader,
        MAX_CARTRIDGE_OBJECTS_V1,
        "too many cartridge objects",
    )?;
    let mut objects = Vec::with_capacity(object_count);
    for _ in 0..object_count {
        reader.charge_node()?;
        objects.push(read_object(reader)?);
    }
    let chunk_count = read_count(reader, MAX_CARTRIDGE_CHUNKS_V1, "too many cartridge chunks")?;
    let mut chunks = Vec::with_capacity(chunk_count);
    for _ in 0..chunk_count {
        reader.charge_node()?;
        chunks.push(ChunkDescriptorV1 {
            id: read_chunk_id(reader)?,
            len: reader.u64()?,
        });
    }
    let attachment_count =
        read_count(reader, MAX_ATTACHMENTS_V1, "too many cartridge attachments")?;
    let mut attachments = Vec::with_capacity(attachment_count);
    for _ in 0..attachment_count {
        reader.charge_node()?;
        attachments.push(ReceiptAttachmentV1 {
            receipt: read_object_id(reader)?,
            role: read_attachment_role(reader)?,
            object: read_object_id(reader)?,
        });
    }
    let extensions = read_extensions(reader)?;
    Ok(CartridgeManifestV1 {
        epoch,
        environment_root,
        root_receipts,
        objects,
        chunks,
        attachments,
        extensions,
    })
}

fn write_object(writer: &mut CanonWriter, object: &CartridgeObjectV1) {
    write_object_id(writer, object.id);
    writer.u8(object.kind.tag());
    writer.u8(match object.requirement {
        ObjectRequirementV1::Required => 0,
        ObjectRequirementV1::Optional => 1,
    });
    match &object.portability {
        ObjectPortabilityV1::Portable => writer.u8(0),
        ObjectPortabilityV1::EpochBound => writer.u8(1),
        ObjectPortabilityV1::PlatformBound { target } => {
            writer.u8(2);
            writer.str(target);
        }
    }
    writer.u64(object.len);
    writer.u64(object.chunks.len() as u64);
    for chunk in &object.chunks {
        write_chunk_id(writer, chunk.id);
        writer.u64(chunk.offset);
        writer.u64(chunk.len);
    }
}

fn read_object(reader: &mut CanonReader<'_>) -> Result<CartridgeObjectV1, CanonError> {
    let id = read_object_id(reader)?;
    let kind = read_object_kind(reader)?;
    let requirement = match reader.u8()? {
        0 => ObjectRequirementV1::Required,
        1 => ObjectRequirementV1::Optional,
        _ => return Err(reader.reject("unknown cartridge requirement tag")),
    };
    let portability = match reader.u8()? {
        0 => ObjectPortabilityV1::Portable,
        1 => ObjectPortabilityV1::EpochBound,
        2 => {
            let target = reader.str()?.to_owned();
            reader.charge_node()?;
            ObjectPortabilityV1::PlatformBound { target }
        }
        _ => return Err(reader.reject("unknown cartridge portability tag")),
    };
    let len = reader.u64()?;
    let chunk_count = read_count(
        reader,
        MAX_OBJECT_CHUNKS_V1,
        "too many chunks in one cartridge object",
    )?;
    let mut chunks = Vec::with_capacity(chunk_count);
    for _ in 0..chunk_count {
        reader.charge_node()?;
        chunks.push(ObjectChunkRefV1 {
            id: read_chunk_id(reader)?,
            offset: reader.u64()?,
            len: reader.u64()?,
        });
    }
    Ok(CartridgeObjectV1 {
        id,
        kind,
        requirement,
        portability,
        len,
        chunks,
    })
}

fn read_object_kind(reader: &mut CanonReader<'_>) -> Result<CartridgeObjectKindV1, CanonError> {
    match reader.u8()? {
        0 => Ok(CartridgeObjectKindV1::Declaration),
        1 => Ok(CartridgeObjectKindV1::Dependency),
        2 => Ok(CartridgeObjectKindV1::Receipt),
        3 => Ok(CartridgeObjectKindV1::Certificate),
        4 => Ok(CartridgeObjectKindV1::Fixture),
        5 => Ok(CartridgeObjectKindV1::Schema),
        6 => Ok(CartridgeObjectKindV1::ResourceContract),
        7 => Ok(CartridgeObjectKindV1::Witness),
        8 => Ok(CartridgeObjectKindV1::WarmDefeqCache),
        _ => Err(reader.reject("unknown cartridge object-kind tag")),
    }
}

fn read_attachment_role(reader: &mut CanonReader<'_>) -> Result<AttachmentRoleV1, CanonError> {
    match reader.u8()? {
        0 => Ok(AttachmentRoleV1::Certificate),
        1 => Ok(AttachmentRoleV1::Dependency),
        2 => Ok(AttachmentRoleV1::Fixture),
        3 => Ok(AttachmentRoleV1::Schema),
        4 => Ok(AttachmentRoleV1::ResourceContract),
        5 => Ok(AttachmentRoleV1::Witness),
        6 => Ok(AttachmentRoleV1::WarmDefeqCache),
        _ => Err(reader.reject("unknown cartridge attachment-role tag")),
    }
}
