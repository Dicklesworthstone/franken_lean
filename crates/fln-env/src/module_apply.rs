//! Atomic module-application input binding.
//!
//! The provenance manifest deliberately retains contribution *identity* rather than a
//! second copy of declarations or extension bytes.  This module is the boundary where
//! those `Arc`-backed values are paired with the validated manifest before later apply
//! phases can build an immutable committed environment state.

use std::fmt;
use std::sync::Arc;

use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::{Inconclusive, Outcome};
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::root::LogicalRoot;

use crate::constants::ConstantInfo;
use crate::environment::{DeclarationDeltaError, Environment};
use crate::extensions::ExtensionDescriptor;
use crate::modules::{ArtifactEvidence, CancellationProbe, ModuleGraph, ModuleId};
use crate::provenance::{
    CaptureStatus, DeclarationClass, ExtensionContribution, ExtensionEntryId,
    ModuleContributionRecord, ModuleProvenanceError, ModuleProvenanceIndexes,
    ModuleProvenanceManifest, ModuleProvenanceRoot, ProvenanceAuthority, ProvenanceCompleteness,
};

/// Schema for the ephemeral payload envelope.  Bumping it invalidates every prepared
/// input: a plan must never be consumed under a payload-binding interpretation it was
/// not checked against.
pub const MODULE_APPLY_SCHEMA_VERSION: u16 = 1;

/// Frozen observation points at which module application may report cancellation.
///
/// A checkpoint is named rather than inferred from a call count so a non-answer records
/// exactly how far the transaction progressed. The final checkpoint is sampled only after
/// base, candidate, and receipt revalidation, immediately before a successful result could
/// release authoritative state.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ModuleApplyCheckpoint {
    BeforePublication,
}

impl fmt::Display for ModuleApplyCheckpoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BeforePublication => f.write_str("module-apply/before-publication"),
        }
    }
}

fn cancelled_before_module_publication<T>() -> Outcome<T> {
    Outcome::Inconclusive(Inconclusive::cancelled(
        ModuleApplyCheckpoint::BeforePublication.to_string(),
    ))
}

/// Stable identity for one exact payload-bearing apply transaction.
///
/// The preimage is root-scoped: the manifest root binds the ordered contribution
/// records and extension entry identities, while the ordered declaration-content
/// digests bind the Arc-backed values that the manifest intentionally does not copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleApplyTransactionId(Digest);

impl ModuleApplyTransactionId {
    fn derive(manifest_root: ModuleProvenanceRoot, declaration_identities: &[Digest]) -> Self {
        let mut bytes = Vec::with_capacity(
            b"fln.env.module-apply.transaction/1"
                .len()
                .saturating_add(32)
                .saturating_add(declaration_identities.len().saturating_mul(32)),
        );
        bytes.extend_from_slice(b"fln.env.module-apply.transaction/1");
        bytes.extend_from_slice(&manifest_root.0.0);
        for identity in declaration_identities {
            bytes.extend_from_slice(&identity.0);
        }
        Self(hash(Domain::Receipt, &bytes))
    }

    fn from_payload(manifest_root: ModuleProvenanceRoot, payload: &AppliedModulePayload) -> Self {
        let declaration_identities = payload
            .declarations()
            .iter()
            .chain(payload.extra_declarations())
            .map(|info| Environment::decl_content_digest(info))
            .collect::<Vec<_>>();
        Self::derive(manifest_root, &declaration_identities)
    }

    fn from_state(state: &ModuleApplyState, module: &ModuleId) -> Option<Self> {
        let payload = state
            .applied_payloads()
            .iter()
            .find(|payload| &payload.contribution().module().id == module)?;
        Some(Self::from_payload(state.manifest().root(), payload))
    }

    pub const fn digest(&self) -> Digest {
        self.0
    }
}

/// One raw extension payload at its precise source occurrence.
///
/// `contribution_index` distinguishes repeated uses of the same descriptor.  The
/// stable content identity remains [`ExtensionEntryId`]; the two ordinals locate an
/// occurrence and therefore never enter that identity.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionPayload {
    contribution_index: usize,
    descriptor: ExtensionDescriptor,
    source_ordinal: u64,
    payload: Arc<[u8]>,
}

impl ExtensionPayload {
    pub fn new(
        contribution_index: usize,
        descriptor: ExtensionDescriptor,
        source_ordinal: u64,
        payload: impl Into<Arc<[u8]>>,
    ) -> Self {
        Self {
            contribution_index,
            descriptor,
            source_ordinal,
            payload: payload.into(),
        }
    }

    pub const fn contribution_index(&self) -> usize {
        self.contribution_index
    }

    pub const fn source_ordinal(&self) -> u64 {
        self.source_ordinal
    }

    pub fn descriptor(&self) -> &ExtensionDescriptor {
        &self.descriptor
    }

    pub fn payload(&self) -> &[u8] {
        &self.payload
    }

    fn payload_arc(&self) -> Arc<[u8]> {
        Arc::clone(&self.payload)
    }

    pub fn shares_payload_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.payload, &other.payload)
    }
}

/// The payload-bearing request which an atomic module apply consumes.
///
/// The manifest remains the sole provenance truth; this envelope is neither a store
/// nor an authority.  It owns no flattened copy of declaration or extension payload
/// storage, only the caller's immutable `Arc` values.
#[derive(Debug, Clone)]
pub struct ModuleApplyTransaction {
    manifest: Arc<ModuleProvenanceManifest>,
    contribution: ModuleContributionRecord,
    declarations: Arc<[Arc<ConstantInfo>]>,
    extra_declarations: Arc<[Arc<ConstantInfo>]>,
    extension_payloads: Arc<[ExtensionPayload]>,
}

impl ModuleApplyTransaction {
    pub fn new(
        manifest: Arc<ModuleProvenanceManifest>,
        contribution: ModuleContributionRecord,
        declarations: Vec<Arc<ConstantInfo>>,
        extra_declarations: Vec<Arc<ConstantInfo>>,
        extension_payloads: Vec<ExtensionPayload>,
    ) -> Self {
        Self {
            manifest,
            contribution,
            declarations: declarations.into(),
            extra_declarations: extra_declarations.into(),
            extension_payloads: extension_payloads.into(),
        }
    }

    pub fn manifest(&self) -> &ModuleProvenanceManifest {
        &self.manifest
    }

    pub fn contribution(&self) -> &ModuleContributionRecord {
        &self.contribution
    }

    pub fn declarations(&self) -> &[Arc<ConstantInfo>] {
        &self.declarations
    }

    pub fn extra_declarations(&self) -> &[Arc<ConstantInfo>] {
        &self.extra_declarations
    }

    pub fn extension_payloads(&self) -> &[ExtensionPayload] {
        &self.extension_payloads
    }
}

/// Caller-supplied resource budgets for one module-application transaction.
///
/// The manifest and graph enforce their own admission limits when a committed
/// state is constructed; these bounds are the envelope-side complement. They cap
/// what one transaction may carry *before* any binding work runs, so an
/// oversized envelope is refused before manifest verification, payload
/// comparison, extension replay, or graph preparation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleApplyLimits {
    pub max_declaration_payloads: usize,
    pub max_extra_declaration_payloads: usize,
    pub max_extension_payloads: usize,
    pub max_extension_payload_bytes: u128,
}

impl ModuleApplyLimits {
    pub const fn new(
        max_declaration_payloads: usize,
        max_extra_declaration_payloads: usize,
        max_extension_payloads: usize,
        max_extension_payload_bytes: u128,
    ) -> Self {
        Self {
            max_declaration_payloads,
            max_extra_declaration_payloads,
            max_extension_payloads,
            max_extension_payload_bytes,
        }
    }
}

impl Default for ModuleApplyLimits {
    /// Matches the generous production posture of [`crate::provenance::ModuleProvenanceLimits`]:
    /// one million payloads per declaration class and twenty million extension
    /// rows, bounded by four GiB of extension bytes.
    fn default() -> Self {
        Self::new(1_000_000, 1_000_000, 20_000_000, 4 * 1024 * 1024 * 1024)
    }
}

/// Which envelope budget refused a transaction.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleApplyResource {
    DeclarationPayloads,
    ExtraDeclarationPayloads,
    ExtensionPayloads,
    ExtensionPayloadBytes,
}

impl fmt::Display for ModuleApplyResource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::DeclarationPayloads => "declaration payloads",
            Self::ExtraDeclarationPayloads => "extra declaration payloads",
            Self::ExtensionPayloads => "extension payloads",
            Self::ExtensionPayloadBytes => "extension payload bytes",
        };
        f.write_str(text)
    }
}

/// Exact usage facts measured from one transaction envelope before any binding
/// work runs. Counts and byte totals only; nothing is allocated or charged.
///
/// The byte total saturates at `u128::MAX`, which every finite budget refuses.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleApplyUsage {
    declaration_payloads: usize,
    extra_declaration_payloads: usize,
    extension_payloads: usize,
    extension_payload_bytes: u128,
}

impl ModuleApplyUsage {
    pub const fn declaration_payloads(&self) -> usize {
        self.declaration_payloads
    }

    pub const fn extra_declaration_payloads(&self) -> usize {
        self.extra_declaration_payloads
    }

    pub const fn extension_payloads(&self) -> usize {
        self.extension_payloads
    }

    pub const fn extension_payload_bytes(&self) -> u128 {
        self.extension_payload_bytes
    }
}

/// A completed, non-authoritative payload-binding check.
#[derive(Debug, Clone)]
pub struct PreflightedModuleApply {
    schema: u16,
    transaction: ModuleApplyTransaction,
    manifest_root: ModuleProvenanceRoot,
    declaration_identities: Arc<[Digest]>,
    transaction_id: ModuleApplyTransactionId,
    usage: ModuleApplyUsage,
}

/// The only aggregate value an application path may expose as committed.
///
/// The environment, graph, manifest, and bidirectional projections travel together:
/// callers cannot construct a state with a detached index side store.  The constructor
/// proves the graph and environment cover exactly the manifest's records, and derives
/// the indexes itself rather than accepting an independently mutable projection.
///
/// This type deliberately does not make a declaration-content claim the current
/// manifest cannot support.  The payload envelope derives those identities at preflight;
/// a future manifest commitment can make that comparison part of this invariant without
/// changing where committed state lives.
#[derive(Debug, Clone, PartialEq)]
pub struct ModuleApplyState {
    environment: Environment,
    options: KVMap,
    graph: ModuleGraph,
    manifest: Arc<ModuleProvenanceManifest>,
    indexes: ModuleProvenanceIndexes,
    payloads: Arc<[AppliedModulePayload]>,
}

/// A root-scoped placement fact for one committed extension range.
///
/// The ordered entry identities are stable content identities; the retained start is
/// only their placement in this exact committed extension journal. This witness is a
/// view over the canonical contribution record, never a mutable placement index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppliedExtensionRangeWitness {
    provenance_root: ModuleProvenanceRoot,
    module: ModuleId,
    artifact: ArtifactEvidence,
    completeness: ProvenanceCompleteness,
    contribution_index: usize,
    contribution: ExtensionContribution,
}

impl AppliedExtensionRangeWitness {
    pub const fn provenance_root(&self) -> ModuleProvenanceRoot {
        self.provenance_root
    }

    pub fn module(&self) -> &ModuleId {
        &self.module
    }

    pub fn artifact(&self) -> &ArtifactEvidence {
        &self.artifact
    }

    pub fn completeness(&self) -> &ProvenanceCompleteness {
        &self.completeness
    }

    pub const fn contribution_index(&self) -> usize {
        self.contribution_index
    }

    pub fn descriptor(&self) -> &ExtensionDescriptor {
        self.contribution.descriptor()
    }

    pub fn start(&self) -> u64 {
        self.contribution.start()
    }

    pub fn entry_ids(&self) -> &[ExtensionEntryId] {
        self.contribution.entries()
    }

    pub fn source_ordinal(&self, index: usize) -> Option<u64> {
        self.contribution.source_ordinal(index)
    }

    pub fn target_position(&self, index: usize) -> Option<u64> {
        self.contribution.target_position(index)
    }
}

impl ModuleApplyState {
    /// Join already-published immutable components only after checking their shared
    /// provenance truth.  `indexes` are never accepted as an argument: accepting them
    /// would permit an application caller to pair a valid manifest with stale indexes.
    pub fn from_parts(
        environment: Environment,
        graph: ModuleGraph,
        manifest: Arc<ModuleProvenanceManifest>,
    ) -> Result<Self, ModuleApplyStateError> {
        Self::from_parts_with_options(environment, graph, manifest, KVMap::new())
    }

    /// Join immutable components with the exact logical-root options they commit.
    pub fn from_parts_with_options(
        environment: Environment,
        graph: ModuleGraph,
        manifest: Arc<ModuleProvenanceManifest>,
        options: KVMap,
    ) -> Result<Self, ModuleApplyStateError> {
        Self::from_parts_with_options_and_payloads(environment, graph, manifest, options, vec![])
    }

    /// Join immutable components with the exact payload carriers they commit.
    ///
    /// `payloads` is canonicalised by module identity and then checked against every
    /// manifest record. A nonempty manifest with an empty carrier array is refused:
    /// an index-only state is not an applied module state.
    pub fn from_parts_with_payloads(
        environment: Environment,
        graph: ModuleGraph,
        manifest: Arc<ModuleProvenanceManifest>,
        payloads: Vec<AppliedModulePayload>,
    ) -> Result<Self, ModuleApplyStateError> {
        Self::from_parts_with_options_and_payloads(
            environment,
            graph,
            manifest,
            KVMap::new(),
            payloads,
        )
    }

    /// Join immutable components with exact payload carriers and logical-root options.
    pub fn from_parts_with_options_and_payloads(
        environment: Environment,
        graph: ModuleGraph,
        manifest: Arc<ModuleProvenanceManifest>,
        options: KVMap,
        mut payloads: Vec<AppliedModulePayload>,
    ) -> Result<Self, ModuleApplyStateError> {
        manifest
            .verify_self_consistency()
            .map_err(ModuleApplyStateError::ManifestInconsistent)?;
        if graph.epoch() != manifest.epoch() {
            return Err(ModuleApplyStateError::GraphEpoch {
                graph: graph.epoch().clone(),
                manifest: manifest.epoch().clone(),
            });
        }
        if graph.len() != manifest.records().len() {
            return Err(ModuleApplyStateError::GraphModuleCount {
                graph: graph.len(),
                manifest: manifest.records().len(),
            });
        }
        payloads.sort_by(|left, right| {
            left.contribution()
                .module()
                .id
                .cmp(&right.contribution().module().id)
        });
        if payloads.len() != manifest.records().len() {
            return Err(ModuleApplyStateError::PayloadCount {
                payloads: payloads.len(),
                manifest: manifest.records().len(),
            });
        }

        let expected_declarations = manifest
            .facts()
            .declarations
            .checked_add(manifest.facts().extra_declarations)
            .ok_or(ModuleApplyStateError::ManifestFactOverflow)?;
        if environment.len() != expected_declarations {
            return Err(ModuleApplyStateError::EnvironmentDeclarationCount {
                environment: environment.len(),
                manifest: expected_declarations,
            });
        }
        for (record, payload) in manifest.records().iter().zip(&payloads) {
            if payload.contribution() != record {
                return Err(ModuleApplyStateError::PayloadRecordMismatch {
                    module: record.module().id.clone(),
                });
            }
            verify_payload_declarations(
                &environment,
                record.declarations(),
                payload.declarations(),
                DeclarationClass::Declaration,
            )?;
            verify_payload_declarations(
                &environment,
                record.extra_declarations(),
                payload.extra_declarations(),
                DeclarationClass::ExtraDeclaration,
            )?;
            verify_payload_extensions(manifest.epoch(), record, payload.extension_payloads())?;
            let module = record.module().id.clone();
            match graph.record(&module) {
                Some(actual) if actual == record.module() => {}
                Some(_) => return Err(ModuleApplyStateError::GraphRecordMismatch { module }),
                None => return Err(ModuleApplyStateError::GraphRecordAbsent { module }),
            }
            for name in record
                .declarations()
                .iter()
                .chain(record.extra_declarations())
            {
                if !environment.contains(name) {
                    return Err(ModuleApplyStateError::EnvironmentDeclarationAbsent {
                        name: name.clone(),
                    });
                }
            }
            for contribution in record.extension_contributions() {
                let descriptor = contribution.descriptor();
                let state = environment.extension(&descriptor.name).ok_or_else(|| {
                    ModuleApplyStateError::UnknownExtension {
                        name: descriptor.name.clone(),
                    }
                })?;
                if state.descriptor != *descriptor {
                    return Err(ModuleApplyStateError::ExtensionDescriptor {
                        name: descriptor.name.clone(),
                    });
                }
                let start = usize::try_from(contribution.start()).map_err(|_| {
                    ModuleApplyStateError::ExtensionRange {
                        name: descriptor.name.clone(),
                    }
                })?;
                let end = start
                    .checked_add(contribution.entries().len())
                    .ok_or_else(|| ModuleApplyStateError::ExtensionRange {
                        name: descriptor.name.clone(),
                    })?;
                let entries: Vec<_> = state.entries().collect();
                let actual = entries.get(start..end).ok_or_else(|| {
                    ModuleApplyStateError::ExtensionRange {
                        name: descriptor.name.clone(),
                    }
                })?;
                for (offset, (entry, expected)) in
                    actual.iter().zip(contribution.entries()).enumerate()
                {
                    let identity =
                        ExtensionEntryId::derive(manifest.epoch(), descriptor, &entry.payload);
                    if identity != *expected {
                        return Err(ModuleApplyStateError::ExtensionIdentity {
                            name: descriptor.name.clone(),
                            offset,
                        });
                    }
                }
            }
        }

        let indexes = ModuleProvenanceIndexes::derive(&manifest)
            .map_err(ModuleApplyStateError::IndexInconsistent)?;
        indexes
            .verify(&manifest)
            .map_err(ModuleApplyStateError::IndexInconsistent)?;
        Ok(Self {
            environment,
            options,
            graph,
            manifest,
            indexes,
            payloads: payloads.into(),
        })
    }

    pub fn environment(&self) -> &Environment {
        &self.environment
    }

    /// Options that participate in this state's logical root.
    pub fn options(&self) -> &KVMap {
        &self.options
    }

    /// The semantic root of this aggregate state, excluding graph and provenance topology.
    pub fn logical_root(&self) -> LogicalRoot {
        self.environment.logical_root(&self.options)
    }

    pub fn graph(&self) -> &ModuleGraph {
        &self.graph
    }

    pub fn manifest(&self) -> &ModuleProvenanceManifest {
        &self.manifest
    }

    pub fn indexes(&self) -> &ModuleProvenanceIndexes {
        &self.indexes
    }

    /// Exact Arc-backed values retained for every manifest contribution.
    pub fn applied_payloads(&self) -> &[AppliedModulePayload] {
        &self.payloads
    }

    /// Exact placement witnesses for one applied module under this committed root.
    pub fn applied_extension_ranges(
        &self,
        module: &ModuleId,
    ) -> Option<Vec<AppliedExtensionRangeWitness>> {
        let record = self.manifest.record(module)?;
        Some(
            record
                .extension_contributions()
                .iter()
                .enumerate()
                .map(
                    |(contribution_index, contribution)| AppliedExtensionRangeWitness {
                        provenance_root: self.manifest.root(),
                        module: module.clone(),
                        artifact: record.module().artifact.clone(),
                        completeness: record.completeness().clone(),
                        contribution_index,
                        contribution: contribution.clone(),
                    },
                )
                .collect(),
        )
    }

    /// Recheck the single-state invariant before a later apply plan consumes it.
    pub fn verify(&self) -> Result<(), ModuleApplyStateError> {
        let rebuilt = Self::from_parts_with_options_and_payloads(
            self.environment.clone(),
            self.graph.clone(),
            Arc::clone(&self.manifest),
            self.options.clone(),
            self.payloads.to_vec(),
        )?;
        if rebuilt.indexes != self.indexes {
            return Err(ModuleApplyStateError::IndexInconsistent(
                ModuleProvenanceError::GraphAdmissionFault {
                    what: "stored provenance indexes disagree with their manifest derivation",
                },
            ));
        }
        Ok(())
    }
}

/// Refusals while joining the immutable components into one committed state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyStateError {
    ManifestInconsistent(ModuleProvenanceError),
    GraphEpoch {
        graph: crate::modules::ModuleEpoch,
        manifest: crate::modules::ModuleEpoch,
    },
    GraphModuleCount {
        graph: usize,
        manifest: usize,
    },
    GraphRecordAbsent {
        module: ModuleId,
    },
    GraphRecordMismatch {
        module: ModuleId,
    },
    PayloadCount {
        payloads: usize,
        manifest: usize,
    },
    PayloadRecordMismatch {
        module: ModuleId,
    },
    PayloadDeclarationCount {
        class: DeclarationClass,
        expected: usize,
        actual: usize,
    },
    PayloadDeclarationName {
        class: DeclarationClass,
        index: usize,
        expected: Name,
        actual: Name,
    },
    PayloadDeclarationValue {
        class: DeclarationClass,
        name: Name,
    },
    PayloadExtensionCount {
        module: ModuleId,
        expected: usize,
        actual: usize,
    },
    PayloadExtensionOccurrence {
        module: ModuleId,
        payload_index: usize,
    },
    PayloadExtensionDescriptor {
        module: ModuleId,
        payload_index: usize,
    },
    PayloadExtensionIdentity {
        module: ModuleId,
        payload_index: usize,
    },
    ManifestFactOverflow,
    EnvironmentDeclarationCount {
        environment: usize,
        manifest: usize,
    },
    EnvironmentDeclarationAbsent {
        name: Name,
    },
    UnknownExtension {
        name: Name,
    },
    ExtensionDescriptor {
        name: Name,
    },
    ExtensionRange {
        name: Name,
    },
    ExtensionIdentity {
        name: Name,
        offset: usize,
    },
    IndexInconsistent(ModuleProvenanceError),
}

fn verify_payload_declarations(
    environment: &Environment,
    expected: &[Name],
    payloads: &[Arc<ConstantInfo>],
    class: DeclarationClass,
) -> Result<(), ModuleApplyStateError> {
    if expected.len() != payloads.len() {
        return Err(ModuleApplyStateError::PayloadDeclarationCount {
            class,
            expected: expected.len(),
            actual: payloads.len(),
        });
    }
    for (index, (expected, payload)) in expected.iter().zip(payloads).enumerate() {
        if payload.name() != expected {
            return Err(ModuleApplyStateError::PayloadDeclarationName {
                class,
                index,
                expected: expected.clone(),
                actual: payload.name().clone(),
            });
        }
        if environment.find(expected) != Some(payload.as_ref()) {
            return Err(ModuleApplyStateError::PayloadDeclarationValue {
                class,
                name: expected.clone(),
            });
        }
    }
    Ok(())
}

fn verify_payload_extensions(
    epoch: &crate::modules::ModuleEpoch,
    record: &ModuleContributionRecord,
    payloads: &[ExtensionPayload],
) -> Result<(), ModuleApplyStateError> {
    let expected = record
        .extension_contributions()
        .iter()
        .map(|contribution| contribution.entries().len())
        .sum::<usize>();
    let module = record.module().id.clone();
    if payloads.len() != expected {
        return Err(ModuleApplyStateError::PayloadExtensionCount {
            module,
            expected,
            actual: payloads.len(),
        });
    }

    let mut payload_index = 0usize;
    for (contribution_index, contribution) in record.extension_contributions().iter().enumerate() {
        for (entry_index, expected_identity) in contribution.entries().iter().enumerate() {
            let payload = payloads.get(payload_index).ok_or_else(|| {
                ModuleApplyStateError::PayloadExtensionCount {
                    module: module.clone(),
                    expected,
                    actual: payloads.len(),
                }
            })?;
            let expected_ordinal = u64::try_from(entry_index).map_err(|_| {
                ModuleApplyStateError::PayloadExtensionOccurrence {
                    module: module.clone(),
                    payload_index,
                }
            })?;
            if payload.contribution_index() != contribution_index
                || payload.source_ordinal() != expected_ordinal
            {
                return Err(ModuleApplyStateError::PayloadExtensionOccurrence {
                    module: module.clone(),
                    payload_index,
                });
            }
            if payload.descriptor() != contribution.descriptor() {
                return Err(ModuleApplyStateError::PayloadExtensionDescriptor {
                    module: module.clone(),
                    payload_index,
                });
            }
            if ExtensionEntryId::derive(epoch, payload.descriptor(), payload.payload())
                != *expected_identity
            {
                return Err(ModuleApplyStateError::PayloadExtensionIdentity {
                    module: module.clone(),
                    payload_index,
                });
            }
            payload_index = payload_index.checked_add(1).ok_or_else(|| {
                ModuleApplyStateError::PayloadExtensionCount {
                    module: module.clone(),
                    expected,
                    actual: payloads.len(),
                }
            })?;
        }
    }
    Ok(())
}

impl PreflightedModuleApply {
    /// A preflight has not published an environment, graph, receipt, or cache entry.
    pub const fn is_cacheable(&self) -> bool {
        false
    }

    pub const fn schema(&self) -> u16 {
        self.schema
    }

    pub fn transaction(&self) -> &ModuleApplyTransaction {
        &self.transaction
    }

    pub const fn manifest_root(&self) -> ModuleProvenanceRoot {
        self.manifest_root
    }

    /// Exact `Domain::DeclContent` identities derived from the retained values.
    /// They are provisional facts for the later plan and never an accepted cache key.
    pub fn declaration_identities(&self) -> &[Digest] {
        &self.declaration_identities
    }

    /// Root-scoped identity of the exact values preflight bound.
    pub const fn transaction_id(&self) -> ModuleApplyTransactionId {
        self.transaction_id
    }

    /// Exact envelope usage facts measured before any binding work ran.
    pub const fn usage(&self) -> ModuleApplyUsage {
        self.usage
    }
}

/// The payload side of one contribution once its manifest binding has completed.
///
/// This retains the original `Arc` allocations rather than a flattened copy. It is
/// still non-authoritative until an aggregate state includes it through a prepared,
/// base-bound commit; the type only prevents a later state layer from losing the
/// values that preflight actually checked.
#[derive(Debug, Clone, PartialEq)]
pub struct AppliedModulePayload {
    contribution: ModuleContributionRecord,
    declarations: Arc<[Arc<ConstantInfo>]>,
    extra_declarations: Arc<[Arc<ConstantInfo>]>,
    extension_payloads: Arc<[ExtensionPayload]>,
}

impl AppliedModulePayload {
    /// Retain exactly the already-validated transaction allocations.
    pub fn from_preflight(
        preflight: &PreflightedModuleApply,
    ) -> Result<Self, ModuleApplyCandidateError> {
        if preflight.schema != MODULE_APPLY_SCHEMA_VERSION {
            return Err(ModuleApplyCandidateError::SupersededPreflightSchema {
                schema: preflight.schema,
            });
        }
        let transaction = preflight.transaction();
        Ok(Self {
            contribution: transaction.contribution.clone(),
            declarations: Arc::clone(&transaction.declarations),
            extra_declarations: Arc::clone(&transaction.extra_declarations),
            extension_payloads: Arc::clone(&transaction.extension_payloads),
        })
    }

    pub fn contribution(&self) -> &ModuleContributionRecord {
        &self.contribution
    }

    pub fn declarations(&self) -> &[Arc<ConstantInfo>] {
        &self.declarations
    }

    pub fn extra_declarations(&self) -> &[Arc<ConstantInfo>] {
        &self.extra_declarations
    }

    pub fn extension_payloads(&self) -> &[ExtensionPayload] {
        &self.extension_payloads
    }

    /// The storage law required before committed state may retain this payload.
    pub fn shares_storage_with_preflight(&self, preflight: &PreflightedModuleApply) -> bool {
        let transaction = preflight.transaction();
        Arc::ptr_eq(&self.declarations, &transaction.declarations)
            && Arc::ptr_eq(&self.extra_declarations, &transaction.extra_declarations)
            && Arc::ptr_eq(&self.extension_payloads, &transaction.extension_payloads)
    }
}

/// Every preflight refusal names the contribution field that disagreed.  No variant
/// chooses a winner or normalizes mismatched payloads.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyPreflightError {
    ManifestInconsistent(ModuleProvenanceError),
    ContributionAbsent {
        module: crate::modules::ModuleId,
    },
    ContributionMismatch {
        module: crate::modules::ModuleId,
    },
    DeclarationCount {
        class: DeclarationClass,
        expected: usize,
        actual: usize,
    },
    DeclarationName {
        class: DeclarationClass,
        index: usize,
        expected: Name,
        actual: Name,
    },
    ExtensionPayloadCount {
        expected: usize,
        actual: usize,
    },
    ExtensionOccurrence {
        payload_index: usize,
        expected_contribution: usize,
        expected_ordinal: u64,
        actual_contribution: usize,
        actual_ordinal: u64,
    },
    ExtensionDescriptor {
        payload_index: usize,
        expected: ExtensionDescriptor,
        actual: ExtensionDescriptor,
    },
    ExtensionIdentity {
        payload_index: usize,
        expected: ExtensionEntryId,
        actual: ExtensionEntryId,
    },
    LimitExceeded {
        resource: ModuleApplyResource,
        limit: u128,
        actual: u128,
    },
}

/// A preflighted module payload can only join a declaration environment when the
/// kernel-produced candidate differs from the recorded base by exactly those retained
/// declaration values. This remains a non-authoritative comparison: kernel admission
/// is deliberately outside this crate's D6 boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyCandidateError {
    SupersededPreflightSchema { schema: u16 },
    DeclarationDelta(DeclarationDeltaError),
}

/// How the current aggregate state relates to the result named by a retry.
///
/// `ManifestDescendant` is an exact canonical-record containment statement, not a
/// claim about unrecorded process history. The current manifest has strictly more
/// records, contains every target record by exact value, and retains the retried
/// module's exact payload values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleApplyRetryRelation {
    ExactResult,
    ManifestDescendant,
}

/// Additional evidence supplied for an already-applied observation.
///
/// Both arms recheck exact manifest and payload values. `PublicationReceipt` adds
/// the private receipt issued by the original successful transition; it never
/// substitutes for those value checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleApplyRetryEvidence {
    ExactValues,
    PublicationReceipt,
}

/// Classify whether one preflight is already represented by the current state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyRetryDisposition {
    NotCurrentResult {
        requested: ModuleProvenanceRoot,
        current: ModuleProvenanceRoot,
    },
    AlreadyApplied {
        module: ModuleId,
        transaction_id: ModuleApplyTransactionId,
        result_provenance_root: ModuleProvenanceRoot,
        current_provenance_root: ModuleProvenanceRoot,
        relation: ModuleApplyRetryRelation,
        evidence: ModuleApplyRetryEvidence,
    },
}

/// A retry is never silently treated as already applied when canonical records or
/// retained values differ.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyRetryError {
    SupersededPreflightSchema {
        schema: u16,
    },
    State(ModuleApplyStateError),
    RootCollision {
        root: ModuleProvenanceRoot,
    },
    MissingPayload {
        module: ModuleId,
    },
    PayloadConflict {
        module: ModuleId,
        expected: ModuleApplyTransactionId,
        actual: ModuleApplyTransactionId,
    },
    PayloadIdentityCollision {
        module: ModuleId,
        transaction_id: ModuleApplyTransactionId,
    },
    Payload(ModuleApplyCandidateError),
    Receipt(ModuleApplyRetryReceiptError),
}

/// Refusals while binding an optional publication receipt to a retry preflight.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyRetryReceiptError {
    SupersededSchema {
        schema: u16,
    },
    Module {
        expected: ModuleId,
        actual: ModuleId,
    },
    Contribution {
        module: ModuleId,
    },
    Grade {
        module: ModuleId,
    },
    Transaction {
        expected: ModuleApplyTransactionId,
        actual: ModuleApplyTransactionId,
    },
    ResultRoot {
        expected: ModuleProvenanceRoot,
        actual: ModuleProvenanceRoot,
    },
}

/// Recognize an exact-result or strict manifest-descendant retry.
///
/// Digest equality is only a fast locator. An accepted result requires exact target
/// record containment and exact equality of the retried module's retained declaration
/// and extension payload values. A different current root that does not satisfy strict
/// containment remains a normal non-current result.
pub fn classify_module_apply_retry(
    preflight: &PreflightedModuleApply,
    current: &ModuleApplyState,
    receipt: Option<&ModuleApplyReceipt>,
) -> Result<ModuleApplyRetryDisposition, ModuleApplyRetryError> {
    if preflight.schema != MODULE_APPLY_SCHEMA_VERSION {
        return Err(ModuleApplyRetryError::SupersededPreflightSchema {
            schema: preflight.schema,
        });
    }
    current.verify().map_err(ModuleApplyRetryError::State)?;
    if let Some(receipt) = receipt {
        receipt
            .verify_retry_for(preflight)
            .map_err(ModuleApplyRetryError::Receipt)?;
    }

    let target = preflight.transaction().manifest();
    let current_root = current.manifest().root();
    let relation = if current_root == preflight.manifest_root() {
        if current.manifest() != target {
            return Err(ModuleApplyRetryError::RootCollision { root: current_root });
        }
        ModuleApplyRetryRelation::ExactResult
    } else {
        let is_strict_manifest_descendant = current.manifest().epoch() == target.epoch()
            && current.manifest().records().len() > target.records().len()
            && target
                .records()
                .iter()
                .all(|record| current.manifest().record(&record.module().id) == Some(record));
        if !is_strict_manifest_descendant {
            return Ok(ModuleApplyRetryDisposition::NotCurrentResult {
                requested: preflight.manifest_root(),
                current: current_root,
            });
        }
        ModuleApplyRetryRelation::ManifestDescendant
    };

    let module = preflight.transaction().contribution().module().id.clone();
    let actual_payload = current
        .applied_payloads()
        .iter()
        .find(|payload| payload.contribution().module().id == module)
        .ok_or_else(|| ModuleApplyRetryError::MissingPayload {
            module: module.clone(),
        })?;
    let expected_payload =
        AppliedModulePayload::from_preflight(preflight).map_err(ModuleApplyRetryError::Payload)?;
    let actual = ModuleApplyTransactionId::from_payload(preflight.manifest_root(), actual_payload);
    let expected = preflight.transaction_id();
    if actual != expected {
        return Err(ModuleApplyRetryError::PayloadConflict {
            module,
            expected,
            actual,
        });
    }
    if actual_payload != &expected_payload {
        return Err(ModuleApplyRetryError::PayloadIdentityCollision {
            module,
            transaction_id: expected,
        });
    }
    Ok(ModuleApplyRetryDisposition::AlreadyApplied {
        module,
        transaction_id: expected,
        result_provenance_root: preflight.manifest_root(),
        current_provenance_root: current_root,
        relation,
        evidence: if receipt.is_some() {
            ModuleApplyRetryEvidence::PublicationReceipt
        } else {
            ModuleApplyRetryEvidence::ExactValues
        },
    })
}

/// Bind a kernel-produced declaration candidate to a preflighted payload envelope.
///
/// The temporary `Vec` clones `Arc` handles only; neither declaration payload bytes nor
/// syntax trees are flattened or re-encoded. Extension state must still equal `base`;
/// extension replay happens only after this check under the contribution's precise
/// descriptor, ordinal, and entry identity binding.
pub fn verify_kernel_declaration_candidate(
    preflight: &PreflightedModuleApply,
    base: &Environment,
    candidate: &Environment,
) -> Result<(), ModuleApplyCandidateError> {
    if preflight.schema != MODULE_APPLY_SCHEMA_VERSION {
        return Err(ModuleApplyCandidateError::SupersededPreflightSchema {
            schema: preflight.schema,
        });
    }
    let transaction = preflight.transaction();
    let mut additions = Vec::with_capacity(
        transaction
            .declarations()
            .len()
            .saturating_add(transaction.extra_declarations().len()),
    );
    additions.extend(transaction.declarations().iter().cloned());
    additions.extend(transaction.extra_declarations().iter().cloned());
    candidate
        .verify_declaration_delta(base, &additions)
        .map_err(ModuleApplyCandidateError::DeclarationDelta)
}

/// Completed refusals while joining a replay candidate to the graph and its target
/// manifest. Resource and cancellation non-answers stay in [`Outcome`]'s outer arms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyPrepareError {
    BaseState(ModuleApplyStateError),
    ExistingModule {
        module: ModuleId,
    },
    ArtifactReplacementConflict {
        module: ModuleId,
        existing_artifact: Box<ArtifactEvidence>,
        incoming_artifact: Box<ArtifactEvidence>,
    },
    TargetEpoch {
        base: crate::modules::ModuleEpoch,
        target: crate::modules::ModuleEpoch,
    },
    TargetRecordCount {
        expected: usize,
        actual: usize,
    },
    TargetBaseRecordMismatch {
        module: ModuleId,
    },
    TargetContributionMismatch {
        module: ModuleId,
    },
    Replay(ModuleApplyReplayError),
    Payload(ModuleApplyCandidateError),
    Retry(ModuleApplyRetryError),
    Graph(crate::modules::ModuleGraphError),
    State(ModuleApplyStateError),
}

/// Build one complete, immutable module-application candidate without publishing it.
///
/// The target manifest must be exactly the base manifest plus this transaction's one
/// contribution. Graph preparation remains consumable and non-authoritative until it
/// is committed against the held base; an inconclusive or fault from that protocol is
/// propagated intact. Every completed refusal returns before a `ModuleApplyState` is
/// constructed, so no partial declaration, extension, graph, or index state escapes.
pub fn prepare_module_apply_candidate(
    preflight: &PreflightedModuleApply,
    base: &ModuleApplyState,
    declaration_candidate: &Environment,
) -> Outcome<Result<ModuleApplyState, ModuleApplyPrepareError>> {
    if let Err(error) = base.verify() {
        return Outcome::complete(Err(ModuleApplyPrepareError::BaseState(error)));
    }
    let transaction = preflight.transaction();
    let contribution = transaction.contribution();
    let module = contribution.module().id.clone();
    let target = transaction.manifest();
    if let Some(existing) = base.manifest().record(&module) {
        if existing.module().artifact != contribution.module().artifact {
            return Outcome::complete(Err(ModuleApplyPrepareError::ArtifactReplacementConflict {
                module,
                existing_artifact: Box::new(existing.module().artifact.clone()),
                incoming_artifact: Box::new(contribution.module().artifact.clone()),
            }));
        }
        return Outcome::complete(Err(ModuleApplyPrepareError::ExistingModule { module }));
    }
    if base.manifest().epoch() != target.epoch() {
        return Outcome::complete(Err(ModuleApplyPrepareError::TargetEpoch {
            base: base.manifest().epoch().clone(),
            target: target.epoch().clone(),
        }));
    }
    let expected_records = match base.manifest().records().len().checked_add(1) {
        Some(value) => value,
        None => {
            return Outcome::complete(Err(ModuleApplyPrepareError::TargetRecordCount {
                expected: usize::MAX,
                actual: target.records().len(),
            }));
        }
    };
    if target.records().len() != expected_records {
        return Outcome::complete(Err(ModuleApplyPrepareError::TargetRecordCount {
            expected: expected_records,
            actual: target.records().len(),
        }));
    }
    for held in base.manifest().records() {
        let held_module = &held.module().id;
        if target.record(held_module) != Some(held) {
            return Outcome::complete(Err(ModuleApplyPrepareError::TargetBaseRecordMismatch {
                module: held_module.clone(),
            }));
        }
    }
    if target.record(&module) != Some(contribution) {
        return Outcome::complete(Err(ModuleApplyPrepareError::TargetContributionMismatch {
            module,
        }));
    }

    let replayed =
        match replay_preflighted_extensions(preflight, base.environment(), declaration_candidate) {
            Ok(candidate) => candidate,
            Err(error) => return Outcome::complete(Err(ModuleApplyPrepareError::Replay(error))),
        };
    let prepared = match base
        .graph()
        .prepare_registration(contribution.module().clone(), None)
        .into_status()
    {
        Outcome::Complete(Ok(prepared)) => prepared,
        Outcome::Complete(Err(error)) => {
            return Outcome::complete(Err(ModuleApplyPrepareError::Graph(error)));
        }
        Outcome::Inconclusive(inconclusive) => return Outcome::Inconclusive(inconclusive),
        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
    };
    let graph = match prepared.commit(base.graph(), None).into_status() {
        Outcome::Complete(Ok(registration)) => registration.graph,
        Outcome::Complete(Err(error)) => {
            return Outcome::complete(Err(ModuleApplyPrepareError::Graph(error)));
        }
        Outcome::Inconclusive(inconclusive) => return Outcome::Inconclusive(inconclusive),
        Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
    };
    let payload = match AppliedModulePayload::from_preflight(preflight) {
        Ok(payload) => payload,
        Err(error) => return Outcome::complete(Err(ModuleApplyPrepareError::Payload(error))),
    };
    let mut payloads = base.applied_payloads().to_vec();
    payloads.push(payload);
    Outcome::complete(
        ModuleApplyState::from_parts_with_options_and_payloads(
            replayed,
            graph,
            Arc::clone(&transaction.manifest),
            base.options().clone(),
            payloads,
        )
        .map_err(ModuleApplyPrepareError::State),
    )
}

/// The authority grade of one applied contribution.
///
/// A contribution can be applied byte-exactly while its decoder reported a partial
/// capture or unresolved direct targets. Those successful applications are explicitly
/// `AppliedIncomplete`: consumers must ask the retained completeness tuple whether a
/// particular cache or invalidation capability was actually earned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyGrade {
    Complete {
        completeness: ProvenanceCompleteness,
    },
    AppliedIncomplete {
        completeness: ProvenanceCompleteness,
    },
}

impl ModuleApplyGrade {
    fn from_completeness(completeness: &ProvenanceCompleteness) -> Self {
        if completeness.capture() == CaptureStatus::Complete
            && completeness.missing_dependencies().is_empty()
        {
            Self::Complete {
                completeness: completeness.clone(),
            }
        } else {
            Self::AppliedIncomplete {
                completeness: completeness.clone(),
            }
        }
    }

    /// The exact canonical completeness tuple, never a lossy boolean summary.
    pub fn completeness(&self) -> &ProvenanceCompleteness {
        match self {
            Self::Complete { completeness } | Self::AppliedIncomplete { completeness } => {
                completeness
            }
        }
    }

    /// Whether this result earned one specific provenance capability.
    pub fn grants(&self, authority: ProvenanceAuthority) -> bool {
        self.completeness().grants(authority)
    }
}

/// Immutable evidence for one successful aggregate transition.
///
/// The receipt is created while the plan still holds both exact states, then checked
/// again immediately before the candidate is released. It retains the exact canonical
/// contribution record (including the resolver-bound artifact evidence) alongside the
/// provenance roots, rather than treating an index projection or a graph lineage
/// binding as a root.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleApplyReceipt {
    schema: u16,
    module: ModuleId,
    contribution: ModuleContributionRecord,
    grade: ModuleApplyGrade,
    transaction_id: ModuleApplyTransactionId,
    base_logical_root: LogicalRoot,
    result_logical_root: LogicalRoot,
    base_provenance_root: ModuleProvenanceRoot,
    result_provenance_root: ModuleProvenanceRoot,
}

impl ModuleApplyReceipt {
    pub const fn schema(&self) -> u16 {
        self.schema
    }

    pub fn module(&self) -> &ModuleId {
        &self.module
    }

    /// Canonical contribution record that was committed, including artifact evidence.
    pub fn contribution(&self) -> &ModuleContributionRecord {
        &self.contribution
    }

    /// The published completeness grade, bound to the canonical contribution record.
    pub fn grade(&self) -> &ModuleApplyGrade {
        &self.grade
    }

    pub const fn transaction_id(&self) -> ModuleApplyTransactionId {
        self.transaction_id
    }

    pub const fn base_logical_root(&self) -> LogicalRoot {
        self.base_logical_root
    }

    pub const fn result_logical_root(&self) -> LogicalRoot {
        self.result_logical_root
    }

    pub const fn base_provenance_root(&self) -> ModuleProvenanceRoot {
        self.base_provenance_root
    }

    pub const fn result_provenance_root(&self) -> ModuleProvenanceRoot {
        self.result_provenance_root
    }

    fn verify_for(
        &self,
        base: &ModuleApplyState,
        candidate: &ModuleApplyState,
    ) -> Result<(), ModuleApplyReceiptError> {
        if self.schema != MODULE_APPLY_SCHEMA_VERSION {
            return Err(ModuleApplyReceiptError::SupersededSchema {
                schema: self.schema,
            });
        }
        let actual_base = base.manifest().root();
        if self.base_provenance_root != actual_base {
            return Err(ModuleApplyReceiptError::BaseRoot {
                expected: self.base_provenance_root,
                actual: actual_base,
            });
        }
        let actual_result = candidate.manifest().root();
        if self.result_provenance_root != actual_result {
            return Err(ModuleApplyReceiptError::ResultRoot {
                expected: self.result_provenance_root,
                actual: actual_result,
            });
        }
        let actual_contribution = candidate.manifest().record(&self.module).ok_or_else(|| {
            ModuleApplyReceiptError::ModuleAbsent {
                module: self.module.clone(),
            }
        })?;
        if actual_contribution != &self.contribution {
            return Err(ModuleApplyReceiptError::Contribution {
                module: self.module.clone(),
            });
        }
        let actual_grade = ModuleApplyGrade::from_completeness(actual_contribution.completeness());
        if self.grade != actual_grade {
            return Err(ModuleApplyReceiptError::Grade {
                module: self.module.clone(),
            });
        }
        let actual_base_logical_root = base.logical_root();
        if self.base_logical_root != actual_base_logical_root {
            return Err(ModuleApplyReceiptError::BaseLogicalRoot {
                expected: self.base_logical_root,
                actual: actual_base_logical_root,
            });
        }
        let actual_result_logical_root = candidate.logical_root();
        if self.result_logical_root != actual_result_logical_root {
            return Err(ModuleApplyReceiptError::ResultLogicalRoot {
                expected: self.result_logical_root,
                actual: actual_result_logical_root,
            });
        }
        let actual_transaction = ModuleApplyTransactionId::from_state(candidate, &self.module)
            .ok_or_else(|| ModuleApplyReceiptError::ModuleAbsent {
                module: self.module.clone(),
            })?;
        if self.transaction_id != actual_transaction {
            return Err(ModuleApplyReceiptError::Transaction {
                expected: self.transaction_id,
                actual: actual_transaction,
            });
        }
        Ok(())
    }

    /// Bind this privately issued publication receipt to the exact retry target.
    ///
    /// The receipt adds evidence that this transaction once completed its original
    /// publication. It does not replace the classifier's exact current-manifest and
    /// payload checks, nor does it claim a process-history edge to the current state.
    fn verify_retry_for(
        &self,
        preflight: &PreflightedModuleApply,
    ) -> Result<(), ModuleApplyRetryReceiptError> {
        if self.schema != MODULE_APPLY_SCHEMA_VERSION {
            return Err(ModuleApplyRetryReceiptError::SupersededSchema {
                schema: self.schema,
            });
        }
        let expected_module = &preflight.transaction().contribution().module().id;
        if &self.module != expected_module {
            return Err(ModuleApplyRetryReceiptError::Module {
                expected: expected_module.clone(),
                actual: self.module.clone(),
            });
        }
        if self.contribution != *preflight.transaction().contribution() {
            return Err(ModuleApplyRetryReceiptError::Contribution {
                module: self.module.clone(),
            });
        }
        let expected_grade = ModuleApplyGrade::from_completeness(
            preflight.transaction().contribution().completeness(),
        );
        if self.grade != expected_grade {
            return Err(ModuleApplyRetryReceiptError::Grade {
                module: self.module.clone(),
            });
        }
        let expected_transaction = preflight.transaction_id();
        if self.transaction_id != expected_transaction {
            return Err(ModuleApplyRetryReceiptError::Transaction {
                expected: expected_transaction,
                actual: self.transaction_id,
            });
        }
        let expected_result = preflight.manifest_root();
        if self.result_provenance_root != expected_result {
            return Err(ModuleApplyRetryReceiptError::ResultRoot {
                expected: expected_result,
                actual: self.result_provenance_root,
            });
        }
        Ok(())
    }
}

/// A state released by a one-shot aggregate commit and the receipt that binds it.
#[derive(Debug, Clone, PartialEq)]
pub struct CommittedModuleApply {
    state: ModuleApplyState,
    receipt: Box<ModuleApplyReceipt>,
}

impl CommittedModuleApply {
    pub fn state(&self) -> &ModuleApplyState {
        &self.state
    }

    pub fn receipt(&self) -> &ModuleApplyReceipt {
        &self.receipt
    }

    pub fn into_state(self) -> ModuleApplyState {
        self.state
    }
}

/// A retry that observed the requested module in an already-published immutable state.
///
/// This is deliberately not a receipt for a second publication: no declaration,
/// extension, graph, manifest, or index is replayed or replaced.
#[derive(Debug, Clone, PartialEq)]
pub struct AlreadyAppliedModuleApply {
    state: ModuleApplyState,
    module: ModuleId,
    transaction_id: ModuleApplyTransactionId,
    result_provenance_root: ModuleProvenanceRoot,
    current_provenance_root: ModuleProvenanceRoot,
    relation: ModuleApplyRetryRelation,
    evidence: ModuleApplyRetryEvidence,
}

impl AlreadyAppliedModuleApply {
    pub fn state(&self) -> &ModuleApplyState {
        &self.state
    }

    pub fn module(&self) -> &ModuleId {
        &self.module
    }

    pub const fn transaction_id(&self) -> ModuleApplyTransactionId {
        self.transaction_id
    }

    pub const fn result_provenance_root(&self) -> ModuleProvenanceRoot {
        self.result_provenance_root
    }

    pub const fn current_provenance_root(&self) -> ModuleProvenanceRoot {
        self.current_provenance_root
    }

    pub const fn relation(&self) -> ModuleApplyRetryRelation {
        self.relation
    }

    pub const fn evidence(&self) -> ModuleApplyRetryEvidence {
        self.evidence
    }
}

/// The terminal result of consuming an aggregate apply plan.
#[derive(Debug, Clone, PartialEq)]
pub enum ModuleApplyCommitResult {
    Published(CommittedModuleApply),
    AlreadyApplied(AlreadyAppliedModuleApply),
}

/// An already-applied observation bound to the exact immutable state seen at prepare.
#[derive(Debug, Clone)]
pub struct ModuleApplyRetryPlan {
    preflight: PreflightedModuleApply,
    observed_state: ModuleApplyState,
    receipt: Option<Box<ModuleApplyReceipt>>,
}

impl ModuleApplyRetryPlan {
    pub const fn is_cacheable(&self) -> bool {
        false
    }

    /// Retry observations are one-shot and cannot move across immutable states.
    pub fn is_valid_for(&self, current: &ModuleApplyState) -> bool {
        self.observed_state == *current
    }

    fn commit(
        self,
        current: &ModuleApplyState,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<AlreadyAppliedModuleApply, ModuleApplyCommitError>> {
        if !self.is_valid_for(current) {
            return Outcome::complete(Err(ModuleApplyCommitError::StaleBase));
        }
        match classify_module_apply_retry(&self.preflight, current, self.receipt.as_deref()) {
            Ok(ModuleApplyRetryDisposition::AlreadyApplied {
                module,
                transaction_id,
                result_provenance_root,
                current_provenance_root,
                relation,
                evidence,
            }) => {
                if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                    return cancelled_before_module_publication();
                }
                Outcome::complete(Ok(AlreadyAppliedModuleApply {
                    state: current.clone(),
                    module,
                    transaction_id,
                    result_provenance_root,
                    current_provenance_root,
                    relation,
                    evidence,
                }))
            }
            Ok(ModuleApplyRetryDisposition::NotCurrentResult { .. }) => {
                Outcome::complete(Err(ModuleApplyCommitError::StaleBase))
            }
            Err(error) => Outcome::complete(Err(ModuleApplyCommitError::Retry(error))),
        }
    }
}

/// A prepared publication or already-applied observation awaiting one final base check.
#[derive(Debug, Clone)]
pub enum ModuleApplyPlan {
    Prepared(Box<PreparedModuleApply>),
    Retry(Box<ModuleApplyRetryPlan>),
}

impl ModuleApplyPlan {
    /// Neither an unpublished candidate nor a retry observation is a cache entry.
    pub const fn is_cacheable(&self) -> bool {
        false
    }

    /// Consume a plan once. Retries re-check the held state and return an
    /// observation; only the prepared arm can publish a new state. Cancellation is
    /// sampled after that revalidation, immediately before either success is released.
    pub fn commit(
        self,
        base: &ModuleApplyState,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<ModuleApplyCommitResult, ModuleApplyCommitError>> {
        match self {
            Self::Prepared(plan) => plan
                .commit(base, cancellation)
                .map_complete(|result| result.map(ModuleApplyCommitResult::Published)),
            Self::Retry(plan) => plan
                .commit(base, cancellation)
                .map_complete(|result| result.map(ModuleApplyCommitResult::AlreadyApplied)),
        }
    }
}

/// A one-shot, non-authoritative aggregate application prepared against one immutable
/// state. Holding a candidate is not publication; only [`Self::commit`] releases it
/// after revalidating every base component.
#[derive(Debug, Clone)]
pub struct PreparedModuleApply {
    schema: u16,
    base_environment: Environment,
    base_graph: ModuleGraph,
    base_manifest: Arc<ModuleProvenanceManifest>,
    candidate: ModuleApplyState,
    receipt: Box<ModuleApplyReceipt>,
}

impl PreparedModuleApply {
    /// Prepared candidates are never cache entries or authoritative state.
    pub const fn is_cacheable(&self) -> bool {
        false
    }

    /// Whether this exact aggregate base remains current for the one-shot commit.
    ///
    /// The manifest comparison is exact-value equality rather than root equality, so a
    /// hypothetical equal-digest/different-manifest pair cannot consume this plan.
    pub fn is_valid_for(&self, base: &ModuleApplyState) -> bool {
        self.schema == MODULE_APPLY_SCHEMA_VERSION
            && self.base_environment == *base.environment()
            && self.base_graph == *base.graph()
            && self.base_manifest.as_ref() == base.manifest()
    }

    /// Revalidate the base and release the one prepared aggregate candidate exactly once.
    ///
    /// The state values are immutable, so every refusal leaves `base` unchanged. A caller
    /// cannot retry the same `PreparedModuleApply` after this method consumes it. A final
    /// cancellation reports a typed non-answer and releases no authoritative state.
    pub fn commit(
        self,
        base: &ModuleApplyState,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<CommittedModuleApply, ModuleApplyCommitError>> {
        if self.schema != MODULE_APPLY_SCHEMA_VERSION || !self.is_valid_for(base) {
            return Outcome::complete(Err(ModuleApplyCommitError::StaleBase));
        }
        if let Err(error) = base.verify() {
            return Outcome::complete(Err(ModuleApplyCommitError::BaseState(error)));
        }
        if let Err(error) = self.candidate.verify() {
            return Outcome::complete(Err(ModuleApplyCommitError::CandidateState(error)));
        }
        if let Err(error) = self.receipt.verify_for(base, &self.candidate) {
            return Outcome::complete(Err(ModuleApplyCommitError::Receipt(error)));
        }
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return cancelled_before_module_publication();
        }
        Outcome::complete(Ok(CommittedModuleApply {
            state: self.candidate,
            receipt: self.receipt,
        }))
    }
}

/// Completed commit refusals. A stale plan names a changed source, not a rejected module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyCommitError {
    StaleBase,
    BaseState(ModuleApplyStateError),
    CandidateState(ModuleApplyStateError),
    Receipt(ModuleApplyReceiptError),
    Retry(ModuleApplyRetryError),
}

/// A receipt cannot be substituted for the states it reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyReceiptError {
    SupersededSchema {
        schema: u16,
    },
    BaseRoot {
        expected: ModuleProvenanceRoot,
        actual: ModuleProvenanceRoot,
    },
    BaseLogicalRoot {
        expected: LogicalRoot,
        actual: LogicalRoot,
    },
    ResultRoot {
        expected: ModuleProvenanceRoot,
        actual: ModuleProvenanceRoot,
    },
    ResultLogicalRoot {
        expected: LogicalRoot,
        actual: LogicalRoot,
    },
    Contribution {
        module: ModuleId,
    },
    Grade {
        module: ModuleId,
    },
    Transaction {
        expected: ModuleApplyTransactionId,
        actual: ModuleApplyTransactionId,
    },
    ModuleAbsent {
        module: ModuleId,
    },
}

/// Prepare one complete aggregate candidate for later one-shot commit.
pub fn prepare_module_apply(
    preflight: &PreflightedModuleApply,
    base: &ModuleApplyState,
    declaration_candidate: &Environment,
) -> Outcome<Result<ModuleApplyPlan, ModuleApplyPrepareError>> {
    prepare_module_apply_inner(preflight, base, declaration_candidate, None)
}

/// Prepare an application while retaining an original publication receipt as
/// additional retry evidence.
///
/// The receipt is validated even when `base` is not yet the requested result. A
/// matching receipt can therefore accompany a legitimate apply on another branch,
/// but a substituted or stale receipt can never be silently ignored.
pub fn prepare_module_apply_with_receipt(
    preflight: &PreflightedModuleApply,
    receipt: &ModuleApplyReceipt,
    base: &ModuleApplyState,
    declaration_candidate: &Environment,
) -> Outcome<Result<ModuleApplyPlan, ModuleApplyPrepareError>> {
    prepare_module_apply_inner(
        preflight,
        base,
        declaration_candidate,
        Some(receipt.clone()),
    )
}

fn prepare_module_apply_inner(
    preflight: &PreflightedModuleApply,
    base: &ModuleApplyState,
    declaration_candidate: &Environment,
    receipt: Option<ModuleApplyReceipt>,
) -> Outcome<Result<ModuleApplyPlan, ModuleApplyPrepareError>> {
    match classify_module_apply_retry(preflight, base, receipt.as_ref()) {
        Ok(ModuleApplyRetryDisposition::AlreadyApplied { .. }) => {
            return Outcome::complete(Ok(ModuleApplyPlan::Retry(Box::new(ModuleApplyRetryPlan {
                preflight: preflight.clone(),
                observed_state: base.clone(),
                receipt: receipt.map(Box::new),
            }))));
        }
        Ok(ModuleApplyRetryDisposition::NotCurrentResult { .. }) => {}
        Err(error) => return Outcome::complete(Err(ModuleApplyPrepareError::Retry(error))),
    }
    match prepare_module_apply_candidate(preflight, base, declaration_candidate) {
        Outcome::Complete(Ok(candidate)) => Outcome::complete(Ok(ModuleApplyPlan::Prepared(
            Box::new(PreparedModuleApply {
                schema: MODULE_APPLY_SCHEMA_VERSION,
                base_environment: base.environment().clone(),
                base_graph: base.graph().clone(),
                base_manifest: Arc::clone(&base.manifest),
                receipt: Box::new(ModuleApplyReceipt {
                    schema: preflight.schema(),
                    module: preflight.transaction().contribution().module().id.clone(),
                    contribution: preflight.transaction().contribution().clone(),
                    grade: ModuleApplyGrade::from_completeness(
                        preflight.transaction().contribution().completeness(),
                    ),
                    transaction_id: preflight.transaction_id(),
                    base_logical_root: base.logical_root(),
                    result_logical_root: candidate.logical_root(),
                    base_provenance_root: base.manifest().root(),
                    result_provenance_root: candidate.manifest().root(),
                }),
                candidate,
            }),
        ))),
        Outcome::Complete(Err(error)) => Outcome::complete(Err(error)),
        Outcome::Inconclusive(inconclusive) => Outcome::Inconclusive(inconclusive),
        Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
    }
}

/// Refusals while replaying a preflighted extension contribution onto a verified
/// declaration candidate. Every arm is raised before a resulting environment is
/// returned, so the caller cannot observe a successful prefix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleApplyReplayError {
    Candidate(ModuleApplyCandidateError),
    UnknownExtension {
        name: Name,
    },
    DescriptorMismatch {
        name: Name,
    },
    RangeStart {
        name: Name,
        expected: u64,
        actual: u64,
    },
    BaseHistory {
        name: Name,
        expected: Digest,
        actual: Digest,
    },
    PayloadStreamExhausted {
        index: usize,
    },
    PayloadDescriptor {
        index: usize,
    },
    PayloadIdentity {
        index: usize,
    },
    PayloadStreamTrailing {
        consumed: usize,
        available: usize,
    },
    Environment(crate::environment::EnvError),
}

/// Replay extension bytes privately after the kernel candidate has been bound.
///
/// Each contribution rechecks its root-scoped placement witness against the exact
/// candidate history immediately before appending. The returned environment is an
/// immutable candidate only; it becomes observable as module-application state only
/// after the graph, manifest, and indexes join in a later commit phase.
pub fn replay_preflighted_extensions(
    preflight: &PreflightedModuleApply,
    base: &Environment,
    candidate: &Environment,
) -> Result<Environment, ModuleApplyReplayError> {
    verify_kernel_declaration_candidate(preflight, base, candidate)
        .map_err(ModuleApplyReplayError::Candidate)?;

    let transaction = preflight.transaction();
    let record = transaction.contribution();
    let mut next = candidate.clone();
    let mut payload_index = 0usize;
    for contribution in record.extension_contributions() {
        let descriptor = contribution.descriptor();
        let state = next.extension(&descriptor.name).ok_or_else(|| {
            ModuleApplyReplayError::UnknownExtension {
                name: descriptor.name.clone(),
            }
        })?;
        if state.descriptor != *descriptor {
            return Err(ModuleApplyReplayError::DescriptorMismatch {
                name: descriptor.name.clone(),
            });
        }
        let actual_start =
            u64::try_from(state.len()).map_err(|_| ModuleApplyReplayError::RangeStart {
                name: descriptor.name.clone(),
                expected: contribution.start(),
                actual: u64::MAX,
            })?;
        if actual_start != contribution.start() {
            return Err(ModuleApplyReplayError::RangeStart {
                name: descriptor.name.clone(),
                expected: contribution.start(),
                actual: actual_start,
            });
        }
        let actual_history = state.content_digest();
        if actual_history != contribution.base_history_digest() {
            return Err(ModuleApplyReplayError::BaseHistory {
                name: descriptor.name.clone(),
                expected: contribution.base_history_digest(),
                actual: actual_history,
            });
        }
        for expected_identity in contribution.entries() {
            let payload = transaction.extension_payloads().get(payload_index).ok_or(
                ModuleApplyReplayError::PayloadStreamExhausted {
                    index: payload_index,
                },
            )?;
            if payload.descriptor() != descriptor {
                return Err(ModuleApplyReplayError::PayloadDescriptor {
                    index: payload_index,
                });
            }
            let identity = ExtensionEntryId::derive(
                preflight.transaction().manifest().epoch(),
                descriptor,
                payload.payload(),
            );
            if identity != *expected_identity {
                return Err(ModuleApplyReplayError::PayloadIdentity {
                    index: payload_index,
                });
            }
            next = next
                .push_extension_entry(&descriptor.name, payload.payload_arc())
                .map_err(ModuleApplyReplayError::Environment)?;
            payload_index = payload_index.saturating_add(1);
        }
    }
    if payload_index != transaction.extension_payloads().len() {
        return Err(ModuleApplyReplayError::PayloadStreamTrailing {
            consumed: payload_index,
            available: transaction.extension_payloads().len(),
        });
    }
    Ok(next)
}

/// Bind every actual payload to the validated contribution record.
///
/// This operation is read-only.  In particular, it does not register a module, add a
/// declaration, append an extension entry, derive a second provenance store, or hand
/// a provisional identity to a cache.  The subsequent prepare/commit slice consumes
/// this exact checked envelope.
pub fn preflight_module_apply(
    transaction: ModuleApplyTransaction,
    limits: &ModuleApplyLimits,
) -> Result<PreflightedModuleApply, ModuleApplyPreflightError> {
    let usage = measure_module_apply_usage(&transaction);
    enforce_module_apply_limits(limits, &usage)?;
    transaction
        .manifest
        .verify_self_consistency()
        .map_err(ModuleApplyPreflightError::ManifestInconsistent)?;

    let module = transaction.contribution.module().id.clone();
    match transaction.manifest.record(&module) {
        None => return Err(ModuleApplyPreflightError::ContributionAbsent { module }),
        Some(record) if record != &transaction.contribution => {
            return Err(ModuleApplyPreflightError::ContributionMismatch { module });
        }
        Some(_) => {}
    }

    verify_declaration_payloads(
        DeclarationClass::Declaration,
        transaction.contribution.declarations(),
        &transaction.declarations,
    )?;
    verify_declaration_payloads(
        DeclarationClass::ExtraDeclaration,
        transaction.contribution.extra_declarations(),
        &transaction.extra_declarations,
    )?;

    let expected_payloads: usize = transaction
        .contribution
        .extension_contributions()
        .iter()
        .map(|contribution| contribution.entries().len())
        .sum();
    if transaction.extension_payloads.len() != expected_payloads {
        return Err(ModuleApplyPreflightError::ExtensionPayloadCount {
            expected: expected_payloads,
            actual: transaction.extension_payloads.len(),
        });
    }
    let expected_occurrences = transaction
        .contribution
        .extension_contributions()
        .iter()
        .enumerate()
        .flat_map(|(contribution_index, contribution)| {
            contribution
                .entries()
                .iter()
                .enumerate()
                .map(move |(index, entry)| (contribution_index, index, contribution, *entry))
        });
    for (
        payload_index,
        (payload, (expected_contribution_index, expected_index, expected_contribution, expected)),
    ) in transaction
        .extension_payloads
        .iter()
        .zip(expected_occurrences)
        .enumerate()
    {
        let expected_ordinal = u64::try_from(expected_index).map_err(|_| {
            ModuleApplyPreflightError::ExtensionOccurrence {
                payload_index,
                expected_contribution: expected_contribution_index,
                expected_ordinal: u64::MAX,
                actual_contribution: payload.contribution_index,
                actual_ordinal: payload.source_ordinal,
            }
        })?;
        if payload.contribution_index != expected_contribution_index
            || payload.source_ordinal != expected_ordinal
        {
            return Err(ModuleApplyPreflightError::ExtensionOccurrence {
                payload_index,
                expected_contribution: expected_contribution_index,
                expected_ordinal,
                actual_contribution: payload.contribution_index,
                actual_ordinal: payload.source_ordinal,
            });
        }
        if payload.descriptor != *expected_contribution.descriptor() {
            return Err(ModuleApplyPreflightError::ExtensionDescriptor {
                payload_index,
                expected: expected_contribution.descriptor().clone(),
                actual: payload.descriptor.clone(),
            });
        }
        let actual = ExtensionEntryId::derive(
            transaction.manifest.epoch(),
            &payload.descriptor,
            &payload.payload,
        );
        if actual != expected {
            return Err(ModuleApplyPreflightError::ExtensionIdentity {
                payload_index,
                expected,
                actual,
            });
        }
    }

    let declaration_identities: Arc<[Digest]> = transaction
        .declarations
        .iter()
        .chain(transaction.extra_declarations.iter())
        .map(|info| crate::environment::Environment::decl_content_digest(info))
        .collect::<Vec<_>>()
        .into();
    let transaction_id =
        ModuleApplyTransactionId::derive(transaction.manifest.root(), &declaration_identities);
    Ok(PreflightedModuleApply {
        schema: MODULE_APPLY_SCHEMA_VERSION,
        manifest_root: transaction.manifest.root(),
        transaction,
        declaration_identities,
        transaction_id,
        usage,
    })
}

fn verify_declaration_payloads(
    class: DeclarationClass,
    expected: &[Name],
    actual: &[Arc<ConstantInfo>],
) -> Result<(), ModuleApplyPreflightError> {
    if actual.len() != expected.len() {
        return Err(ModuleApplyPreflightError::DeclarationCount {
            class,
            expected: expected.len(),
            actual: actual.len(),
        });
    }
    for (index, (expected, actual)) in expected.iter().zip(actual).enumerate() {
        if actual.name() != expected {
            return Err(ModuleApplyPreflightError::DeclarationName {
                class,
                index,
                expected: expected.clone(),
                actual: actual.name().clone(),
            });
        }
    }
    Ok(())
}

/// Measure one envelope's resource facts without allocating or copying payload bytes.
fn measure_module_apply_usage(transaction: &ModuleApplyTransaction) -> ModuleApplyUsage {
    let mut extension_payload_bytes: u128 = 0;
    for payload in transaction.extension_payloads() {
        extension_payload_bytes =
            extension_payload_bytes.saturating_add(payload.payload().len() as u128);
    }
    ModuleApplyUsage {
        declaration_payloads: transaction.declarations().len(),
        extra_declaration_payloads: transaction.extra_declarations().len(),
        extension_payloads: transaction.extension_payloads().len(),
        extension_payload_bytes,
    }
}

/// Refuse an envelope exceeding any caller-supplied budget before any binding
/// work runs: no manifest verification, no payload comparison, no graph work.
fn enforce_module_apply_limits(
    limits: &ModuleApplyLimits,
    usage: &ModuleApplyUsage,
) -> Result<(), ModuleApplyPreflightError> {
    let checks = [
        (
            ModuleApplyResource::DeclarationPayloads,
            limits.max_declaration_payloads as u128,
            usage.declaration_payloads() as u128,
        ),
        (
            ModuleApplyResource::ExtraDeclarationPayloads,
            limits.max_extra_declaration_payloads as u128,
            usage.extra_declaration_payloads() as u128,
        ),
        (
            ModuleApplyResource::ExtensionPayloads,
            limits.max_extension_payloads as u128,
            usage.extension_payloads() as u128,
        ),
        (
            ModuleApplyResource::ExtensionPayloadBytes,
            limits.max_extension_payload_bytes,
            usage.extension_payload_bytes(),
        ),
    ];
    for (resource, limit, actual) in checks {
        if actual > limit {
            return Err(ModuleApplyPreflightError::LimitExceeded {
                resource,
                limit,
                actual,
            });
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{AxiomVal, ConstantVal};
    use crate::extensions::{CheckpointSemantics, MergeSemantics, PayloadProvenance};
    use crate::modules::{
        ArtifactEvidence, ArtifactGrade, ArtifactProducer, DirectImport, ModuleEpoch,
        ModuleGraphLimits, ModuleId, ModuleRecord,
    };
    use crate::provenance::{
        CaptureStatus, ExtensionContribution, ModuleProvenanceLimits, PayloadTransparency,
        ProvenanceCompleteness,
    };
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::options::DataValue;
    use fln_core::outcome::InconclusiveCause;
    use std::sync::atomic::AtomicBool;

    fn completed<T: std::fmt::Debug, E: std::fmt::Debug>(
        outcome: Outcome<Result<T, E>>,
        context: &str,
    ) -> Result<T, E> {
        match outcome {
            Outcome::Complete(result) => result,
            other => panic!("{context}: expected a completed result, got {other:?}"),
        }
    }

    fn name(value: &str) -> Name {
        Name::str(Name::anonymous(), value)
    }

    fn epoch() -> ModuleEpoch {
        ModuleEpoch::new("v4.32.0", "0123456789abcdef0123456789abcdef01234567")
    }

    fn descriptor() -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: name("fixture.ext"),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        }
    }

    fn opaque_descriptor() -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: name("fixture.opaque-ext"),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Opaque,
        }
    }

    fn axiom(value: &str) -> Arc<ConstantInfo> {
        Arc::new(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: name(value),
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        }))
    }

    fn record(contributions: Vec<ExtensionContribution>) -> ModuleContributionRecord {
        record_with_completeness(
            contributions,
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        )
    }

    fn record_with_completeness(
        contributions: Vec<ExtensionContribution>,
        completeness: ProvenanceCompleteness,
    ) -> ModuleContributionRecord {
        record_with_imports(vec![], contributions, completeness)
    }

    fn record_with_imports(
        imports: Vec<DirectImport>,
        contributions: Vec<ExtensionContribution>,
        completeness: ProvenanceCompleteness,
    ) -> ModuleContributionRecord {
        let epoch = epoch();
        ModuleContributionRecord::new(
            ModuleRecord::new(
                ModuleId::new(name("fixture.module")),
                true,
                imports,
                ArtifactEvidence {
                    epoch,
                    content_digest: Digest([7; 32]),
                    producer: ArtifactProducer::Reference,
                    grade: ArtifactGrade::Verified,
                },
            ),
            vec![name("fixture.decl")],
            vec![name("fixture.extra")],
            contributions,
            completeness,
        )
    }

    fn transaction(
        contribution: ModuleContributionRecord,
        extension_payloads: Vec<ExtensionPayload>,
    ) -> ModuleApplyTransaction {
        let manifest = ModuleProvenanceManifest::new(
            epoch(),
            vec![contribution.clone()],
            ModuleProvenanceLimits::default(),
        )
        .expect("fixture manifest is valid");
        ModuleApplyTransaction::new(
            Arc::new(manifest),
            contribution,
            vec![axiom("fixture.decl")],
            vec![axiom("fixture.extra")],
            extension_payloads,
        )
    }

    fn named_record(
        module: &str,
        declaration: &str,
        extra_declaration: &str,
        artifact_seed: u8,
    ) -> ModuleContributionRecord {
        ModuleContributionRecord::new(
            ModuleRecord::new(
                ModuleId::new(name(module)),
                true,
                vec![],
                ArtifactEvidence {
                    epoch: epoch(),
                    content_digest: Digest([artifact_seed; 32]),
                    producer: ArtifactProducer::Reference,
                    grade: ArtifactGrade::Verified,
                },
            ),
            vec![name(declaration)],
            vec![name(extra_declaration)],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        )
    }

    fn transaction_with_target(
        target_records: Vec<ModuleContributionRecord>,
        contribution: ModuleContributionRecord,
        declaration: &str,
        extra_declaration: &str,
    ) -> ModuleApplyTransaction {
        let manifest = ModuleProvenanceManifest::new(
            epoch(),
            target_records,
            ModuleProvenanceLimits::default(),
        )
        .expect("fixture target manifest is valid");
        ModuleApplyTransaction::new(
            Arc::new(manifest),
            contribution,
            vec![axiom(declaration)],
            vec![axiom(extra_declaration)],
            vec![],
        )
    }

    fn applied_payload(
        contribution: ModuleContributionRecord,
        extension_payloads: Vec<ExtensionPayload>,
    ) -> AppliedModulePayload {
        let checked = preflight_module_apply(
            transaction(contribution, extension_payloads),
            &ModuleApplyLimits::default(),
        )
        .expect("fixture payload binding is valid");
        AppliedModulePayload::from_preflight(&checked)
            .expect("current preflight schema retains fixture payloads")
    }

    fn graph_with(record: &ModuleContributionRecord) -> ModuleGraph {
        let graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("fixture graph construction admits");
        graph
            .register(record.module().clone())
            .into_admitted_value()
            .expect("fixture graph registration admits")
            .graph
    }

    fn environment_with_extension(payload: Option<&[u8]>) -> Environment {
        let environment = Environment::new()
            .add_decl((*axiom("fixture.decl")).clone())
            .expect("fixture declaration is unique")
            .add_decl((*axiom("fixture.extra")).clone())
            .expect("fixture extra declaration is unique")
            .register_extension(descriptor())
            .expect("fixture extension is unique");
        match payload {
            Some(payload) => environment
                .push_extension_entry(&name("fixture.ext"), payload)
                .expect("fixture extension is registered"),
            None => environment,
        }
    }

    fn empty_apply_state() -> ModuleApplyState {
        let manifest = Arc::new(
            ModuleProvenanceManifest::new(epoch(), vec![], ModuleProvenanceLimits::default())
                .expect("empty manifest is valid"),
        );
        let graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("empty graph construction admits");
        ModuleApplyState::from_parts(Environment::new(), graph, manifest)
            .expect("empty aggregate state is coherent")
    }

    fn declaration_candidate_for(
        preflight: &PreflightedModuleApply,
        base: &ModuleApplyState,
    ) -> Environment {
        base.environment()
            .add_decl((*preflight.transaction().declarations()[0]).clone())
            .expect("fixture declaration is unique")
            .add_decl((*preflight.transaction().extra_declarations()[0]).clone())
            .expect("fixture extra declaration is unique")
    }

    fn publish_fixture(
        preflight: &PreflightedModuleApply,
        base: &ModuleApplyState,
    ) -> CommittedModuleApply {
        let candidate = declaration_candidate_for(preflight, base);
        let plan = match prepare_module_apply(preflight, base, &candidate) {
            Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => plan,
            other => panic!("expected a prepared fixture application, got {other:?}"),
        };
        completed(
            plan.commit(base, None),
            "uncancelled fixture publication must complete",
        )
        .expect("fixture base remains current")
    }

    fn descendant_retry_fixture() -> (
        PreflightedModuleApply,
        CommittedModuleApply,
        ModuleApplyState,
    ) {
        let base = empty_apply_state();
        let left = named_record(
            "fixture.retry-left",
            "fixture.retry-left.decl",
            "fixture.retry-left.extra",
            21,
        );
        let right = named_record(
            "fixture.retry-right",
            "fixture.retry-right.decl",
            "fixture.retry-right.extra",
            22,
        );
        let left_preflight = preflight_module_apply(
            transaction_with_target(
                vec![left.clone()],
                left.clone(),
                "fixture.retry-left.decl",
                "fixture.retry-left.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("left retry fixture preflights");
        let left_publication = publish_fixture(&left_preflight, &base);
        let right_preflight = preflight_module_apply(
            transaction_with_target(
                vec![left, right.clone()],
                right,
                "fixture.retry-right.decl",
                "fixture.retry-right.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("right descendant fixture preflights");
        let descendant = publish_fixture(&right_preflight, left_publication.state()).into_state();
        (left_preflight, left_publication, descendant)
    }

    #[test]
    fn preflight_binds_arc_payloads_without_publishing_or_copying() {
        let descriptor = descriptor();
        let payload: Arc<[u8]> = Arc::from(&b"opaque bytes"[..]);
        let entry = ExtensionEntryId::derive(&epoch(), &descriptor, &payload);
        let contribution = record(vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            Digest([0; 32]),
            vec![entry],
        )]);
        let transaction = transaction(
            contribution,
            vec![ExtensionPayload::new(
                0,
                descriptor.clone(),
                0,
                Arc::clone(&payload),
            )],
        );
        let declaration = Arc::clone(&transaction.declarations()[0]);
        let checked = preflight_module_apply(transaction, &ModuleApplyLimits::default())
            .expect("exact payload binding");
        let applied = AppliedModulePayload::from_preflight(&checked)
            .expect("current preflight schema retains payloads");

        assert!(!checked.is_cacheable());
        assert_eq!(checked.schema(), MODULE_APPLY_SCHEMA_VERSION);
        assert_eq!(checked.declaration_identities().len(), 2);
        assert_eq!(
            checked.transaction_id(),
            ModuleApplyTransactionId::derive(
                checked.manifest_root(),
                checked.declaration_identities(),
            )
        );
        assert!(Arc::ptr_eq(
            &declaration,
            &checked.transaction().declarations()[0]
        ));
        assert!(
            checked.transaction().extension_payloads()[0]
                .shares_payload_with(&ExtensionPayload::new(0, descriptor.clone(), 0, payload))
        );
        assert!(applied.shares_storage_with_preflight(&checked));
        assert!(Arc::ptr_eq(&declaration, &applied.declarations()[0]));
        assert_eq!(applied.contribution(), checked.transaction().contribution());
    }

    #[test]
    fn declaration_order_is_a_typed_payload_binding_refusal() {
        let contribution = record(vec![]);
        let manifest = ModuleProvenanceManifest::new(
            epoch(),
            vec![contribution.clone()],
            ModuleProvenanceLimits::default(),
        )
        .expect("fixture manifest is valid");
        let transaction = ModuleApplyTransaction::new(
            Arc::new(manifest),
            contribution,
            vec![axiom("fixture.extra")],
            vec![axiom("fixture.decl")],
            vec![],
        );

        assert!(matches!(
            preflight_module_apply(transaction, &ModuleApplyLimits::default()),
            Err(ModuleApplyPreflightError::DeclarationName {
                class: DeclarationClass::Declaration,
                index: 0,
                ..
            })
        ));
    }

    #[test]
    fn extension_bytes_and_occurrence_order_are_both_bound() {
        let descriptor = descriptor();
        let first = ExtensionEntryId::derive(&epoch(), &descriptor, b"first");
        let second = ExtensionEntryId::derive(&epoch(), &descriptor, b"second");
        let contribution = record(vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            Digest([0; 32]),
            vec![first, second],
        )]);
        let wrong_bytes = transaction(
            contribution.clone(),
            vec![
                ExtensionPayload::new(0, descriptor.clone(), 0, &b"changed"[..]),
                ExtensionPayload::new(0, descriptor.clone(), 1, &b"second"[..]),
            ],
        );
        assert!(matches!(
            preflight_module_apply(wrong_bytes, &ModuleApplyLimits::default()),
            Err(ModuleApplyPreflightError::ExtensionIdentity {
                payload_index: 0,
                ..
            })
        ));

        let reordered = transaction(
            contribution,
            vec![
                ExtensionPayload::new(0, descriptor.clone(), 1, &b"second"[..]),
                ExtensionPayload::new(0, descriptor, 0, &b"first"[..]),
            ],
        );
        assert!(matches!(
            preflight_module_apply(reordered, &ModuleApplyLimits::default()),
            Err(ModuleApplyPreflightError::ExtensionOccurrence {
                payload_index: 0,
                ..
            })
        ));
    }

    #[test]
    fn committed_state_derives_and_keeps_both_provenance_directions() {
        let descriptor = descriptor();
        let entry = ExtensionEntryId::derive(&epoch(), &descriptor, b"payload");
        let contribution = record(vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            Digest([0; 32]),
            vec![entry],
        )]);
        let manifest = Arc::new(
            ModuleProvenanceManifest::new(
                epoch(),
                vec![contribution.clone()],
                ModuleProvenanceLimits::default(),
            )
            .expect("fixture manifest is valid"),
        );
        let payload = applied_payload(
            contribution.clone(),
            vec![ExtensionPayload::new(
                0,
                descriptor.clone(),
                0,
                &b"payload"[..],
            )],
        );
        let wrong_extension_payload = AppliedModulePayload {
            contribution: contribution.clone(),
            declarations: Arc::clone(&payload.declarations),
            extra_declarations: Arc::clone(&payload.extra_declarations),
            extension_payloads: vec![ExtensionPayload::new(
                0,
                descriptor,
                0,
                &b"wrong payload"[..],
            )]
            .into(),
        };
        let state = ModuleApplyState::from_parts_with_payloads(
            environment_with_extension(Some(b"payload")),
            graph_with(&contribution),
            Arc::clone(&manifest),
            vec![payload],
        )
        .expect("joined state is coherent");

        assert!(matches!(
            ModuleApplyState::from_parts_with_payloads(
                environment_with_extension(Some(b"payload")),
                graph_with(&contribution),
                manifest,
                vec![wrong_extension_payload],
            ),
            Err(ModuleApplyStateError::PayloadExtensionIdentity { .. })
        ));

        state.verify().expect("stored state remains coherent");
        let owner = state
            .indexes()
            .owner_of(&name("fixture.decl"))
            .expect("forward declaration has a reverse owner");
        assert_eq!(owner.0, contribution.module().id);
        assert!(
            state
                .indexes()
                .declarations_of(&contribution.module().id)
                .expect("reverse owner has a forward declaration list")
                .contains(&name("fixture.decl"))
        );
        assert_eq!(
            state
                .indexes()
                .occurrences_of(&entry)
                .expect("extension entry has reverse occurrences")
                .len(),
            1
        );
    }

    #[test]
    fn committed_state_refuses_a_late_extension_range_without_constructing_state() {
        let descriptor = descriptor();
        let entry = ExtensionEntryId::derive(&epoch(), &descriptor, b"payload");
        let contribution = record(vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            Digest([0; 32]),
            vec![entry],
        )]);
        let manifest = Arc::new(
            ModuleProvenanceManifest::new(
                epoch(),
                vec![contribution.clone()],
                ModuleProvenanceLimits::default(),
            )
            .expect("fixture manifest is valid"),
        );
        let environment = environment_with_extension(None);
        let graph = graph_with(&contribution);

        let payload = applied_payload(
            contribution,
            vec![ExtensionPayload::new(0, descriptor, 0, &b"payload"[..])],
        );
        assert!(matches!(
            ModuleApplyState::from_parts_with_payloads(
                environment.clone(),
                graph.clone(),
                manifest,
                vec![payload],
            ),
            Err(ModuleApplyStateError::ExtensionRange { .. })
        ));
        assert_eq!(environment.len(), 2);
        assert_eq!(graph.len(), 1);
    }

    #[test]
    fn kernel_candidate_must_be_the_exact_declaration_delta_and_nothing_else() {
        let transaction = transaction(record(vec![]), vec![]);
        let checked = preflight_module_apply(transaction, &ModuleApplyLimits::default())
            .expect("payloads preflight");
        let base = Environment::new()
            .register_extension(descriptor())
            .expect("fixture extension is unique");
        let candidate = base
            .add_decl((*checked.transaction().declarations()[0]).clone())
            .expect("fixture declaration is unique")
            .add_decl((*checked.transaction().extra_declarations()[0]).clone())
            .expect("fixture extra declaration is unique");

        verify_kernel_declaration_candidate(&checked, &base, &candidate)
            .expect("kernel candidate is the exact declared delta");

        let substituted = base
            .add_decl(ConstantInfo::Axiom(AxiomVal {
                base: ConstantVal {
                    name: name("fixture.decl"),
                    level_params: vec![],
                    type_: Expr::sort(Level::zero()),
                },
                is_unsafe: true,
            }))
            .expect("fixture declaration is unique")
            .add_decl((*checked.transaction().extra_declarations()[0]).clone())
            .expect("fixture extra declaration is unique");
        assert!(matches!(
            verify_kernel_declaration_candidate(&checked, &base, &substituted),
            Err(ModuleApplyCandidateError::DeclarationDelta(
                DeclarationDeltaError::AdditionMismatch { .. }
            ))
        ));

        let extension_smuggled = candidate
            .push_extension_entry(&name("fixture.ext"), &b"unbound"[..])
            .expect("fixture extension is registered");
        assert!(matches!(
            verify_kernel_declaration_candidate(&checked, &base, &extension_smuggled),
            Err(ModuleApplyCandidateError::DeclarationDelta(
                DeclarationDeltaError::ExtensionStateChanged
            ))
        ));
    }

    #[test]
    fn extension_replay_is_private_exact_and_refuses_a_stale_base() {
        let descriptor = descriptor();
        let base = Environment::new()
            .register_extension(descriptor.clone())
            .expect("fixture extension is unique");
        let history = base
            .extension(&descriptor.name)
            .expect("fixture extension is registered")
            .content_digest();
        let entry = ExtensionEntryId::derive(&epoch(), &descriptor, b"replay");
        let contribution = record(vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            history,
            vec![entry],
        )]);
        let checked = preflight_module_apply(
            transaction(
                contribution,
                vec![ExtensionPayload::new(
                    0,
                    descriptor.clone(),
                    0,
                    &b"replay"[..],
                )],
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("payloads preflight");
        let candidate = base
            .add_decl((*checked.transaction().declarations()[0]).clone())
            .expect("fixture declaration is unique")
            .add_decl((*checked.transaction().extra_declarations()[0]).clone())
            .expect("fixture extra declaration is unique");

        let replayed = replay_preflighted_extensions(&checked, &base, &candidate)
            .expect("bound replay admits the private candidate");
        assert_eq!(
            candidate
                .extension(&descriptor.name)
                .expect("candidate extension is registered")
                .len(),
            0
        );
        assert_eq!(
            replayed
                .extension(&descriptor.name)
                .expect("replayed extension is registered")
                .entries()
                .next()
                .expect("replayed payload exists")
                .payload
                .as_ref(),
            b"replay"
        );

        let stale = preflight_module_apply(
            transaction(
                record(vec![ExtensionContribution::new(
                    descriptor.clone(),
                    0,
                    Digest([0; 32]),
                    vec![entry],
                )]),
                vec![ExtensionPayload::new(0, descriptor, 0, &b"replay"[..])],
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("stale history does not alter payload binding");
        assert!(matches!(
            replay_preflighted_extensions(&stale, &base, &candidate),
            Err(ModuleApplyReplayError::BaseHistory { .. })
        ));
        assert_eq!(
            candidate
                .extension(&name("fixture.ext"))
                .expect("candidate extension is registered")
                .len(),
            0
        );
    }

    #[test]
    fn prepare_candidate_joins_every_component_only_after_target_binding() {
        let descriptor = descriptor();
        let environment = Environment::new()
            .register_extension(descriptor.clone())
            .expect("fixture extension is unique");
        let empty_manifest = Arc::new(
            ModuleProvenanceManifest::new(epoch(), vec![], ModuleProvenanceLimits::default())
                .expect("empty manifest is valid"),
        );
        let empty_graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("empty graph construction admits");
        let mut options = KVMap::new();
        options.insert(name("fixture.option"), DataValue::OfBool(true));
        let base = ModuleApplyState::from_parts_with_options(
            environment.clone(),
            empty_graph,
            empty_manifest,
            options.clone(),
        )
        .expect("empty aggregate state is coherent");
        let history = environment
            .extension(&descriptor.name)
            .expect("fixture extension is registered")
            .content_digest();
        let entry = ExtensionEntryId::derive(&epoch(), &descriptor, b"candidate");
        let contribution = record(vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            history,
            vec![entry],
        )]);
        let checked = preflight_module_apply(
            transaction(
                contribution.clone(),
                vec![ExtensionPayload::new(0, descriptor, 0, &b"candidate"[..])],
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("payloads preflight");
        assert!(matches!(
            classify_module_apply_retry(&checked, &base, None),
            Ok(ModuleApplyRetryDisposition::NotCurrentResult { .. })
        ));
        let declaration_candidate = base
            .environment()
            .add_decl((*checked.transaction().declarations()[0]).clone())
            .expect("fixture declaration is unique")
            .add_decl((*checked.transaction().extra_declarations()[0]).clone())
            .expect("fixture extra declaration is unique");

        let prepared = match prepare_module_apply_candidate(&checked, &base, &declaration_candidate)
        {
            Outcome::Complete(Ok(prepared)) => prepared,
            other => panic!("expected a complete aggregate candidate, got {other:?}"),
        };
        prepared.verify().expect("aggregate candidate is coherent");
        assert_eq!(prepared.graph().len(), 1);
        assert_eq!(prepared.manifest().records().len(), 1);
        assert_eq!(prepared.applied_payloads().len(), 1);
        assert_eq!(prepared.options(), &options);
        assert_ne!(prepared.logical_root(), base.logical_root());
        assert!(prepared.applied_payloads()[0].shares_storage_with_preflight(&checked));
        assert_eq!(
            prepared
                .environment()
                .extension(&name("fixture.ext"))
                .expect("replayed extension is registered")
                .len(),
            1
        );
        assert_eq!(base.graph().len(), 0);
        assert_eq!(base.environment().len(), 0);
        assert!(matches!(
            prepare_module_apply_candidate(&checked, &base, &declaration_candidate),
            Outcome::Complete(Ok(_))
        ));

        let stale_plan = match prepare_module_apply(&checked, &base, &declaration_candidate) {
            Outcome::Complete(Ok(plan)) => plan,
            other => panic!("expected a complete application plan, got {other:?}"),
        };
        assert!(!stale_plan.is_cacheable());
        let stale_environment = base
            .environment()
            .register_extension(ExtensionDescriptor {
                name: name("fixture.unrelated"),
                merge: MergeSemantics::AppendOrdered,
                checkpoint: CheckpointSemantics::JournalSuffix,
                provenance: PayloadProvenance::Understood,
            })
            .expect("unrelated fixture extension is unique");
        let stale_base = ModuleApplyState::from_parts_with_options(
            stale_environment,
            base.graph().clone(),
            Arc::clone(&base.manifest),
            base.options().clone(),
        )
        .expect("unrelated extension keeps the empty state coherent");
        assert!(matches!(
            stale_plan.commit(&stale_base, None),
            Outcome::Complete(Err(ModuleApplyCommitError::StaleBase))
        ));

        let cancellable_plan = match prepare_module_apply(&checked, &base, &declaration_candidate) {
            Outcome::Complete(Ok(plan)) => plan,
            other => panic!("expected a complete application plan, got {other:?}"),
        };
        let cancellation = AtomicBool::new(true);
        let cancelled = cancellable_plan.clone().commit(&base, Some(&cancellation));
        let Outcome::Inconclusive(inconclusive) = cancelled else {
            panic!("final cancellation must be a typed non-answer, got {cancelled:?}");
        };
        assert!(matches!(
            inconclusive.cause,
            InconclusiveCause::Cancelled { ref at }
                if at.text() == ModuleApplyCheckpoint::BeforePublication.to_string()
        ));
        assert_eq!(base.graph().len(), 0, "cancelled commit published a module");
        assert_eq!(
            base.environment().len(),
            0,
            "cancelled commit published declarations"
        );
        assert_eq!(
            base.manifest().records().len(),
            0,
            "cancelled commit published provenance"
        );

        let recovered = completed(
            cancellable_plan.commit(&base, None),
            "withdrawn cancellation must permit a clean recovery",
        )
        .expect("the unchanged base remains current after cancellation");
        assert!(matches!(recovered, ModuleApplyCommitResult::Published(_)));

        let mut tampered_receipt_plan =
            match prepare_module_apply(&checked, &base, &declaration_candidate) {
                Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => plan,
                Outcome::Complete(Ok(other)) => {
                    panic!("expected a prepared application plan, got {other:?}")
                }
                other => panic!("expected a complete application plan, got {other:?}"),
            };
        tampered_receipt_plan.receipt.result_provenance_root = base.manifest().root();
        assert!(matches!(
            tampered_receipt_plan.commit(&base, None),
            Outcome::Complete(Err(ModuleApplyCommitError::Receipt(
                ModuleApplyReceiptError::ResultRoot { .. }
            )))
        ));

        let mut tampered_logical_root_plan =
            match prepare_module_apply(&checked, &base, &declaration_candidate) {
                Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => plan,
                Outcome::Complete(Ok(other)) => {
                    panic!("expected a prepared application plan, got {other:?}")
                }
                other => panic!("expected a complete application plan, got {other:?}"),
            };
        tampered_logical_root_plan.receipt.result_logical_root = base.logical_root();
        assert!(matches!(
            tampered_logical_root_plan.commit(&base, None),
            Outcome::Complete(Err(ModuleApplyCommitError::Receipt(
                ModuleApplyReceiptError::ResultLogicalRoot { .. }
            )))
        ));

        let mut tampered_contribution_plan =
            match prepare_module_apply(&checked, &base, &declaration_candidate) {
                Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => plan,
                Outcome::Complete(Ok(other)) => {
                    panic!("expected a prepared application plan, got {other:?}")
                }
                other => panic!("expected a complete application plan, got {other:?}"),
            };
        let mut forged_artifact = contribution.module().artifact.clone();
        forged_artifact.content_digest = Digest([8; 32]);
        tampered_contribution_plan.receipt.contribution = ModuleContributionRecord::new(
            ModuleRecord::new(
                contribution.module().id.clone(),
                contribution.module().is_module,
                contribution.module().direct_imports().to_vec(),
                forged_artifact,
            ),
            contribution.declarations().to_vec(),
            contribution.extra_declarations().to_vec(),
            contribution.extension_contributions().to_vec(),
            contribution.completeness().clone(),
        );
        assert!(matches!(
            tampered_contribution_plan.commit(&base, None),
            Outcome::Complete(Err(ModuleApplyCommitError::Receipt(
                ModuleApplyReceiptError::Contribution { .. }
            )))
        ));

        let mut tampered_grade_plan =
            match prepare_module_apply(&checked, &base, &declaration_candidate) {
                Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => plan,
                Outcome::Complete(Ok(other)) => {
                    panic!("expected a prepared application plan, got {other:?}")
                }
                other => panic!("expected a complete application plan, got {other:?}"),
            };
        tampered_grade_plan.receipt.grade = ModuleApplyGrade::AppliedIncomplete {
            completeness: ProvenanceCompleteness::new(
                CaptureStatus::Partial,
                PayloadTransparency::Understood,
                vec![],
            ),
        };
        assert!(matches!(
            tampered_grade_plan.commit(&base, None),
            Outcome::Complete(Err(ModuleApplyCommitError::Receipt(
                ModuleApplyReceiptError::Grade { .. }
            )))
        ));

        let mut tampered_transaction_plan =
            match prepare_module_apply(&checked, &base, &declaration_candidate) {
                Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => plan,
                Outcome::Complete(Ok(other)) => {
                    panic!("expected a prepared application plan, got {other:?}")
                }
                other => panic!("expected a complete application plan, got {other:?}"),
            };
        tampered_transaction_plan.receipt.transaction_id =
            ModuleApplyTransactionId(Digest([9; 32]));
        assert!(matches!(
            tampered_transaction_plan.commit(&base, None),
            Outcome::Complete(Err(ModuleApplyCommitError::Receipt(
                ModuleApplyReceiptError::Transaction { .. }
            )))
        ));

        let committed = match prepare_module_apply(&checked, &base, &declaration_candidate) {
            Outcome::Complete(Ok(plan)) => match plan.commit(&base, None) {
                Outcome::Complete(Ok(ModuleApplyCommitResult::Published(committed))) => committed,
                Outcome::Complete(Ok(ModuleApplyCommitResult::AlreadyApplied(other))) => {
                    panic!("first apply unexpectedly observed an existing state: {other:?}")
                }
                Outcome::Complete(Err(error)) => panic!("base remains current: {error:?}"),
                other => panic!("uncancelled commit must complete, got {other:?}"),
            },
            other => panic!("expected a complete application plan, got {other:?}"),
        };
        assert_eq!(committed.state().graph().len(), 1);
        assert_eq!(committed.receipt().module(), &contribution.module().id);
        assert_eq!(committed.receipt().contribution(), &contribution);
        assert!(matches!(
            committed.receipt().grade(),
            ModuleApplyGrade::Complete { .. }
        ));
        assert!(
            committed
                .receipt()
                .grade()
                .grants(ProvenanceAuthority::FineInvalidation)
        );
        assert_eq!(
            committed.receipt().transaction_id(),
            checked.transaction_id()
        );
        assert_eq!(
            committed.receipt().base_provenance_root(),
            base.manifest().root()
        );
        assert_eq!(
            committed.receipt().result_provenance_root(),
            committed.state().manifest().root()
        );
        assert_eq!(committed.receipt().base_logical_root(), base.logical_root());
        assert_eq!(
            committed.receipt().result_logical_root(),
            committed.state().logical_root()
        );
        assert_ne!(
            committed.receipt().base_logical_root(),
            committed.receipt().result_logical_root()
        );
        let ranges = committed
            .state()
            .applied_extension_ranges(&contribution.module().id)
            .expect("committed module has a range witness");
        assert_eq!(ranges.len(), 1);
        let range = &ranges[0];
        assert_eq!(range.provenance_root(), committed.state().manifest().root());
        assert_eq!(range.module(), &contribution.module().id);
        assert_eq!(range.artifact(), &contribution.module().artifact);
        assert_eq!(range.completeness(), contribution.completeness());
        assert_eq!(range.contribution_index(), 0);
        assert_eq!(range.descriptor().name, name("fixture.ext"));
        assert_eq!(range.start(), 0);
        assert_eq!(range.entry_ids(), &[entry]);
        assert_eq!(range.source_ordinal(0), Some(0));
        assert_eq!(range.target_position(0), Some(0));
        assert!(range.target_position(1).is_none());
        assert!(
            committed
                .state()
                .applied_extension_ranges(&ModuleId::new(name("fixture.absent")))
                .is_none()
        );
        assert!(matches!(
            classify_module_apply_retry(&checked, committed.state(), None),
            Ok(ModuleApplyRetryDisposition::AlreadyApplied {
                transaction_id,
                relation: ModuleApplyRetryRelation::ExactResult,
                evidence: ModuleApplyRetryEvidence::ExactValues,
                ..
            }) if transaction_id == checked.transaction_id()
        ));

        let exact_retry_plan = match prepare_module_apply(
            &checked,
            committed.state(),
            committed.state().environment(),
        ) {
            Outcome::Complete(Ok(ModuleApplyPlan::Retry(plan))) => plan,
            Outcome::Complete(Ok(other)) => {
                panic!("expected an exact-result retry plan, got {other:?}")
            }
            other => panic!("expected a complete retry plan, got {other:?}"),
        };
        let retry_cancellation = AtomicBool::new(true);
        let cancelled_retry = ModuleApplyPlan::Retry(exact_retry_plan.clone())
            .commit(committed.state(), Some(&retry_cancellation));
        let Outcome::Inconclusive(inconclusive) = cancelled_retry else {
            panic!("final retry cancellation must be a typed non-answer, got {cancelled_retry:?}");
        };
        assert!(matches!(
            inconclusive.cause,
            InconclusiveCause::Cancelled { ref at }
                if at.text() == ModuleApplyCheckpoint::BeforePublication.to_string()
        ));

        let exact_retry = match completed(
            ModuleApplyPlan::Retry(exact_retry_plan).commit(committed.state(), None),
            "exact retry must complete without cancellation",
        )
        .expect("exact retry revalidates the same immutable state")
        {
            ModuleApplyCommitResult::AlreadyApplied(retry) => retry,
            ModuleApplyCommitResult::Published(other) => {
                panic!("exact retry must not publish: {other:?}")
            }
        };
        assert_eq!(exact_retry.state(), committed.state());
        assert_eq!(exact_retry.module(), &contribution.module().id);
        assert_eq!(exact_retry.transaction_id(), checked.transaction_id());
        assert_eq!(
            exact_retry.current_provenance_root(),
            committed.state().manifest().root()
        );
        assert_eq!(
            exact_retry.result_provenance_root(),
            committed.state().manifest().root()
        );
        assert_eq!(
            exact_retry.relation(),
            ModuleApplyRetryRelation::ExactResult
        );
        assert_eq!(
            exact_retry.evidence(),
            ModuleApplyRetryEvidence::ExactValues
        );

        let mut replacement_module = contribution.module().clone();
        replacement_module.artifact.content_digest = Digest([8; 32]);
        let replacement = ModuleContributionRecord::new(
            replacement_module,
            contribution.declarations().to_vec(),
            contribution.extra_declarations().to_vec(),
            contribution.extension_contributions().to_vec(),
            contribution.completeness().clone(),
        );
        let replacement_preflight = preflight_module_apply(
            transaction(
                replacement,
                checked.transaction().extension_payloads().to_vec(),
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("replacement fixture binds its own canonical manifest");
        assert!(matches!(
            prepare_module_apply(
                &replacement_preflight,
                committed.state(),
                committed.state().environment(),
            ),
            Outcome::Complete(Err(ModuleApplyPrepareError::ArtifactReplacementConflict {
                existing_artifact,
                incoming_artifact,
                ..
            })) if existing_artifact.content_digest == contribution.module().artifact.content_digest
                && incoming_artifact.content_digest == Digest([8; 32])
        ));
        assert_eq!(committed.state().graph().len(), 1);

        let altered_declaration = match checked.transaction().declarations()[0].as_ref() {
            ConstantInfo::Axiom(axiom) => {
                let mut altered = axiom.clone();
                altered.is_unsafe = true;
                Arc::new(ConstantInfo::Axiom(altered))
            }
            other => panic!("fixture declaration changed kind: {other:?}"),
        };
        let altered = preflight_module_apply(
            ModuleApplyTransaction::new(
                Arc::clone(&checked.transaction().manifest),
                contribution.clone(),
                vec![altered_declaration],
                checked.transaction().extra_declarations().to_vec(),
                checked.transaction().extension_payloads().to_vec(),
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("same-name fixture mutation remains preflight-valid");
        assert!(matches!(
            classify_module_apply_retry(&altered, committed.state(), None),
            Err(ModuleApplyRetryError::PayloadConflict { .. })
        ));
        assert_eq!(base.graph().len(), 0);
    }

    #[test]
    fn later_descendant_retry_without_receipt_observes_exact_values_without_publication() {
        let (preflight, original, descendant) = descendant_retry_fixture();
        let disposition = classify_module_apply_retry(&preflight, &descendant, None)
            .expect("exact target containment is a completed retry classification");
        assert!(matches!(
            disposition,
            ModuleApplyRetryDisposition::AlreadyApplied {
                transaction_id,
                result_provenance_root,
                current_provenance_root,
                relation: ModuleApplyRetryRelation::ManifestDescendant,
                evidence: ModuleApplyRetryEvidence::ExactValues,
                ..
            } if transaction_id == preflight.transaction_id()
                && result_provenance_root == original.state().manifest().root()
                && current_provenance_root == descendant.manifest().root()
        ));

        let retry_plan =
            match prepare_module_apply(&preflight, &descendant, descendant.environment()) {
                Outcome::Complete(Ok(ModuleApplyPlan::Retry(plan))) => plan,
                other => panic!("expected a descendant retry plan, got {other:?}"),
            };
        assert!(!retry_plan.is_cacheable());
        assert!(retry_plan.is_valid_for(&descendant));
        assert!(!retry_plan.is_valid_for(original.state()));
        assert!(matches!(
            ModuleApplyPlan::Retry(retry_plan.clone()).commit(original.state(), None),
            Outcome::Complete(Err(ModuleApplyCommitError::StaleBase))
        ));

        let cancellation = AtomicBool::new(true);
        let cancelled =
            ModuleApplyPlan::Retry(retry_plan.clone()).commit(&descendant, Some(&cancellation));
        assert!(matches!(
            cancelled,
            Outcome::Inconclusive(Inconclusive {
                cause: InconclusiveCause::Cancelled { ref at },
                ..
            }) if at.text() == ModuleApplyCheckpoint::BeforePublication.to_string()
        ));

        let observed = match completed(
            ModuleApplyPlan::Retry(retry_plan).commit(&descendant, None),
            "uncancelled descendant retry must complete",
        )
        .expect("the exact observed state remains current")
        {
            ModuleApplyCommitResult::AlreadyApplied(observed) => observed,
            ModuleApplyCommitResult::Published(other) => {
                panic!("descendant retry must not publish: {other:?}")
            }
        };
        assert_eq!(observed.state(), &descendant);
        assert_eq!(
            observed.relation(),
            ModuleApplyRetryRelation::ManifestDescendant
        );
        assert_eq!(observed.evidence(), ModuleApplyRetryEvidence::ExactValues);
        assert_eq!(
            observed.result_provenance_root(),
            original.state().manifest().root()
        );
        assert_eq!(
            observed.current_provenance_root(),
            descendant.manifest().root()
        );
        descendant
            .verify()
            .expect("retry observation leaves the descendant unchanged");
    }

    #[test]
    fn exact_and_descendant_retries_revalidate_optional_publication_receipts() {
        let (preflight, original, descendant) = descendant_retry_fixture();
        let receipt = original.receipt();

        let exact_plan = match prepare_module_apply_with_receipt(
            &preflight,
            receipt,
            original.state(),
            original.state().environment(),
        ) {
            Outcome::Complete(Ok(ModuleApplyPlan::Retry(plan))) => plan,
            other => panic!("expected a receipt-bound exact retry plan, got {other:?}"),
        };
        let exact = completed(
            ModuleApplyPlan::Retry(exact_plan).commit(original.state(), None),
            "receipt-bound exact retry must complete",
        )
        .expect("the exact result remains current");
        let ModuleApplyCommitResult::AlreadyApplied(exact) = exact else {
            panic!("receipt-bound exact retry must not publish")
        };
        assert_eq!(exact.relation(), ModuleApplyRetryRelation::ExactResult);
        assert_eq!(
            exact.evidence(),
            ModuleApplyRetryEvidence::PublicationReceipt
        );

        let descendant_plan = match prepare_module_apply_with_receipt(
            &preflight,
            receipt,
            &descendant,
            descendant.environment(),
        ) {
            Outcome::Complete(Ok(ModuleApplyPlan::Retry(plan))) => plan,
            other => panic!("expected a receipt-bound descendant retry plan, got {other:?}"),
        };
        let observed = completed(
            ModuleApplyPlan::Retry(descendant_plan).commit(&descendant, None),
            "receipt-bound descendant retry must complete",
        )
        .expect("the descendant remains current");
        let ModuleApplyCommitResult::AlreadyApplied(observed) = observed else {
            panic!("receipt-bound descendant retry must not publish")
        };
        assert_eq!(
            observed.relation(),
            ModuleApplyRetryRelation::ManifestDescendant
        );
        assert_eq!(
            observed.evidence(),
            ModuleApplyRetryEvidence::PublicationReceipt
        );
        assert_eq!(observed.state(), &descendant);

        let mut substituted_receipt = receipt.clone();
        substituted_receipt.result_provenance_root = descendant.manifest().root();
        assert!(matches!(
            classify_module_apply_retry(&preflight, &descendant, Some(&substituted_receipt)),
            Err(ModuleApplyRetryError::Receipt(
                ModuleApplyRetryReceiptError::ResultRoot { .. }
            ))
        ));

        let mut superseded_receipt = receipt.clone();
        superseded_receipt.schema = MODULE_APPLY_SCHEMA_VERSION + 1;
        assert!(matches!(
            classify_module_apply_retry(&preflight, &descendant, Some(&superseded_receipt)),
            Err(ModuleApplyRetryError::Receipt(
                ModuleApplyRetryReceiptError::SupersededSchema { .. }
            ))
        ));

        let mut wrong_module_receipt = receipt.clone();
        wrong_module_receipt.module = ModuleId::new(name("fixture.other-receipt"));
        assert!(matches!(
            classify_module_apply_retry(&preflight, &descendant, Some(&wrong_module_receipt)),
            Err(ModuleApplyRetryError::Receipt(
                ModuleApplyRetryReceiptError::Module { .. }
            ))
        ));

        let mut wrong_contribution_receipt = receipt.clone();
        let held_contribution = receipt.contribution();
        let mut wrong_artifact = held_contribution.module().artifact.clone();
        wrong_artifact.content_digest = Digest([31; 32]);
        wrong_contribution_receipt.contribution = ModuleContributionRecord::new(
            ModuleRecord::new(
                held_contribution.module().id.clone(),
                held_contribution.module().is_module,
                held_contribution.module().direct_imports().to_vec(),
                wrong_artifact,
            ),
            held_contribution.declarations().to_vec(),
            held_contribution.extra_declarations().to_vec(),
            held_contribution.extension_contributions().to_vec(),
            held_contribution.completeness().clone(),
        );
        assert!(matches!(
            classify_module_apply_retry(&preflight, &descendant, Some(&wrong_contribution_receipt)),
            Err(ModuleApplyRetryError::Receipt(
                ModuleApplyRetryReceiptError::Contribution { .. }
            ))
        ));

        let mut wrong_grade_receipt = receipt.clone();
        wrong_grade_receipt.grade = ModuleApplyGrade::AppliedIncomplete {
            completeness: receipt.grade().completeness().clone(),
        };
        assert!(matches!(
            classify_module_apply_retry(&preflight, &descendant, Some(&wrong_grade_receipt)),
            Err(ModuleApplyRetryError::Receipt(
                ModuleApplyRetryReceiptError::Grade { .. }
            ))
        ));

        let mut wrong_transaction_receipt = receipt.clone();
        wrong_transaction_receipt.transaction_id = ModuleApplyTransactionId(Digest([32; 32]));
        assert!(matches!(
            classify_module_apply_retry(&preflight, &descendant, Some(&wrong_transaction_receipt)),
            Err(ModuleApplyRetryError::Receipt(
                ModuleApplyRetryReceiptError::Transaction { .. }
            ))
        ));
        descendant
            .verify()
            .expect("receipt substitution refusal leaves the descendant unchanged");
    }

    #[test]
    fn module_presence_without_full_target_containment_is_not_a_descendant_retry() {
        let base = empty_apply_state();
        let subject = named_record(
            "fixture.retry-subject",
            "fixture.retry-subject.decl",
            "fixture.retry-subject.extra",
            41,
        );
        let unrelated_one = named_record(
            "fixture.unrelated-one",
            "fixture.unrelated-one.decl",
            "fixture.unrelated-one.extra",
            42,
        );
        let unrelated_two = named_record(
            "fixture.unrelated-two",
            "fixture.unrelated-two.decl",
            "fixture.unrelated-two.extra",
            43,
        );
        let required = named_record(
            "fixture.required-base",
            "fixture.required-base.decl",
            "fixture.required-base.extra",
            44,
        );

        let subject_first = preflight_module_apply(
            transaction_with_target(
                vec![subject.clone()],
                subject.clone(),
                "fixture.retry-subject.decl",
                "fixture.retry-subject.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("subject-first transaction preflights");
        let after_subject = publish_fixture(&subject_first, &base).into_state();
        let unrelated_one_next = preflight_module_apply(
            transaction_with_target(
                vec![subject.clone(), unrelated_one.clone()],
                unrelated_one.clone(),
                "fixture.unrelated-one.decl",
                "fixture.unrelated-one.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("first unrelated transaction preflights");
        let after_unrelated_one = publish_fixture(&unrelated_one_next, &after_subject).into_state();
        let unrelated_two_next = preflight_module_apply(
            transaction_with_target(
                vec![subject.clone(), unrelated_one, unrelated_two.clone()],
                unrelated_two,
                "fixture.unrelated-two.decl",
                "fixture.unrelated-two.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("second unrelated transaction preflights");
        let current = publish_fixture(&unrelated_two_next, &after_unrelated_one).into_state();

        let requested = preflight_module_apply(
            transaction_with_target(
                vec![required, subject.clone()],
                subject.clone(),
                "fixture.retry-subject.decl",
                "fixture.retry-subject.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("subject-after-required transaction preflights");
        assert!(
            current.manifest().records().len() > requested.transaction().manifest().records().len()
        );
        assert_eq!(
            current.manifest().record(&subject.module().id),
            Some(&subject),
            "the negative must hold module presence and exact module-record equality fixed"
        );
        assert!(matches!(
            classify_module_apply_retry(&requested, &current, None),
            Ok(ModuleApplyRetryDisposition::NotCurrentResult { .. })
        ));
        assert!(matches!(
            prepare_module_apply(&requested, &current, current.environment()),
            Outcome::Complete(Err(ModuleApplyPrepareError::ExistingModule { .. }))
        ));
        current
            .verify()
            .expect("non-descendant classification leaves the current state unchanged");
    }

    /// Bounded model: this injects the equality that a declaration-content digest
    /// collision would create. It neither finds nor claims a cryptographic collision.
    #[test]
    fn retry_payload_identity_collision_is_reported_not_resolved() {
        let base = empty_apply_state();
        let contribution = record(vec![]);
        let checked = preflight_module_apply(
            transaction(contribution.clone(), vec![]),
            &ModuleApplyLimits::default(),
        )
        .expect("baseline retry fixture preflights");
        let committed = publish_fixture(&checked, &base);

        let altered_declaration = match checked.transaction().declarations()[0].as_ref() {
            ConstantInfo::Axiom(axiom) => {
                let mut altered = axiom.clone();
                altered.is_unsafe = true;
                Arc::new(ConstantInfo::Axiom(altered))
            }
            other => panic!("fixture declaration changed kind: {other:?}"),
        };
        let mut injected = preflight_module_apply(
            ModuleApplyTransaction::new(
                Arc::clone(&checked.transaction().manifest),
                contribution,
                vec![altered_declaration],
                checked.transaction().extra_declarations().to_vec(),
                vec![],
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("the unequal declaration remains structurally preflight-valid");
        assert_ne!(
            injected.transaction_id(),
            checked.transaction_id(),
            "the unmodified digest derivation distinguishes the unequal values"
        );

        injected.declaration_identities = Arc::clone(&checked.declaration_identities);
        injected.transaction_id = checked.transaction_id();
        assert!(matches!(
            classify_module_apply_retry(&injected, committed.state(), None),
            Err(ModuleApplyRetryError::PayloadIdentityCollision {
                transaction_id,
                ..
            }) if transaction_id == checked.transaction_id()
        ));
        committed
            .state()
            .verify()
            .expect("collision refusal leaves the committed state unchanged");
    }

    #[test]
    fn partial_capture_publishes_as_applied_incomplete_without_cache_authority() {
        let environment = Environment::new();
        let empty_manifest = Arc::new(
            ModuleProvenanceManifest::new(epoch(), vec![], ModuleProvenanceLimits::default())
                .expect("empty manifest is valid"),
        );
        let empty_graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("empty graph construction admits");
        let base = ModuleApplyState::from_parts(environment, empty_graph, empty_manifest)
            .expect("empty aggregate state is coherent");
        let completeness = ProvenanceCompleteness::new(
            CaptureStatus::Partial,
            PayloadTransparency::Understood,
            vec![],
        );
        let checked = preflight_module_apply(
            transaction(
                record_with_completeness(vec![], completeness.clone()),
                vec![],
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("partial capture still binds every retained payload exactly");
        let declaration_candidate = base
            .environment()
            .add_decl((*checked.transaction().declarations()[0]).clone())
            .expect("fixture declaration is unique")
            .add_decl((*checked.transaction().extra_declarations()[0]).clone())
            .expect("fixture extra declaration is unique");
        let committed = match prepare_module_apply(&checked, &base, &declaration_candidate) {
            Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                plan.commit(&base, None),
                "uncancelled partial application must complete",
            )
            .expect("base remains current"),
            Outcome::Complete(Ok(ModuleApplyPlan::Retry(other))) => {
                panic!("first partial application unexpectedly retried: {other:?}")
            }
            other => panic!("expected a complete partial application plan, got {other:?}"),
        };
        assert!(matches!(
            committed.receipt().grade(),
            ModuleApplyGrade::AppliedIncomplete { completeness: actual }
                if actual == &completeness
        ));
        assert!(
            committed
                .receipt()
                .grade()
                .grants(ProvenanceAuthority::Inspection)
        );
        assert!(
            !committed
                .receipt()
                .grade()
                .grants(ProvenanceAuthority::CompleteInventory)
        );
        assert!(
            !committed
                .receipt()
                .grade()
                .grants(ProvenanceAuthority::AuthoritativeCache)
        );
        assert!(
            !committed
                .receipt()
                .grade()
                .grants(ProvenanceAuthority::FineInvalidation)
        );
        assert_eq!(base.graph().len(), 0);
        assert_eq!(committed.state().graph().len(), 1);
    }

    #[test]
    fn unresolved_direct_target_publishes_as_applied_incomplete_without_cache_authority() {
        let environment = Environment::new();
        let empty_manifest = Arc::new(
            ModuleProvenanceManifest::new(epoch(), vec![], ModuleProvenanceLimits::default())
                .expect("empty manifest is valid"),
        );
        let empty_graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("empty graph construction admits");
        let base = ModuleApplyState::from_parts(environment, empty_graph, empty_manifest)
            .expect("empty aggregate state is coherent");
        let missing = ModuleId::new(name("fixture.unresolved"));
        let completeness = ProvenanceCompleteness::new(
            CaptureStatus::Complete,
            PayloadTransparency::Understood,
            vec![missing.clone()],
        );
        let checked = preflight_module_apply(
            transaction(
                record_with_imports(
                    vec![DirectImport::new(missing.clone(), false, false, false)],
                    vec![],
                    completeness.clone(),
                ),
                vec![],
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("unresolved target still binds every retained payload exactly");
        let declaration_candidate = base
            .environment()
            .add_decl((*checked.transaction().declarations()[0]).clone())
            .expect("fixture declaration is unique")
            .add_decl((*checked.transaction().extra_declarations()[0]).clone())
            .expect("fixture extra declaration is unique");
        let committed = match prepare_module_apply(&checked, &base, &declaration_candidate) {
            Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                plan.commit(&base, None),
                "uncancelled unresolved-target application must complete",
            )
            .expect("base remains current"),
            other => panic!("expected a complete unresolved-target plan, got {other:?}"),
        };
        assert!(matches!(
            committed.receipt().grade(),
            ModuleApplyGrade::AppliedIncomplete { completeness: actual }
                if actual == &completeness
        ));
        assert_eq!(
            committed
                .receipt()
                .grade()
                .completeness()
                .missing_dependencies(),
            &[missing]
        );
        assert!(
            committed
                .receipt()
                .grade()
                .grants(ProvenanceAuthority::CompleteInventory)
        );
        assert!(
            !committed
                .receipt()
                .grade()
                .grants(ProvenanceAuthority::AuthoritativeCache)
        );
        assert!(
            !committed
                .receipt()
                .grade()
                .grants(ProvenanceAuthority::FineInvalidation)
        );
        assert_eq!(base.graph().len(), 0);
        assert_eq!(committed.state().graph().len(), 1);
    }

    #[test]
    fn opaque_complete_payload_retains_cache_identity_but_blocks_fine_invalidation() {
        let descriptor = opaque_descriptor();
        let environment = Environment::new()
            .register_extension(descriptor.clone())
            .expect("opaque fixture extension is unique");
        let empty_manifest = Arc::new(
            ModuleProvenanceManifest::new(epoch(), vec![], ModuleProvenanceLimits::default())
                .expect("empty manifest is valid"),
        );
        let empty_graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("empty graph construction admits");
        let base = ModuleApplyState::from_parts(environment.clone(), empty_graph, empty_manifest)
            .expect("empty aggregate state is coherent");
        let bytes: Arc<[u8]> = Arc::from(&b"opaque bytes remain exact"[..]);
        let entry = ExtensionEntryId::derive(&epoch(), &descriptor, &bytes);
        let completeness = ProvenanceCompleteness::new(
            CaptureStatus::Complete,
            PayloadTransparency::Opaque,
            vec![],
        );
        let checked = preflight_module_apply(
            transaction(
                record_with_completeness(
                    vec![ExtensionContribution::new(
                        descriptor.clone(),
                        0,
                        environment
                            .extension(&descriptor.name)
                            .expect("opaque extension is registered")
                            .content_digest(),
                        vec![entry],
                    )],
                    completeness.clone(),
                ),
                vec![ExtensionPayload::new(
                    0,
                    descriptor.clone(),
                    0,
                    Arc::clone(&bytes),
                )],
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("opaque bytes bind without decoding or normalization");
        let declaration_candidate = base
            .environment()
            .add_decl((*checked.transaction().declarations()[0]).clone())
            .expect("fixture declaration is unique")
            .add_decl((*checked.transaction().extra_declarations()[0]).clone())
            .expect("fixture extra declaration is unique");
        let committed = match prepare_module_apply(&checked, &base, &declaration_candidate) {
            Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                plan.commit(&base, None),
                "uncancelled opaque application must complete",
            )
            .expect("base remains current"),
            other => panic!("expected a complete opaque application plan, got {other:?}"),
        };
        assert!(matches!(
            committed.receipt().grade(),
            ModuleApplyGrade::Complete { completeness: actual } if actual == &completeness
        ));
        for authority in [
            ProvenanceAuthority::Inspection,
            ProvenanceAuthority::ExactReplay,
            ProvenanceAuthority::CompleteInventory,
            ProvenanceAuthority::AuthoritativeCache,
        ] {
            assert!(committed.receipt().grade().grants(authority));
        }
        assert!(
            !committed
                .receipt()
                .grade()
                .grants(ProvenanceAuthority::FineInvalidation)
        );
        assert_eq!(
            committed
                .state()
                .environment()
                .extension(&descriptor.name)
                .expect("opaque extension remains registered")
                .entries()
                .next()
                .expect("opaque payload was replayed")
                .payload,
            bytes
        );
    }

    #[test]
    fn independent_module_apply_order_converges_on_one_committed_state() {
        let empty_manifest = Arc::new(
            ModuleProvenanceManifest::new(epoch(), vec![], ModuleProvenanceLimits::default())
                .expect("empty manifest is valid"),
        );
        let empty_graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("empty graph construction admits");
        let base = ModuleApplyState::from_parts(Environment::new(), empty_graph, empty_manifest)
            .expect("empty aggregate state is coherent");
        let left = named_record(
            "fixture.left",
            "fixture.left.decl",
            "fixture.left.extra",
            11,
        );
        let right = named_record(
            "fixture.right",
            "fixture.right.decl",
            "fixture.right.extra",
            12,
        );

        let left_first = preflight_module_apply(
            transaction_with_target(
                vec![left.clone()],
                left.clone(),
                "fixture.left.decl",
                "fixture.left.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("left transaction preflights");
        let left_candidate = base
            .environment()
            .add_decl((*left_first.transaction().declarations()[0]).clone())
            .expect("left declaration is unique")
            .add_decl((*left_first.transaction().extra_declarations()[0]).clone())
            .expect("left extra declaration is unique");
        let after_left = match prepare_module_apply(&left_first, &base, &left_candidate) {
            Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                plan.commit(&base, None),
                "uncancelled left application must complete",
            )
            .expect("left base remains current")
            .into_state(),
            other => panic!("expected a prepared left application, got {other:?}"),
        };
        let right_after_left = preflight_module_apply(
            transaction_with_target(
                vec![left.clone(), right.clone()],
                right.clone(),
                "fixture.right.decl",
                "fixture.right.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("right-after-left transaction preflights");
        let right_candidate = after_left
            .environment()
            .add_decl((*right_after_left.transaction().declarations()[0]).clone())
            .expect("right declaration is unique")
            .add_decl((*right_after_left.transaction().extra_declarations()[0]).clone())
            .expect("right extra declaration is unique");
        let final_left_then_right =
            match prepare_module_apply(&right_after_left, &after_left, &right_candidate) {
                Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                    plan.commit(&after_left, None),
                    "uncancelled right-after-left application must complete",
                )
                .expect("right-after-left base remains current")
                .into_state(),
                other => panic!("expected a prepared right-after-left application, got {other:?}"),
            };

        let right_first = preflight_module_apply(
            transaction_with_target(
                vec![right.clone()],
                right.clone(),
                "fixture.right.decl",
                "fixture.right.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("right transaction preflights");
        let right_candidate = base
            .environment()
            .add_decl((*right_first.transaction().declarations()[0]).clone())
            .expect("right declaration is unique")
            .add_decl((*right_first.transaction().extra_declarations()[0]).clone())
            .expect("right extra declaration is unique");
        let after_right = match prepare_module_apply(&right_first, &base, &right_candidate) {
            Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                plan.commit(&base, None),
                "uncancelled right application must complete",
            )
            .expect("right base remains current")
            .into_state(),
            other => panic!("expected a prepared right application, got {other:?}"),
        };
        let left_after_right = preflight_module_apply(
            transaction_with_target(
                vec![left.clone(), right.clone()],
                left.clone(),
                "fixture.left.decl",
                "fixture.left.extra",
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("left-after-right transaction preflights");
        let left_candidate = after_right
            .environment()
            .add_decl((*left_after_right.transaction().declarations()[0]).clone())
            .expect("left declaration is unique")
            .add_decl((*left_after_right.transaction().extra_declarations()[0]).clone())
            .expect("left extra declaration is unique");
        let final_right_then_left =
            match prepare_module_apply(&left_after_right, &after_right, &left_candidate) {
                Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                    plan.commit(&after_right, None),
                    "uncancelled left-after-right application must complete",
                )
                .expect("left-after-right base remains current")
                .into_state(),
                other => panic!("expected a prepared left-after-right application, got {other:?}"),
            };

        assert_eq!(final_left_then_right, final_right_then_left);
        assert_eq!(
            final_left_then_right.manifest().root(),
            final_right_then_left.manifest().root()
        );
        assert_eq!(
            final_left_then_right.logical_root(),
            final_right_then_left.logical_root()
        );
        assert_eq!(
            final_left_then_right.indexes(),
            final_right_then_left.indexes()
        );
    }

    /// The thread-order half of the metamorphic matrix the bead requires
    /// ("insertion and thread-order metamorphic matrices").
    ///
    /// The sibling above varies the order in which two modules are applied
    /// SEQUENTIALLY: each transaction is prepared against the state the previous
    /// one published, so no plan is ever prepared against a base that later
    /// moves. That is the insertion-order half, and cod_2's own landing comment
    /// marks it as "not a thread-matrix claim".
    ///
    /// Concurrency introduces a case sequential ordering cannot: two plans
    /// prepared against the SAME base, only one of which can publish. This test
    /// prepares both on real threads against one shared base and then asserts
    /// the three things that must hold when they race:
    ///
    /// 1. the loser is refused as `StaleBase` — the bead requires base/checkpoint
    ///    drift to be typed before publication and says conflicts are "never
    ///    last-writer-wins", so a silent success here would be the defect;
    /// 2. re-preparing the loser against the winner's published state converges;
    /// 3. the converged state is IDENTICAL whichever thread won — state,
    ///    provenance root, logical root and both indexes.
    ///
    /// Point 3 is the metamorphic proper: the schedule is free, the result is
    /// not.
    #[test]
    fn concurrent_module_apply_resolves_by_stale_base_and_converges_either_way() {
        let empty_manifest = Arc::new(
            ModuleProvenanceManifest::new(epoch(), vec![], ModuleProvenanceLimits::default())
                .expect("empty manifest is valid"),
        );
        let empty_graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("empty graph construction admits");
        let base = ModuleApplyState::from_parts(Environment::new(), empty_graph, empty_manifest)
            .expect("empty aggregate state is coherent");
        let left = named_record(
            "fixture.left",
            "fixture.left.decl",
            "fixture.left.extra",
            11,
        );
        let right = named_record(
            "fixture.right",
            "fixture.right.decl",
            "fixture.right.extra",
            12,
        );

        // Prepare BOTH plans against the same base, on real threads. Preparation
        // is the phase that reads the base, so this is where a schedule can
        // actually differ; the commits below then model the two resolutions of
        // that race.
        let prepare =
            |record: ModuleContributionRecord, decl: &'static str, extra: &'static str| {
                let base = base.clone();
                move || {
                    let preflight = preflight_module_apply(
                        transaction_with_target(vec![record.clone()], record, decl, extra),
                        &ModuleApplyLimits::default(),
                    )
                    .expect("transaction preflights");
                    let candidate = base
                        .environment()
                        .add_decl((*preflight.transaction().declarations()[0]).clone())
                        .expect("declaration is unique")
                        .add_decl((*preflight.transaction().extra_declarations()[0]).clone())
                        .expect("extra declaration is unique");
                    match prepare_module_apply(&preflight, &base, &candidate) {
                        Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => plan,
                        other => panic!("expected a prepared application, got {other:?}"),
                    }
                }
            };

        // Run the two resolutions of the race. `winner_first` decides which
        // thread's plan publishes; the loser must then be refused and replayed.
        let resolve = |left_wins: bool| {
            let left_thread = std::thread::spawn(prepare(
                left.clone(),
                "fixture.left.decl",
                "fixture.left.extra",
            ));
            let right_thread = std::thread::spawn(prepare(
                right.clone(),
                "fixture.right.decl",
                "fixture.right.extra",
            ));
            let left_plan = left_thread.join().expect("left preparation thread");
            let right_plan = right_thread.join().expect("right preparation thread");

            let (winner_plan, loser_plan, winner_record, loser_record, loser_decl, loser_extra) =
                if left_wins {
                    (
                        left_plan,
                        right_plan,
                        left.clone(),
                        right.clone(),
                        "fixture.right.decl",
                        "fixture.right.extra",
                    )
                } else {
                    (
                        right_plan,
                        left_plan,
                        right.clone(),
                        left.clone(),
                        "fixture.left.decl",
                        "fixture.left.extra",
                    )
                };

            let published = completed(
                winner_plan.commit(&base, None),
                "uncancelled winning plan must complete",
            )
            .expect("the winning plan was prepared against the current base")
            .into_state();

            // (1) The loser was prepared against a base that has since moved. It
            // must be REFUSED, by name, rather than publishing over the winner.
            match loser_plan.commit(&published, None) {
                Outcome::Complete(Err(ModuleApplyCommitError::StaleBase)) => {}
                Outcome::Complete(Ok(_)) => panic!(
                    "the losing plan published against a base that had already moved; \
                     this is last-writer-wins, which the bead forbids"
                ),
                Outcome::Complete(Err(other)) => {
                    panic!("expected StaleBase for the losing plan, got {other:?}")
                }
                other => panic!("stale-base classification did not complete: {other:?}"),
            }

            // (2) Replaying the loser against the published state converges.
            let replay = preflight_module_apply(
                transaction_with_target(
                    vec![winner_record, loser_record.clone()],
                    loser_record,
                    loser_decl,
                    loser_extra,
                ),
                &ModuleApplyLimits::default(),
            )
            .expect("replayed transaction preflights");
            let candidate = published
                .environment()
                .add_decl((*replay.transaction().declarations()[0]).clone())
                .expect("replayed declaration is unique")
                .add_decl((*replay.transaction().extra_declarations()[0]).clone())
                .expect("replayed extra declaration is unique");
            match prepare_module_apply(&replay, &published, &candidate) {
                Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                    plan.commit(&published, None),
                    "uncancelled replay must complete",
                )
                .expect("replay base remains current")
                .into_state(),
                other => panic!("expected a prepared replay application, got {other:?}"),
            }
        };

        let left_won = resolve(true);
        let right_won = resolve(false);

        // (3) The metamorphic: which thread won is a scheduling accident and may
        // not survive into the published evidence.
        assert_eq!(
            left_won, right_won,
            "the committed state depends on which thread won the race"
        );
        assert_eq!(
            left_won.manifest().root(),
            right_won.manifest().root(),
            "provenance root depends on the schedule"
        );
        assert_eq!(
            left_won.logical_root(),
            right_won.logical_root(),
            "logical root depends on the schedule"
        );
        assert_eq!(
            left_won.indexes(),
            right_won.indexes(),
            "bidirectional indexes depend on the schedule"
        );
    }

    /// The primary-class sibling of this check is killed by
    /// `declaration_order_is_a_typed_payload_binding_refusal`; this class was
    /// NOT, and a mutation campaign found it: deleting the
    /// `DeclarationClass::ExtraDeclaration` call to `verify_declaration_payloads`
    /// left the whole `fln-env` suite green.
    ///
    /// The reason is ordering, and it is why the sibling cannot cover this.
    /// `verify_declaration_payloads` runs for `Declaration` FIRST, and the
    /// sibling's fixture swaps the two vectors — so the primary check fires and
    /// the extra-declaration check is never reached. Binding this class needs a
    /// transaction whose primary payloads are CORRECT and whose extra payloads
    /// are not, which is what this cell supplies.
    #[test]
    fn extra_declaration_payloads_are_bound_independently_of_the_primary_class() {
        let contribution = record(vec![]);
        let manifest = ModuleProvenanceManifest::new(
            epoch(),
            vec![contribution.clone()],
            ModuleProvenanceLimits::default(),
        )
        .expect("fixture manifest is valid");
        let transaction = ModuleApplyTransaction::new(
            Arc::new(manifest),
            contribution,
            vec![axiom("fixture.decl")],
            vec![axiom("fixture.wrong")],
            vec![],
        );

        assert!(matches!(
            preflight_module_apply(transaction, &ModuleApplyLimits::default()),
            Err(ModuleApplyPreflightError::DeclarationName {
                class: DeclarationClass::ExtraDeclaration,
                index: 0,
                ..
            })
        ));
    }

    /// The manifest is identity-only, so the count of supplied extension
    /// payloads is a binding the envelope must satisfy rather than a property of
    /// the payloads themselves. A mutation campaign found this unguarded:
    /// deleting the `ExtensionPayloadCount` refusal left the suite green, so a
    /// transaction could carry fewer payloads than the record it claims to
    /// implement and reach preparation.
    #[test]
    fn an_extension_payload_shortfall_is_a_typed_count_refusal() {
        let descriptor = descriptor();
        let first = ExtensionEntryId::derive(&epoch(), &descriptor, b"first");
        let second = ExtensionEntryId::derive(&epoch(), &descriptor, b"second");
        let contribution = record(vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            Digest([0; 32]),
            vec![first, second],
        )]);

        // The record declares TWO entries; the envelope supplies ONE.
        let short = transaction(
            contribution,
            vec![ExtensionPayload::new(0, descriptor, 0, &b"first"[..])],
        );

        assert!(matches!(
            preflight_module_apply(short, &ModuleApplyLimits::default()),
            Err(ModuleApplyPreflightError::ExtensionPayloadCount {
                expected: 2,
                actual: 1,
            })
        ));
    }

    // -----------------------------------------------------------------------
    // as7 resource-budget tranche: envelope budgets, exact usage facts, and
    // the zero / one-under / exact / one-over fault matrix, every refusal
    // proving zero publication followed by a clean verified recovery.
    // -----------------------------------------------------------------------

    fn preflight_under(
        make: &impl Fn() -> ModuleApplyTransaction,
        limits: &ModuleApplyLimits,
    ) -> Result<PreflightedModuleApply, ModuleApplyPreflightError> {
        preflight_module_apply(make(), limits)
    }

    fn record_with_payload_counts(
        declarations: usize,
        extras: usize,
        contributions: Vec<ExtensionContribution>,
    ) -> ModuleContributionRecord {
        let epoch = epoch();
        let declaration_names: Vec<Name> = (0..declarations)
            .map(|index| name(&format!("fixture.decl{index}")))
            .collect();
        let extra_names: Vec<Name> = (0..extras)
            .map(|index| name(&format!("fixture.extra{index}")))
            .collect();
        ModuleContributionRecord::new(
            ModuleRecord::new(
                ModuleId::new(name("fixture.module")),
                true,
                vec![],
                ArtifactEvidence {
                    epoch,
                    content_digest: Digest([7; 32]),
                    producer: ArtifactProducer::Reference,
                    grade: ArtifactGrade::Verified,
                },
            ),
            declaration_names,
            extra_names,
            contributions,
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        )
    }

    fn axioms(prefix: &str, count: usize) -> Vec<Arc<ConstantInfo>> {
        (0..count)
            .map(|index| axiom(&format!("{prefix}{index}")))
            .collect()
    }

    fn sized_transaction(
        declarations: usize,
        extras: usize,
        contributions: Vec<ExtensionContribution>,
        extension_payloads: Vec<ExtensionPayload>,
    ) -> ModuleApplyTransaction {
        let contribution = record_with_payload_counts(declarations, extras, contributions);
        let manifest = ModuleProvenanceManifest::new(
            epoch(),
            vec![contribution.clone()],
            ModuleProvenanceLimits::default(),
        )
        .expect("fixture manifest is valid");
        ModuleApplyTransaction::new(
            Arc::new(manifest),
            contribution,
            axioms("fixture.decl", declarations),
            axioms("fixture.extra", extras),
            extension_payloads,
        )
    }

    fn expect_limit_refusal(
        error: &ModuleApplyPreflightError,
        resource: ModuleApplyResource,
        limit: u128,
        actual: u128,
    ) {
        assert!(
            matches!(
                error,
                ModuleApplyPreflightError::LimitExceeded {
                    resource: refused,
                    limit: refused_limit,
                    actual: refused_actual,
                } if *refused == resource && *refused_limit == limit && *refused_actual == actual
            ),
            "expected a {resource:?} refusal at limit {limit} against {actual}, got {error:?}"
        );
    }

    fn empty_base() -> ModuleApplyState {
        let manifest = Arc::new(
            ModuleProvenanceManifest::new(epoch(), vec![], ModuleProvenanceLimits::default())
                .expect("empty manifest is valid"),
        );
        let graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("empty graph construction admits");
        ModuleApplyState::from_parts(Environment::new(), graph, manifest)
            .expect("empty aggregate state is coherent")
    }

    /// Extension-bearing transactions replay onto an environment that has
    /// already registered their descriptor; this base carries exactly that.
    fn base_with_registered_extension() -> ModuleApplyState {
        let environment = Environment::new()
            .register_extension(descriptor())
            .expect("fixture extension is unique");
        let manifest = Arc::new(
            ModuleProvenanceManifest::new(epoch(), vec![], ModuleProvenanceLimits::default())
                .expect("empty manifest is valid"),
        );
        let graph = ModuleGraph::new(epoch(), ModuleGraphLimits::default())
            .into_admitted_value()
            .expect("empty graph construction admits");
        ModuleApplyState::from_parts(environment, graph, manifest)
            .expect("empty aggregate state is coherent")
    }

    fn committed_recovery(
        base: &ModuleApplyState,
        make: &impl Fn() -> ModuleApplyTransaction,
    ) -> CommittedModuleApply {
        let checked = preflight_module_apply(make(), &ModuleApplyLimits::default())
            .expect("the default posture admits the recovery envelope");
        let mut candidate = base.environment().clone();
        for info in checked
            .transaction()
            .declarations()
            .iter()
            .chain(checked.transaction().extra_declarations())
        {
            candidate = candidate
                .add_decl((**info).clone())
                .expect("fixture declaration is unique");
        }
        match prepare_module_apply(&checked, base, &candidate) {
            Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                plan.commit(base, None),
                "uncancelled recovery application must complete",
            )
            .expect("the recovery base remains current"),
            other => panic!("expected a prepared recovery plan, got {other:?}"),
        }
    }

    /// Refuse the envelope under `limits`, prove the base published nothing,
    /// then run one clean default-posture application to a fully verified state.
    fn refuse_then_recover(
        base: &ModuleApplyState,
        make: &impl Fn() -> ModuleApplyTransaction,
        limits: &ModuleApplyLimits,
        resource: ModuleApplyResource,
        limit: u128,
        actual: u128,
    ) -> CommittedModuleApply {
        let before = base.clone();
        let error =
            preflight_under(make, limits).expect_err("an over-budget envelope must be refused");
        expect_limit_refusal(&error, resource, limit, actual);
        assert_eq!(base, &before, "a refused envelope publishes nothing");
        committed_recovery(base, make)
    }

    #[test]
    fn a_zero_budget_admits_the_empty_envelope_and_refuses_any_payload() {
        let zero = ModuleApplyLimits::new(0, 0, 0, 0);
        let empty = preflight_module_apply(sized_transaction(0, 0, vec![], vec![]), &zero)
            .expect("an empty envelope carries nothing any budget could refuse");
        assert_eq!(
            empty.usage(),
            ModuleApplyUsage {
                declaration_payloads: 0,
                extra_declaration_payloads: 0,
                extension_payloads: 0,
                extension_payload_bytes: 0,
            }
        );

        let base = empty_base();
        let error = preflight_module_apply(sized_transaction(1, 0, vec![], vec![]), &zero)
            .expect_err("a zero budget refuses any declaration payload");
        expect_limit_refusal(&error, ModuleApplyResource::DeclarationPayloads, 0, 1);
        let error = preflight_module_apply(sized_transaction(0, 1, vec![], vec![]), &zero)
            .expect_err("a zero budget refuses any extra declaration payload");
        expect_limit_refusal(&error, ModuleApplyResource::ExtraDeclarationPayloads, 0, 1);
        assert_eq!(base, empty_base());
    }

    #[test]
    fn declaration_payload_budget_boundaries_refuse_then_recover() {
        let base = empty_base();
        let make = || sized_transaction(2, 0, vec![], vec![]);
        let usage = 2u128;
        let committed = refuse_then_recover(
            &base,
            &make,
            &ModuleApplyLimits::new(1, usize::MAX, usize::MAX, u128::MAX),
            ModuleApplyResource::DeclarationPayloads,
            1,
            usage,
        );
        assert_eq!(committed.state().graph().len(), 1);
        assert_ne!(committed.state().logical_root(), base.logical_root());
        assert_ne!(committed.state().manifest().root(), base.manifest().root());

        for limit in [usage, usage + 1] {
            let checked = preflight_module_apply(
                make(),
                &ModuleApplyLimits::new(limit as usize, usize::MAX, usize::MAX, u128::MAX),
            )
            .expect("exact and one-over budgets both admit");
            assert_eq!(checked.usage().declaration_payloads() as u128, usage);
        }
    }

    #[test]
    fn extra_declaration_payload_budget_boundaries_refuse_then_recover() {
        let base = empty_base();
        let make = || sized_transaction(0, 2, vec![], vec![]);
        let committed = refuse_then_recover(
            &base,
            &make,
            &ModuleApplyLimits::new(usize::MAX, 1, usize::MAX, u128::MAX),
            ModuleApplyResource::ExtraDeclarationPayloads,
            1,
            2,
        );
        assert_eq!(committed.state().graph().len(), 1);
        assert_ne!(committed.state().manifest().root(), base.manifest().root());

        for limit in [2usize, 3] {
            let checked = preflight_module_apply(
                make(),
                &ModuleApplyLimits::new(usize::MAX, limit, usize::MAX, u128::MAX),
            )
            .expect("exact and one-over budgets both admit");
            assert_eq!(checked.usage().extra_declaration_payloads(), 2);
        }
    }

    #[test]
    fn extension_payload_count_budget_boundaries_refuse_then_recover() {
        let base = base_with_registered_extension();
        let descriptor = descriptor();
        let history = base
            .environment()
            .extension(&descriptor.name)
            .expect("fixture extension is registered")
            .content_digest();
        let entries = vec![
            ExtensionEntryId::derive(&epoch(), &descriptor, b"first"),
            ExtensionEntryId::derive(&epoch(), &descriptor, b"second"),
        ];
        let contribution = vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            history,
            entries,
        )];
        let payloads = || {
            vec![
                ExtensionPayload::new(0, descriptor.clone(), 0, &b"first"[..]),
                ExtensionPayload::new(0, descriptor.clone(), 1, &b"second"[..]),
            ]
        };
        let base = base_with_registered_extension();
        let make = || sized_transaction(0, 0, contribution.clone(), payloads());
        let committed = refuse_then_recover(
            &base,
            &make,
            &ModuleApplyLimits::new(usize::MAX, usize::MAX, 1, u128::MAX),
            ModuleApplyResource::ExtensionPayloads,
            1,
            2,
        );
        assert_eq!(committed.state().graph().len(), 1);
        assert_ne!(committed.state().logical_root(), base.logical_root());

        for limit in [2usize, 3] {
            let checked = preflight_module_apply(
                make(),
                &ModuleApplyLimits::new(usize::MAX, usize::MAX, limit, u128::MAX),
            )
            .expect("exact and one-over budgets both admit");
            assert_eq!(checked.usage().extension_payloads(), 2);
        }
    }

    #[test]
    fn extension_payload_byte_budget_boundaries_refuse_then_recover() {
        let base = base_with_registered_extension();
        let descriptor = descriptor();
        let history = base
            .environment()
            .extension(&descriptor.name)
            .expect("fixture extension is registered")
            .content_digest();
        let entry = ExtensionEntryId::derive(&epoch(), &descriptor, b"payload");
        let contribution = vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            history,
            vec![entry],
        )];
        let base = base_with_registered_extension();
        let make = || {
            sized_transaction(
                0,
                0,
                contribution.clone(),
                vec![ExtensionPayload::new(
                    0,
                    descriptor.clone(),
                    0,
                    &b"payload"[..],
                )],
            )
        };
        let committed = refuse_then_recover(
            &base,
            &make,
            &ModuleApplyLimits::new(usize::MAX, usize::MAX, usize::MAX, 6),
            ModuleApplyResource::ExtensionPayloadBytes,
            6,
            7,
        );
        assert_eq!(committed.state().graph().len(), 1);
        assert_ne!(committed.state().manifest().root(), base.manifest().root());

        for limit in [7u128, 8] {
            let checked = preflight_module_apply(
                make(),
                &ModuleApplyLimits::new(usize::MAX, usize::MAX, usize::MAX, limit),
            )
            .expect("exact and one-over byte budgets both admit");
            assert_eq!(checked.usage().extension_payload_bytes(), 7);
        }
    }

    #[test]
    fn usage_facts_are_recorded_exactly_for_a_mixed_envelope() {
        let descriptor = descriptor();
        let entries = vec![
            ExtensionEntryId::derive(&epoch(), &descriptor, b"alpha"),
            ExtensionEntryId::derive(&epoch(), &descriptor, b"beta"),
        ];
        let contribution = vec![ExtensionContribution::new(
            descriptor.clone(),
            0,
            Digest([0; 32]),
            entries,
        )];
        let checked = preflight_module_apply(
            sized_transaction(
                3,
                2,
                contribution,
                vec![
                    ExtensionPayload::new(0, descriptor.clone(), 0, &b"alpha"[..]),
                    ExtensionPayload::new(0, descriptor, 1, &b"beta"[..]),
                ],
            ),
            &ModuleApplyLimits::default(),
        )
        .expect("the default posture admits the mixed fixture");
        assert_eq!(checked.usage().declaration_payloads(), 3);
        assert_eq!(checked.usage().extra_declaration_payloads(), 2);
        assert_eq!(checked.usage().extension_payloads(), 2);
        assert_eq!(checked.usage().extension_payload_bytes(), 9);
    }

    /// The broader same-base half of the bead's metamorphic requirement.
    /// The two-module sibling above established order convergence pairwise;
    /// this matrix widens it to every insertion order of THREE independent
    /// modules over one empty base. Each sequence applies its modules
    /// sequentially (every plan prepared against the state the previous one
    /// published), and all six final states must be identical — state,
    /// provenance root, logical root, and both index directions.
    #[test]
    fn three_module_insertion_orders_all_converge_on_one_committed_state() {
        let specs = [
            ("fixture.m1", "fixture.m1.decl", "fixture.m1.extra", 21u8),
            ("fixture.m2", "fixture.m2.decl", "fixture.m2.extra", 22),
            ("fixture.m3", "fixture.m3.decl", "fixture.m3.extra", 23),
        ];
        let records: Vec<ModuleContributionRecord> = specs
            .iter()
            .map(|(module, declaration, extra, seed)| {
                named_record(module, declaration, extra, *seed)
            })
            .collect();
        let run = |permutation: [usize; 3], base: &ModuleApplyState| -> ModuleApplyState {
            let mut current = base.clone();
            for step in 0..3 {
                let which = permutation[step];
                let target = permutation[..=step]
                    .iter()
                    .map(|&index| records[index].clone())
                    .collect();
                let checked = preflight_module_apply(
                    transaction_with_target(
                        target,
                        records[which].clone(),
                        specs[which].1,
                        specs[which].2,
                    ),
                    &ModuleApplyLimits::default(),
                )
                .expect("matrix transaction preflights");
                let candidate = current
                    .environment()
                    .add_decl((*checked.transaction().declarations()[0]).clone())
                    .expect("matrix declaration is unique")
                    .add_decl((*checked.transaction().extra_declarations()[0]).clone())
                    .expect("matrix extra declaration is unique");
                current = match prepare_module_apply(&checked, &current, &candidate) {
                    Outcome::Complete(Ok(ModuleApplyPlan::Prepared(plan))) => completed(
                        plan.commit(&current, None),
                        "uncancelled matrix application must complete",
                    )
                    .expect("matrix base remains current")
                    .into_state(),
                    other => panic!("expected a prepared matrix application, got {other:?}"),
                };
            }
            current
        };

        let empty = empty_base();
        let reference = run([0, 1, 2], &empty);
        assert_eq!(reference.graph().len(), 3);
        for permutation in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let converged = run(permutation, &empty);
            assert_eq!(
                converged, reference,
                "insertion order {permutation:?} diverged from the reference state"
            );
            assert_eq!(converged.manifest().root(), reference.manifest().root());
            assert_eq!(converged.logical_root(), reference.logical_root());
            assert_eq!(converged.indexes(), reference.indexes());
        }
    }

    /// The transaction-ID matrix the bead names alongside same-base retries:
    /// identity is a deterministic function of the manifest root plus the
    /// retained payload values, so re-preflighting an equal envelope is
    /// stable, while a different manifest root or a different payload set
    /// yields a different identity even when the other component matches.
    #[test]
    fn transaction_identity_is_deterministic_and_sensitive_to_root_and_payload() {
        let default_limits = ModuleApplyLimits::default();
        let first =
            preflight_module_apply(sized_transaction(2, 1, vec![], vec![]), &default_limits)
                .expect("the first envelope preflights");
        let second =
            preflight_module_apply(sized_transaction(2, 1, vec![], vec![]), &default_limits)
                .expect("the repeated envelope preflights");
        assert_eq!(
            first.transaction_id(),
            second.transaction_id(),
            "an equal envelope must preflight to an equal identity"
        );

        // Different payload set, same construction path: identity moves.
        let narrower =
            preflight_module_apply(sized_transaction(1, 1, vec![], vec![]), &default_limits)
                .expect("the narrower envelope preflights");
        assert_ne!(narrower.transaction_id(), first.transaction_id());

        // Same retained payload VALUES under a different manifest root:
        // identity still moves, because the preimage is root-scoped.
        let alternate_epoch =
            ModuleEpoch::new("v9.99.9", "ffffffffffffffffffffffffffffffffffffffff");
        let contribution = ModuleContributionRecord::new(
            ModuleRecord::new(
                ModuleId::new(name("fixture.altmodule")),
                true,
                vec![],
                ArtifactEvidence {
                    epoch: alternate_epoch.clone(),
                    content_digest: Digest([7; 32]),
                    producer: ArtifactProducer::Reference,
                    grade: ArtifactGrade::Verified,
                },
            ),
            vec![name("fixture.decl0"), name("fixture.decl1")],
            vec![name("fixture.extra0")],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );
        let manifest = Arc::new(
            ModuleProvenanceManifest::new(
                alternate_epoch,
                vec![contribution.clone()],
                crate::provenance::ModuleProvenanceLimits::default(),
            )
            .expect("alternate-epoch manifest is valid"),
        );
        let relocated = preflight_module_apply(
            ModuleApplyTransaction::new(
                manifest,
                contribution,
                axioms("fixture.decl", 2),
                axioms("fixture.extra", 1),
                vec![],
            ),
            &default_limits,
        )
        .expect("the relocated envelope preflights");
        assert_ne!(
            relocated.transaction_id(),
            first.transaction_id(),
            "equal payloads under a different manifest root cannot share an identity"
        );
        assert_ne!(
            relocated.manifest_root(),
            first.manifest_root(),
            "the fixture must actually move the manifest root"
        );
    }
}
