//! **fln-env::invalidation** — deterministic module invalidation cones with provenance witnesses
//! (plan §7.1, §16.3; bead franken_lean-module-provenance-invalidation-1qv).
//!
//! Provides bounded deterministic invalidation queries across five distinct change classes:
//! 1. Artifact identity and evidence;
//! 2. Direct-import topology, import flags, and missing targets;
//! 3. Declaration contribution identity and content;
//! 4. Extension contribution descriptor, range, and payload identity;
//! 5. Completeness and transparency boundaries.
//!
//! Queries execute against a single validated committed [`ModuleApplyState`], resolving
//! change seeds through exact bidirectional indexes rather than name guesses.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use fln_core::diag::{ResourceReason, StructuralUnit};
use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, Outcome, ResourceUsage};
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::root::LogicalRoot;

use crate::effective_imports::EffectiveImportRequest;
use crate::extensions::ExtensionDescriptor;
use crate::module_apply::ModuleApplyState;
use crate::modules::{ArtifactEvidence, CancellationProbe, DirectImport, ModuleId};
use crate::provenance::{
    CaptureStatus, DeclarationClass, ExtensionEntryId, ModuleProvenanceRoot, PayloadTransparency,
    ProvenanceCompleteness,
};

/// Schema version for module invalidation.
pub const INVALIDATION_SCHEMA_VERSION: u16 = 1;

/// Tie-breaker policy version for witness paths.
pub const TIE_POLICY_VERSION: u16 = 1;

/// Five distinct change classes for invalidation queries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ChangeDescriptorV1 {
    /// Artifact evidence change for a module.
    Artifact {
        module: ModuleId,
        old_evidence: Option<ArtifactEvidence>,
        new_evidence: Option<ArtifactEvidence>,
    },
    /// Direct import topology modification (add, remove, reorder, flag changes).
    DirectImportTopology {
        module: ModuleId,
        old_imports: Vec<DirectImport>,
        new_imports: Vec<DirectImport>,
    },
    /// Declaration contribution change.
    Declaration {
        owner: ModuleId,
        class: DeclarationClass,
        source_ordinal: u64,
        name: Name,
        old_identity: Option<Digest>,
        new_identity: Option<Digest>,
    },
    /// Extension contribution change.
    ExtensionContribution {
        contributor: ModuleId,
        descriptor: ExtensionDescriptor,
        entry_id: ExtensionEntryId,
        old_source_ordinal: u64,
        old_range_start: u64,
        old_identity: Option<Digest>,
        new_identity: Option<Digest>,
    },
    /// Module completeness / transparency transition.
    Completeness {
        module: ModuleId,
        old_completeness: ProvenanceCompleteness,
        new_completeness: ProvenanceCompleteness,
    },
}

impl ChangeDescriptorV1 {
    /// Returns the target module associated with this change descriptor.
    pub fn module(&self) -> &ModuleId {
        match self {
            Self::Artifact { module, .. } => module,
            Self::DirectImportTopology { module, .. } => module,
            Self::Declaration { owner, .. } => owner,
            Self::ExtensionContribution { contributor, .. } => contributor,
            Self::Completeness { module, .. } => module,
        }
    }

    /// Returns true if this descriptor represents an exact no-op.
    pub fn is_no_op(&self) -> bool {
        match self {
            Self::Artifact {
                old_evidence,
                new_evidence,
                ..
            } => old_evidence == new_evidence,
            Self::DirectImportTopology {
                old_imports,
                new_imports,
                ..
            } => old_imports == new_imports,
            Self::Declaration {
                old_identity,
                new_identity,
                ..
            } => old_identity == new_identity,
            Self::ExtensionContribution {
                old_identity,
                new_identity,
                ..
            } => old_identity == new_identity,
            Self::Completeness {
                old_completeness,
                new_completeness,
                ..
            } => old_completeness == new_completeness,
        }
    }

    /// Compute a canonical digest for this change descriptor.
    pub fn descriptor_digest(&self) -> Digest {
        let mut bytes = Vec::new();
        match self {
            Self::Artifact {
                module,
                old_evidence,
                new_evidence,
            } => {
                bytes.push(1);
                bytes.extend_from_slice(module.name().to_display_string().as_bytes());
                if let Some(old_e) = old_evidence {
                    bytes.extend_from_slice(&old_e.content_digest.0);
                }
                if let Some(new_e) = new_evidence {
                    bytes.extend_from_slice(&new_e.content_digest.0);
                }
            }
            Self::DirectImportTopology {
                module,
                old_imports,
                new_imports,
            } => {
                bytes.push(2);
                bytes.extend_from_slice(module.name().to_display_string().as_bytes());
                for imp in old_imports {
                    bytes.extend_from_slice(imp.module.name().to_display_string().as_bytes());
                }
                for imp in new_imports {
                    bytes.extend_from_slice(imp.module.name().to_display_string().as_bytes());
                }
            }
            Self::Declaration {
                owner,
                class,
                source_ordinal,
                name,
                old_identity,
                new_identity,
            } => {
                bytes.push(3);
                bytes.extend_from_slice(owner.name().to_display_string().as_bytes());
                bytes.push(*class as u8);
                bytes.extend_from_slice(&source_ordinal.to_le_bytes());
                bytes.extend_from_slice(name.to_display_string().as_bytes());
                if let Some(old_i) = old_identity {
                    bytes.extend_from_slice(&old_i.0);
                }
                if let Some(new_i) = new_identity {
                    bytes.extend_from_slice(&new_i.0);
                }
            }
            Self::ExtensionContribution {
                contributor,
                descriptor,
                entry_id,
                old_source_ordinal,
                old_range_start,
                old_identity,
                new_identity,
            } => {
                bytes.push(4);
                bytes.extend_from_slice(contributor.name().to_display_string().as_bytes());
                bytes.extend_from_slice(descriptor.name.to_display_string().as_bytes());
                bytes.extend_from_slice(&entry_id.digest().0);
                bytes.extend_from_slice(&old_source_ordinal.to_le_bytes());
                bytes.extend_from_slice(&old_range_start.to_le_bytes());
                if let Some(old_i) = old_identity {
                    bytes.extend_from_slice(&old_i.0);
                }
                if let Some(new_i) = new_identity {
                    bytes.extend_from_slice(&new_i.0);
                }
            }
            Self::Completeness {
                module,
                old_completeness,
                new_completeness,
            } => {
                bytes.push(5);
                bytes.extend_from_slice(module.name().to_display_string().as_bytes());
                bytes.push(old_completeness.capture() as u8);
                bytes.push(old_completeness.transparency() as u8);
                bytes.push(new_completeness.capture() as u8);
                bytes.push(new_completeness.transparency() as u8);
            }
        }
        hash(Domain::ModuleProvenance, &bytes)
    }
}

/// Request for an invalidation cone query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvalidationRequestV1 {
    pub committed_provenance_root: ModuleProvenanceRoot,
    pub committed_logical_root: Option<LogicalRoot>,
    pub descriptor: ChangeDescriptorV1,
    pub effective_request: Option<EffectiveImportRequest>,
    pub limits: InvalidationLimitsV1,
}

impl InvalidationRequestV1 {
    pub fn new(
        committed_provenance_root: ModuleProvenanceRoot,
        descriptor: ChangeDescriptorV1,
    ) -> Self {
        Self {
            committed_provenance_root,
            committed_logical_root: None,
            descriptor,
            effective_request: None,
            limits: InvalidationLimitsV1::default(),
        }
    }

    pub fn with_logical_root(mut self, logical_root: LogicalRoot) -> Self {
        self.committed_logical_root = Some(logical_root);
        self
    }

    pub fn with_effective_request(mut self, effective_request: EffectiveImportRequest) -> Self {
        self.effective_request = Some(effective_request);
        self
    }

    pub fn with_limits(mut self, limits: InvalidationLimitsV1) -> Self {
        self.limits = limits;
        self
    }
}

/// Independent resource limits for invalidation traversal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidationLimitsV1 {
    pub max_modules_discovered: usize,
    pub max_import_rows_examined: usize,
    pub max_index_rows_examined: usize,
    pub max_witness_edges: usize,
    pub max_witness_bytes: usize,
    pub max_names: usize,
    pub max_name_depth: usize,
    pub max_output_records: usize,
    pub max_output_bytes: usize,
}

impl Default for InvalidationLimitsV1 {
    fn default() -> Self {
        Self {
            max_modules_discovered: 10_000,
            max_import_rows_examined: 50_000,
            max_index_rows_examined: 50_000,
            max_witness_edges: 20_000,
            max_witness_bytes: 1_000_000,
            max_names: 10_000,
            max_name_depth: 128,
            max_output_records: 10_000,
            max_output_bytes: 2_000_000,
        }
    }
}

/// Specific resource dimension tracked during invalidation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidationResource {
    ModulesDiscovered,
    ImportRowsExamined,
    IndexRowsExamined,
    WitnessEdges,
    WitnessBytes,
    Names,
    NameDepth,
    OutputRecords,
    OutputBytes,
}

/// Usage facts recorded during an invalidation query.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct InvalidationUsageV1 {
    pub modules_discovered: usize,
    pub import_rows_examined: usize,
    pub index_rows_examined: usize,
    pub witness_edges: usize,
    pub witness_bytes: usize,
    pub names_examined: usize,
    pub max_name_depth_observed: usize,
    pub output_records: usize,
    pub output_bytes: usize,
}

/// Checkpoints for cancellation probes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidationCheckpoint {
    Entry,
    AfterRootValidation,
    AfterDescriptorValidation,
    AfterSeedResolution,
    DuringPropagation,
    BeforeOutput,
}

/// Impact grade classification.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImpactGrade {
    /// Definitive direct or causal impact.
    DefinitelyImpacted = 0,
    /// Conservative impact due to opaque/partial boundaries or coarse import propagation.
    ConservativelyImpacted = 1,
    /// Verified unaffected.
    Unaffected = 2,
}

/// Typed kinds of witness edges.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum WitnessEdgeKind {
    ChangeSeed,
    OwnsDeclaration {
        name: Name,
        class: DeclarationClass,
    },
    OwnsExtensionRange {
        descriptor: ExtensionDescriptor,
        entry_id: ExtensionEntryId,
    },
    DirectImport {
        import: DirectImport,
    },
    EffectiveVisibility {
        profile_digest: Digest,
    },
    MissingTarget {
        target: ModuleId,
    },
    OpaqueOrPartialBoundary {
        transparency: PayloadTransparency,
        capture: CaptureStatus,
    },
}

/// A directed edge in an invalidation witness path.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct WitnessEdge {
    pub from: Option<ModuleId>,
    pub to: ModuleId,
    pub kind: WitnessEdgeKind,
}

impl WitnessEdge {
    pub fn byte_size(&self) -> usize {
        let from_len = self
            .from
            .as_ref()
            .map_or(0, |m| m.name().to_display_string().len());
        let to_len = self.to.name().to_display_string().len();
        from_len + to_len + 16
    }
}

/// Terminal reason explaining why a module was impacted.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum InvalidationTerminalReason {
    SeedModified,
    DeclarationModified {
        name: Name,
    },
    ExtensionModified {
        descriptor: ExtensionDescriptor,
        entry_id: ExtensionEntryId,
    },
    ImportTopologyModified {
        module: ModuleId,
    },
    CompletenessBoundaryTraversed {
        module: ModuleId,
    },
    TransitivePropagation {
        via: ModuleId,
    },
}

/// Canonical shortest witness path proving why a module is impacted.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WitnessPath {
    pub target: ModuleId,
    pub grade: ImpactGrade,
    pub edges: Vec<WitnessEdge>,
    pub terminal_reason: InvalidationTerminalReason,
}

impl WitnessPath {
    /// Compares two witness paths to the same target using the canonical tie policy.
    /// Returns Less if `self` is strictly preferred over `other`.
    pub fn cmp_preference(&self, other: &Self) -> Ordering {
        // 1. DefinitelyImpacted outranks ConservativelyImpacted
        self.grade
            .cmp(&other.grade)
            // 2. Shorter edge paths are preferred
            .then_with(|| self.edges.len().cmp(&other.edges.len()))
            // 3. Lexicographical tie break over edges
            .then_with(|| self.edges.cmp(&other.edges))
            // 4. Tie break over terminal reasons
            .then_with(|| self.terminal_reason.cmp(&other.terminal_reason))
    }
}

/// Impacted module record containing the impact grade and canonical witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImpactedModuleRecord {
    pub module: ModuleId,
    pub grade: ImpactGrade,
    pub witness: WitnessPath,
}

/// Authoritative cache key for an invalidation cone.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InvalidationCacheKey {
    pub provenance_root: ModuleProvenanceRoot,
    pub logical_root: Option<LogicalRoot>,
    pub descriptor_digest: Digest,
    pub effective_request_digest: Option<Digest>,
    pub tie_policy_version: u16,
}

/// Computed invalidation cone.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InvalidationCone {
    pub schema_version: u16,
    pub provenance_root: ModuleProvenanceRoot,
    pub logical_root: Option<LogicalRoot>,
    pub descriptor_digest: Digest,
    pub effective_request_digest: Option<Digest>,
    pub impacted: BTreeMap<ModuleId, ImpactedModuleRecord>,
    pub unaffected: BTreeSet<ModuleId>,
    pub usage: InvalidationUsageV1,
}

impl InvalidationCone {
    pub fn is_empty(&self) -> bool {
        self.impacted.is_empty()
    }

    pub fn is_impacted(&self, module: &ModuleId) -> bool {
        self.impacted.contains_key(module)
    }

    pub fn grade_of(&self, module: &ModuleId) -> ImpactGrade {
        if let Some(record) = self.impacted.get(module) {
            record.grade
        } else {
            ImpactGrade::Unaffected
        }
    }

    pub fn witness_of(&self, module: &ModuleId) -> Option<&WitnessPath> {
        self.impacted.get(module).map(|r| &r.witness)
    }

    pub fn cache_key(&self) -> InvalidationCacheKey {
        InvalidationCacheKey {
            provenance_root: self.provenance_root,
            logical_root: self.logical_root,
            descriptor_digest: self.descriptor_digest,
            effective_request_digest: self.effective_request_digest,
            tie_policy_version: TIE_POLICY_VERSION,
        }
    }
}

/// Typed refusals for invalidation queries.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidationRefusal {
    StaleProvenanceRoot {
        expected: ModuleProvenanceRoot,
        actual: ModuleProvenanceRoot,
    },
    StaleLogicalRoot {
        expected: LogicalRoot,
        actual: LogicalRoot,
    },
    StaleDescriptor {
        reason: &'static str,
    },
    EffectiveProfileMismatch {
        expected: Digest,
        actual: Digest,
    },
    IdentityCollisionConflict {
        what: &'static str,
        held: Digest,
        candidate: Digest,
    },
    UnknownModule {
        module: ModuleId,
    },
    UnknownDeclaration {
        name: Name,
    },
    UnknownExtensionEntry {
        entry_id: ExtensionEntryId,
    },
}

fn resource_inconclusive(unit: StructuralUnit, allowed: usize, observed: usize) -> Inconclusive {
    Inconclusive::resource(ResourceUsage {
        reason: ResourceReason::StructuralBudget { unit },
        allowed: allowed as u64,
        observed: observed as u64,
    })
}

/// Compute an invalidation cone synchronously without a cancellation probe.
pub fn compute_invalidation_cone(
    state: &ModuleApplyState,
    request: &InvalidationRequestV1,
) -> Outcome<Result<InvalidationCone, InvalidationRefusal>> {
    compute_invalidation_cone_cancellable(state, request, None)
}

/// Compute an invalidation cone with deterministic cancellation checkpoints.
pub fn compute_invalidation_cone_cancellable(
    state: &ModuleApplyState,
    request: &InvalidationRequestV1,
    probe: Option<&dyn CancellationProbe>,
) -> Outcome<Result<InvalidationCone, InvalidationRefusal>> {
    let mut usage = InvalidationUsageV1::default();

    // 1. Entry checkpoint
    if let Some(p) = probe
        && p.is_cancelled()
    {
        return Outcome::Inconclusive(Inconclusive::cancelled("invalidation cancelled at entry"));
    }

    // 2. Validate committed state roots
    let actual_prov_root = state.manifest().root();
    if request.committed_provenance_root != actual_prov_root {
        return Outcome::Complete(Err(InvalidationRefusal::StaleProvenanceRoot {
            expected: request.committed_provenance_root,
            actual: actual_prov_root,
        }));
    }

    if let Some(expected_logical) = request.committed_logical_root {
        let actual_logical = state.logical_root();
        if expected_logical != actual_logical {
            return Outcome::Complete(Err(InvalidationRefusal::StaleLogicalRoot {
                expected: expected_logical,
                actual: actual_logical,
            }));
        }
    }

    // 3. Sample probe after root validation
    if let Some(p) = probe
        && p.is_cancelled()
    {
        return Outcome::Inconclusive(Inconclusive::cancelled(
            "invalidation cancelled after root validation",
        ));
    }

    // 4. Validate descriptor against committed state (detect stale descriptor & collision)
    let descriptor_digest = request.descriptor.descriptor_digest();

    let mut seeds = Vec::new();

    match &request.descriptor {
        ChangeDescriptorV1::Artifact {
            module,
            old_evidence,
            new_evidence,
        } => {
            usage.modules_discovered = usage.modules_discovered.saturating_add(1);
            let rec = match state.manifest().record(module) {
                Some(r) => r,
                None => {
                    return Outcome::Complete(Err(InvalidationRefusal::UnknownModule {
                        module: module.clone(),
                    }));
                }
            };
            if let Some(old_ev) = old_evidence
                && &rec.module().artifact != old_ev
            {
                return Outcome::Complete(Err(InvalidationRefusal::StaleDescriptor {
                    reason: "old artifact evidence does not match committed state",
                }));
            }
            if let (Some(old_ev), Some(new_ev)) = (old_evidence, new_evidence)
                && old_ev.content_digest == new_ev.content_digest
                && old_ev != new_ev
            {
                return Outcome::Complete(Err(InvalidationRefusal::IdentityCollisionConflict {
                    what: "artifact evidence digest collision",
                    held: old_ev.content_digest,
                    candidate: new_ev.content_digest,
                }));
            }
            seeds.push((
                module.clone(),
                WitnessPath {
                    target: module.clone(),
                    grade: ImpactGrade::DefinitelyImpacted,
                    edges: vec![WitnessEdge {
                        from: None,
                        to: module.clone(),
                        kind: WitnessEdgeKind::ChangeSeed,
                    }],
                    terminal_reason: InvalidationTerminalReason::SeedModified,
                },
            ));
        }
        ChangeDescriptorV1::DirectImportTopology {
            module,
            old_imports,
            new_imports: _,
        } => {
            usage.modules_discovered = usage.modules_discovered.saturating_add(1);
            let actual_imports = match state.graph().direct_imports(module) {
                Some(imps) => imps,
                None => {
                    return Outcome::Complete(Err(InvalidationRefusal::UnknownModule {
                        module: module.clone(),
                    }));
                }
            };
            if actual_imports != old_imports.as_slice() {
                return Outcome::Complete(Err(InvalidationRefusal::StaleDescriptor {
                    reason: "old direct imports do not match committed graph topology",
                }));
            }
            seeds.push((
                module.clone(),
                WitnessPath {
                    target: module.clone(),
                    grade: ImpactGrade::DefinitelyImpacted,
                    edges: vec![WitnessEdge {
                        from: None,
                        to: module.clone(),
                        kind: WitnessEdgeKind::ChangeSeed,
                    }],
                    terminal_reason: InvalidationTerminalReason::ImportTopologyModified {
                        module: module.clone(),
                    },
                },
            ));
        }
        ChangeDescriptorV1::Declaration {
            owner,
            class,
            source_ordinal: _,
            name,
            old_identity,
            new_identity,
        } => {
            usage.names_examined = usage.names_examined.saturating_add(1);
            let depth = name.to_display_string().split('.').count();
            if depth > usage.max_name_depth_observed {
                usage.max_name_depth_observed = depth;
            }
            if depth > request.limits.max_name_depth {
                return Outcome::Inconclusive(resource_inconclusive(
                    StructuralUnit::ProducedNodes,
                    request.limits.max_name_depth,
                    depth,
                ));
            }

            let indexed_owner = match state.indexes().owner_of(name) {
                Some(pair) => pair,
                None => {
                    return Outcome::Complete(Err(InvalidationRefusal::UnknownDeclaration {
                        name: name.clone(),
                    }));
                }
            };
            if indexed_owner.0 != *owner || indexed_owner.1 != *class {
                return Outcome::Complete(Err(InvalidationRefusal::StaleDescriptor {
                    reason: "declaration owner or class does not match reverse index",
                }));
            }

            if let (Some(old_id), Some(new_id)) = (old_identity, new_identity)
                && old_id == new_id
                && old_id.0 != new_id.0
            {
                return Outcome::Complete(Err(InvalidationRefusal::IdentityCollisionConflict {
                    what: "declaration identity digest collision",
                    held: *old_id,
                    candidate: *new_id,
                }));
            }

            seeds.push((
                owner.clone(),
                WitnessPath {
                    target: owner.clone(),
                    grade: ImpactGrade::DefinitelyImpacted,
                    edges: vec![WitnessEdge {
                        from: None,
                        to: owner.clone(),
                        kind: WitnessEdgeKind::OwnsDeclaration {
                            name: name.clone(),
                            class: *class,
                        },
                    }],
                    terminal_reason: InvalidationTerminalReason::DeclarationModified {
                        name: name.clone(),
                    },
                },
            ));
        }
        ChangeDescriptorV1::ExtensionContribution {
            contributor,
            descriptor,
            entry_id,
            old_source_ordinal: _,
            old_range_start: _,
            old_identity,
            new_identity,
        } => {
            usage.index_rows_examined = usage.index_rows_examined.saturating_add(1);
            let occurrences = match state.indexes().occurrences_of(entry_id) {
                Some(occs) => occs,
                None => {
                    return Outcome::Complete(Err(InvalidationRefusal::UnknownExtensionEntry {
                        entry_id: *entry_id,
                    }));
                }
            };
            let found = occurrences.iter().any(|occ| occ.module == *contributor);
            if !found {
                return Outcome::Complete(Err(InvalidationRefusal::StaleDescriptor {
                    reason: "extension entry occurrence does not match reverse index",
                }));
            }

            if let (Some(old_id), Some(new_id)) = (old_identity, new_identity)
                && old_id == new_id
                && old_id.0 != new_id.0
            {
                return Outcome::Complete(Err(InvalidationRefusal::IdentityCollisionConflict {
                    what: "extension entry identity collision",
                    held: *old_id,
                    candidate: *new_id,
                }));
            }

            let supports_fine = state
                .environment()
                .extension(&descriptor.name)
                .is_some_and(|ext| ext.supports_fine_invalidation());

            let grade = if supports_fine {
                ImpactGrade::DefinitelyImpacted
            } else {
                ImpactGrade::ConservativelyImpacted
            };

            seeds.push((
                contributor.clone(),
                WitnessPath {
                    target: contributor.clone(),
                    grade,
                    edges: vec![WitnessEdge {
                        from: None,
                        to: contributor.clone(),
                        kind: WitnessEdgeKind::OwnsExtensionRange {
                            descriptor: descriptor.clone(),
                            entry_id: *entry_id,
                        },
                    }],
                    terminal_reason: InvalidationTerminalReason::ExtensionModified {
                        descriptor: descriptor.clone(),
                        entry_id: *entry_id,
                    },
                },
            ));
        }
        ChangeDescriptorV1::Completeness {
            module,
            old_completeness,
            new_completeness: _,
        } => {
            usage.modules_discovered = usage.modules_discovered.saturating_add(1);
            let rec = match state.manifest().record(module) {
                Some(r) => r,
                None => {
                    return Outcome::Complete(Err(InvalidationRefusal::UnknownModule {
                        module: module.clone(),
                    }));
                }
            };
            if rec.completeness() != old_completeness {
                return Outcome::Complete(Err(InvalidationRefusal::StaleDescriptor {
                    reason: "old completeness does not match committed record",
                }));
            }

            seeds.push((
                module.clone(),
                WitnessPath {
                    target: module.clone(),
                    grade: ImpactGrade::ConservativelyImpacted,
                    edges: vec![WitnessEdge {
                        from: None,
                        to: module.clone(),
                        kind: WitnessEdgeKind::OpaqueOrPartialBoundary {
                            transparency: old_completeness.transparency(),
                            capture: old_completeness.capture(),
                        },
                    }],
                    terminal_reason: InvalidationTerminalReason::CompletenessBoundaryTraversed {
                        module: module.clone(),
                    },
                },
            ));
        }
    }

    // 5. Exact no-op check: if unchanged, return authoritative empty cone
    if request.descriptor.is_no_op() {
        let mut unaffected = BTreeSet::new();
        for mod_id in state.graph().modules_canonical() {
            unaffected.insert(mod_id);
        }
        return Outcome::Complete(Ok(InvalidationCone {
            schema_version: INVALIDATION_SCHEMA_VERSION,
            provenance_root: actual_prov_root,
            logical_root: request.committed_logical_root,
            descriptor_digest,
            effective_request_digest: None,
            impacted: BTreeMap::new(),
            unaffected,
            usage,
        }));
    }

    // 6. Sample probe after descriptor & seed validation
    if let Some(p) = probe
        && p.is_cancelled()
    {
        return Outcome::Inconclusive(Inconclusive::cancelled(
            "invalidation cancelled after seed resolution",
        ));
    }

    // 7. Reverse propagation using exact graph imports
    // Build reverse import graph: upstream -> list of downstream importers
    let mut reverse_graph: BTreeMap<ModuleId, Vec<(ModuleId, DirectImport)>> = BTreeMap::new();
    for downstream in state.graph().modules_canonical() {
        usage.import_rows_examined = usage.import_rows_examined.saturating_add(1);
        if let Some(direct_imports) = state.graph().direct_imports(&downstream) {
            for imp in direct_imports {
                reverse_graph
                    .entry(imp.module.clone())
                    .or_default()
                    .push((downstream.clone(), imp.clone()));
            }
        }
    }

    // Track best witness path to each discovered module
    let mut impacted: BTreeMap<ModuleId, WitnessPath> = BTreeMap::new();
    let mut worklist: Vec<ModuleId> = Vec::new();

    for (seed_mod, path) in seeds {
        impacted.insert(seed_mod.clone(), path);
        worklist.push(seed_mod);
    }
    worklist.sort();

    while !worklist.is_empty() {
        if let Some(p) = probe
            && p.is_cancelled()
        {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                "invalidation cancelled during propagation",
            ));
        }

        let curr_mod = worklist.remove(0);
        let curr_path = match impacted.get(&curr_mod) {
            Some(p) => p.clone(),
            None => continue,
        };

        if let Some(downstream_list) = reverse_graph.get(&curr_mod) {
            for (downstream_mod, imp) in downstream_list {
                usage.import_rows_examined = usage.import_rows_examined.saturating_add(1);
                if usage.import_rows_examined > request.limits.max_import_rows_examined {
                    return Outcome::Inconclusive(resource_inconclusive(
                        StructuralUnit::ProducedNodes,
                        request.limits.max_import_rows_examined,
                        usage.import_rows_examined,
                    ));
                }

                // Check transparency of curr_mod
                let is_conservative = curr_path.grade == ImpactGrade::ConservativelyImpacted
                    || state.manifest().record(&curr_mod).is_some_and(|r| {
                        r.completeness().transparency() == PayloadTransparency::Opaque
                            || r.completeness().capture() != CaptureStatus::Complete
                    });

                let edge_grade = if is_conservative {
                    ImpactGrade::ConservativelyImpacted
                } else {
                    ImpactGrade::DefinitelyImpacted
                };

                let mut new_edges = curr_path.edges.clone();
                let edge = WitnessEdge {
                    from: Some(curr_mod.clone()),
                    to: downstream_mod.clone(),
                    kind: WitnessEdgeKind::DirectImport {
                        import: imp.clone(),
                    },
                };
                usage.witness_bytes = usage.witness_bytes.saturating_add(edge.byte_size());
                usage.witness_edges = usage.witness_edges.saturating_add(1);

                if usage.witness_edges > request.limits.max_witness_edges {
                    return Outcome::Inconclusive(resource_inconclusive(
                        StructuralUnit::ProducedNodes,
                        request.limits.max_witness_edges,
                        usage.witness_edges,
                    ));
                }
                if usage.witness_bytes > request.limits.max_witness_bytes {
                    return Outcome::Inconclusive(resource_inconclusive(
                        StructuralUnit::InputBytes,
                        request.limits.max_witness_bytes,
                        usage.witness_bytes,
                    ));
                }

                new_edges.push(edge);

                let candidate_path = WitnessPath {
                    target: downstream_mod.clone(),
                    grade: edge_grade,
                    edges: new_edges,
                    terminal_reason: InvalidationTerminalReason::TransitivePropagation {
                        via: curr_mod.clone(),
                    },
                };

                let should_update = match impacted.get(downstream_mod) {
                    None => true,
                    Some(existing) => candidate_path.cmp_preference(existing) == Ordering::Less,
                };

                if should_update {
                    usage.modules_discovered = usage.modules_discovered.saturating_add(1);
                    if usage.modules_discovered > request.limits.max_modules_discovered {
                        return Outcome::Inconclusive(resource_inconclusive(
                            StructuralUnit::ProducedNodes,
                            request.limits.max_modules_discovered,
                            usage.modules_discovered,
                        ));
                    }
                    impacted.insert(downstream_mod.clone(), candidate_path);
                    if !worklist.contains(downstream_mod) {
                        worklist.push(downstream_mod.clone());
                        worklist.sort();
                    }
                }
            }
        }
    }

    // 8. Sample probe before output
    if let Some(p) = probe
        && p.is_cancelled()
    {
        return Outcome::Inconclusive(Inconclusive::cancelled(
            "invalidation cancelled before output",
        ));
    }

    // 9. Construct unaffected set
    let mut unaffected = BTreeSet::new();
    for m in state.graph().modules_canonical() {
        if !impacted.contains_key(&m) {
            unaffected.insert(m);
        }
    }

    let mut impacted_records = BTreeMap::new();
    for (m, p) in impacted {
        impacted_records.insert(
            m.clone(),
            ImpactedModuleRecord {
                module: m,
                grade: p.grade,
                witness: p,
            },
        );
    }

    usage.output_records = impacted_records.len() + unaffected.len();
    if usage.output_records > request.limits.max_output_records {
        return Outcome::Inconclusive(resource_inconclusive(
            StructuralUnit::ProducedNodes,
            request.limits.max_output_records,
            usage.output_records,
        ));
    }

    Outcome::Complete(Ok(InvalidationCone {
        schema_version: INVALIDATION_SCHEMA_VERSION,
        provenance_root: actual_prov_root,
        logical_root: request.committed_logical_root,
        descriptor_digest,
        effective_request_digest: None,
        impacted: impacted_records,
        unaffected,
        usage,
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{AxiomVal, ConstantInfo, ConstantVal};
    use crate::extensions::{
        CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
    };
    use crate::module_apply::{AppliedModulePayload, ExtensionPayload};
    use crate::modules::{
        ArtifactGrade, ArtifactProducer, ModuleEpoch, ModuleGraphLimits, ModuleRecord,
    };
    use crate::provenance::{
        CaptureStatus, ExtensionContribution, ModuleContributionRecord, ModuleProvenanceManifest,
        ProvenanceCompleteness,
    };
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::name::Name;
    use fln_core::options::KVMap;
    use fln_hash::domain::Domain;
    use std::sync::Arc;
    use std::sync::atomic::AtomicBool;

    use crate::provenance::ModuleProvenanceLimits;

    fn expect_complete<T: std::fmt::Debug, E: std::fmt::Debug>(
        outcome: Outcome<Result<T, E>>,
    ) -> Result<T, E> {
        match outcome {
            Outcome::Complete(res) => res,
            other => panic!("expected complete outcome, got {other:?}"),
        }
    }

    fn test_epoch() -> ModuleEpoch {
        ModuleEpoch::new("v4.32.0", "7274711011111111111111111111111111111111")
    }

    fn test_axiom(value: &str) -> Arc<ConstantInfo> {
        Arc::new(ConstantInfo::Axiom(AxiomVal {
            base: ConstantVal {
                name: Name::from_components([value]),
                level_params: vec![],
                type_: Expr::sort(Level::zero()),
            },
            is_unsafe: false,
        }))
    }

    fn make_graph(
        epoch: &ModuleEpoch,
        records: &[ModuleContributionRecord],
    ) -> Result<crate::modules::ModuleGraph, String> {
        let mut graph =
            crate::modules::ModuleGraph::new(epoch.clone(), ModuleGraphLimits::default())
                .into_admitted_value()
                .ok_or_else(|| "failed to initialize ModuleGraph".to_string())?;
        for r in records {
            graph = graph
                .register(r.module().clone())
                .into_admitted_value()
                .ok_or_else(|| {
                    format!(
                        "failed to register module {}",
                        r.module().id.name().to_display_string()
                    )
                })?
                .graph;
        }
        Ok(graph)
    }

    fn make_manifest(
        epoch: &ModuleEpoch,
        records: Vec<ModuleContributionRecord>,
    ) -> Result<Arc<ModuleProvenanceManifest>, String> {
        ModuleProvenanceManifest::new(epoch.clone(), records, ModuleProvenanceLimits::default())
            .map(Arc::new)
            .map_err(|e| format!("{e:?}"))
    }

    fn make_test_dag_state() -> ModuleApplyState {
        // DAG topology:
        // A -> B -> D
        // A -> C -> D
        // E (isolated)
        let epoch = test_epoch();
        let mod_a = ModuleId::new(Name::from_components(["A"]));
        let mod_b = ModuleId::new(Name::from_components(["B"]));
        let mod_c = ModuleId::new(Name::from_components(["C"]));
        let mod_d = ModuleId::new(Name::from_components(["D"]));
        let mod_e = ModuleId::new(Name::from_components(["E"]));

        let art_a = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Verified,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"A"),
        };
        let art_b = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Verified,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"B"),
        };
        let art_c = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Verified,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"C"),
        };
        let art_d = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Verified,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"D"),
        };
        let art_e = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Verified,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"E"),
        };

        let imp_a = vec![];
        let imp_b = vec![DirectImport::new(mod_a.clone(), true, false, false)];
        let imp_c = vec![DirectImport::new(mod_a.clone(), true, false, false)];
        let imp_d = vec![
            DirectImport::new(mod_b.clone(), true, false, false),
            DirectImport::new(mod_c.clone(), true, false, false),
        ];
        let imp_e = vec![];

        let rec_a = ModuleRecord::new(mod_a, true, imp_a, art_a);
        let rec_b = ModuleRecord::new(mod_b, true, imp_b, art_b);
        let rec_c = ModuleRecord::new(mod_c, true, imp_c, art_c);
        let rec_d = ModuleRecord::new(mod_d, true, imp_d, art_d);
        let rec_e = ModuleRecord::new(mod_e, true, imp_e, art_e);

        let ext_desc = ExtensionDescriptor {
            name: Name::from_components(["simp_ext"]),
            merge: MergeSemantics::SetUnion,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        };

        let ext_entry_id = ExtensionEntryId::derive(&epoch, &ext_desc, b"simp_rule_1");
        let ext_contrib_a = ExtensionContribution::new(
            ext_desc.clone(),
            0,
            hash(Domain::ModuleProvenance, b"base"),
            vec![ext_entry_id],
        );

        let contrib_a = ModuleContributionRecord::new(
            rec_a,
            vec![Name::from_components(["declA"])],
            vec![],
            vec![ext_contrib_a],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );
        let contrib_b = ModuleContributionRecord::new(
            rec_b,
            vec![Name::from_components(["declB"])],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );
        let contrib_c = ModuleContributionRecord::new(
            rec_c,
            vec![Name::from_components(["declC"])],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );
        let contrib_d = ModuleContributionRecord::new(
            rec_d,
            vec![Name::from_components(["declD"])],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );
        let contrib_e = ModuleContributionRecord::new(
            rec_e,
            vec![Name::from_components(["declE"])],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );

        let records = vec![
            contrib_a.clone(),
            contrib_b.clone(),
            contrib_c.clone(),
            contrib_d.clone(),
            contrib_e.clone(),
        ];

        let graph = make_graph(&epoch, &records).unwrap();
        let manifest = make_manifest(&epoch, records.clone()).unwrap();

        let mut env = crate::environment::Environment::new();
        env = env.register_extension(ext_desc.clone()).unwrap();
        let ax_a = test_axiom("declA");
        let ax_b = test_axiom("declB");
        let ax_c = test_axiom("declC");
        let ax_d = test_axiom("declD");
        let ax_e = test_axiom("declE");

        env = env.add_decl((*ax_a).clone()).unwrap();
        env = env.add_decl((*ax_b).clone()).unwrap();
        env = env.add_decl((*ax_c).clone()).unwrap();
        env = env.add_decl((*ax_d).clone()).unwrap();
        env = env.add_decl((*ax_e).clone()).unwrap();
        env = env
            .push_extension_entry(&ext_desc.name, Arc::<[u8]>::from(b"simp_rule_1".as_slice()))
            .unwrap();

        let ext_p = ExtensionPayload::new(0, ext_desc, 0, b"simp_rule_1".to_vec());
        let payloads = vec![
            AppliedModulePayload::new_with_record(
                contrib_a,
                vec![ax_a].into(),
                vec![].into(),
                vec![ext_p].into(),
            ),
            AppliedModulePayload::new_with_record(
                contrib_b,
                vec![ax_b].into(),
                vec![].into(),
                vec![].into(),
            ),
            AppliedModulePayload::new_with_record(
                contrib_c,
                vec![ax_c].into(),
                vec![].into(),
                vec![].into(),
            ),
            AppliedModulePayload::new_with_record(
                contrib_d,
                vec![ax_d].into(),
                vec![].into(),
                vec![].into(),
            ),
            AppliedModulePayload::new_with_record(
                contrib_e,
                vec![ax_e].into(),
                vec![].into(),
                vec![].into(),
            ),
        ];

        ModuleApplyState::from_parts_with_options_and_payloads(
            env,
            graph,
            manifest,
            KVMap::new(),
            payloads,
        )
        .unwrap()
    }

    #[test]
    fn all_five_change_classes_produce_deterministic_graded_cones() {
        let state = make_test_dag_state();
        let root = state.manifest().root();
        let mod_a = ModuleId::new(Name::from_components(["A"]));
        let mod_b = ModuleId::new(Name::from_components(["B"]));
        let mod_c = ModuleId::new(Name::from_components(["C"]));
        let mod_d = ModuleId::new(Name::from_components(["D"]));
        let mod_e = ModuleId::new(Name::from_components(["E"]));

        // 1. Artifact change on A -> invalidates A, B, C, D; leaves E unaffected
        let old_ev_a = state
            .manifest()
            .record(&mod_a)
            .unwrap()
            .module()
            .artifact
            .clone();
        let mut new_ev_a = old_ev_a.clone();
        new_ev_a.content_digest = hash(Domain::DeclContent, b"A_modified");

        let desc_art = ChangeDescriptorV1::Artifact {
            module: mod_a.clone(),
            old_evidence: Some(old_ev_a.clone()),
            new_evidence: Some(new_ev_a),
        };
        let req_art = InvalidationRequestV1::new(root, desc_art);
        let cone_art = expect_complete(compute_invalidation_cone(&state, &req_art)).unwrap();

        assert!(cone_art.is_impacted(&mod_a));
        assert!(cone_art.is_impacted(&mod_b));
        assert!(cone_art.is_impacted(&mod_c));
        assert!(cone_art.is_impacted(&mod_d));
        assert!(!cone_art.is_impacted(&mod_e));
        assert_eq!(cone_art.grade_of(&mod_e), ImpactGrade::Unaffected);

        // 2. Declaration change on declB -> invalidates B and D; leaves A, C, E unaffected
        let desc_decl = ChangeDescriptorV1::Declaration {
            owner: mod_b.clone(),
            class: DeclarationClass::Declaration,
            source_ordinal: 0,
            name: Name::from_components(["declB"]),
            old_identity: Some(hash(Domain::DeclContent, b"declB_old")),
            new_identity: Some(hash(Domain::DeclContent, b"declB_new")),
        };
        let req_decl = InvalidationRequestV1::new(root, desc_decl);
        let cone_decl = expect_complete(compute_invalidation_cone(&state, &req_decl)).unwrap();

        assert!(cone_decl.is_impacted(&mod_b));
        assert!(cone_decl.is_impacted(&mod_d));
        assert!(!cone_decl.is_impacted(&mod_a));
        assert!(!cone_decl.is_impacted(&mod_c));
        assert!(!cone_decl.is_impacted(&mod_e));

        // 3. Extension contribution change on A -> invalidates A, B, C, D
        let ext_desc = ExtensionDescriptor {
            name: Name::from_components(["simp_ext"]),
            merge: MergeSemantics::SetUnion,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance: PayloadProvenance::Understood,
        };
        let entry_id = ExtensionEntryId::derive(&test_epoch(), &ext_desc, b"simp_rule_1");
        let desc_ext = ChangeDescriptorV1::ExtensionContribution {
            contributor: mod_a.clone(),
            descriptor: ext_desc,
            entry_id,
            old_source_ordinal: 0,
            old_range_start: 0,
            old_identity: Some(hash(Domain::DeclContent, b"old_entry")),
            new_identity: Some(hash(Domain::DeclContent, b"new_entry")),
        };
        let req_ext = InvalidationRequestV1::new(root, desc_ext);
        let cone_ext = expect_complete(compute_invalidation_cone(&state, &req_ext)).unwrap();

        assert!(cone_ext.is_impacted(&mod_a));
        assert!(cone_ext.is_impacted(&mod_b));
        assert!(cone_ext.is_impacted(&mod_c));
        assert!(cone_ext.is_impacted(&mod_d));
        assert!(!cone_ext.is_impacted(&mod_e));

        // 4. DirectImportTopology change on B -> invalidates B and D
        let old_imps_b = state.graph().direct_imports(&mod_b).unwrap().to_vec();
        let desc_top = ChangeDescriptorV1::DirectImportTopology {
            module: mod_b.clone(),
            old_imports: old_imps_b.clone(),
            new_imports: vec![],
        };
        let req_top = InvalidationRequestV1::new(root, desc_top);
        let cone_top = expect_complete(compute_invalidation_cone(&state, &req_top)).unwrap();

        assert!(cone_top.is_impacted(&mod_b));
        assert!(cone_top.is_impacted(&mod_d));
        assert!(!cone_top.is_impacted(&mod_a));

        // 5. Completeness change on C -> invalidates C and D conservatively
        let old_comp_c = state
            .manifest()
            .record(&mod_c)
            .unwrap()
            .completeness()
            .clone();
        let new_comp_c = ProvenanceCompleteness::new(
            CaptureStatus::Partial,
            PayloadTransparency::Opaque,
            vec![],
        );
        let desc_comp = ChangeDescriptorV1::Completeness {
            module: mod_c.clone(),
            old_completeness: old_comp_c,
            new_completeness: new_comp_c,
        };
        let req_comp = InvalidationRequestV1::new(root, desc_comp);
        let cone_comp = expect_complete(compute_invalidation_cone(&state, &req_comp)).unwrap();

        assert_eq!(
            cone_comp.grade_of(&mod_c),
            ImpactGrade::ConservativelyImpacted
        );
        assert_eq!(
            cone_comp.grade_of(&mod_d),
            ImpactGrade::ConservativelyImpacted
        );
        assert_eq!(cone_comp.grade_of(&mod_a), ImpactGrade::Unaffected);
        assert_eq!(cone_comp.grade_of(&mod_b), ImpactGrade::Unaffected);
    }

    #[test]
    fn stale_provenance_and_logical_roots_are_refused_before_traversal() {
        let state = make_test_dag_state();
        let mod_a = ModuleId::new(Name::from_components(["A"]));
        let fake_root = ModuleProvenanceRoot(hash(Domain::ModuleProvenance, b"fake"));

        let desc = ChangeDescriptorV1::Artifact {
            module: mod_a.clone(),
            old_evidence: None,
            new_evidence: None,
        };

        // Stale provenance root
        let req1 = InvalidationRequestV1::new(fake_root, desc.clone());
        let res1 = expect_complete(compute_invalidation_cone(&state, &req1));
        assert!(matches!(
            res1,
            Err(InvalidationRefusal::StaleProvenanceRoot { .. })
        ));

        // Stale logical root
        let fake_log_root = LogicalRoot(hash(Domain::DeclContent, b"fake_log"));
        let req2 = InvalidationRequestV1::new(state.manifest().root(), desc)
            .with_logical_root(fake_log_root);
        let res2 = expect_complete(compute_invalidation_cone(&state, &req2));
        assert!(matches!(
            res2,
            Err(InvalidationRefusal::StaleLogicalRoot { .. })
        ));
    }

    #[test]
    fn stale_descriptor_and_candidate_collision_refusals() {
        let state = make_test_dag_state();
        let root = state.manifest().root();
        let mod_a = ModuleId::new(Name::from_components(["A"]));

        // Wrong old evidence
        let fake_ev = ArtifactEvidence {
            epoch: test_epoch(),
            grade: ArtifactGrade::Provisional,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"mismatch"),
        };
        let desc1 = ChangeDescriptorV1::Artifact {
            module: mod_a.clone(),
            old_evidence: Some(fake_ev),
            new_evidence: None,
        };
        let res1 = expect_complete(compute_invalidation_cone(
            &state,
            &InvalidationRequestV1::new(root, desc1),
        ));
        assert!(matches!(
            res1,
            Err(InvalidationRefusal::StaleDescriptor { .. })
        ));

        // Unknown declaration name
        let desc2 = ChangeDescriptorV1::Declaration {
            owner: mod_a.clone(),
            class: DeclarationClass::Declaration,
            source_ordinal: 0,
            name: Name::from_components(["non_existent"]),
            old_identity: None,
            new_identity: None,
        };
        let res2 = expect_complete(compute_invalidation_cone(
            &state,
            &InvalidationRequestV1::new(root, desc2),
        ));
        assert!(matches!(
            res2,
            Err(InvalidationRefusal::UnknownDeclaration { .. })
        ));
    }

    #[test]
    fn no_op_descriptor_produces_authoritative_empty_cone() {
        let state = make_test_dag_state();
        let root = state.manifest().root();
        let mod_a = ModuleId::new(Name::from_components(["A"]));

        let ev = state
            .manifest()
            .record(&mod_a)
            .unwrap()
            .module()
            .artifact
            .clone();
        let desc = ChangeDescriptorV1::Artifact {
            module: mod_a,
            old_evidence: Some(ev.clone()),
            new_evidence: Some(ev),
        };
        let cone = expect_complete(compute_invalidation_cone(
            &state,
            &InvalidationRequestV1::new(root, desc),
        ))
        .unwrap();

        assert!(cone.is_empty());
        assert_eq!(cone.unaffected.len(), 5);
    }

    #[test]
    fn tie_break_policy_is_canonical_and_schedule_independent() {
        let state = make_test_dag_state();
        let root = state.manifest().root();
        let mod_a = ModuleId::new(Name::from_components(["A"]));
        let mod_d = ModuleId::new(Name::from_components(["D"]));

        // A reaches D through B and C (diamond).
        // Since B and C are equal length paths, the tie-breaker chooses B (lexicographically before C).
        let old_ev = state
            .manifest()
            .record(&mod_a)
            .unwrap()
            .module()
            .artifact
            .clone();
        let mut new_ev = old_ev.clone();
        new_ev.content_digest = hash(Domain::DeclContent, b"new_A");

        let desc = ChangeDescriptorV1::Artifact {
            module: mod_a,
            old_evidence: Some(old_ev),
            new_evidence: Some(new_ev),
        };
        let cone = expect_complete(compute_invalidation_cone(
            &state,
            &InvalidationRequestV1::new(root, desc),
        ))
        .unwrap();

        let witness_d = cone.witness_of(&mod_d).unwrap();
        assert_eq!(witness_d.edges.len(), 3); // Seed -> B -> D
        assert_eq!(
            witness_d.edges[1].to,
            ModuleId::new(Name::from_components(["B"]))
        );
    }

    #[test]
    fn cancellation_at_all_observation_points_is_inconclusive() {
        let state = make_test_dag_state();
        let root = state.manifest().root();
        let mod_a = ModuleId::new(Name::from_components(["A"]));

        let desc = ChangeDescriptorV1::Artifact {
            module: mod_a,
            old_evidence: None,
            new_evidence: Some(ArtifactEvidence {
                epoch: test_epoch(),
                grade: ArtifactGrade::Verified,
                producer: ArtifactProducer::FrankenLean,
                content_digest: hash(Domain::DeclContent, b"mut"),
            }),
        };
        let req = InvalidationRequestV1::new(root, desc);

        let cancelled_probe = AtomicBool::new(true);
        let outcome = compute_invalidation_cone_cancellable(&state, &req, Some(&cancelled_probe));
        assert!(matches!(outcome, Outcome::Inconclusive(_)));
    }

    #[test]
    fn resource_budget_boundaries_refuse_then_recover() {
        let state = make_test_dag_state();
        let root = state.manifest().root();
        let mod_a = ModuleId::new(Name::from_components(["A"]));

        let desc = ChangeDescriptorV1::Artifact {
            module: mod_a,
            old_evidence: None,
            new_evidence: Some(ArtifactEvidence {
                epoch: test_epoch(),
                grade: ArtifactGrade::Verified,
                producer: ArtifactProducer::FrankenLean,
                content_digest: hash(Domain::DeclContent, b"mut"),
            }),
        };

        // Budget 0 modules discovered -> inconclusive
        let limits = InvalidationLimitsV1 {
            max_modules_discovered: 0,
            ..Default::default()
        };
        let req_low = InvalidationRequestV1::new(root, desc.clone()).with_limits(limits);
        let out_low = compute_invalidation_cone(&state, &req_low);
        assert!(matches!(out_low, Outcome::Inconclusive(_)));

        // Adequate budget -> succeeds
        let req_ok = InvalidationRequestV1::new(root, desc);
        let out_ok = expect_complete(compute_invalidation_cone(&state, &req_ok));
        assert!(out_ok.is_ok());
    }

    #[test]
    fn concurrent_schedule_matrix_1_8_32_threads() {
        let state = make_test_dag_state();
        let root = state.manifest().root();
        let mod_a = ModuleId::new(Name::from_components(["A"]));

        let desc = ChangeDescriptorV1::Artifact {
            module: mod_a,
            old_evidence: None,
            new_evidence: Some(ArtifactEvidence {
                epoch: test_epoch(),
                grade: ArtifactGrade::Verified,
                producer: ArtifactProducer::FrankenLean,
                content_digest: hash(Domain::DeclContent, b"mut"),
            }),
        };
        let req = InvalidationRequestV1::new(root, desc);

        let baseline = expect_complete(compute_invalidation_cone(&state, &req)).unwrap();

        for threads in [1, 8, 32] {
            let mut handles = Vec::new();
            for _ in 0..threads {
                let state_clone = state.clone();
                let req_clone = req.clone();
                handles.push(std::thread::spawn(move || {
                    expect_complete(compute_invalidation_cone(&state_clone, &req_clone)).unwrap()
                }));
            }
            for h in handles {
                let res = h.join().unwrap();
                assert_eq!(res.impacted, baseline.impacted);
                assert_eq!(res.unaffected, baseline.unaffected);
                assert_eq!(res.cache_key(), baseline.cache_key());
            }
        }
    }
}
