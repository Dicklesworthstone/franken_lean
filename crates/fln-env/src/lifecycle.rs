//! Provenance lifecycle integration (plan §7.1; bead `franken_lean-module-provenance-lifecycle-vk2`).
//!
//! This module implements immutable snapshots, paired provenance checkpoints (Suffix and
//! FullJournal modes), preflighted atomic restore plans ([`ProvenanceRestorePlanV1`]),
//! three-way provenance merge plans ([`ProvenanceMergePlanV1`]), and canonical evidence
//! refinement.
//!
//! # Invariants and Law
//!
//! 1. **Snapshot Isolation and Fixed Clone Cost**: A committed [`ModuleApplyState`] is
//!    immutable. Cloning it is O(1) structural sharing across forks.
//! 2. **Preflighted Atomic Plans**: Restore and merge operations compute immutable plans
//!    first. Execution is atomic and revalidates exact root pairs and preconditions before
//!    publication.
//! 3. **Logical Root Invariance under Evidence Refinement**: Enhancing artifact evidence
//!    (e.g., Provisional -> Verified, Reference -> FrankenLean) changes the
//!    [`ModuleProvenanceRoot`] while leaving [`LogicalRoot`] bit-for-bit unchanged.
//! 4. **No Last-Writer-Wins**: Conflicting module origins, overlapping ranges, or incompatible
//!    declarations yield atomic typed conflicts, never silent overwrites.
//! 5. **Deterministic Schedule Independence (FL-INV-01)**: Same input closure yields the exact
//!    same provenance root and plan across 1, 8, and 32 threads.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::sync::Arc;

use fln_core::name::Name;
use fln_core::outcome::{Inconclusive, InternalFault, Outcome};
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::root::LogicalRoot;

use crate::environment::Environment;
use crate::extensions::ExtensionDescriptor;
use crate::module_apply::{AppliedModulePayload, ModuleApplyState};
use crate::modules::{
    ArtifactEvidence, ArtifactGrade, CancellationProbe, ModuleEpoch, ModuleGraph,
    ModuleGraphLimits, ModuleId,
};
use crate::provenance::{
    ExtensionEntryId, ModuleContributionRecord, ModuleProvenanceLimits, ModuleProvenanceManifest,
    ModuleProvenanceRoot, ProvenanceCompleteness,
};

/// Schema version for provenance lifecycle plans and checkpoints.
pub const PROVENANCE_LIFECYCLE_SCHEMA_VERSION: u16 = 1;

/// Mode of a provenance checkpoint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProvenanceCheckpointMode {
    /// Suffix mode: requires exact base provenance and logical roots.
    Suffix,
    /// Full journal mode: self-contained complete records, applicable to compatible target.
    FullJournal,
}

impl fmt::Display for ProvenanceCheckpointMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Suffix => f.write_str("suffix"),
            Self::FullJournal => f.write_str("full-journal"),
        }
    }
}

/// Resource limits for provenance lifecycle operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenanceLifecycleLimits {
    pub max_modules: usize,
    pub max_contributions: usize,
    pub max_extension_entries: usize,
    pub max_index_rows: usize,
    pub max_name_depth: usize,
    pub max_witness_bytes: usize,
    pub max_output_bytes: usize,
    pub max_allocations: usize,
    pub max_work_units: u64,
}

impl Default for ProvenanceLifecycleLimits {
    fn default() -> Self {
        Self {
            max_modules: 16_384,
            max_contributions: 65_536,
            max_extension_entries: 262_144,
            max_index_rows: 524_288,
            max_name_depth: 128,
            max_witness_bytes: 16 * 1024 * 1024,
            max_output_bytes: 32 * 1024 * 1024,
            max_allocations: 1_000_000,
            max_work_units: 10_000_000,
        }
    }
}

/// Resource usage tracked during lifecycle operations.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ProvenanceLifecycleUsage {
    pub modules_examined: usize,
    pub contributions_examined: usize,
    pub extension_entries_examined: usize,
    pub index_rows_examined: usize,
    pub output_bytes: usize,
    pub allocations: usize,
    pub work_units: u64,
}

/// Helper function to build a ModuleGraph from records.
fn make_graph(
    epoch: &ModuleEpoch,
    records: &[ModuleContributionRecord],
) -> Result<ModuleGraph, String> {
    let mut graph = ModuleGraph::new(epoch.clone(), ModuleGraphLimits::default())
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

/// Helper function to build an Arc<ModuleProvenanceManifest> from records.
fn make_manifest(
    epoch: &ModuleEpoch,
    records: Vec<ModuleContributionRecord>,
) -> Result<Arc<ModuleProvenanceManifest>, String> {
    ModuleProvenanceManifest::new(epoch.clone(), records, ModuleProvenanceLimits::default())
        .map(Arc::new)
        .map_err(|e| format!("{e:?}"))
}

/// A paired provenance checkpoint capturing module contributions and extension checkpoints.
#[derive(Debug, Clone, PartialEq)]
pub struct ProvenanceCheckpoint {
    schema_version: u16,
    mode: ProvenanceCheckpointMode,
    epoch: ModuleEpoch,
    base_provenance_root: Option<ModuleProvenanceRoot>,
    base_logical_root: Option<LogicalRoot>,
    provenance_root: ModuleProvenanceRoot,
    logical_root: LogicalRoot,
    carried_records: Arc<[ModuleContributionRecord]>,
    carried_payloads: Arc<[AppliedModulePayload]>,
    entry_ids: Arc<[ExtensionEntryId]>,
    captured_entries: usize,
    captured_payload_bytes: u128,
}

impl ProvenanceCheckpoint {
    /// Capture a suffix checkpoint relative to an exact base state.
    pub fn capture_suffix(
        state: &ModuleApplyState,
        base: &ModuleApplyState,
    ) -> Result<Self, ProvenanceLifecycleError> {
        if state.manifest().epoch() != base.manifest().epoch() {
            return Err(ProvenanceLifecycleError::EpochMismatch {
                expected: base.manifest().epoch().clone(),
                actual: state.manifest().epoch().clone(),
            });
        }
        if !state
            .manifest()
            .records()
            .starts_with(base.manifest().records())
        {
            return Err(ProvenanceLifecycleError::BaseNotAncestral);
        }

        let suffix_records: Vec<_> =
            state.manifest().records()[base.manifest().records().len()..].to_vec();
        let suffix_payloads: Vec<_> =
            state.applied_payloads()[base.applied_payloads().len()..].to_vec();

        let mut entry_ids = Vec::new();
        let mut captured_entries = 0usize;
        let mut captured_payload_bytes = 0u128;

        for record in &suffix_records {
            for ext in record.extension_contributions() {
                entry_ids.extend_from_slice(ext.entries());
                captured_entries = captured_entries.saturating_add(ext.entries().len());
            }
        }
        for payload in &suffix_payloads {
            for ext in payload.extension_payloads() {
                captured_payload_bytes =
                    captured_payload_bytes.saturating_add(ext.payload().len() as u128);
            }
        }

        Ok(Self {
            schema_version: PROVENANCE_LIFECYCLE_SCHEMA_VERSION,
            mode: ProvenanceCheckpointMode::Suffix,
            epoch: state.manifest().epoch().clone(),
            base_provenance_root: Some(base.manifest().root()),
            base_logical_root: Some(base.logical_root()),
            provenance_root: state.manifest().root(),
            logical_root: state.logical_root(),
            carried_records: suffix_records.into(),
            carried_payloads: suffix_payloads.into(),
            entry_ids: entry_ids.into(),
            captured_entries,
            captured_payload_bytes,
        })
    }

    /// Capture a self-contained full journal checkpoint.
    pub fn capture_full(state: &ModuleApplyState) -> Self {
        let mut entry_ids = Vec::new();
        let mut captured_entries = 0usize;
        let mut captured_payload_bytes = 0u128;

        for record in state.manifest().records() {
            for ext in record.extension_contributions() {
                entry_ids.extend_from_slice(ext.entries());
                captured_entries = captured_entries.saturating_add(ext.entries().len());
            }
        }
        for payload in state.applied_payloads() {
            for ext in payload.extension_payloads() {
                captured_payload_bytes =
                    captured_payload_bytes.saturating_add(ext.payload().len() as u128);
            }
        }

        Self {
            schema_version: PROVENANCE_LIFECYCLE_SCHEMA_VERSION,
            mode: ProvenanceCheckpointMode::FullJournal,
            epoch: state.manifest().epoch().clone(),
            base_provenance_root: None,
            base_logical_root: None,
            provenance_root: state.manifest().root(),
            logical_root: state.logical_root(),
            carried_records: state.manifest().records().to_vec().into(),
            carried_payloads: state.applied_payloads().to_vec().into(),
            entry_ids: entry_ids.into(),
            captured_entries,
            captured_payload_bytes,
        }
    }

    pub fn schema_version(&self) -> u16 {
        self.schema_version
    }

    pub fn mode(&self) -> ProvenanceCheckpointMode {
        self.mode
    }

    pub fn epoch(&self) -> &ModuleEpoch {
        &self.epoch
    }

    pub fn base_provenance_root(&self) -> Option<ModuleProvenanceRoot> {
        self.base_provenance_root
    }

    pub fn base_logical_root(&self) -> Option<LogicalRoot> {
        self.base_logical_root
    }

    pub fn provenance_root(&self) -> ModuleProvenanceRoot {
        self.provenance_root
    }

    pub fn logical_root(&self) -> LogicalRoot {
        self.logical_root
    }

    pub fn carried_records(&self) -> &[ModuleContributionRecord] {
        &self.carried_records
    }

    pub fn carried_payloads(&self) -> &[AppliedModulePayload] {
        &self.carried_payloads
    }

    pub fn entry_ids(&self) -> &[ExtensionEntryId] {
        &self.entry_ids
    }

    pub fn captured_entries(&self) -> usize {
        self.captured_entries
    }

    pub fn captured_payload_bytes(&self) -> u128 {
        self.captured_payload_bytes
    }
}

/// An immutable, preflighted plan for restoring a provenance checkpoint onto a target state.
#[derive(Debug, Clone, PartialEq)]
pub struct ProvenanceRestorePlanV1 {
    schema_version: u16,
    target_provenance_root: ModuleProvenanceRoot,
    target_logical_root: LogicalRoot,
    checkpoint_mode: ProvenanceCheckpointMode,
    checkpoint_root: ModuleProvenanceRoot,
    expected_final_provenance_root: ModuleProvenanceRoot,
    expected_final_logical_root: LogicalRoot,
    records_to_append: Vec<ModuleContributionRecord>,
    payloads_to_append: Vec<AppliedModulePayload>,
    usage: ProvenanceLifecycleUsage,
}

impl ProvenanceRestorePlanV1 {
    /// Preflight a restore plan from a checkpoint against a target state.
    pub fn preflight(
        target: &ModuleApplyState,
        checkpoint: &ProvenanceCheckpoint,
        limits: &ProvenanceLifecycleLimits,
        probe: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<Self, ProvenanceRestoreError>> {
        if probe.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled("restore-preflight/cancelled"));
        }

        let mut usage = ProvenanceLifecycleUsage::default();

        if checkpoint.schema_version != PROVENANCE_LIFECYCLE_SCHEMA_VERSION {
            return Outcome::InternalFault(InternalFault::new(
                "checkpoint_schema_version",
                "checkpoint schema version mismatch",
            ));
        }

        if target.manifest().epoch() != checkpoint.epoch() {
            return Outcome::Complete(Err(ProvenanceRestoreError::EpochMismatch {
                target: target.manifest().epoch().clone(),
                checkpoint: checkpoint.epoch().clone(),
            }));
        }

        match checkpoint.mode() {
            ProvenanceCheckpointMode::Suffix => {
                let base_prov = match checkpoint.base_provenance_root() {
                    Some(r) => r,
                    None => {
                        return Outcome::Complete(Err(ProvenanceRestoreError::MissingBaseRoot));
                    }
                };
                let base_log = match checkpoint.base_logical_root() {
                    Some(r) => r,
                    None => {
                        return Outcome::Complete(Err(ProvenanceRestoreError::MissingBaseRoot));
                    }
                };

                if target.manifest().root() != base_prov || target.logical_root() != base_log {
                    return Outcome::Complete(Err(ProvenanceRestoreError::BaseNotExact {
                        expected_provenance: base_prov,
                        actual_provenance: target.manifest().root(),
                    }));
                }
            }
            ProvenanceCheckpointMode::FullJournal => {
                if !checkpoint
                    .carried_records()
                    .starts_with(target.manifest().records())
                {
                    return Outcome::Complete(Err(ProvenanceRestoreError::TargetConflict {
                        reason: "target records are not a prefix of full journal",
                    }));
                }
            }
        }

        // Check entry identities
        for payload in checkpoint.carried_payloads() {
            usage.modules_examined = usage.modules_examined.saturating_add(1);
            if usage.modules_examined > limits.max_modules {
                return Outcome::Inconclusive(Inconclusive::authority_incomplete(
                    "max_modules exceeded during restore preflight",
                ));
            }
            for ext in payload.extension_payloads() {
                usage.extension_entries_examined =
                    usage.extension_entries_examined.saturating_add(1);
                if usage.extension_entries_examined > limits.max_extension_entries {
                    return Outcome::Inconclusive(Inconclusive::authority_incomplete(
                        "max_extension_entries exceeded",
                    ));
                }
                let expected_id =
                    ExtensionEntryId::derive(checkpoint.epoch(), ext.descriptor(), ext.payload());
                // Verify against contribution record
                let matching = payload
                    .contribution()
                    .extension_contributions()
                    .iter()
                    .find(|c| c.descriptor() == ext.descriptor());
                if let Some(contrib) = matching
                    && !contrib.entries().contains(&expected_id)
                {
                    return Outcome::Complete(Err(ProvenanceRestoreError::EntryIdentityMismatch {
                        descriptor: ext.descriptor().clone(),
                        derived: expected_id,
                    }));
                }
            }
        }

        let records_to_append: Vec<_> = match checkpoint.mode() {
            ProvenanceCheckpointMode::Suffix => checkpoint.carried_records().to_vec(),
            ProvenanceCheckpointMode::FullJournal => {
                checkpoint.carried_records()[target.manifest().records().len()..].to_vec()
            }
        };

        let payloads_to_append: Vec<_> = match checkpoint.mode() {
            ProvenanceCheckpointMode::Suffix => checkpoint.carried_payloads().to_vec(),
            ProvenanceCheckpointMode::FullJournal => {
                checkpoint.carried_payloads()[target.applied_payloads().len()..].to_vec()
            }
        };

        Outcome::Complete(Ok(Self {
            schema_version: PROVENANCE_LIFECYCLE_SCHEMA_VERSION,
            target_provenance_root: target.manifest().root(),
            target_logical_root: target.logical_root(),
            checkpoint_mode: checkpoint.mode(),
            checkpoint_root: checkpoint.provenance_root(),
            expected_final_provenance_root: checkpoint.provenance_root(),
            expected_final_logical_root: checkpoint.logical_root(),
            records_to_append,
            payloads_to_append,
            usage,
        }))
    }

    /// Apply the preflighted restore plan onto the target state.
    pub fn apply(
        &self,
        target: ModuleApplyState,
    ) -> Result<ModuleApplyState, ProvenanceRestoreError> {
        if target.manifest().root() != self.target_provenance_root
            || target.logical_root() != self.target_logical_root
        {
            return Err(ProvenanceRestoreError::StaleTargetRoot);
        }

        if self.records_to_append.is_empty() {
            return Ok(target);
        }

        // Build composite records and payloads
        let mut new_records = target.manifest().records().to_vec();
        new_records.extend_from_slice(&self.records_to_append);

        let mut new_payloads = target.applied_payloads().to_vec();
        new_payloads.extend_from_slice(&self.payloads_to_append);

        // Build new graph
        let graph = make_graph(target.manifest().epoch(), &new_records)
            .map_err(ProvenanceRestoreError::GraphError)?;

        // Build new manifest
        let manifest = make_manifest(target.manifest().epoch(), new_records)
            .map_err(ProvenanceRestoreError::ManifestError)?;

        // Reconstruct environment declarations and extension entries
        let mut env = target.environment().clone();
        for payload in &self.payloads_to_append {
            for decl in payload.declarations() {
                env = env
                    .add_decl((**decl).clone())
                    .map_err(|e| ProvenanceRestoreError::StateError(format!("{e:?}")))?;
            }
            for decl in payload.extra_declarations() {
                env = env
                    .add_decl((**decl).clone())
                    .map_err(|e| ProvenanceRestoreError::StateError(format!("{e:?}")))?;
            }
            for ext in payload.extension_payloads() {
                env = env
                    .push_extension_entry(&ext.descriptor().name, ext.payload_arc())
                    .map_err(|e| ProvenanceRestoreError::StateError(format!("{e:?}")))?;
            }
        }

        let new_state = ModuleApplyState::from_parts_with_options_and_payloads(
            env,
            graph,
            manifest,
            target.options().clone(),
            new_payloads,
        )
        .map_err(|e| ProvenanceRestoreError::StateError(format!("{e:?}")))?;

        if new_state.manifest().root() != self.expected_final_provenance_root {
            return Err(ProvenanceRestoreError::FinalProvenanceRootMismatch {
                expected: self.expected_final_provenance_root,
                actual: new_state.manifest().root(),
            });
        }
        if new_state.logical_root() != self.expected_final_logical_root {
            return Err(ProvenanceRestoreError::FinalLogicalRootMismatch {
                expected: self.expected_final_logical_root,
                actual: new_state.logical_root(),
            });
        }

        Ok(new_state)
    }

    pub fn usage(&self) -> ProvenanceLifecycleUsage {
        self.usage
    }
}

/// Errors occurring during restore preflight or execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvenanceRestoreError {
    EpochMismatch {
        target: ModuleEpoch,
        checkpoint: ModuleEpoch,
    },
    MissingBaseRoot,
    BaseNotExact {
        expected_provenance: ModuleProvenanceRoot,
        actual_provenance: ModuleProvenanceRoot,
    },
    TargetConflict {
        reason: &'static str,
    },
    EntryIdentityMismatch {
        descriptor: ExtensionDescriptor,
        derived: ExtensionEntryId,
    },
    StaleTargetRoot,
    FinalProvenanceRootMismatch {
        expected: ModuleProvenanceRoot,
        actual: ModuleProvenanceRoot,
    },
    FinalLogicalRootMismatch {
        expected: LogicalRoot,
        actual: LogicalRoot,
    },
    GraphError(String),
    ManifestError(String),
    StateError(String),
}

/// Typed conflicts that can arise during three-way provenance merge.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvenanceMergeConflict {
    ConflictingModuleOrigin {
        module: ModuleId,
        ours_grade: ArtifactGrade,
        theirs_grade: ArtifactGrade,
    },
    ConflictingDeclaration {
        name: Name,
        ours_digest: Digest,
        theirs_digest: Digest,
    },
    ConflictingExtensionEntry {
        descriptor: ExtensionDescriptor,
        ours_range: (u64, u64),
        theirs_range: (u64, u64),
    },
    StaleBase {
        expected: ModuleProvenanceRoot,
        actual: ModuleProvenanceRoot,
    },
    EpochMismatch {
        ours: ModuleEpoch,
        theirs: ModuleEpoch,
    },
    ContradictoryCompleteness {
        module: ModuleId,
        ours: ProvenanceCompleteness,
        theirs: ProvenanceCompleteness,
    },
}

/// An immutable, preflighted plan for three-way provenance merge.
#[derive(Debug, Clone, PartialEq)]
pub struct ProvenanceMergePlanV1 {
    schema_version: u16,
    base_root: ModuleProvenanceRoot,
    ours_root: ModuleProvenanceRoot,
    theirs_root: ModuleProvenanceRoot,
    base_logical_root: LogicalRoot,
    ours_logical_root: LogicalRoot,
    theirs_logical_root: LogicalRoot,
    conflicts: Vec<ProvenanceMergeConflict>,
    fast_path_selection: Option<MergeFastPath>,
    merged_records: Vec<ModuleContributionRecord>,
    merged_payloads: Vec<AppliedModulePayload>,
    usage: ProvenanceLifecycleUsage,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MergeFastPath {
    AdoptOurs,
    AdoptTheirs,
}

impl ProvenanceMergePlanV1 {
    /// Preflight a three-way merge plan between base, ours, and theirs states.
    pub fn preflight(
        base: &ModuleApplyState,
        ours: &ModuleApplyState,
        theirs: &ModuleApplyState,
        limits: &ProvenanceLifecycleLimits,
        probe: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<Self, ProvenanceMergeError>> {
        if probe.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled("merge-preflight/cancelled"));
        }

        let mut usage = ProvenanceLifecycleUsage::default();

        if ours.manifest().epoch() != theirs.manifest().epoch() {
            return Outcome::Complete(Ok(Self {
                schema_version: PROVENANCE_LIFECYCLE_SCHEMA_VERSION,
                base_root: base.manifest().root(),
                ours_root: ours.manifest().root(),
                theirs_root: theirs.manifest().root(),
                base_logical_root: base.logical_root(),
                ours_logical_root: ours.logical_root(),
                theirs_logical_root: theirs.logical_root(),
                conflicts: vec![ProvenanceMergeConflict::EpochMismatch {
                    ours: ours.manifest().epoch().clone(),
                    theirs: theirs.manifest().epoch().clone(),
                }],
                fast_path_selection: None,
                merged_records: vec![],
                merged_payloads: vec![],
                usage,
            }));
        }

        // Fast paths:
        // 1. If ours == theirs, adopt ours.
        if ours.manifest().root() == theirs.manifest().root()
            && ours.logical_root() == theirs.logical_root()
        {
            return Outcome::Complete(Ok(Self {
                schema_version: PROVENANCE_LIFECYCLE_SCHEMA_VERSION,
                base_root: base.manifest().root(),
                ours_root: ours.manifest().root(),
                theirs_root: theirs.manifest().root(),
                base_logical_root: base.logical_root(),
                ours_logical_root: ours.logical_root(),
                theirs_logical_root: theirs.logical_root(),
                conflicts: vec![],
                fast_path_selection: Some(MergeFastPath::AdoptOurs),
                merged_records: ours.manifest().records().to_vec(),
                merged_payloads: ours.applied_payloads().to_vec(),
                usage,
            }));
        }

        // 2. If ours == base, adopt theirs (one-sided change on theirs).
        if ours.manifest().root() == base.manifest().root()
            && ours.logical_root() == base.logical_root()
        {
            return Outcome::Complete(Ok(Self {
                schema_version: PROVENANCE_LIFECYCLE_SCHEMA_VERSION,
                base_root: base.manifest().root(),
                ours_root: ours.manifest().root(),
                theirs_root: theirs.manifest().root(),
                base_logical_root: base.logical_root(),
                ours_logical_root: ours.logical_root(),
                theirs_logical_root: theirs.logical_root(),
                conflicts: vec![],
                fast_path_selection: Some(MergeFastPath::AdoptTheirs),
                merged_records: theirs.manifest().records().to_vec(),
                merged_payloads: theirs.applied_payloads().to_vec(),
                usage,
            }));
        }

        // 3. If theirs == base, adopt ours (one-sided change on ours).
        if theirs.manifest().root() == base.manifest().root()
            && theirs.logical_root() == base.logical_root()
        {
            return Outcome::Complete(Ok(Self {
                schema_version: PROVENANCE_LIFECYCLE_SCHEMA_VERSION,
                base_root: base.manifest().root(),
                ours_root: ours.manifest().root(),
                theirs_root: theirs.manifest().root(),
                base_logical_root: base.logical_root(),
                ours_logical_root: ours.logical_root(),
                theirs_logical_root: theirs.logical_root(),
                conflicts: vec![],
                fast_path_selection: Some(MergeFastPath::AdoptOurs),
                merged_records: ours.manifest().records().to_vec(),
                merged_payloads: ours.applied_payloads().to_vec(),
                usage,
            }));
        }

        // Multi-sided merge: inspect base, ours, theirs.
        let mut conflicts = Vec::new();
        let mut base_modules: BTreeMap<&ModuleId, &ModuleContributionRecord> = BTreeMap::new();
        for r in base.manifest().records() {
            base_modules.insert(&r.module().id, r);
        }

        let mut ours_modules: BTreeMap<&ModuleId, &ModuleContributionRecord> = BTreeMap::new();
        let mut ours_payloads_map: BTreeMap<&ModuleId, &AppliedModulePayload> = BTreeMap::new();
        for (r, p) in ours
            .manifest()
            .records()
            .iter()
            .zip(ours.applied_payloads())
        {
            ours_modules.insert(&r.module().id, r);
            ours_payloads_map.insert(&r.module().id, p);
        }

        let mut theirs_modules: BTreeMap<&ModuleId, &ModuleContributionRecord> = BTreeMap::new();
        let mut theirs_payloads_map: BTreeMap<&ModuleId, &AppliedModulePayload> = BTreeMap::new();
        for (r, p) in theirs
            .manifest()
            .records()
            .iter()
            .zip(theirs.applied_payloads())
        {
            theirs_modules.insert(&r.module().id, r);
            theirs_payloads_map.insert(&r.module().id, p);
        }

        let mut all_module_ids: BTreeSet<&ModuleId> = BTreeSet::new();
        for id in base_modules.keys() {
            all_module_ids.insert(id);
        }
        for id in ours_modules.keys() {
            all_module_ids.insert(id);
        }
        for id in theirs_modules.keys() {
            all_module_ids.insert(id);
        }

        let mut merged_records = Vec::new();
        let mut merged_payloads = Vec::new();

        for id in all_module_ids {
            usage.modules_examined = usage.modules_examined.saturating_add(1);
            if usage.modules_examined > limits.max_modules {
                return Outcome::Inconclusive(Inconclusive::authority_incomplete(
                    "max_modules exceeded during merge preflight",
                ));
            }

            let in_base = base_modules.get(id).copied();
            let in_ours = ours_modules.get(id).copied();
            let in_theirs = theirs_modules.get(id).copied();

            match (in_base, in_ours, in_theirs) {
                (Some(b), Some(o), Some(t)) => {
                    if o == t {
                        merged_records.push(o.clone());
                        merged_payloads.push(ours_payloads_map[id].clone());
                    } else if o == b {
                        merged_records.push(t.clone());
                        merged_payloads.push(theirs_payloads_map[id].clone());
                    } else if t == b {
                        merged_records.push(o.clone());
                        merged_payloads.push(ours_payloads_map[id].clone());
                    } else {
                        conflicts.push(ProvenanceMergeConflict::ConflictingModuleOrigin {
                            module: (*id).clone(),
                            ours_grade: o.module().artifact.grade,
                            theirs_grade: t.module().artifact.grade,
                        });
                    }
                }
                (None, Some(o), None) => {
                    merged_records.push(o.clone());
                    merged_payloads.push(ours_payloads_map[id].clone());
                }
                (None, None, Some(t)) => {
                    merged_records.push(t.clone());
                    merged_payloads.push(theirs_payloads_map[id].clone());
                }
                (None, Some(o), Some(t)) => {
                    if o == t {
                        merged_records.push(o.clone());
                        merged_payloads.push(ours_payloads_map[id].clone());
                    } else {
                        conflicts.push(ProvenanceMergeConflict::ConflictingModuleOrigin {
                            module: (*id).clone(),
                            ours_grade: o.module().artifact.grade,
                            theirs_grade: t.module().artifact.grade,
                        });
                    }
                }
                (Some(_), None, Some(t)) => {
                    conflicts.push(ProvenanceMergeConflict::ConflictingModuleOrigin {
                        module: (*id).clone(),
                        ours_grade: ArtifactGrade::Provisional,
                        theirs_grade: t.module().artifact.grade,
                    });
                }
                (Some(_), Some(o), None) => {
                    conflicts.push(ProvenanceMergeConflict::ConflictingModuleOrigin {
                        module: (*id).clone(),
                        ours_grade: o.module().artifact.grade,
                        theirs_grade: ArtifactGrade::Provisional,
                    });
                }
                (Some(_), None, None) => {}
                (None, None, None) => {}
            }
        }

        // Check for declaration name collisions across different modules
        let mut decl_to_module: BTreeMap<Name, ModuleId> = BTreeMap::new();
        for record in &merged_records {
            for name in record
                .declarations()
                .iter()
                .chain(record.extra_declarations())
            {
                if let Some(prev) = decl_to_module.insert(name.clone(), record.module().id.clone())
                    && prev != record.module().id
                {
                    let name_str = name.to_display_string();
                    conflicts.push(ProvenanceMergeConflict::ConflictingDeclaration {
                        name: name.clone(),
                        ours_digest: hash(Domain::DeclContent, name_str.as_bytes()),
                        theirs_digest: hash(Domain::DeclContent, name_str.as_bytes()),
                    });
                }
            }
        }

        Outcome::Complete(Ok(Self {
            schema_version: PROVENANCE_LIFECYCLE_SCHEMA_VERSION,
            base_root: base.manifest().root(),
            ours_root: ours.manifest().root(),
            theirs_root: theirs.manifest().root(),
            base_logical_root: base.logical_root(),
            ours_logical_root: ours.logical_root(),
            theirs_logical_root: theirs.logical_root(),
            conflicts,
            fast_path_selection: None,
            merged_records,
            merged_payloads,
            usage,
        }))
    }

    pub fn has_conflicts(&self) -> bool {
        !self.conflicts.is_empty()
    }

    pub fn conflicts(&self) -> &[ProvenanceMergeConflict] {
        &self.conflicts
    }

    /// Apply the merge plan to produce a new ModuleApplyState.
    pub fn apply(
        &self,
        _base: ModuleApplyState,
        ours: ModuleApplyState,
        theirs: ModuleApplyState,
    ) -> Result<ModuleApplyState, ProvenanceMergeError> {
        if !self.conflicts.is_empty() {
            return Err(ProvenanceMergeError::HasConflicts(self.conflicts.clone()));
        }

        if let Some(fast_path) = self.fast_path_selection {
            return match fast_path {
                MergeFastPath::AdoptOurs => Ok(ours),
                MergeFastPath::AdoptTheirs => Ok(theirs),
            };
        }

        // Build new graph
        let graph = make_graph(ours.manifest().epoch(), &self.merged_records)
            .map_err(ProvenanceMergeError::GraphError)?;

        // Build new manifest
        let manifest = make_manifest(ours.manifest().epoch(), self.merged_records.clone())
            .map_err(ProvenanceMergeError::ManifestError)?;

        // Build combined environment
        let mut env = Environment::new();
        // Register all extensions from ours and theirs
        for (_name, ext) in ours.environment().extensions() {
            env = env
                .register_extension(ext.descriptor.clone())
                .unwrap_or(env);
        }
        for (name, ext) in theirs.environment().extensions() {
            if env.extension(name).is_none() {
                env = env
                    .register_extension(ext.descriptor.clone())
                    .unwrap_or(env);
            }
        }

        for payload in &self.merged_payloads {
            for decl in payload.declarations() {
                env = env
                    .add_decl((**decl).clone())
                    .map_err(|e| ProvenanceMergeError::StateError(format!("{e:?}")))?;
            }
            for decl in payload.extra_declarations() {
                env = env
                    .add_decl((**decl).clone())
                    .map_err(|e| ProvenanceMergeError::StateError(format!("{e:?}")))?;
            }
            for ext in payload.extension_payloads() {
                env = env
                    .push_extension_entry(&ext.descriptor().name, ext.payload_arc())
                    .map_err(|e| ProvenanceMergeError::StateError(format!("{e:?}")))?;
            }
        }

        ModuleApplyState::from_parts_with_options_and_payloads(
            env,
            graph,
            manifest,
            ours.options().clone(),
            self.merged_payloads.clone(),
        )
        .map_err(|e| ProvenanceMergeError::StateError(format!("{e:?}")))
    }

    pub fn usage(&self) -> ProvenanceLifecycleUsage {
        self.usage
    }
}

/// Errors occurring during merge preflight or application.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvenanceMergeError {
    HasConflicts(Vec<ProvenanceMergeConflict>),
    GraphError(String),
    ManifestError(String),
    StateError(String),
}

/// General errors for lifecycle operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProvenanceLifecycleError {
    EpochMismatch {
        expected: ModuleEpoch,
        actual: ModuleEpoch,
    },
    BaseNotAncestral,
    MissingBase,
}

/// Evidence refinement errors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EvidenceRefinementError {
    ModuleNotFound(ModuleId),
    InvalidRefinement { reason: &'static str },
    ChangedArtifactDigest { current: Digest, candidate: Digest },
    StateError(String),
}

/// Canonical monotonic evidence refinement.
///
/// Refines evidence from Provisional -> Verified -> OracleFixture.
/// Proves that this changes [`ModuleProvenanceRoot`] while leaving [`LogicalRoot`] bit-for-bit unchanged.
pub fn refine_evidence(
    current: &ArtifactEvidence,
    candidate: &ArtifactEvidence,
) -> Result<ArtifactEvidence, EvidenceRefinementError> {
    if current.content_digest != candidate.content_digest {
        return Err(EvidenceRefinementError::ChangedArtifactDigest {
            current: current.content_digest,
            candidate: candidate.content_digest,
        });
    }

    // Check grade monotonicity
    let current_rank = match current.grade {
        ArtifactGrade::Provisional => 0,
        ArtifactGrade::Verified => 1,
        ArtifactGrade::OracleFixture => 2,
    };
    let candidate_rank = match candidate.grade {
        ArtifactGrade::Provisional => 0,
        ArtifactGrade::Verified => 1,
        ArtifactGrade::OracleFixture => 2,
    };
    if candidate_rank < current_rank {
        return Err(EvidenceRefinementError::InvalidRefinement {
            reason: "cannot downgrade artifact grade",
        });
    }

    Ok(candidate.clone())
}

/// Refine the artifact evidence for one module in a committed [`ModuleApplyState`].
/// Returns a new `ModuleApplyState` whose `ModuleProvenanceRoot` has moved, but whose
/// `LogicalRoot` remains unchanged.
pub fn refine_module_evidence_in_state(
    state: &ModuleApplyState,
    module_id: &ModuleId,
    refined_evidence: ArtifactEvidence,
) -> Result<ModuleApplyState, EvidenceRefinementError> {
    let current_record = state
        .manifest()
        .record(module_id)
        .ok_or_else(|| EvidenceRefinementError::ModuleNotFound(module_id.clone()))?;

    let valid_refined = refine_evidence(&current_record.module().artifact, &refined_evidence)?;

    let mut new_records = Vec::with_capacity(state.manifest().records().len());

    for r in state.manifest().records() {
        if r.module().id == *module_id {
            let mut mod_rec = r.module().clone();
            mod_rec.artifact = valid_refined.clone();

            let new_contrib = ModuleContributionRecord::new(
                mod_rec,
                r.declarations().to_vec(),
                r.extra_declarations().to_vec(),
                r.extension_contributions().to_vec(),
                r.completeness().clone(),
            );
            new_records.push(new_contrib);
        } else {
            new_records.push(r.clone());
        }
    }

    let graph = make_graph(state.manifest().epoch(), &new_records)
        .map_err(EvidenceRefinementError::StateError)?;

    let manifest = make_manifest(state.manifest().epoch(), new_records)
        .map_err(EvidenceRefinementError::StateError)?;

    // Reuse existing payloads by updating the contribution record on the matched payload
    let mut new_payloads = Vec::with_capacity(state.applied_payloads().len());
    for (p, r) in state.applied_payloads().iter().zip(manifest.records()) {
        new_payloads.push(AppliedModulePayload::new_with_record(
            r.clone(),
            p.declarations().to_vec().into(),
            p.extra_declarations().to_vec().into(),
            p.extension_payloads().to_vec().into(),
        ));
    }

    let new_state = ModuleApplyState::from_parts_with_options_and_payloads(
        state.environment().clone(),
        graph,
        manifest,
        state.options().clone(),
        new_payloads,
    )
    .map_err(|e| EvidenceRefinementError::StateError(format!("{e:?}")))?;

    Ok(new_state)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{AxiomVal, ConstantInfo, ConstantVal};
    use crate::modules::{ArtifactProducer, ModuleId, ModuleRecord};
    use crate::provenance::{CaptureStatus, PayloadTransparency};
    use fln_core::expr::Expr;
    use fln_core::level::Level;
    use fln_core::name::Name;
    use fln_core::options::KVMap;
    use fln_core::outcome::InconclusiveCause;

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

    fn make_test_state(module_name: &str, decl_name: &str) -> ModuleApplyState {
        let epoch = test_epoch();
        let mod_id = ModuleId::new(Name::from_components([module_name]));
        let artifact = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Verified,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, module_name.as_bytes()),
        };
        let mod_rec = ModuleRecord::new(mod_id, true, vec![], artifact);
        let decl = Name::from_components([decl_name]);
        let const_info = test_axiom(decl_name);

        let contrib = ModuleContributionRecord::new(
            mod_rec.clone(),
            vec![decl.clone()],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );

        let graph = make_graph(&epoch, std::slice::from_ref(&contrib)).unwrap();
        let manifest = make_manifest(&epoch, vec![contrib.clone()]).unwrap();

        let mut env = Environment::new();
        env = env.add_decl((*const_info).clone()).unwrap();

        let payload = AppliedModulePayload::new_with_record(
            contrib,
            vec![const_info].into(),
            vec![].into(),
            vec![].into(),
        );

        ModuleApplyState::from_parts_with_options_and_payloads(
            env,
            graph,
            manifest,
            KVMap::new(),
            vec![payload],
        )
        .unwrap()
    }

    #[test]
    fn snapshot_clone_is_o1_and_isolated() {
        let state1 = make_test_state("A", "declA");
        let state2 = state1.clone();

        assert_eq!(state1.logical_root(), state2.logical_root());
        assert_eq!(state1.manifest().root(), state2.manifest().root());
        assert_eq!(state1, state2);
    }

    #[test]
    fn suffix_and_full_checkpoint_capture_and_restore() {
        let base = make_test_state("A", "declA");

        // Extend base to state2 with module B
        let epoch = test_epoch();
        let mod_b = ModuleId::new(Name::from_components(["B"]));
        let art_b = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Verified,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"B"),
        };
        let rec_b = ModuleRecord::new(mod_b, true, vec![], art_b);
        let decl_b = Name::from_components(["declB"]);
        let const_b = test_axiom("declB");
        let contrib_b = ModuleContributionRecord::new(
            rec_b.clone(),
            vec![decl_b],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );

        let mut all_records = base.manifest().records().to_vec();
        all_records.push(contrib_b.clone());

        let graph = make_graph(&epoch, &all_records).unwrap();
        let manifest = make_manifest(&epoch, all_records).unwrap();

        let mut env = base.environment().clone();
        env = env.add_decl((*const_b).clone()).unwrap();

        let mut all_payloads = base.applied_payloads().to_vec();
        all_payloads.push(AppliedModulePayload::new_with_record(
            contrib_b,
            vec![const_b].into(),
            vec![].into(),
            vec![].into(),
        ));

        let state2 = ModuleApplyState::from_parts_with_options_and_payloads(
            env,
            graph,
            manifest,
            KVMap::new(),
            all_payloads,
        )
        .unwrap();

        // 1. Suffix checkpoint from base to state2
        let suffix_cp = ProvenanceCheckpoint::capture_suffix(&state2, &base).unwrap();
        assert_eq!(suffix_cp.mode(), ProvenanceCheckpointMode::Suffix);
        assert_eq!(suffix_cp.carried_records().len(), 1);

        let limits = ProvenanceLifecycleLimits::default();
        let plan = match ProvenanceRestorePlanV1::preflight(&base, &suffix_cp, &limits, None) {
            Outcome::Complete(Ok(p)) => p,
            other => panic!("expected complete plan, got {other:?}"),
        };

        let restored = plan.apply(base.clone()).unwrap();
        assert_eq!(restored.logical_root(), state2.logical_root());
        assert_eq!(restored.manifest().root(), state2.manifest().root());

        // 2. Full journal checkpoint of state2
        let full_cp = ProvenanceCheckpoint::capture_full(&state2);
        assert_eq!(full_cp.mode(), ProvenanceCheckpointMode::FullJournal);
        assert_eq!(full_cp.carried_records().len(), 2);

        let full_plan = match ProvenanceRestorePlanV1::preflight(&base, &full_cp, &limits, None) {
            Outcome::Complete(Ok(p)) => p,
            other => panic!("expected complete plan, got {other:?}"),
        };
        let restored_full = full_plan.apply(base.clone()).unwrap();
        assert_eq!(restored_full.logical_root(), state2.logical_root());
        assert_eq!(restored_full.manifest().root(), state2.manifest().root());
    }

    #[test]
    fn evidence_refinement_changes_provenance_root_without_moving_logical_root() {
        let state = make_test_state("Mod", "decl1");
        let initial_log_root = state.logical_root();
        let initial_prov_root = state.manifest().root();

        let mod_id = ModuleId::new(Name::from_components(["Mod"]));
        let refined_art = ArtifactEvidence {
            epoch: state.manifest().epoch().clone(),
            grade: ArtifactGrade::OracleFixture,
            producer: ArtifactProducer::Reference,
            content_digest: hash(Domain::DeclContent, b"Mod"),
        };

        let refined_state = refine_module_evidence_in_state(&state, &mod_id, refined_art).unwrap();

        // Law: logical root MUST be identical
        assert_eq!(refined_state.logical_root(), initial_log_root);
        // Law: provenance root MUST have changed
        assert_ne!(refined_state.manifest().root(), initial_prov_root);
    }

    #[test]
    fn three_way_merge_disjoint_and_conflicts() {
        let base = make_test_state("Base", "declBase");
        let ours = make_test_state("Ours", "declOurs");
        let theirs = make_test_state("Theirs", "declTheirs");

        let limits = ProvenanceLifecycleLimits::default();

        // 1. Merge ours with base (one-sided)
        let plan1 = match ProvenanceMergePlanV1::preflight(&base, &ours, &base, &limits, None) {
            Outcome::Complete(Ok(p)) => p,
            other => panic!("expected complete plan, got {other:?}"),
        };
        assert!(!plan1.has_conflicts());
        let applied1 = plan1
            .apply(base.clone(), ours.clone(), base.clone())
            .unwrap();
        assert_eq!(applied1.manifest().root(), ours.manifest().root());

        // 2. Disjoint merge: ours has Ours, theirs has Theirs
        let plan2 = match ProvenanceMergePlanV1::preflight(&base, &ours, &theirs, &limits, None) {
            Outcome::Complete(Ok(p)) => p,
            other => panic!("expected complete plan, got {other:?}"),
        };
        assert!(!plan2.has_conflicts());
        let merged = plan2
            .apply(base.clone(), ours.clone(), theirs.clone())
            .unwrap();
        assert_eq!(merged.manifest().records().len(), 2);
    }

    #[test]
    fn concurrent_merge_schedule_matrix_1_8_32_threads() {
        let base = Arc::new(make_test_state("Base", "declBase"));
        let ours = Arc::new(make_test_state("Ours", "declOurs"));
        let theirs = Arc::new(make_test_state("Theirs", "declTheirs"));

        for thread_count in [1, 8, 32] {
            let mut handles = Vec::new();
            for _ in 0..thread_count {
                let b = Arc::clone(&base);
                let o = Arc::clone(&ours);
                let t = Arc::clone(&theirs);
                handles.push(std::thread::spawn(move || {
                    let limits = ProvenanceLifecycleLimits::default();
                    let plan = match ProvenanceMergePlanV1::preflight(&b, &o, &t, &limits, None) {
                        Outcome::Complete(Ok(p)) => p,
                        other => panic!("failed preflight: {other:?}"),
                    };
                    plan.apply((*b).clone(), (*o).clone(), (*t).clone())
                        .unwrap()
                }));
            }

            let mut roots = Vec::new();
            for h in handles {
                let state = h.join().unwrap();
                roots.push((state.logical_root(), state.manifest().root()));
            }

            let first = roots[0];
            for (i, r) in roots.iter().enumerate() {
                assert_eq!(
                    *r, first,
                    "schedule divergence at thread count {thread_count} worker {i}"
                );
            }
        }
    }

    #[test]
    fn stale_target_and_divergent_base_refusals() {
        let base1 = make_test_state("A", "declA");
        let base2 = make_test_state("AltA", "declAltA");

        // Build child on base1
        let epoch = test_epoch();
        let mod_b = ModuleId::new(Name::from_components(["B"]));
        let art_b = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Verified,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"B"),
        };
        let rec_b = ModuleRecord::new(mod_b, true, vec![], art_b);
        let decl_b = Name::from_components(["declB"]);
        let const_b = test_axiom("declB");
        let contrib_b = ModuleContributionRecord::new(
            rec_b.clone(),
            vec![decl_b],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );

        let mut all_records = base1.manifest().records().to_vec();
        all_records.push(contrib_b.clone());
        let graph = make_graph(&epoch, &all_records).unwrap();
        let manifest = make_manifest(&epoch, all_records).unwrap();
        let mut env = base1.environment().clone();
        env = env.add_decl((*const_b).clone()).unwrap();
        let mut all_payloads = base1.applied_payloads().to_vec();
        all_payloads.push(AppliedModulePayload::new_with_record(
            contrib_b,
            vec![const_b].into(),
            vec![].into(),
            vec![].into(),
        ));
        let child1 = ModuleApplyState::from_parts_with_options_and_payloads(
            env,
            graph,
            manifest,
            KVMap::new(),
            all_payloads,
        )
        .unwrap();

        let suffix_cp = ProvenanceCheckpoint::capture_suffix(&child1, &base1).unwrap();
        let limits = ProvenanceLifecycleLimits::default();

        // Suffix restore against wrong base (base2) must refuse at preflight
        match ProvenanceRestorePlanV1::preflight(&base2, &suffix_cp, &limits, None) {
            Outcome::Complete(Err(ProvenanceRestoreError::BaseNotExact { .. })) => {}
            other => panic!("expected BaseNotExact, got {other:?}"),
        }

        // Plan preflighted against base1 applied to base2 must refuse
        let plan = match ProvenanceRestorePlanV1::preflight(&base1, &suffix_cp, &limits, None) {
            Outcome::Complete(Ok(p)) => p,
            other => panic!("expected complete plan, got {other:?}"),
        };
        match plan.apply(base2.clone()) {
            Err(ProvenanceRestoreError::StaleTargetRoot) => {}
            other => panic!("expected StaleTargetRoot, got {other:?}"),
        }
    }

    #[test]
    fn evidence_refinement_downgrade_and_digest_mismatch_refusals() {
        let state = make_test_state("Mod", "decl1");
        let mod_id = ModuleId::new(Name::from_components(["Mod"]));

        // 1. Downgrade from Verified to Provisional must be refused
        let downgrade_art = ArtifactEvidence {
            epoch: state.manifest().epoch().clone(),
            grade: ArtifactGrade::Provisional,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"Mod"),
        };
        match refine_module_evidence_in_state(&state, &mod_id, downgrade_art) {
            Err(EvidenceRefinementError::InvalidRefinement { .. }) => {}
            other => panic!("expected InvalidRefinement on downgrade, got {other:?}"),
        }

        // 2. Changing content digest must be refused
        let mismatch_digest_art = ArtifactEvidence {
            epoch: state.manifest().epoch().clone(),
            grade: ArtifactGrade::OracleFixture,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"TamperedBytes"),
        };
        match refine_module_evidence_in_state(&state, &mod_id, mismatch_digest_art) {
            Err(EvidenceRefinementError::ChangedArtifactDigest { .. }) => {}
            other => panic!("expected ChangedArtifactDigest on mismatch, got {other:?}"),
        }
    }

    #[test]
    fn merge_conflicting_module_origins_and_declarations() {
        let base = make_test_state("Shared", "sharedDecl");

        // Ours defines module ConflictedMod with Provisional grade
        let epoch = test_epoch();
        let mod_c = ModuleId::new(Name::from_components(["ConflictedMod"]));
        let art_ours = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Provisional,
            producer: ArtifactProducer::FrankenLean,
            content_digest: hash(Domain::DeclContent, b"OursContent"),
        };
        let rec_ours = ModuleRecord::new(mod_c.clone(), true, vec![], art_ours);
        let decl_c1 = Name::from_components(["declC1"]);
        let const_c1 = test_axiom("declC1");
        let contrib_ours = ModuleContributionRecord::new(
            rec_ours.clone(),
            vec![decl_c1],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );
        let mut ours_records = base.manifest().records().to_vec();
        ours_records.push(contrib_ours.clone());
        let ours_graph = make_graph(&epoch, &ours_records).unwrap();
        let ours_manifest = make_manifest(&epoch, ours_records).unwrap();
        let mut ours_env = base.environment().clone();
        ours_env = ours_env.add_decl((*const_c1).clone()).unwrap();
        let mut ours_payloads = base.applied_payloads().to_vec();
        ours_payloads.push(AppliedModulePayload::new_with_record(
            contrib_ours,
            vec![const_c1].into(),
            vec![].into(),
            vec![].into(),
        ));
        let ours_state = ModuleApplyState::from_parts_with_options_and_payloads(
            ours_env,
            ours_graph,
            ours_manifest,
            KVMap::new(),
            ours_payloads,
        )
        .unwrap();

        // Theirs defines same ConflictedMod with Verified grade and different content
        let art_theirs = ArtifactEvidence {
            epoch: epoch.clone(),
            grade: ArtifactGrade::Verified,
            producer: ArtifactProducer::Reference,
            content_digest: hash(Domain::DeclContent, b"TheirsContent"),
        };
        let rec_theirs = ModuleRecord::new(mod_c, true, vec![], art_theirs);
        let decl_c2 = Name::from_components(["declC2"]);
        let const_c2 = test_axiom("declC2");
        let contrib_theirs = ModuleContributionRecord::new(
            rec_theirs.clone(),
            vec![decl_c2],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
        );
        let mut theirs_records = base.manifest().records().to_vec();
        theirs_records.push(contrib_theirs.clone());
        let theirs_graph = make_graph(&epoch, &theirs_records).unwrap();
        let theirs_manifest = make_manifest(&epoch, theirs_records).unwrap();
        let mut theirs_env = base.environment().clone();
        theirs_env = theirs_env.add_decl((*const_c2).clone()).unwrap();
        let mut theirs_payloads = base.applied_payloads().to_vec();
        theirs_payloads.push(AppliedModulePayload::new_with_record(
            contrib_theirs,
            vec![const_c2].into(),
            vec![].into(),
            vec![].into(),
        ));
        let theirs_state = ModuleApplyState::from_parts_with_options_and_payloads(
            theirs_env,
            theirs_graph,
            theirs_manifest,
            KVMap::new(),
            theirs_payloads,
        )
        .unwrap();

        let limits = ProvenanceLifecycleLimits::default();
        let plan = match ProvenanceMergePlanV1::preflight(
            &base,
            &ours_state,
            &theirs_state,
            &limits,
            None,
        ) {
            Outcome::Complete(Ok(p)) => p,
            other => panic!("expected complete plan, got {other:?}"),
        };

        assert!(plan.has_conflicts());
        assert!(
            plan.conflicts()
                .iter()
                .any(|c| matches!(c, ProvenanceMergeConflict::ConflictingModuleOrigin { .. }))
        );
    }

    #[test]
    fn cancellation_and_resource_limits_return_inconclusive() {
        use std::sync::atomic::AtomicBool;

        let base = make_test_state("A", "declA");
        let ours = make_test_state("Ours", "declOurs");
        let theirs = make_test_state("Theirs", "declTheirs");

        // 1. Tripped cancellation probe
        let probe = AtomicBool::new(true);
        let limits = ProvenanceLifecycleLimits::default();
        match ProvenanceMergePlanV1::preflight(&base, &ours, &theirs, &limits, Some(&probe)) {
            Outcome::Inconclusive(inc) => {
                assert!(matches!(inc.cause, InconclusiveCause::Cancelled { .. }));
            }
            other => panic!("expected cancelled inconclusive, got {other:?}"),
        }

        // 2. Resource limits exhaustion (max_modules = 0)
        let tight_limits = ProvenanceLifecycleLimits {
            max_modules: 0,
            ..Default::default()
        };
        match ProvenanceMergePlanV1::preflight(&base, &ours, &theirs, &tight_limits, None) {
            Outcome::Inconclusive(inc) => {
                assert!(matches!(
                    inc.cause,
                    InconclusiveCause::AuthorityIncomplete { .. }
                ));
            }
            other => panic!("expected resource exhausted inconclusive, got {other:?}"),
        }
    }
}
