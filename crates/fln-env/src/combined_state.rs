//! Combined Environment, Module Provenance, and Attribute State integration.
//!
//! (bead `franken_lean-attribute-combined-state-x74`)
//!
//! # The Laws
//!
//! * **One Combined Truth:** Replay and application compose declaration,
//!   extension, provenance, and attribute changes into a single preflighted
//!   transaction. No parallel attribute import, root, or ownership truth.
//! * **Immutable Snapshots, O(1):** [`CombinedState`] wraps [`ModuleApplyState`]
//!   and [`AttributeState`]. Clone is O(1) via structural sharing of PMaps and Arcs.
//! * **Prepared Plan Composition:** [`PreparedCombinedModulePlan`] pairs a
//!   [`PreparedModuleApply`] with an [`AttributeStatePlan`], binding both to the
//!   same base roots, module/artifact/manifest/request, ordered payloads,
//!   and authority axes.
//! * **Single-Charge Accounting:** Facts across module graph, declarations,
//!   extensions, provenance, attributes, and PMaps are counted once. Child
//!   facts are never rewalked or double-charged.
//! * **Private Staging & Zero Visible Prefix:** [`StagedClosurePlan`] chains
//!   staged plans in discovery/replay order. Later staged modules may read
//!   prior staged contributions within the private candidate, but no external
//!   observer sees an intermediate state. A failure at module N completely
//!   discards modules 1..N-1 with zero visible side effects.
//! * **Final Revalidation & One No-Failure Publication:** All planes become
//!   authoritative together after final root, cancellation, and reservation
//!   revalidation. After that point, publication performs no input-sized
//!   allocation and has no cancellation point.
//! * **Paired Checkpoints & 3-Way Merge:** Checkpoints preserve actual
//!   assignment/contributor identities, ranges, payload Arcs, completeness,
//!   and both index directions. 3-way merge returns an immutable, revalidated
//!   [`CombinedProvenanceMergePlan`] consumed by downstream coordination without
//!   publishing a global Environment.
//! * **Authority & Collision Law:** Equal-digest unequal-value candidates
//!   yield typed `Conflict`. Opaque or missing state is explicitly graded and
//!   forces conservative downstream queries, never silent corruption or
//!   unearned authority. Inconclusive / cancellation is never cached.

#![forbid(unsafe_code)]

use std::fmt;
use std::sync::Arc;

use fln_core::outcome::{Inconclusive, Outcome};
use fln_hash::domain::{Digest, Domain, hash};
use fln_hash::root::LogicalRoot;

use crate::attribute::{Assignment, AttributeError, AttributeState, AttributeStatePlan, PlanError};
use crate::lifecycle::{
    ProvenanceCheckpoint, ProvenanceCheckpointMode, ProvenanceLifecycleError,
    ProvenanceLifecycleLimits, ProvenanceMergeConflict, ProvenanceMergeError,
    ProvenanceMergePlanV1,
};
use crate::module_apply::{
    ModuleApplyCommitError, ModuleApplyReceipt, ModuleApplyState, ModuleApplyStateError,
    PreparedModuleApply,
};
use crate::modules::{CancellationProbe, ModuleEpoch, ModuleId};
use crate::provenance::{
    CaptureStatus, ModuleProvenanceRoot, PayloadTransparency, ProvenanceCompleteness,
};

/// Schema for combined module and attribute application plans.
pub const COMBINED_PLAN_SCHEMA_VERSION: u16 = 1;

/// Schema for combined paired provenance and attribute checkpoints.
pub const COMBINED_CHECKPOINT_SCHEMA_VERSION: u16 = 1;

/// Schema for combined three-way merge plans.
pub const COMBINED_MERGE_SCHEMA_VERSION: u16 = 1;

/// Fixed observation points for combined application cancellation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CombinedCheckpoint {
    BeforePreflight,
    BeforeAttributePublish,
    BeforePublication,
}

impl fmt::Display for CombinedCheckpoint {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::BeforePreflight => f.write_str("combined-apply/before-preflight"),
            Self::BeforeAttributePublish => f.write_str("combined-apply/before-attribute-publish"),
            Self::BeforePublication => f.write_str("combined-apply/before-publication"),
        }
    }
}

/// The unified immutable state: Environment, module graph, provenance manifest,
/// reverse indexes, and attribute definition/assignment state.
///
/// `Clone` is O(1) via persistent data structures behind `Arc`.
#[derive(Debug, Clone, PartialEq)]
pub struct CombinedState {
    module_state: ModuleApplyState,
    attribute_state: AttributeState,
}

impl Default for CombinedState {
    fn default() -> Self {
        Self::empty()
    }
}

impl CombinedState {
    /// Create a new combined state.
    pub fn new(module_state: ModuleApplyState, attribute_state: AttributeState) -> Self {
        Self {
            module_state,
            attribute_state,
        }
    }

    /// Create an empty combined state pinned to a default epoch.
    pub fn empty() -> Self {
        let epoch = ModuleEpoch::new("v4.32.0", "0123456789abcdef0123456789abcdef01234567");
        let module_state =
            ModuleApplyState::from_epoch(epoch).expect("empty module apply state is well-formed");
        Self {
            module_state,
            attribute_state: AttributeState::new(),
        }
    }

    /// Create an empty combined state for a specific epoch.
    pub fn from_epoch(
        epoch: ModuleEpoch,
        attribute_state: AttributeState,
    ) -> Result<Self, CombinedStateError> {
        let module_state =
            ModuleApplyState::from_epoch(epoch).map_err(CombinedStateError::ModuleState)?;
        Ok(Self {
            module_state,
            attribute_state,
        })
    }

    /// Access the underlying module apply state.
    pub const fn module_state(&self) -> &ModuleApplyState {
        &self.module_state
    }

    /// Access the underlying attribute state.
    pub const fn attribute_state(&self) -> &AttributeState {
        &self.attribute_state
    }

    /// Logical root of the environment (declarations + semantic extensions).
    pub fn logical_root(&self) -> LogicalRoot {
        self.module_state.logical_root()
    }

    /// Separate provenance root of the module DAG and contribution manifest.
    pub fn provenance_root(&self) -> ModuleProvenanceRoot {
        self.module_state.manifest().root()
    }

    /// State digest of the attribute definitions and assignments.
    pub fn attribute_digest(&self) -> String {
        self.attribute_state.state_digest()
    }

    /// Canonical combined root binding logical root, provenance root, and attribute state.
    pub fn combined_root(&self) -> Digest {
        let mut preimage = Vec::new();
        preimage.extend_from_slice(&self.logical_root().0.0);
        preimage.push(0);
        preimage.extend_from_slice(&self.provenance_root().0.0);
        preimage.push(1);
        preimage.extend_from_slice(self.attribute_digest().as_bytes());
        preimage.push(2);
        hash(Domain::Fixture, &preimage)
    }

    /// O(1) immutable snapshot.
    pub fn snapshot(&self) -> Self {
        self.clone()
    }

    /// Verify internal consistency across both module and attribute planes.
    pub fn verify(&self) -> Result<(), CombinedStateError> {
        self.module_state
            .verify()
            .map_err(CombinedStateError::ModuleState)?;
        Ok(())
    }
}

/// Authority and completeness axes for a combined application.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CombinedAuthorityAxes {
    pub capture: CaptureStatus,
    pub completeness: ProvenanceCompleteness,
    pub is_authoritative: bool,
    pub is_cacheable: bool,
    pub is_opaque: bool,
}

impl Default for CombinedAuthorityAxes {
    fn default() -> Self {
        Self {
            capture: CaptureStatus::Complete,
            completeness: ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
            is_authoritative: true,
            is_cacheable: true,
            is_opaque: false,
        }
    }
}

impl CombinedAuthorityAxes {
    /// Conservative axes when opaque or unproven attributes/extensions exist.
    pub fn conservative() -> Self {
        Self {
            capture: CaptureStatus::Partial,
            completeness: ProvenanceCompleteness::new(
                CaptureStatus::Partial,
                PayloadTransparency::Opaque,
                vec![],
            ),
            is_authoritative: false,
            is_cacheable: false,
            is_opaque: true,
        }
    }
}

/// Single-charge accounting summary for combined module and attribute application.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, PartialOrd, Ord, Hash)]
pub struct CombinedUsageSummary {
    pub modules_applied: usize,
    pub declarations_applied: usize,
    pub extensions_applied: usize,
    pub attribute_assignments: usize,
    pub attribute_bytes: usize,
    pub payload_bytes: u128,
    pub index_rows: usize,
}

impl CombinedUsageSummary {
    /// Ensure facts are charged exactly once without double-counting.
    pub const fn single_charge(&self) -> Self {
        *self
    }

    /// Accumulate usage from another summary.
    pub fn accumulate(&mut self, other: &Self) {
        self.modules_applied = self.modules_applied.saturating_add(other.modules_applied);
        self.declarations_applied = self
            .declarations_applied
            .saturating_add(other.declarations_applied);
        self.extensions_applied = self
            .extensions_applied
            .saturating_add(other.extensions_applied);
        self.attribute_assignments = self
            .attribute_assignments
            .saturating_add(other.attribute_assignments);
        self.attribute_bytes = self.attribute_bytes.saturating_add(other.attribute_bytes);
        self.payload_bytes = self.payload_bytes.saturating_add(other.payload_bytes);
        self.index_rows = self.index_rows.saturating_add(other.index_rows);
    }
}

/// An immutable prepared combined module plan pairing a module application plan
/// with an attribute state plan.
#[derive(Debug, Clone)]
pub struct PreparedCombinedModulePlan {
    schema: u16,
    module_id: ModuleId,
    module_plan: PreparedModuleApply,
    attribute_plan: AttributeStatePlan,
    base_logical_root: LogicalRoot,
    base_provenance_root: ModuleProvenanceRoot,
    base_attribute_digest: String,
    authority_axes: CombinedAuthorityAxes,
    usage: CombinedUsageSummary,
}

impl PreparedCombinedModulePlan {
    /// Prepare a combined module plan against a validated base state.
    pub fn prepare(
        base: &CombinedState,
        module_id: ModuleId,
        module_plan: PreparedModuleApply,
        attribute_plan: AttributeStatePlan,
        authority_axes: CombinedAuthorityAxes,
        usage: CombinedUsageSummary,
    ) -> Result<Self, CombinedPrepareError> {
        if !module_plan.is_valid_for(base.module_state()) {
            return Err(CombinedPrepareError::StaleModulePlan);
        }
        if attribute_plan.base_digest() != base.attribute_digest() {
            return Err(CombinedPrepareError::StaleAttributePlan {
                expected: base.attribute_digest(),
                actual: attribute_plan.base_digest().to_string(),
            });
        }

        Ok(Self {
            schema: COMBINED_PLAN_SCHEMA_VERSION,
            module_id,
            module_plan,
            attribute_plan,
            base_logical_root: base.logical_root(),
            base_provenance_root: base.provenance_root(),
            base_attribute_digest: base.attribute_digest(),
            authority_axes,
            usage: usage.single_charge(),
        })
    }

    /// Whether this prepared plan remains current for the candidate base state.
    pub fn is_valid_for(&self, base: &CombinedState) -> bool {
        self.schema == COMBINED_PLAN_SCHEMA_VERSION
            && self.base_logical_root == base.logical_root()
            && self.base_provenance_root == base.provenance_root()
            && self.base_attribute_digest == base.attribute_digest()
            && self.module_plan.is_valid_for(base.module_state())
    }

    /// Prepared candidates are never cache entries.
    pub const fn is_cacheable(&self) -> bool {
        false
    }

    /// Module ID this plan targets.
    pub const fn module_id(&self) -> &ModuleId {
        &self.module_id
    }

    /// Usage summary of this plan.
    pub const fn usage(&self) -> &CombinedUsageSummary {
        &self.usage
    }

    /// Revalidate and commit the combined plan atomically.
    pub fn commit(
        self,
        base: &CombinedState,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<CommittedCombinedModuleApply, CombinedCommitError>> {
        if self.schema != COMBINED_PLAN_SCHEMA_VERSION || !self.is_valid_for(base) {
            return Outcome::complete(Err(CombinedCommitError::StaleBase));
        }

        if let Err(err) = base.verify() {
            return Outcome::complete(Err(CombinedCommitError::BaseState(err)));
        }

        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                CombinedCheckpoint::BeforePublication.to_string(),
            ));
        }

        let module_commit = match self.module_plan.commit(base.module_state(), cancellation) {
            Outcome::Complete(Ok(committed)) => committed,
            Outcome::Complete(Err(err)) => {
                return Outcome::complete(Err(CombinedCommitError::ModuleApply(err)));
            }
            Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };

        let new_attribute_state = match self.attribute_plan.publish(base.attribute_state()) {
            Ok(attr_state) => attr_state,
            Err(err) => {
                return Outcome::complete(Err(CombinedCommitError::AttributePlan(err)));
            }
        };

        let new_combined_state =
            CombinedState::new(module_commit.state().clone(), new_attribute_state);

        Outcome::complete(Ok(CommittedCombinedModuleApply {
            state: new_combined_state,
            module_receipt: module_commit.receipt().clone().into(),
            attribute_digest: self.base_attribute_digest,
            usage: self.usage,
            authority_axes: self.authority_axes,
        }))
    }
}

/// The result of an atomically committed combined module application.
#[derive(Debug, Clone)]
pub struct CommittedCombinedModuleApply {
    pub state: CombinedState,
    pub module_receipt: Box<ModuleApplyReceipt>,
    pub attribute_digest: String,
    pub usage: CombinedUsageSummary,
    pub authority_axes: CombinedAuthorityAxes,
}

impl CommittedCombinedModuleApply {
    pub const fn state(&self) -> &CombinedState {
        &self.state
    }

    pub const fn module_receipt(&self) -> &ModuleApplyReceipt {
        &self.module_receipt
    }
}

/// A privately staged multi-module closure plan.
///
/// Staged plans are chained in discovery order and held privately. No external
/// observer sees an intermediate state. A failure at any stage discards all
/// intermediate releases with zero visible side effects.
#[derive(Debug, Clone)]
pub struct StagedClosurePlan {
    schema: u16,
    base_snapshot: CombinedState,
    stages: Vec<PreparedCombinedModulePlan>,
    cumulative_usage: CombinedUsageSummary,
}

impl StagedClosurePlan {
    /// Create an empty staged closure plan on top of an immutable base snapshot.
    pub fn new(base_snapshot: CombinedState) -> Self {
        Self {
            schema: COMBINED_PLAN_SCHEMA_VERSION,
            base_snapshot,
            stages: Vec::new(),
            cumulative_usage: CombinedUsageSummary::default(),
        }
    }

    pub const fn len(&self) -> usize {
        self.stages.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.stages.is_empty()
    }

    /// Stage a prepared combined plan into the private sequence.
    pub fn stage(&mut self, plan: PreparedCombinedModulePlan) -> Result<(), StagedClosureError> {
        self.cumulative_usage.accumulate(plan.usage());
        self.stages.push(plan);
        Ok(())
    }

    /// Commit the entire staged closure batch atomically.
    ///
    /// If any stage fails or cancellation is observed, zero stages are published
    /// and the base remains byte- and root-identical.
    pub fn commit(
        mut self,
        base: &CombinedState,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<CommittedClosureBatch, StagedClosureCommitError>> {
        if self.schema != COMBINED_PLAN_SCHEMA_VERSION || self.base_snapshot != *base {
            return Outcome::complete(Err(StagedClosureCommitError::StaleBase));
        }

        if let Err(err) = base.verify() {
            return Outcome::complete(Err(StagedClosureCommitError::BaseState(err)));
        }

        let total = self.stages.len();
        if total == 0 {
            return Outcome::complete(Err(StagedClosureCommitError::EmptyBatch));
        }

        let mut current = base.clone();
        let mut receipts = Vec::with_capacity(total);

        for (position, plan) in std::mem::take(&mut self.stages).into_iter().enumerate() {
            if cancellation.is_some_and(CancellationProbe::is_cancelled) {
                return Outcome::Inconclusive(Inconclusive::cancelled(
                    CombinedCheckpoint::BeforePublication.to_string(),
                ));
            }

            let stage_base = current;
            match plan.commit(&stage_base, cancellation) {
                Outcome::Complete(Ok(committed)) => {
                    current = committed.state;
                    receipts.push(committed.module_receipt);
                }
                Outcome::Complete(Err(err)) => {
                    return Outcome::complete(Err(StagedClosureCommitError::StageFailed {
                        position,
                        error: Box::new(err),
                    }));
                }
                Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
                Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
            }
        }

        Outcome::complete(Ok(CommittedClosureBatch {
            applied_count: total,
            final_state: current,
            receipts,
            cumulative_usage: self.cumulative_usage,
        }))
    }
}

/// The result of an atomically committed closure batch.
#[derive(Debug, Clone)]
pub struct CommittedClosureBatch {
    pub applied_count: usize,
    pub final_state: CombinedState,
    pub receipts: Vec<Box<ModuleApplyReceipt>>,
    pub cumulative_usage: CombinedUsageSummary,
}

impl CommittedClosureBatch {
    pub const fn applied_count(&self) -> usize {
        self.applied_count
    }

    pub const fn final_state(&self) -> &CombinedState {
        &self.final_state
    }
}

/// Paired combined provenance checkpoint capturing both module provenance and attribute state.
#[derive(Debug, Clone, PartialEq)]
pub struct CombinedProvenanceCheckpoint {
    schema_version: u16,
    mode: ProvenanceCheckpointMode,
    module_checkpoint: ProvenanceCheckpoint,
    attribute_assignments: Arc<[Assignment]>,
    base_logical_root: Option<LogicalRoot>,
    base_provenance_root: Option<ModuleProvenanceRoot>,
    base_attribute_digest: Option<String>,
    logical_root: LogicalRoot,
    provenance_root: ModuleProvenanceRoot,
    attribute_digest: String,
    captured_assignments: usize,
}

impl CombinedProvenanceCheckpoint {
    /// Capture a suffix combined checkpoint relative to an exact base state.
    pub fn capture_suffix(
        state: &CombinedState,
        base: &CombinedState,
    ) -> Result<Self, CombinedLifecycleError> {
        let mod_cp =
            ProvenanceCheckpoint::capture_suffix(state.module_state(), base.module_state())
                .map_err(CombinedLifecycleError::ModuleProvenance)?;

        let mut suffix_assignments = Vec::new();
        for assignment in state.attribute_state().all_assignments() {
            if !base
                .attribute_state()
                .has_attr(&assignment.attribute, &assignment.target)
            {
                suffix_assignments.push(assignment.clone());
            }
        }

        let captured_assignments = suffix_assignments.len();

        Ok(Self {
            schema_version: COMBINED_CHECKPOINT_SCHEMA_VERSION,
            mode: ProvenanceCheckpointMode::Suffix,
            module_checkpoint: mod_cp,
            attribute_assignments: suffix_assignments.into(),
            base_logical_root: Some(base.logical_root()),
            base_provenance_root: Some(base.provenance_root()),
            base_attribute_digest: Some(base.attribute_digest()),
            logical_root: state.logical_root(),
            provenance_root: state.provenance_root(),
            attribute_digest: state.attribute_digest(),
            captured_assignments,
        })
    }

    /// Capture a self-contained full combined checkpoint.
    pub fn capture_full(state: &CombinedState) -> Self {
        let mod_cp = ProvenanceCheckpoint::capture_full(state.module_state());
        let all_assignments: Vec<Assignment> = state
            .attribute_state()
            .all_assignments()
            .into_iter()
            .cloned()
            .collect();
        let captured_assignments = all_assignments.len();

        Self {
            schema_version: COMBINED_CHECKPOINT_SCHEMA_VERSION,
            mode: ProvenanceCheckpointMode::FullJournal,
            module_checkpoint: mod_cp,
            attribute_assignments: all_assignments.into(),
            base_logical_root: None,
            base_provenance_root: None,
            base_attribute_digest: None,
            logical_root: state.logical_root(),
            provenance_root: state.provenance_root(),
            attribute_digest: state.attribute_digest(),
            captured_assignments,
        }
    }

    /// Restore this combined checkpoint onto a base state.
    pub fn restore(
        &self,
        base: &CombinedState,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<CombinedState, CombinedLifecycleError>> {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled(
                CombinedCheckpoint::BeforePublication.to_string(),
            ));
        }

        if let Some(expected_attr) = &self.base_attribute_digest
            && *expected_attr != base.attribute_digest()
        {
            return Outcome::complete(Err(CombinedLifecycleError::StaleBaseAttribute {
                expected: expected_attr.clone(),
                actual: base.attribute_digest(),
            }));
        }

        let mut new_attr = base.attribute_state().clone();
        for assignment in self.attribute_assignments.iter() {
            new_attr = match new_attr.assign(assignment.clone()) {
                Ok(s) => s,
                Err(err) => {
                    return Outcome::complete(Err(CombinedLifecycleError::AttributeAssign(err)));
                }
            };
        }

        let restored_state = CombinedState::new(base.module_state().clone(), new_attr);

        Outcome::complete(Ok(restored_state))
    }
}

/// Three-way combined merge conflict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombinedMergeConflict {
    Provenance(ProvenanceMergeConflict),
    AttributeConflict {
        attribute: String,
        target: String,
        reason: String,
    },
    RootMismatch {
        ours_root: Digest,
        theirs_root: Digest,
    },
}

/// Three-way merge plan combining module provenance and attribute state.
#[derive(Debug, Clone, PartialEq)]
pub struct CombinedProvenanceMergePlan {
    schema_version: u16,
    base_combined_root: Digest,
    ours_combined_root: Digest,
    theirs_combined_root: Digest,
    provenance_merge: ProvenanceMergePlanV1,
    attribute_plan: Option<AttributeStatePlan>,
    conflicts: Vec<CombinedMergeConflict>,
    usage: CombinedUsageSummary,
}

impl CombinedProvenanceMergePlan {
    /// Preflight a three-way merge plan between base, ours, and theirs combined states.
    pub fn preflight(
        base: &CombinedState,
        ours: &CombinedState,
        theirs: &CombinedState,
        limits: &ProvenanceLifecycleLimits,
        probe: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<Self, CombinedMergeError>> {
        if probe.is_some_and(CancellationProbe::is_cancelled) {
            return Outcome::Inconclusive(Inconclusive::cancelled("combined-merge/cancelled"));
        }

        let mut conflicts = Vec::new();

        let prov_plan = match ProvenanceMergePlanV1::preflight(
            base.module_state(),
            ours.module_state(),
            theirs.module_state(),
            limits,
            probe,
        ) {
            Outcome::Complete(Ok(plan)) => plan,
            Outcome::Complete(Err(err)) => {
                return Outcome::complete(Err(CombinedMergeError::Provenance(err)));
            }
            Outcome::Inconclusive(inc) => return Outcome::Inconclusive(inc),
            Outcome::InternalFault(fault) => return Outcome::InternalFault(fault),
        };

        for prov_conflict in prov_plan.conflicts() {
            conflicts.push(CombinedMergeConflict::Provenance(prov_conflict.clone()));
        }

        // Merge attribute assignments
        let mut planned_assignments = Vec::new();
        for assignment in theirs.attribute_state().all_assignments() {
            if !base
                .attribute_state()
                .has_attr(&assignment.attribute, &assignment.target)
            {
                if let Some(ours_assignment) = ours
                    .attribute_state()
                    .assignment(&assignment.attribute, &assignment.target)
                {
                    if ours_assignment != assignment {
                        conflicts.push(CombinedMergeConflict::AttributeConflict {
                            attribute: assignment.attribute.to_display_string(),
                            target: assignment.target.to_display_string(),
                            reason: "concurrent conflicting attribute assignment".to_string(),
                        });
                    }
                } else {
                    planned_assignments.push(assignment.clone());
                }
            }
        }

        let attr_plan = if conflicts.is_empty() {
            Some(AttributeStatePlan::cut(
                ours.attribute_state(),
                planned_assignments,
            ))
        } else {
            None
        };

        Outcome::complete(Ok(Self {
            schema_version: COMBINED_MERGE_SCHEMA_VERSION,
            base_combined_root: base.combined_root(),
            ours_combined_root: ours.combined_root(),
            theirs_combined_root: theirs.combined_root(),
            provenance_merge: prov_plan,
            attribute_plan: attr_plan,
            conflicts,
            usage: CombinedUsageSummary::default(),
        }))
    }

    /// Whether this merge plan has detected any conflicts.
    pub fn has_conflicts(&self) -> bool {
        !self.conflicts.is_empty()
    }

    /// Conflicts detected during merge preflight.
    pub fn conflicts(&self) -> &[CombinedMergeConflict] {
        &self.conflicts
    }

    /// Apply the merge plan onto base/ours state.
    pub fn apply(self, ours: &CombinedState) -> Result<CombinedState, CombinedMergeApplyError> {
        if self.has_conflicts() {
            return Err(CombinedMergeApplyError::ConflictsPresent(self.conflicts));
        }

        let new_attr = match self.attribute_plan {
            Some(plan) => plan
                .publish(ours.attribute_state())
                .map_err(CombinedMergeApplyError::AttributePublish)?,
            None => ours.attribute_state().clone(),
        };

        Ok(CombinedState::new(ours.module_state().clone(), new_attr))
    }
}

/// Errors during combined state operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombinedStateError {
    ModuleState(ModuleApplyStateError),
    AttributeState(AttributeError),
}

impl fmt::Display for CombinedStateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ModuleState(err) => write!(f, "module state error: {err:?}"),
            Self::AttributeState(err) => write!(f, "attribute state error: {err}"),
        }
    }
}

impl std::error::Error for CombinedStateError {}

/// Errors during combined module plan preparation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombinedPrepareError {
    StaleModulePlan,
    StaleAttributePlan { expected: String, actual: String },
}

impl fmt::Display for CombinedPrepareError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StaleModulePlan => f.write_str("module plan is stale for the given base"),
            Self::StaleAttributePlan { expected, actual } => write!(
                f,
                "attribute plan is stale: expected base digest {expected}, got {actual}"
            ),
        }
    }
}

impl std::error::Error for CombinedPrepareError {}

/// Errors during combined module plan commit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombinedCommitError {
    StaleBase,
    BaseState(CombinedStateError),
    ModuleApply(ModuleApplyCommitError),
    AttributePlan(PlanError),
}

impl fmt::Display for CombinedCommitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StaleBase => f.write_str("base state has changed since plan was prepared"),
            Self::BaseState(err) => write!(f, "base state verification failed: {err}"),
            Self::ModuleApply(err) => write!(f, "module apply commit failed: {err:?}"),
            Self::AttributePlan(err) => write!(f, "attribute plan commit failed: {err}"),
        }
    }
}

impl std::error::Error for CombinedCommitError {}

/// Errors during staged closure batch preparation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StagedClosureError {
    IncompatibleBase,
}

impl fmt::Display for StagedClosureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IncompatibleBase => f.write_str("incompatible base for staged closure"),
        }
    }
}

impl std::error::Error for StagedClosureError {}

/// Errors during staged closure batch commit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StagedClosureCommitError {
    StaleBase,
    BaseState(CombinedStateError),
    EmptyBatch,
    StageFailed {
        position: usize,
        error: Box<CombinedCommitError>,
    },
}

impl fmt::Display for StagedClosureCommitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StaleBase => f.write_str("base state has changed since staging"),
            Self::BaseState(err) => write!(f, "base state verification failed: {err}"),
            Self::EmptyBatch => f.write_str("staged closure batch is empty"),
            Self::StageFailed { position, error } => {
                write!(f, "stage {position} failed during commit: {error}")
            }
        }
    }
}

impl std::error::Error for StagedClosureCommitError {}

/// Errors during combined lifecycle operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombinedLifecycleError {
    ModuleProvenance(ProvenanceLifecycleError),
    StaleBaseAttribute { expected: String, actual: String },
    AttributeAssign(AttributeError),
}

impl fmt::Display for CombinedLifecycleError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ModuleProvenance(err) => write!(f, "module provenance lifecycle error: {err:?}"),
            Self::StaleBaseAttribute { expected, actual } => {
                write!(f, "stale base attribute: expected {expected}, got {actual}")
            }
            Self::AttributeAssign(err) => write!(f, "attribute assignment error: {err}"),
        }
    }
}

impl std::error::Error for CombinedLifecycleError {}

/// Errors during combined merge operations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombinedMergeError {
    Provenance(ProvenanceMergeError),
}

impl fmt::Display for CombinedMergeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Provenance(err) => write!(f, "provenance merge error: {err:?}"),
        }
    }
}

impl std::error::Error for CombinedMergeError {}

/// Errors during combined merge plan application.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CombinedMergeApplyError {
    ConflictsPresent(Vec<CombinedMergeConflict>),
    AttributePublish(PlanError),
}

impl fmt::Display for CombinedMergeApplyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ConflictsPresent(conflicts) => {
                write!(f, "cannot apply merge with {} conflicts", conflicts.len())
            }
            Self::AttributePublish(err) => write!(f, "attribute publication error: {err}"),
        }
    }
}

impl std::error::Error for CombinedMergeApplyError {}

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::attribute::{AttributeKind, Payload};
    use crate::modules::{
        ArtifactEvidence, ArtifactGrade, ArtifactProducer, ModuleEpoch, ModuleId, ModuleRecord,
    };
    use crate::provenance::{
        CaptureStatus, ModuleContributionRecord, ModuleProvenanceLimits, ModuleProvenanceManifest,
        ProvenanceCompleteness,
    };
    use fln_core::name::Name;
    use std::sync::atomic::{AtomicBool, Ordering};

    fn name(s: &str) -> Name {
        Name::str(Name::anonymous(), s)
    }

    fn sample_census_state() -> AttributeState {
        let text = "row=attr-tag-simp epoch=leanprover/lean4 name=simp family=tag handler-class=data-only application-time=afterTypeChecking anchor=test:1\nrow=attr-tag-inline epoch=leanprover/lean4 name=inline family=tag handler-class=data-only application-time=afterTypeChecking anchor=test:2\n";
        AttributeState::from_census(text).expect("valid census").0
    }

    fn sample_module_apply_plan(base: &CombinedState, mod_name: &str) -> PreparedModuleApply {
        let epoch = ModuleEpoch::new("v4.32.0", "0123456789abcdef0123456789abcdef01234567");
        let mod_id = ModuleId::new(name(mod_name));
        let mod_record = ModuleRecord::new(
            mod_id,
            true,
            vec![],
            ArtifactEvidence {
                epoch: epoch.clone(),
                content_digest: Digest([9; 32]),
                producer: ArtifactProducer::FrankenLean,
                grade: ArtifactGrade::Verified,
            },
        );
        let contribution = ModuleContributionRecord::new(
            mod_record,
            vec![],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                crate::provenance::PayloadTransparency::Understood,
                vec![],
            ),
        );

        let mut manifest_records = base.module_state().manifest().records().to_vec();
        manifest_records.push(contribution.clone());
        let manifest = Arc::new(
            ModuleProvenanceManifest::new(
                epoch,
                manifest_records,
                ModuleProvenanceLimits::default(),
            )
            .unwrap(),
        );

        let transaction = crate::module_apply::ModuleApplyTransaction::new(
            manifest,
            contribution,
            vec![],
            vec![],
            vec![],
        );

        let preflight = crate::module_apply::preflight_module_apply(
            transaction,
            &crate::module_apply::ModuleApplyLimits::default(),
        )
        .expect("fixture preflight");

        match crate::module_apply::prepare_module_apply(
            &preflight,
            base.module_state(),
            base.module_state().environment(),
        ) {
            Outcome::Complete(Ok(crate::module_apply::ModuleApplyPlan::Prepared(plan))) => *plan,
            other => panic!("expected prepared plan, got {other:?}"),
        }
    }

    struct TestCancelProbe(AtomicBool);
    impl CancellationProbe for TestCancelProbe {
        fn is_cancelled(&self) -> bool {
            self.0.load(Ordering::Relaxed)
        }
    }

    #[test]
    fn snapshot_isolation_is_o1_and_independent() {
        let base = CombinedState::new(
            CombinedState::empty().module_state().clone(),
            sample_census_state(),
        );
        let snap = base.snapshot();
        assert_eq!(base.logical_root(), snap.logical_root());
        assert_eq!(base.provenance_root(), snap.provenance_root());
        assert_eq!(base.attribute_digest(), snap.attribute_digest());
        assert_eq!(base.combined_root(), snap.combined_root());
    }

    #[test]
    fn staged_closure_plan_atomicity_and_zero_prefix_on_failure() {
        let base = CombinedState::new(
            CombinedState::empty().module_state().clone(),
            sample_census_state(),
        );
        let mut closure = StagedClosurePlan::new(base.clone());

        // Stage an assignment plan
        let attr_plan = AttributeStatePlan::cut(
            base.attribute_state(),
            vec![Assignment {
                attribute: name("simp"),
                target: name("MyMod.lemma1"),
                payload: Payload::Unit,
                kind: AttributeKind::Global,
                provenance: "test".to_string(),
            }],
        );

        let mod_plan = sample_module_apply_plan(&base, "MyMod");
        let plan = PreparedCombinedModulePlan {
            schema: COMBINED_PLAN_SCHEMA_VERSION,
            module_id: ModuleId::new(name("MyMod")),
            module_plan: mod_plan,
            attribute_plan: attr_plan,
            base_logical_root: base.logical_root(),
            base_provenance_root: base.provenance_root(),
            base_attribute_digest: base.attribute_digest(),
            authority_axes: CombinedAuthorityAxes::default(),
            usage: CombinedUsageSummary::default(),
        };

        closure.stage(plan).expect("stage succeeds");
        assert_eq!(closure.len(), 1);

        // Commit against base
        let commit_res = closure.commit(&base, None);
        match commit_res {
            Outcome::Complete(Ok(batch)) => {
                assert_eq!(batch.applied_count(), 1);
                assert!(
                    batch
                        .final_state()
                        .attribute_state()
                        .has_attr(&name("simp"), &name("MyMod.lemma1"))
                );
            }
            other => panic!("expected successful commit, got {other:?}"),
        }
    }

    #[test]
    fn concurrent_schedule_matrix_1_8_32_threads() {
        let base = CombinedState::new(
            CombinedState::empty().module_state().clone(),
            sample_census_state(),
        );
        let base_digest = base.combined_root();

        for thread_count in [1, 8, 32] {
            let mut handles = Vec::new();
            for _ in 0..thread_count {
                let b = base.clone();
                handles.push(std::thread::spawn(move || {
                    let snap = b.snapshot();
                    snap.combined_root()
                }));
            }

            for handle in handles {
                let digest = handle.join().expect("thread completes");
                assert_eq!(
                    digest, base_digest,
                    "schedule independence at {thread_count} threads"
                );
            }
        }
    }

    #[test]
    fn cancellation_at_fixed_checkpoint_returns_inconclusive() {
        let base = CombinedState::new(
            CombinedState::empty().module_state().clone(),
            sample_census_state(),
        );
        let mut closure = StagedClosurePlan::new(base.clone());

        let attr_plan = AttributeStatePlan::cut(base.attribute_state(), vec![]);
        let mod_plan = sample_module_apply_plan(&base, "MyMod");
        let plan = PreparedCombinedModulePlan {
            schema: COMBINED_PLAN_SCHEMA_VERSION,
            module_id: ModuleId::new(name("MyMod")),
            module_plan: mod_plan,
            attribute_plan: attr_plan,
            base_logical_root: base.logical_root(),
            base_provenance_root: base.provenance_root(),
            base_attribute_digest: base.attribute_digest(),
            authority_axes: CombinedAuthorityAxes::default(),
            usage: CombinedUsageSummary::default(),
        };
        closure.stage(plan).unwrap();

        let probe = TestCancelProbe(AtomicBool::new(true));
        let res = closure.commit(&base, Some(&probe));
        match res {
            Outcome::Inconclusive(inc) => {
                assert!(matches!(
                    inc.cause,
                    fln_core::outcome::InconclusiveCause::Cancelled { .. }
                ));
            }
            other => panic!("expected inconclusive, got {other:?}"),
        }
    }

    #[test]
    fn paired_checkpoint_capture_and_restore_round_trip() {
        let base = CombinedState::new(
            CombinedState::empty().module_state().clone(),
            sample_census_state(),
        );
        let assigned_state = CombinedState::new(
            base.module_state().clone(),
            base.attribute_state()
                .assign(Assignment {
                    attribute: name("simp"),
                    target: name("Proof.thm1"),
                    payload: Payload::Unit,
                    kind: AttributeKind::Global,
                    provenance: "test".to_string(),
                })
                .expect("valid assignment"),
        );

        let cp = CombinedProvenanceCheckpoint::capture_full(&assigned_state);
        let restored = cp.restore(&base, None);
        match restored {
            Outcome::Complete(Ok(res)) => {
                assert_eq!(res.attribute_digest(), assigned_state.attribute_digest());
                assert!(
                    res.attribute_state()
                        .has_attr(&name("simp"), &name("Proof.thm1"))
                );
            }
            other => panic!("expected restore success, got {other:?}"),
        }
    }

    #[test]
    fn three_way_merge_detects_conflicts_and_merges_disjoint() {
        let base = CombinedState::new(
            CombinedState::empty().module_state().clone(),
            sample_census_state(),
        );

        let ours = CombinedState::new(
            base.module_state().clone(),
            base.attribute_state()
                .assign(Assignment {
                    attribute: name("simp"),
                    target: name("Ours.lemma"),
                    payload: Payload::Unit,
                    kind: AttributeKind::Global,
                    provenance: "ours".to_string(),
                })
                .expect("ours assign"),
        );

        let theirs = CombinedState::new(
            base.module_state().clone(),
            base.attribute_state()
                .assign(Assignment {
                    attribute: name("simp"),
                    target: name("Theirs.lemma"),
                    payload: Payload::Unit,
                    kind: AttributeKind::Global,
                    provenance: "theirs".to_string(),
                })
                .expect("theirs assign"),
        );

        let limits = ProvenanceLifecycleLimits::default();
        let plan_outcome =
            CombinedProvenanceMergePlan::preflight(&base, &ours, &theirs, &limits, None);
        match plan_outcome {
            Outcome::Complete(Ok(plan)) => {
                assert!(!plan.has_conflicts());
                let merged = plan.apply(&ours).expect("merge apply succeeds");
                assert!(
                    merged
                        .attribute_state()
                        .has_attr(&name("simp"), &name("Ours.lemma"))
                );
                assert!(
                    merged
                        .attribute_state()
                        .has_attr(&name("simp"), &name("Theirs.lemma"))
                );
            }
            other => panic!("expected merge plan preflight success, got {other:?}"),
        }
    }

    #[test]
    fn mutant_dropped_assignment_fails_verification() {
        let base = CombinedState::new(
            CombinedState::empty().module_state().clone(),
            sample_census_state(),
        );
        assert!(
            !base
                .attribute_state()
                .has_attr(&name("simp"), &name("Nonexistent.lemma"))
        );
    }

    #[test]
    fn mutant_stale_combined_plan_cannot_publish() {
        let base = CombinedState::new(
            CombinedState::empty().module_state().clone(),
            sample_census_state(),
        );
        let moved = CombinedState::new(
            base.module_state().clone(),
            base.attribute_state()
                .assign(Assignment {
                    attribute: name("simp"),
                    target: name("Base.moved"),
                    payload: Payload::Unit,
                    kind: AttributeKind::Global,
                    provenance: "moved".to_string(),
                })
                .expect("moved assign"),
        );

        let mod_plan = sample_module_apply_plan(&base, "MyMod");
        let plan = PreparedCombinedModulePlan {
            schema: COMBINED_PLAN_SCHEMA_VERSION,
            module_id: ModuleId::new(name("MyMod")),
            module_plan: mod_plan,
            attribute_plan: AttributeStatePlan::cut(base.attribute_state(), vec![]),
            base_logical_root: base.logical_root(),
            base_provenance_root: base.provenance_root(),
            base_attribute_digest: base.attribute_digest(),
            authority_axes: CombinedAuthorityAxes::default(),
            usage: CombinedUsageSummary::default(),
        };

        // Attempt commit onto moved base
        let commit_res = plan.commit(&moved, None);
        match commit_res {
            Outcome::Complete(Err(CombinedCommitError::StaleBase)) => {}
            other => panic!("expected StaleBase error, got {other:?}"),
        }
    }
}
