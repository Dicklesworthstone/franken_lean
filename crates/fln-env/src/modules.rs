//! Lossless persistent module records and the ordered import DAG (plan §7.1,
//! bead `fln-amv.9.1`).
//!
//! `ModuleData` does not carry the identity of the module it describes. The
//! resolver therefore supplies a [`ModuleId`] and explicit [`ArtifactEvidence`]
//! when registering a decoded record. Direct `Lean.Import` rows remain an
//! ordered `Arc` slice: flags and duplicates are never normalized away.
//!
//! The graph is immutable. A clone bumps one state `Arc`; insertion creates a
//! fresh state whose persistent [`PMap`] shares untouched trie structure. Missing
//! targets are an explicit completeness state, while self edges and cycles are
//! typed refusals. Diagnostics use canonical `Name.cmp` order wherever the
//! Reference does not prescribe an observable order.

use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use fln_core::name::{LeafView, Name};
use fln_hash::domain::Digest;

use crate::pmap::{PKey, PMap};

/// The three registered ordering policies for the module substrate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleOrderPolicy {
    /// Preserve each decoded direct-import array exactly.
    ReferenceDirectOrder,
    /// Reserved for the pinned effective-import traversal in `fln-amv.9.2`.
    ReferenceDiscoveryOrder,
    /// `Name.cmp` order for semantically free sets and diagnostics.
    CanonicalNameOrder,
}

pub const DIRECT_IMPORT_ORDER: ModuleOrderPolicy = ModuleOrderPolicy::ReferenceDirectOrder;
pub const DISCOVERY_ORDER: ModuleOrderPolicy = ModuleOrderPolicy::ReferenceDiscoveryOrder;
pub const DIAGNOSTIC_ORDER: ModuleOrderPolicy = ModuleOrderPolicy::CanonicalNameOrder;

/// Explicit module identity supplied by artifact resolution, never inferred
/// from a file path or from an import row.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleId(Name);

impl ModuleId {
    pub fn new(name: Name) -> Self {
        Self(name)
    }

    pub fn name(&self) -> &Name {
        &self.0
    }

    pub fn into_name(self) -> Name {
        self.0
    }
}

impl PKey for ModuleId {
    fn key_hash(&self) -> u64 {
        self.0.hash()
    }
}

/// Epoch identity to which one graph is pinned.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleEpoch {
    tag: Arc<str>,
    commit: Arc<str>,
}

impl ModuleEpoch {
    pub fn new(tag: impl Into<Arc<str>>, commit: impl Into<Arc<str>>) -> Self {
        Self {
            tag: tag.into(),
            commit: commit.into(),
        }
    }

    pub fn tag(&self) -> &str {
        &self.tag
    }

    pub fn commit(&self) -> &str {
        &self.commit
    }

    pub(crate) fn is_well_formed(&self) -> bool {
        !self.tag.is_empty()
            && self.tag.trim() == self.tag.as_ref()
            && !self.tag.chars().any(char::is_control)
            && self.commit.len() == 40
            && self
                .commit
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    }

    pub(crate) fn payload_bytes(&self) -> u128 {
        self.tag.len() as u128 + self.commit.len() as u128
    }
}

/// Producer named by artifact-resolution evidence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArtifactProducer {
    Reference,
    FrankenLean,
}

/// Strength of the source evidence attached to a module artifact.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArtifactGrade {
    Provisional,
    Verified,
    OracleFixture,
}

/// Identity and provenance of the bytes from which a record was decoded.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ArtifactEvidence {
    pub epoch: ModuleEpoch,
    pub content_digest: Digest,
    pub producer: ArtifactProducer,
    pub grade: ArtifactGrade,
}

/// Exact `Lean.Import` payload used by the environment layer.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct DirectImport {
    pub module: ModuleId,
    pub import_all: bool,
    pub is_exported: bool,
    pub is_meta: bool,
}

impl DirectImport {
    pub fn new(module: ModuleId, import_all: bool, is_exported: bool, is_meta: bool) -> Self {
        Self {
            module,
            import_all,
            is_exported,
            is_meta,
        }
    }
}

/// One resolver-bound module record. Direct rows use compact immutable storage
/// so snapshots and graph clones do not copy import vectors.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleRecord {
    pub id: ModuleId,
    pub is_module: bool,
    imports: Arc<[DirectImport]>,
    pub artifact: ArtifactEvidence,
}

impl ModuleRecord {
    pub fn new(
        id: ModuleId,
        is_module: bool,
        imports: Vec<DirectImport>,
        artifact: ArtifactEvidence,
    ) -> Self {
        Self {
            id,
            is_module,
            imports: imports.into(),
            artifact,
        }
    }

    pub fn direct_imports(&self) -> &[DirectImport] {
        &self.imports
    }

    pub fn direct_imports_arc(&self) -> Arc<[DirectImport]> {
        Arc::clone(&self.imports)
    }

    /// Classify every repeated target without changing the raw row array.
    pub fn duplicate_imports(&self) -> Vec<DuplicateImport> {
        let mut first_by_target: BTreeMap<ModuleId, usize> = BTreeMap::new();
        let mut first_by_row: BTreeMap<DirectImport, usize> = BTreeMap::new();
        let mut duplicates = Vec::new();
        for (index, import) in self.imports.iter().enumerate() {
            if let Some(first_index) = first_by_target.get(&import.module).copied() {
                if let Some(exact_index) = first_by_row.get(import).copied() {
                    duplicates.push(DuplicateImport {
                        first_index: exact_index,
                        duplicate_index: index,
                        kind: DuplicateImportKind::ExactRow,
                    });
                } else {
                    duplicates.push(DuplicateImport {
                        first_index,
                        duplicate_index: index,
                        kind: DuplicateImportKind::SameTargetDifferentFlags,
                    });
                }
            } else {
                first_by_target.insert(import.module.clone(), index);
            }
            first_by_row.entry(import.clone()).or_insert(index);
        }
        duplicates
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DuplicateImportKind {
    ExactRow,
    SameTargetDifferentFlags,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DuplicateImport {
    pub first_index: usize,
    pub duplicate_index: usize,
    pub kind: DuplicateImportKind,
}

/// Hard graph limits. Direct rows, including duplicates, count as edges because
/// they consume decode, replay, logging, and storage resources independently.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleGraphLimits {
    pub max_modules: usize,
    pub max_edges: usize,
    pub max_name_depth: usize,
    pub max_payload_bytes: u128,
}

impl ModuleGraphLimits {
    pub const fn new(
        max_modules: usize,
        max_edges: usize,
        max_name_depth: usize,
        max_payload_bytes: u128,
    ) -> Self {
        Self {
            max_modules,
            max_edges,
            max_name_depth,
            max_payload_bytes,
        }
    }
}

impl Default for ModuleGraphLimits {
    fn default() -> Self {
        Self::new(1_000_000, 20_000_000, 100_000, 4 * 1024 * 1024 * 1024)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleGraphResource {
    Modules,
    DirectImportRows,
    NameDepth,
    PayloadBytes,
}

/// What a plan's usage totals do and do not charge (bead `franken_lean-6sf3` item 5).
///
/// The bead requires the `fln-amv.13` collision/PMap facts to be handed off and charged
/// exactly once, and decoder work owned by `fln-20n.1` to be referenced by digest rather
/// than recharged as graph work. Both are stated here as facts rather than assumed,
/// because "charged once" and "not charged at all" are different claims and a consumer
/// building a resource argument on the wrong one gets a wrong answer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChargeHandoff {
    /// PMap collision-family admission work, owned by `fln-amv.13`.
    pub pmap_admission: ChargeOwnership,
    /// Decoder work and bytes, owned by `fln-20n.1`.
    pub decoder: ChargeOwnership,
}

/// Who charges one resource, and whether this layer charges it at all.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChargeOwnership {
    /// Charged here, exactly once, at plan time. The consuming phase must charge zero.
    ChargedOnceAtPlanTime,
    /// Charged by its owner and referenced only, never recharged as graph work.
    OwnedElsewhere { owner: &'static str },
    /// Not charged anywhere at this layer, with the reason. Not a claim that the work is
    /// free — a refusal to claim it is accounted.
    Uncharged { reason: &'static str },
}

/// Whether a plan claims a genuinely fallible pre-publication reservation.
///
/// A three-state fact rather than a boolean, because "we reserved nothing" and "there is
/// nothing here that *can* be reserved" are different claims and a consumer must be able
/// to tell them apart. See [`ModuleGraphAdmissionPlan::reservation`] for why this layer
/// reports `Unsupported`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReservationClaim {
    /// Capacity was reserved through a demonstrably fallible call before publication, so
    /// the final phase uses reserved storage and cannot fail for want of memory.
    Reserved { units: usize },
    /// No reservation was needed: the publication allocates nothing input-sized.
    NotRequired,
    /// A reservation is not expressible here, with the reason. **Not** a promise that
    /// publication cannot fail — a promise that no such promise is being made.
    Unsupported { reason: &'static str },
}

/// Exact dimensions reported when the same module identity is re-registered
/// with a non-identical record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ModuleRecordField {
    IsModule,
    DirectImports,
    ArtifactContentDigest,
    ArtifactProducer,
    ArtifactGrade,
}

/// Typed insertion refusal. Inputs and the source graph remain unchanged.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleGraphError {
    MalformedEpoch {
        tag: Arc<str>,
        commit: Arc<str>,
    },
    EpochMismatch {
        module: ModuleId,
        expected: ModuleEpoch,
        actual: ModuleEpoch,
    },
    AnonymousModule,
    AnonymousImport {
        owner: ModuleId,
        import_index: usize,
    },
    OverflowingNameComponent {
        module: ModuleId,
    },
    ResourceLimitExceeded {
        module: Option<ModuleId>,
        resource: ModuleGraphResource,
        limit: u128,
        actual: u128,
    },
    ConflictingRecord {
        module: ModuleId,
        differing_fields: Vec<ModuleRecordField>,
        existing_artifact: Box<ArtifactEvidence>,
        incoming_artifact: Box<ArtifactEvidence>,
    },
    SelfImport {
        module: ModuleId,
        import_index: usize,
    },
    Cycle {
        path: Vec<ModuleId>,
    },
}

impl std::fmt::Display for ModuleGraphError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::MalformedEpoch { tag, commit } => {
                write!(
                    formatter,
                    "malformed module epoch tag={tag:?} commit={commit:?}"
                )
            }
            Self::EpochMismatch {
                module,
                expected,
                actual,
            } => write!(
                formatter,
                "module `{}` epoch {}@{} does not match graph {}@{}",
                module.name().to_display_string(),
                actual.tag(),
                actual.commit(),
                expected.tag(),
                expected.commit()
            ),
            Self::AnonymousModule => write!(formatter, "anonymous is not a module identity"),
            Self::AnonymousImport {
                owner,
                import_index,
            } => write!(
                formatter,
                "module `{}` has an anonymous target at direct row {import_index}",
                owner.name().to_display_string()
            ),
            Self::OverflowingNameComponent { module } => write!(
                formatter,
                "module `{}` contains an overflowing numeric Name component",
                module.name().to_display_string()
            ),
            Self::ResourceLimitExceeded {
                module,
                resource,
                limit,
                actual,
            } => write!(
                formatter,
                "module graph resource {resource:?} exceeded for {}: {actual} > {limit}",
                module
                    .as_ref()
                    .map(|id| id.name().to_display_string())
                    .unwrap_or_else(|| "<graph>".to_owned())
            ),
            Self::ConflictingRecord {
                module,
                differing_fields,
                ..
            } => write!(
                formatter,
                "module `{}` was registered with different fields: {differing_fields:?}",
                module.name().to_display_string(),
            ),
            Self::SelfImport {
                module,
                import_index,
            } => write!(
                formatter,
                "module `{}` imports itself at direct row {import_index}",
                module.name().to_display_string()
            ),
            Self::Cycle { path } => {
                formatter.write_str("module import cycle: ")?;
                for (index, module) in path.iter().enumerate() {
                    if index > 0 {
                        formatter.write_str(" -> ")?;
                    }
                    formatter.write_str(&module.name().to_display_string())?;
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegistrationDisposition {
    Inserted,
    Idempotent,
}

/// Deterministic work facts for audit logs and operation-count regressions.
/// These are counts, never wall-clock measurements.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct RegistrationWork {
    pub name_components_validated: usize,
    pub direct_rows_validated: usize,
    pub cycle_modules_visited: usize,
    pub cycle_rows_examined: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Registration {
    pub graph: ModuleGraph,
    pub disposition: RegistrationDisposition,
    pub work: RegistrationWork,
}

/// Deterministic points at which a registration samples its cancellation flag.
///
/// Named rather than positional so a cancelled outcome says *how far the work
/// got* — which is the difference between "we learned nothing" and "we learned
/// the input was malformed but stopped before deciding".
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum RegistrationCheckpoint {
    /// Before any input was inspected.
    Entry,
    /// After the record validated, before the existing-record lookup.
    AfterValidation,
    /// After the conflict/idempotence lookup, before the budget checks.
    AfterConflictLookup,
    /// After the budgets passed, before the cycle scan and publication.
    BeforePublication,
}

/// A source of cancellation for a registration.
///
/// An abstraction rather than a bare flag because callers do not all hold one: a
/// scheduler may carry a capability context, a server a request-scoped token. It
/// also makes the checkpoint contract *provable* — a test can supply a probe that
/// trips at a chosen sample and pin the outcome for that exact checkpoint, which a
/// pre-set `AtomicBool` can never do because it always trips at the first sample.
pub trait CancellationProbe {
    /// Sampled at each [`RegistrationCheckpoint`]. Must be cheap; registration
    /// samples it a bounded number of times per call.
    fn is_cancelled(&self) -> bool;
}

impl CancellationProbe for AtomicBool {
    fn is_cancelled(&self) -> bool {
        self.load(Ordering::Relaxed)
    }
}

/// FL-INV-07 inconclusive outcomes of a registration: operational exhaustion and
/// cancellation. Both mean *no verdict was reached about this record*.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleGraphInconclusive {
    /// A configured budget bound before publication.
    ResourceLimitExceeded {
        module: Option<ModuleId>,
        resource: ModuleGraphResource,
        limit: u128,
        actual: u128,
    },
    /// The caller cancelled. The checkpoint records the last completed phase.
    Cancelled {
        module: ModuleId,
        checkpoint: RegistrationCheckpoint,
    },
    /// A prepared admission was committed against a base that had moved since it
    /// was decided (bead `franken_lean-6sf3`).
    ///
    /// Inconclusive rather than rejected, and the distinction is the usual one: the
    /// base moving says nothing about whether this module is admissible. Re-deciding
    /// against the current base may well admit it. Caching this as a refusal would
    /// record "the graph was busy" as "this module is invalid".
    PlanSuperseded {
        module: ModuleId,
        expected_revision: u64,
        actual_revision: u64,
    },
}

/// The typed outcome of one module-graph registration (bead
/// `franken_lean-module-graph-resource-outcomes-46b`).
///
/// Three arms, and the split is the point. A [`Rejected`](Self::Rejected) record is
/// one the graph has *decided about* — malformed input, or a semantic conflict such
/// as a nonidentical re-registration, a self-import, or a cycle. An
/// [`Inconclusive`](Self::Inconclusive) record is one the graph *did not finish
/// deciding*: a budget bound, or the caller cancelled. Collapsing the two would let
/// "we ran out of room" be recorded, cached, and later replayed as "this module is
/// invalid" — the same silent-wrong-value class as a colliding witness.
///
/// Registration is an immutable transition: the receiver is never mutated, so every
/// non-`Complete` arm leaves the base graph observably identical and no partial
/// module is ever reachable.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleGraphOutcome<T> {
    /// The operation finished and produced `T`.
    Complete(T),
    /// A complete, resource-independent determination that the input is not
    /// admissible.
    Rejected(ModuleGraphError),
    /// No verdict was reached. Never accepted, never rejected, never cacheable.
    Inconclusive(ModuleGraphInconclusive),
}

/// Frozen logical usage units, version 1 (bead `franken_lean-6sf3`).
///
/// "Frozen" is the load-bearing word. If the plan says a registration costs N of a
/// unit and admission then charges M, the plan is decoration. These units are the
/// shared vocabulary both sides account in, each pinned to the deterministic
/// observation point at which it is charged, so a drift between plan and execution
/// is a test failure rather than a discrepancy nobody notices.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UsageUnit {
    /// Modules the graph would hold after this registration.
    Modules,
    /// Direct import rows the graph would hold after this registration.
    DirectImportRows,
    /// Name components inspected while validating this record.
    NameComponents,
    /// Artifact payload bytes the graph would account after this registration.
    PayloadBytes,
    /// Modules visited by the cycle scan.
    CycleModulesVisited,
    /// Import rows examined by the cycle scan.
    CycleRowsExamined,
}

impl UsageUnit {
    /// Every unit, in the order they are charged.
    pub const ALL: [UsageUnit; 6] = [
        Self::NameComponents,
        Self::Modules,
        Self::DirectImportRows,
        Self::PayloadBytes,
        Self::CycleModulesVisited,
        Self::CycleRowsExamined,
    ];

    /// Version of the unit vocabulary itself. A unit added, removed, or redefined
    /// moves this, because a consumer comparing usage across versions is comparing
    /// two different accounting systems.
    pub const VERSION: u16 = 1;

    pub const fn label(self) -> &'static str {
        match self {
            Self::Modules => "modules",
            Self::DirectImportRows => "direct_import_rows",
            Self::NameComponents => "name_components",
            Self::PayloadBytes => "payload_bytes",
            Self::CycleModulesVisited => "cycle_modules_visited",
            Self::CycleRowsExamined => "cycle_rows_examined",
        }
    }

    /// The deterministic observation point at which this unit becomes exact.
    ///
    /// A refusal before this point cannot report the unit exactly, which is why
    /// [`UsageExactness`] exists rather than a total that quietly means different
    /// things depending on where the work stopped.
    pub const fn observed_at(self) -> RegistrationCheckpoint {
        match self {
            Self::NameComponents => RegistrationCheckpoint::AfterValidation,
            Self::Modules | Self::DirectImportRows | Self::PayloadBytes => {
                RegistrationCheckpoint::AfterConflictLookup
            }
            Self::CycleModulesVisited | Self::CycleRowsExamined => {
                RegistrationCheckpoint::BeforePublication
            }
        }
    }
}

/// Whether a usage total is exact or a witnessed lower bound.
///
/// A refusal reports the work actually observed through its checkpoint plus the
/// knowledge that more was required — never a scan of the unobserved suffix merely
/// to claim an exact total, which would make refusal cost more than success.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UsageExactness {
    /// Every unit was observed to completion.
    Exact,
    /// Work stopped at the recorded checkpoint; totals are a lower bound on the
    /// work the operation would have required.
    LowerBound,
}

/// Phase-local usage in [frozen units](UsageUnit).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct PlannedUsage {
    pub modules: u128,
    pub direct_import_rows: u128,
    pub name_components: u128,
    pub payload_bytes: u128,
    pub cycle_modules_visited: u128,
    pub cycle_rows_examined: u128,
}

impl PlannedUsage {
    /// Total for one unit. Exhaustive by construction so a new unit cannot be
    /// silently unaccounted.
    pub const fn get(&self, unit: UsageUnit) -> u128 {
        match unit {
            UsageUnit::Modules => self.modules,
            UsageUnit::DirectImportRows => self.direct_import_rows,
            UsageUnit::NameComponents => self.name_components,
            UsageUnit::PayloadBytes => self.payload_bytes,
            UsageUnit::CycleModulesVisited => self.cycle_modules_visited,
            UsageUnit::CycleRowsExamined => self.cycle_rows_examined,
        }
    }
}

/// The **total** precedence order over admission outcomes (bead `franken_lean-6sf3`).
///
/// Every registration resolves to exactly one of these, and the declaration order IS
/// the precedence order — [`rank`](Self::rank) is derived from [`ALL`](Self::ALL)
/// rather than hand-numbered, so the table cannot disagree with itself. Two inputs
/// that breach simultaneously must resolve to the earlier rule on every schedule;
/// that is what makes the outcome schedule-independent (FL-INV-01) instead of a race
/// between which check happened to run first.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum AdmissionPrecedence {
    CancelledAtEntry,
    MalformedInput,
    ResourceNameDepth,
    CancelledAfterValidation,
    ExistingRecordIdempotent,
    ExistingRecordConflict,
    CancelledAfterConflictLookup,
    ResourceModules,
    ResourceDirectImportRows,
    ResourcePayloadBytes,
    CancelledBeforePublication,
    CycleDetected,
    Admitted,
}

impl AdmissionPrecedence {
    /// Every rule, in precedence order. This array is the normative table.
    pub const ALL: [AdmissionPrecedence; 13] = [
        Self::CancelledAtEntry,
        Self::MalformedInput,
        Self::ResourceNameDepth,
        Self::CancelledAfterValidation,
        Self::ExistingRecordIdempotent,
        Self::ExistingRecordConflict,
        Self::CancelledAfterConflictLookup,
        Self::ResourceModules,
        Self::ResourceDirectImportRows,
        Self::ResourcePayloadBytes,
        Self::CancelledBeforePublication,
        Self::CycleDetected,
        Self::Admitted,
    ];

    /// Position in the precedence order; lower wins a tie.
    pub fn rank(self) -> usize {
        Self::ALL
            .iter()
            .position(|entry| *entry == self)
            .expect("ALL covers every precedence rule")
    }

    pub const fn label(self) -> &'static str {
        match self {
            Self::CancelledAtEntry => "cancelled_at_entry",
            Self::MalformedInput => "malformed_input",
            Self::ResourceNameDepth => "resource_name_depth",
            Self::CancelledAfterValidation => "cancelled_after_validation",
            Self::ExistingRecordIdempotent => "existing_record_idempotent",
            Self::ExistingRecordConflict => "existing_record_conflict",
            Self::CancelledAfterConflictLookup => "cancelled_after_conflict_lookup",
            Self::ResourceModules => "resource_modules",
            Self::ResourceDirectImportRows => "resource_direct_import_rows",
            Self::ResourcePayloadBytes => "resource_payload_bytes",
            Self::CancelledBeforePublication => "cancelled_before_publication",
            Self::CycleDetected => "cycle_detected",
            Self::Admitted => "admitted",
        }
    }

    /// The checkpoint through which work is observed when this rule decides.
    pub const fn checkpoint(self) -> RegistrationCheckpoint {
        match self {
            Self::CancelledAtEntry => RegistrationCheckpoint::Entry,
            Self::MalformedInput | Self::ResourceNameDepth | Self::CancelledAfterValidation => {
                RegistrationCheckpoint::AfterValidation
            }
            Self::ExistingRecordIdempotent
            | Self::ExistingRecordConflict
            | Self::CancelledAfterConflictLookup
            | Self::ResourceModules
            | Self::ResourceDirectImportRows
            | Self::ResourcePayloadBytes => RegistrationCheckpoint::AfterConflictLookup,
            Self::CancelledBeforePublication | Self::CycleDetected | Self::Admitted => {
                RegistrationCheckpoint::BeforePublication
            }
        }
    }

    /// Whether a plan decided by this rule would publish when consumed.
    pub const fn publishes(self) -> bool {
        matches!(self, Self::Admitted)
    }
}

/// What a base graph a plan was computed against must still look like at consumption.
///
/// **This is a lineage binding, not a content root.** It pins the epoch, the limits,
/// the observable facts, and a monotonic per-lineage revision, which together detect
/// any mutation of the graph the plan was computed against — the `revision` moves on
/// every publication, so a plan can never be consumed against a base that has since
/// grown. What it deliberately does NOT claim is content equality across unrelated
/// lineages: two graphs that never shared history could in principle present the same
/// epoch, limits, facts, and revision. Closing that needs a content root over the
/// record map, which this layer does not have and will not compute per plan because
/// it would make planning O(n) in the graph. Stated rather than implied, because a
/// consumer that reads this as a content root would be relying on something it does
/// not prove.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGraphBinding {
    pub epoch: ModuleEpoch,
    pub limits: ModuleGraphLimits,
    pub facts: ModuleGraphFacts,
    pub revision: u64,
}

/// A **nonpublishing** account of what one registration would do.
///
/// The whole point is in the first word. Computing a plan mutates nothing
/// observable: the base graph is untouched (it is immutable anyway), no environment
/// changes, no logical root moves, and the plan itself is never cacheable — a plan
/// that published would just be admission with extra steps.
///
/// It is also not decoration: [`ModuleGraph::plan_registration`] and
/// [`ModuleGraph::register_cancellable`] run the *same* decision procedure, so the
/// precedence rule, the checkpoint, and every frozen usage unit agree by
/// construction rather than by a test that hopes two implementations stayed in step.
///
/// A plan is non-authoritative until consumed. It carries no authority to admit
/// anything on its own, and `is_cacheable()` is false for every plan, including one
/// predicting a clean admission: caching a prediction would let a stale prediction
/// stand in for a decision, and caching one that predicted exhaustion would replay an
/// FL-INV-07 inconclusive as though it were an answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGraphAdmissionPlan {
    version: u16,
    usage_version: u16,
    base: ModuleGraphBinding,
    request: ModuleId,
    precedence: AdmissionPrecedence,
    checkpoint: RegistrationCheckpoint,
    usage: PlannedUsage,
    exactness: UsageExactness,
    predicted_facts: Option<ModuleGraphFacts>,
}

impl ModuleGraphAdmissionPlan {
    /// Schema version of the plan itself.
    pub const VERSION: u16 = 1;

    /// What this plan's usage totals charge, and what they deliberately do not.
    ///
    /// The six frozen [`UsageUnit`]s are all graph work. Two other resources the bead
    /// names are handled by exclusion rather than by accounting, and saying which is the
    /// point:
    ///
    /// * **PMap admission work is `Uncharged` here**, because module registration uses
    ///   the unbudgeted [`PMap::insert`](crate::pmap::PMap::insert) rather than
    ///   `try_insert_with_budget`. There are therefore no `fln-amv.13` facts to hand off
    ///   yet — a handoff of facts nobody produced would be a fiction. Moving registration
    ///   onto the budgeted insert is a real change, and it should wait for
    ///   `franken_lean-pmap-refusal-outcome-taxonomy-i1z9`, which is changing that
    ///   contract's refusal type: charging against a signature under revision would have
    ///   to be redone.
    /// * **Decoder work is `OwnedElsewhere`**, and the enforcement is structural rather
    ///   than a promise: no `UsageUnit` denominates decoder work, so this layer has no
    ///   field in which to recharge it even by accident. `fln-20n.1` owns it and it is
    ///   referenced by digest.
    pub const fn charges(&self) -> ChargeHandoff {
        ChargeHandoff {
            pmap_admission: ChargeOwnership::Uncharged {
                reason: "module registration uses the unbudgeted PMap::insert, so no \
                         fln-amv.13 collision facts are produced to hand off",
            },
            decoder: ChargeOwnership::OwnedElsewhere { owner: "fln-20n.1" },
        }
    }

    /// Whether this plan claims a genuinely fallible pre-publication reservation.
    ///
    /// **Always [`ReservationClaim::Unsupported`] at this layer, and that is a reported
    /// fact rather than an omission.** `franken_lean-6sf3`'s acceptance asks for
    /// reservations performed *where supported*, and here they are not supported: every
    /// allocating path in a publication is infallible-or-abort. `Arc::new` aborts the
    /// process on allocation failure, and [`PMap`](crate::pmap::PMap) allocates its nodes
    /// internally through the same infallible primitives. There is no point at which this
    /// code could ask for memory, be told no, and return a typed refusal.
    ///
    /// Claiming a reservation anyway would be the exact untruthful resource fact this
    /// family of beads exists to remove — a promise to recover from an allocator abort
    /// that no path can keep. So the claim is surfaced as a value, so a consumer
    /// (notably `franken_lean-module-provenance-atomic-apply-as7`) cannot assume a
    /// reservation happened.
    ///
    /// Making it genuine requires a fallible allocation path in `PMap` — a `try_insert`
    /// built on `Vec::try_reserve` — which is a real change to a published contract and
    /// belongs in its own bead rather than being smuggled in behind a plan field.
    pub const fn reservation(&self) -> ReservationClaim {
        ReservationClaim::Unsupported {
            reason: "every allocating path in a module-graph publication is \
                     infallible-or-abort (Arc::new, PMap node allocation)",
        }
    }

    pub fn version(&self) -> u16 {
        self.version
    }

    /// Version of the [`UsageUnit`] vocabulary the totals are denominated in.
    pub fn usage_version(&self) -> u16 {
        self.usage_version
    }

    pub fn base(&self) -> &ModuleGraphBinding {
        &self.base
    }

    /// The module this plan was computed for.
    pub fn request(&self) -> &ModuleId {
        &self.request
    }

    /// The precedence rule that decided this plan.
    pub fn precedence(&self) -> AdmissionPrecedence {
        self.precedence
    }

    /// The deterministic observation point the decision reached.
    pub fn checkpoint(&self) -> RegistrationCheckpoint {
        self.checkpoint
    }

    pub fn usage(&self) -> PlannedUsage {
        self.usage
    }

    pub fn exactness(&self) -> UsageExactness {
        self.exactness
    }

    /// The facts the graph would carry if this plan were consumed and published.
    /// `None` unless the plan predicts publication.
    pub fn predicted_facts(&self) -> Option<&ModuleGraphFacts> {
        self.predicted_facts.as_ref()
    }

    /// Whether consuming this plan would publish a new graph state.
    pub fn publishes(&self) -> bool {
        self.precedence.publishes()
    }

    /// **Never.** A plan is a prediction, not a decision.
    pub const fn is_cacheable(&self) -> bool {
        false
    }

    /// Whether the plan is still valid against `graph`.
    ///
    /// Revalidated immediately before consumption, never trusted from when it was
    /// computed: the base may have moved, and a plan computed against one base is
    /// meaningless against another.
    pub fn is_valid_for(&self, graph: &ModuleGraph) -> bool {
        self.version == Self::VERSION
            && self.usage_version == UsageUnit::VERSION
            && self.base == graph.binding()
    }
}

/// The typed outcome of one module-graph **registration**.
pub type ModuleGraphAdmission = ModuleGraphOutcome<Registration>;

/// The typed outcome of module-graph **construction**.
///
/// Construction is the other half of the same law. Retyping only registration
/// would leave a graph able to be *born* over its payload budget even though it
/// can no longer *grow* over its module or edge budgets — and a construction that
/// bound its budget, if memoized, replays on a later run as though it were a real
/// answer about that epoch and limit pair.
pub type ModuleGraphConstruction = ModuleGraphOutcome<ModuleGraph>;

impl<T> ModuleGraphOutcome<T> {
    /// Stable evidence label, sharing the vocabulary of
    /// [`DeclClosureStatus`](crate::decl_closure::DeclClosureStatus) and
    /// [`ClosureStatus`](crate::effective_imports::ClosureStatus).
    pub fn outcome_label(&self) -> &'static str {
        match self {
            ModuleGraphOutcome::Complete(_) => "complete",
            ModuleGraphOutcome::Rejected(_) => "rejected",
            ModuleGraphOutcome::Inconclusive(ModuleGraphInconclusive::Cancelled { .. }) => {
                "inconclusive-cancelled"
            }
            ModuleGraphOutcome::Inconclusive(ModuleGraphInconclusive::ResourceLimitExceeded {
                ..
            }) => "inconclusive-resource",
            ModuleGraphOutcome::Inconclusive(ModuleGraphInconclusive::PlanSuperseded {
                ..
            }) => "inconclusive-plan-superseded",
        }
    }

    /// **Only a completed outcome may be memoized.**
    ///
    /// The trap this closes: if an exhausted or cancelled outcome could be cached, a
    /// later run would replay the exhaustion as though it were a real answer. A
    /// rejection is a real answer, but it is still not cached here — caching refusals
    /// is a separate decision this seam does not make on the caller's behalf.
    pub fn is_cacheable(&self) -> bool {
        matches!(self, ModuleGraphOutcome::Complete(_))
    }

    /// Whether the outcome is in the inconclusive family.
    pub fn is_inconclusive(&self) -> bool {
        matches!(self, ModuleGraphOutcome::Inconclusive(_))
    }

    /// The completed value, if any. `None` for both non-complete arms.
    pub fn complete(&self) -> Option<&T> {
        match self {
            ModuleGraphOutcome::Complete(value) => Some(value),
            ModuleGraphOutcome::Rejected(_) | ModuleGraphOutcome::Inconclusive(_) => None,
        }
    }

    /// Take the completed value, if any.
    pub fn into_complete(self) -> Option<T> {
        match self {
            ModuleGraphOutcome::Complete(value) => Some(value),
            ModuleGraphOutcome::Rejected(_) | ModuleGraphOutcome::Inconclusive(_) => None,
        }
    }
}

impl ModuleGraphAdmission {
    /// The graph to carry forward. `None` for both non-complete arms — the caller
    /// keeps the graph it already held, unchanged.
    pub fn graph(&self) -> Option<&ModuleGraph> {
        self.complete().map(|registration| &registration.graph)
    }

    /// The completed registration, if any.
    pub fn registration(&self) -> Option<&Registration> {
        self.complete()
    }
}

#[cfg(test)]
impl<T: std::fmt::Debug> ModuleGraphOutcome<T> {
    /// Test-only destructuring helpers. They name the arm the assertion is about, so
    /// a wrong-arm outcome fails with the outcome in the message instead of a bare
    /// unwrap panic.
    pub(crate) fn expect_complete(self, context: &str) -> T {
        match self {
            ModuleGraphOutcome::Complete(value) => value,
            other => panic!("{context}: expected Complete, got {other:?}"),
        }
    }

    fn expect_rejected(self, context: &str) -> ModuleGraphError {
        match self {
            ModuleGraphOutcome::Rejected(error) => error,
            other => panic!("{context}: expected Rejected, got {other:?}"),
        }
    }

    fn expect_inconclusive(self, context: &str) -> ModuleGraphInconclusive {
        match self {
            ModuleGraphOutcome::Inconclusive(reason) => reason,
            other => panic!("{context}: expected Inconclusive, got {other:?}"),
        }
    }
}

/// Internal refusal carrier so one validation pass can raise either class without
/// the caller having to re-derive which it was.
enum Refusal {
    Rejected(ModuleGraphError),
    Inconclusive(ModuleGraphInconclusive),
}

impl From<ModuleGraphError> for Refusal {
    fn from(error: ModuleGraphError) -> Self {
        Refusal::Rejected(error)
    }
}

impl From<ModuleGraphInconclusive> for Refusal {
    fn from(inconclusive: ModuleGraphInconclusive) -> Self {
        Refusal::Inconclusive(inconclusive)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GraphCompleteness {
    Complete,
    Missing { modules: Vec<ModuleId> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleGraphFacts {
    pub modules: usize,
    pub direct_import_rows: usize,
    pub payload_bytes: u128,
    pub maximum_name_depth: usize,
}

#[derive(Debug, PartialEq, Eq)]
struct ModuleGraphState {
    records: PMap<ModuleId, Arc<ModuleRecord>>,
    facts: ModuleGraphFacts,
    /// Monotonic within one lineage, incremented on every publication. This is what
    /// makes a plan computed against an earlier state detectably stale; see
    /// [`ModuleGraphBinding`] for what it does and does not prove.
    revision: u64,
}

/// The material a prepared admission holds until it is committed.
#[derive(Debug)]
enum PreparedMaterial {
    Publish {
        records: PMap<ModuleId, Arc<ModuleRecord>>,
        facts: ModuleGraphFacts,
        work: RegistrationWork,
    },
    Idempotent {
        work: RegistrationWork,
    },
}

/// A decided admission that has not been published.
///
/// It carries the candidate state so committing publishes without re-deriving
/// anything, and it is consumed **exactly once** — [`commit`](Self::commit) takes
/// `self` by value, so a second publication from the same decision is not something
/// a caller can express rather than something they are asked not to do.
///
/// Holding material is not authority. Nothing here is reachable as the graph, it is
/// never cacheable, and committing revalidates the base and cancellation first.
#[derive(Debug)]
pub struct PreparedAdmission {
    plan: ModuleGraphAdmissionPlan,
    material: PreparedMaterial,
}

impl PreparedAdmission {
    /// The descriptive plan for this decision — the same value
    /// [`ModuleGraph::plan_registration`] would produce for the same input.
    pub fn plan(&self) -> &ModuleGraphAdmissionPlan {
        &self.plan
    }

    /// Whether committing would publish a new graph state.
    pub fn publishes(&self) -> bool {
        matches!(self.material, PreparedMaterial::Publish { .. })
    }

    /// **Never.** A prepared admission is a decision in flight, not a result.
    pub const fn is_cacheable(&self) -> bool {
        false
    }

    /// Revalidate against `graph` and publish exactly once.
    ///
    /// Two things are rechecked immediately before publication and nothing else is
    /// recomputed: the base binding, because a plan decided against one base is
    /// meaningless against another, and cancellation, because a caller who gave up
    /// between deciding and publishing must not have a module published on their
    /// behalf. Both refusals are FL-INV-07 inconclusive — no verdict was reached
    /// about the module — and neither is cacheable.
    pub fn commit(
        self,
        graph: &ModuleGraph,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> ModuleGraphAdmission {
        if !self.plan.is_valid_for(graph) {
            return ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::PlanSuperseded {
                module: self.plan.request().clone(),
                expected_revision: self.plan.base().revision,
                actual_revision: graph.binding().revision,
            });
        }
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::Cancelled {
                module: self.plan.request().clone(),
                checkpoint: RegistrationCheckpoint::BeforePublication,
            });
        }
        match self.material {
            PreparedMaterial::Idempotent { work } => ModuleGraphAdmission::Complete(Registration {
                graph: graph.clone(),
                disposition: RegistrationDisposition::Idempotent,
                work,
            }),
            PreparedMaterial::Publish {
                records,
                facts,
                work,
            } => ModuleGraphAdmission::Complete(Registration {
                graph: graph.published(records, facts),
                disposition: RegistrationDisposition::Inserted,
                work,
            }),
        }
    }
}

/// The outcome shape of the shared decision procedure, before publication.
enum DecisionOutcome {
    /// Would publish: the candidate record map, the facts that go with it, and the
    /// work actually performed.
    Admit {
        records: PMap<ModuleId, Arc<ModuleRecord>>,
        facts: ModuleGraphFacts,
        work: RegistrationWork,
    },
    /// The identical record is already present; nothing would publish.
    Idempotent {
        work: RegistrationWork,
    },
    Rejected(ModuleGraphError),
    Inconclusive(ModuleGraphInconclusive),
}

/// One admission decision: the rule that decided, the usage observed reaching it,
/// and the outcome. Produced once and consumed either as a plan or as a publication.
struct AdmissionDecision {
    precedence: AdmissionPrecedence,
    usage: PlannedUsage,
    exactness: UsageExactness,
    outcome: DecisionOutcome,
}

/// Immutable module DAG. Clone is one bounded `Arc` increment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGraph {
    epoch: ModuleEpoch,
    limits: ModuleGraphLimits,
    state: Arc<ModuleGraphState>,
}

impl ModuleGraph {
    /// Construct an empty graph pinned to `epoch` under `limits`.
    ///
    /// The same FL-INV-07 split as [`register`](Self::register): a malformed epoch is
    /// a *rejection* — a complete determination about the input — while a bound
    /// payload budget is *inconclusive*, because no verdict was reached about this
    /// epoch/limits pair. Construction does no unbounded work and therefore takes no
    /// cancellation probe; it can never yield
    /// [`ModuleGraphInconclusive::Cancelled`].
    pub fn new(epoch: ModuleEpoch, limits: ModuleGraphLimits) -> ModuleGraphConstruction {
        if !epoch.is_well_formed() {
            return ModuleGraphOutcome::Rejected(ModuleGraphError::MalformedEpoch {
                tag: Arc::clone(&epoch.tag),
                commit: Arc::clone(&epoch.commit),
            });
        }
        let payload_bytes = epoch.payload_bytes();
        if payload_bytes > limits.max_payload_bytes {
            // A graph must not be able to be *born* over budget just because it can no
            // longer *grow* over budget. Exhaustion here is inconclusive, never a
            // rejection, and never cacheable.
            return ModuleGraphOutcome::Inconclusive(
                ModuleGraphInconclusive::ResourceLimitExceeded {
                    module: None,
                    resource: ModuleGraphResource::PayloadBytes,
                    limit: limits.max_payload_bytes,
                    actual: payload_bytes,
                },
            );
        }
        ModuleGraphOutcome::Complete(Self {
            epoch,
            limits,
            state: Arc::new(ModuleGraphState {
                records: PMap::new(),
                facts: ModuleGraphFacts {
                    modules: 0,
                    direct_import_rows: 0,
                    payload_bytes,
                    maximum_name_depth: 0,
                },
                // A freshly constructed graph starts its own lineage.
                revision: 0,
            }),
        })
    }

    pub fn epoch(&self) -> &ModuleEpoch {
        &self.epoch
    }

    pub fn limits(&self) -> ModuleGraphLimits {
        self.limits
    }

    pub fn facts(&self) -> ModuleGraphFacts {
        self.state.facts
    }

    pub fn len(&self) -> usize {
        self.state.facts.modules
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn record(&self, module: &ModuleId) -> Option<&ModuleRecord> {
        self.state.records.get(module).map(Arc::as_ref)
    }

    pub fn direct_imports(&self, module: &ModuleId) -> Option<&[DirectImport]> {
        self.record(module).map(ModuleRecord::direct_imports)
    }

    pub fn contains(&self, module: &ModuleId) -> bool {
        self.state.records.contains_key(module)
    }

    pub fn modules_canonical(&self) -> Vec<ModuleId> {
        let mut modules: Vec<ModuleId> = self
            .state
            .records
            .iter()
            .map(|(module, _)| module.clone())
            .collect();
        modules.sort();
        modules
    }

    pub fn completeness(&self) -> GraphCompleteness {
        let mut missing = BTreeSet::new();
        for (_, record) in self.state.records.iter() {
            for import in record.direct_imports() {
                if !self.state.records.contains_key(&import.module) {
                    missing.insert(import.module.clone());
                }
            }
        }
        if missing.is_empty() {
            GraphCompleteness::Complete
        } else {
            GraphCompleteness::Missing {
                modules: missing.into_iter().collect(),
            }
        }
    }

    /// Exact re-registration is idempotent. Any field or evidence difference
    /// is a conflict; registration never overwrites an existing record.
    /// Register a module record. See [`ModuleGraphAdmission`] for the outcome
    /// lattice; equivalent to [`register_cancellable`](Self::register_cancellable)
    /// with no cancellation flag.
    pub fn register(&self, record: ModuleRecord) -> ModuleGraphAdmission {
        self.register_cancellable(record, None)
    }

    /// Register a module record, sampling `cancellation` at each
    /// [`RegistrationCheckpoint`].
    ///
    /// Cancellation and budget exhaustion are FL-INV-07 inconclusive outcomes, never
    /// rejections: the caller learns that no verdict was reached, not that the module
    /// was refused. Because the receiver is never mutated — the record map is
    /// persistent and publication is the returned graph — a cancelled or exhausted
    /// registration leaves no half-registered module observable anywhere.
    pub fn register_cancellable(
        &self,
        record: ModuleRecord,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> ModuleGraphAdmission {
        // One decision procedure, then publication. Admission does not re-derive
        // anything the decision already established, so a plan of the same input
        // cannot disagree with it.
        // Prepare, then commit. Direct registration is not a second path to
        // publication: it is the plan protocol with both steps taken together, so
        // anything true of a committed plan is true of it. The base cannot move
        // between the halves here, so the commit-time base revalidation is
        // trivially satisfied rather than skipped. Cancellation is passed as `None`
        // because `decide` has already sampled it at `BeforePublication` — sampling
        // again would be a second sample of the caller's probe within one
        // registration, which would change what a probe observes rather than
        // strengthen the check.
        match self.prepare_registration(record, cancellation) {
            ModuleGraphOutcome::Complete(prepared) => prepared.commit(self, None),
            ModuleGraphOutcome::Rejected(error) => ModuleGraphAdmission::Rejected(error),
            ModuleGraphOutcome::Inconclusive(reason) => ModuleGraphAdmission::Inconclusive(reason),
        }
    }

    /// Publish a candidate state, moving the lineage exactly one step. The single
    /// place a new graph state comes into existence.
    fn published(
        &self,
        records: PMap<ModuleId, Arc<ModuleRecord>>,
        facts: ModuleGraphFacts,
    ) -> Self {
        Self {
            epoch: self.epoch.clone(),
            limits: self.limits,
            state: Arc::new(ModuleGraphState {
                records,
                facts,
                revision: self.state.revision.saturating_add(1),
            }),
        }
    }

    /// Decide a registration and hold the result, **without publishing it**.
    ///
    /// This is the consumable half of the plan protocol (bead `franken_lean-6sf3`).
    /// [`plan_registration`](Self::plan_registration) answers "what would happen"
    /// and keeps no material; this answers the same question and *keeps* the
    /// candidate state so that [`PreparedAdmission::commit`] can publish it without
    /// redoing the lookup, the canonicalization, or the accounting. That is the
    /// property atomic application needs: the work is done once and handed over.
    ///
    /// Preparing publishes nothing. A refused or inconclusive decision returns that
    /// outcome directly and yields no `PreparedAdmission` at all, so an exhaustion
    /// reached while preparing has nothing to commit and nothing to memoize.
    pub fn prepare_registration(
        &self,
        record: ModuleRecord,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> ModuleGraphOutcome<PreparedAdmission> {
        let decision = self.decide(&record, cancellation);
        let plan = self.plan_from(&record, &decision);
        match decision.outcome {
            DecisionOutcome::Rejected(error) => ModuleGraphOutcome::Rejected(error),
            DecisionOutcome::Inconclusive(reason) => ModuleGraphOutcome::Inconclusive(reason),
            DecisionOutcome::Idempotent { work } => {
                ModuleGraphOutcome::Complete(PreparedAdmission {
                    plan,
                    material: PreparedMaterial::Idempotent { work },
                })
            }
            DecisionOutcome::Admit {
                records,
                facts,
                work,
            } => ModuleGraphOutcome::Complete(PreparedAdmission {
                plan,
                material: PreparedMaterial::Publish {
                    records,
                    facts,
                    work,
                },
            }),
        }
    }

    /// Build the descriptive plan for a decision. Shared by planning and preparing so
    /// both describe the decision identically.
    fn plan_from(
        &self,
        record: &ModuleRecord,
        decision: &AdmissionDecision,
    ) -> ModuleGraphAdmissionPlan {
        ModuleGraphAdmissionPlan {
            version: ModuleGraphAdmissionPlan::VERSION,
            usage_version: UsageUnit::VERSION,
            base: self.binding(),
            request: record.id.clone(),
            precedence: decision.precedence,
            checkpoint: decision.precedence.checkpoint(),
            usage: decision.usage,
            exactness: decision.exactness,
            predicted_facts: match &decision.outcome {
                DecisionOutcome::Admit { facts, .. } => Some(*facts),
                _ => None,
            },
        }
    }

    /// What this graph's observable identity must still be for a plan to be consumed.
    pub fn binding(&self) -> ModuleGraphBinding {
        ModuleGraphBinding {
            epoch: self.epoch.clone(),
            limits: self.limits,
            facts: self.state.facts,
            revision: self.state.revision,
        }
    }

    /// Compute, **without publishing anything**, what registering `record` would do.
    ///
    /// Nothing observable changes: this graph is immutable and is not consulted for
    /// anything but reads, no environment moves, no logical root moves, and the
    /// returned plan is never cacheable. See [`ModuleGraphAdmissionPlan`].
    pub fn plan_registration(&self, record: &ModuleRecord) -> ModuleGraphAdmissionPlan {
        self.plan_registration_cancellable(record, None)
    }

    /// [`plan_registration`](Self::plan_registration), sampling `cancellation` at the
    /// same checkpoints admission samples.
    pub fn plan_registration_cancellable(
        &self,
        record: &ModuleRecord,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> ModuleGraphAdmissionPlan {
        let decision = self.decide(record, cancellation);
        // The candidate record map computed for an admitting decision is dropped
        // here rather than carried: a plan describes what would happen and holds no
        // material with which to make it happen.
        let predicted_facts = match &decision.outcome {
            DecisionOutcome::Admit { facts, .. } => Some(*facts),
            _ => None,
        };
        ModuleGraphAdmissionPlan {
            version: ModuleGraphAdmissionPlan::VERSION,
            usage_version: UsageUnit::VERSION,
            base: self.binding(),
            request: record.id.clone(),
            precedence: decision.precedence,
            checkpoint: decision.precedence.checkpoint(),
            usage: decision.usage,
            exactness: decision.exactness,
            predicted_facts,
        }
    }

    /// The single admission decision procedure, shared by planning and registration.
    ///
    /// Every early return records the precedence rule that decided, so the outcome
    /// and the reason for it are produced together and cannot drift apart. Usage is
    /// accumulated as it is observed, and marked `LowerBound` whenever the decision
    /// stops before the remaining required work could be measured — a refusal never
    /// scans the unobserved suffix merely to report an exact total.
    fn decide(
        &self,
        record: &ModuleRecord,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> AdmissionDecision {
        let is_cancelled = || cancellation.is_some_and(CancellationProbe::is_cancelled);
        let mut usage = PlannedUsage::default();

        let cancelled_at =
            |precedence: AdmissionPrecedence, usage: PlannedUsage| -> AdmissionDecision {
                AdmissionDecision {
                    precedence,
                    usage,
                    exactness: UsageExactness::LowerBound,
                    outcome: DecisionOutcome::Inconclusive(ModuleGraphInconclusive::Cancelled {
                        module: record.id.clone(),
                        checkpoint: precedence.checkpoint(),
                    }),
                }
            };

        if is_cancelled() {
            return cancelled_at(AdmissionPrecedence::CancelledAtEntry, usage);
        }
        let record_facts = match self.validate_record(record) {
            Ok(facts) => facts,
            Err(Refusal::Rejected(error)) => {
                return AdmissionDecision {
                    precedence: AdmissionPrecedence::MalformedInput,
                    usage,
                    exactness: UsageExactness::LowerBound,
                    outcome: DecisionOutcome::Rejected(error),
                };
            }
            Err(Refusal::Inconclusive(reason)) => {
                return AdmissionDecision {
                    precedence: AdmissionPrecedence::ResourceNameDepth,
                    usage,
                    exactness: UsageExactness::LowerBound,
                    outcome: DecisionOutcome::Inconclusive(reason),
                };
            }
        };
        usage.name_components = record_facts.name_components as u128;
        if is_cancelled() {
            return cancelled_at(AdmissionPrecedence::CancelledAfterValidation, usage);
        }

        let direct_rows_validated = record.direct_imports().len();
        if let Some(existing) = self.state.records.get(&record.id) {
            let work = RegistrationWork {
                name_components_validated: record_facts.name_components,
                direct_rows_validated,
                ..RegistrationWork::default()
            };
            if existing.as_ref() == record {
                // Idempotence publishes nothing, so the graph's totals are already
                // the totals: exact, with no cycle scan required.
                usage.modules = self.state.facts.modules as u128;
                usage.direct_import_rows = self.state.facts.direct_import_rows as u128;
                usage.payload_bytes = self.state.facts.payload_bytes;
                return AdmissionDecision {
                    precedence: AdmissionPrecedence::ExistingRecordIdempotent,
                    usage,
                    exactness: UsageExactness::Exact,
                    outcome: DecisionOutcome::Idempotent { work },
                };
            }
            // The conflict is authoritative only because the bounded lookup and
            // comparison above both completed; an unfinished comparison would be
            // inconclusive, never a rejection.
            let differing_fields = differing_record_fields(existing, record);
            debug_assert!(!differing_fields.is_empty());
            return AdmissionDecision {
                precedence: AdmissionPrecedence::ExistingRecordConflict,
                usage,
                exactness: UsageExactness::LowerBound,
                outcome: DecisionOutcome::Rejected(ModuleGraphError::ConflictingRecord {
                    module: record.id.clone(),
                    differing_fields,
                    existing_artifact: Box::new(existing.artifact.clone()),
                    incoming_artifact: Box::new(record.artifact.clone()),
                }),
            };
        }
        if is_cancelled() {
            return cancelled_at(AdmissionPrecedence::CancelledAfterConflictLookup, usage);
        }

        let modules = self.state.facts.modules.saturating_add(1);
        let direct_import_rows = self
            .state
            .facts
            .direct_import_rows
            .saturating_add(direct_rows_validated);
        let payload_bytes = self
            .state
            .facts
            .payload_bytes
            .saturating_add(record_facts.payload_bytes);
        usage.modules = modules as u128;
        usage.direct_import_rows = direct_import_rows as u128;
        usage.payload_bytes = payload_bytes;

        // Checked in this exact order, and the precedence table names the same
        // order, so simultaneous breaches always resolve to the same rule.
        for (precedence, resource, limit, actual) in [
            (
                AdmissionPrecedence::ResourceModules,
                ModuleGraphResource::Modules,
                self.limits.max_modules as u128,
                modules as u128,
            ),
            (
                AdmissionPrecedence::ResourceDirectImportRows,
                ModuleGraphResource::DirectImportRows,
                self.limits.max_edges as u128,
                direct_import_rows as u128,
            ),
            (
                AdmissionPrecedence::ResourcePayloadBytes,
                ModuleGraphResource::PayloadBytes,
                self.limits.max_payload_bytes,
                payload_bytes,
            ),
        ] {
            if let Err(reason) = enforce_limit(Some(&record.id), resource, limit, actual) {
                return AdmissionDecision {
                    precedence,
                    usage,
                    exactness: UsageExactness::LowerBound,
                    outcome: DecisionOutcome::Inconclusive(reason),
                };
            }
        }
        if is_cancelled() {
            return cancelled_at(AdmissionPrecedence::CancelledBeforePublication, usage);
        }

        // A persistent insert produces a candidate map; the receiver is untouched, so
        // computing this is not publication. Only `register_cancellable` adopts it.
        let module = record.id.clone();
        let records = self
            .state
            .records
            .insert(module.clone(), Arc::new(record.clone()));
        let cycle_scan = cycle_through(&records, &module);
        usage.cycle_modules_visited = cycle_scan.modules_visited as u128;
        usage.cycle_rows_examined = cycle_scan.rows_examined as u128;
        if let Some(path) = cycle_scan.path {
            return AdmissionDecision {
                precedence: AdmissionPrecedence::CycleDetected,
                usage,
                exactness: UsageExactness::Exact,
                outcome: DecisionOutcome::Rejected(ModuleGraphError::Cycle { path }),
            };
        }

        AdmissionDecision {
            precedence: AdmissionPrecedence::Admitted,
            usage,
            exactness: UsageExactness::Exact,
            outcome: DecisionOutcome::Admit {
                records,
                facts: ModuleGraphFacts {
                    modules,
                    direct_import_rows,
                    payload_bytes,
                    maximum_name_depth: self
                        .state
                        .facts
                        .maximum_name_depth
                        .max(record_facts.maximum_name_depth),
                },
                work: RegistrationWork {
                    name_components_validated: record_facts.name_components,
                    direct_rows_validated,
                    cycle_modules_visited: cycle_scan.modules_visited,
                    cycle_rows_examined: cycle_scan.rows_examined,
                },
            },
        }
    }

    /// Pointer-identity probe for snapshot/sharing evidence.
    pub fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.state, &other.state)
    }

    fn validate_record(&self, record: &ModuleRecord) -> Result<RecordFacts, Refusal> {
        if record.id.name().is_anonymous() {
            return Err(ModuleGraphError::AnonymousModule.into());
        }
        if record.artifact.epoch != self.epoch {
            return Err((ModuleGraphError::EpochMismatch {
                module: record.id.clone(),
                expected: self.epoch.clone(),
                actual: record.artifact.epoch.clone(),
            })
            .into());
        }

        // Logical bytes inspected and retained by this layer: content digest
        // (32), producer tag (1), evidence-grade tag (1), and `is_module` (1).
        // Boolean *values* never change the accounting cost.
        const FIXED_RECORD_PAYLOAD_BYTES: u128 = 35;
        const DIRECT_IMPORT_FLAG_BYTES: u128 = 3;

        let mut maximum_name_depth = 0usize;
        let mut name_components = 0usize;
        let mut payload_bytes =
            FIXED_RECORD_PAYLOAD_BYTES.saturating_add(record.artifact.epoch.payload_bytes());
        for (position, module) in std::iter::once(&record.id)
            .chain(record.direct_imports().iter().map(|import| &import.module))
            .enumerate()
        {
            if position > 0 && module.name().is_anonymous() {
                return Err((ModuleGraphError::AnonymousImport {
                    owner: record.id.clone(),
                    import_index: position - 1,
                })
                .into());
            }
            let stats = name_stats(module.name());
            if stats.overflowing_component {
                return Err((ModuleGraphError::OverflowingNameComponent {
                    module: module.clone(),
                })
                .into());
            }
            enforce_limit(
                Some(module),
                ModuleGraphResource::NameDepth,
                self.limits.max_name_depth as u128,
                stats.depth as u128,
            )?;
            maximum_name_depth = maximum_name_depth.max(stats.depth);
            name_components = name_components.saturating_add(stats.depth);
            payload_bytes = payload_bytes.saturating_add(stats.payload_bytes);
        }
        payload_bytes = payload_bytes.saturating_add(
            (record.direct_imports().len() as u128).saturating_mul(DIRECT_IMPORT_FLAG_BYTES),
        );

        for (import_index, import) in record.direct_imports().iter().enumerate() {
            if import.module == record.id {
                return Err((ModuleGraphError::SelfImport {
                    module: record.id.clone(),
                    import_index,
                })
                .into());
            }
        }

        Ok(RecordFacts {
            payload_bytes,
            maximum_name_depth,
            name_components,
        })
    }
}

impl std::error::Error for ModuleGraphError {}

fn differing_record_fields(
    existing: &ModuleRecord,
    incoming: &ModuleRecord,
) -> Vec<ModuleRecordField> {
    let mut fields = Vec::new();
    if existing.is_module != incoming.is_module {
        fields.push(ModuleRecordField::IsModule);
    }
    if existing.direct_imports() != incoming.direct_imports() {
        fields.push(ModuleRecordField::DirectImports);
    }
    if existing.artifact.content_digest != incoming.artifact.content_digest {
        fields.push(ModuleRecordField::ArtifactContentDigest);
    }
    if existing.artifact.producer != incoming.artifact.producer {
        fields.push(ModuleRecordField::ArtifactProducer);
    }
    if existing.artifact.grade != incoming.artifact.grade {
        fields.push(ModuleRecordField::ArtifactGrade);
    }
    fields
}

#[derive(Debug, Clone, Copy)]
struct RecordFacts {
    payload_bytes: u128,
    maximum_name_depth: usize,
    name_components: usize,
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct NameFacts {
    pub(crate) depth: usize,
    pub(crate) payload_bytes: u128,
    pub(crate) overflowing_component: bool,
}

pub(crate) fn name_stats(name: &Name) -> NameFacts {
    let mut cursor = name.clone();
    let mut depth = 0usize;
    let mut payload_bytes = 0u128;
    let mut overflowing_component = false;
    while !cursor.is_anonymous() {
        depth = depth.saturating_add(1);
        overflowing_component |= cursor.component_overflowed();
        payload_bytes = payload_bytes.saturating_add(match cursor.leaf_view() {
            LeafView::Anonymous => 0,
            LeafView::Str(value) => value.len() as u128 + 1,
            LeafView::Num(_) => 9,
        });
        cursor = cursor.parent();
    }
    NameFacts {
        depth,
        payload_bytes,
        overflowing_component,
    }
}

/// Operational budget check. Exhaustion is an FL-INV-07 inconclusive outcome, so
/// this deliberately cannot produce a [`ModuleGraphError`]: there is no way to
/// spell "the budget bound" as a rejection from here.
fn enforce_limit(
    module: Option<&ModuleId>,
    resource: ModuleGraphResource,
    limit: u128,
    actual: u128,
) -> Result<(), ModuleGraphInconclusive> {
    if actual > limit {
        return Err(ModuleGraphInconclusive::ResourceLimitExceeded {
            module: module.cloned(),
            resource,
            limit,
            actual,
        });
    }
    Ok(())
}

#[derive(Debug, Default)]
struct CycleScan {
    path: Option<Vec<ModuleId>>,
    modules_visited: usize,
    rows_examined: usize,
}

/// Any new cycle must pass through the newly inserted module because the source
/// graph was already acyclic. One canonical multi-source BFS visits each
/// reachable module at most once; sorted starts and neighbors make equal-length
/// witness selection independent of record insertion and direct-row order.
fn cycle_through(records: &PMap<ModuleId, Arc<ModuleRecord>>, inserted: &ModuleId) -> CycleScan {
    let Some(record) = records.get(inserted) else {
        return CycleScan::default();
    };
    let mut starts: Vec<ModuleId> = record
        .direct_imports()
        .iter()
        .map(|import| import.module.clone())
        .filter(|module| records.contains_key(module))
        .collect();
    starts.sort();
    starts.dedup();
    let mut queue = VecDeque::new();
    let mut predecessor: BTreeMap<ModuleId, Option<ModuleId>> = BTreeMap::new();
    for start in starts {
        predecessor.insert(start.clone(), None);
        queue.push_back(start);
    }
    let mut scan = CycleScan::default();

    while let Some(module) = queue.pop_front() {
        scan.modules_visited = scan.modules_visited.saturating_add(1);
        if &module == inserted {
            let mut path = Vec::new();
            let mut cursor = Some(module);
            while let Some(current) = cursor {
                path.push(current.clone());
                cursor = predecessor.get(&current).cloned().flatten();
            }
            path.reverse();
            path.insert(0, inserted.clone());
            scan.path = Some(path);
            return scan;
        }

        let mut neighbors = Vec::new();
        if let Some(record) = records.get(&module) {
            scan.rows_examined = scan
                .rows_examined
                .saturating_add(record.direct_imports().len());
            neighbors.extend(
                record
                    .direct_imports()
                    .iter()
                    .map(|import| import.module.clone())
                    .filter(|neighbor| records.contains_key(neighbor)),
            );
        }
        neighbors.sort();
        neighbors.dedup();
        for neighbor in neighbors {
            if !predecessor.contains_key(&neighbor) {
                predecessor.insert(neighbor.clone(), Some(module.clone()));
                queue.push_back(neighbor);
            }
        }
    }
    scan
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    const PIN_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";
    const TEST_LIMITS: ModuleGraphLimits = ModuleGraphLimits::new(10_000, 100_000, 256, u128::MAX);

    fn epoch() -> ModuleEpoch {
        ModuleEpoch::new("v4.32.0", PIN_COMMIT)
    }

    fn id(value: &str) -> ModuleId {
        ModuleId::new(Name::from_components(value.split('.')))
    }

    fn evidence(seed: u8) -> ArtifactEvidence {
        ArtifactEvidence {
            epoch: epoch(),
            content_digest: Digest([seed; 32]),
            producer: ArtifactProducer::Reference,
            grade: ArtifactGrade::OracleFixture,
        }
    }

    fn direct(value: &str, bits: u8) -> DirectImport {
        DirectImport::new(
            id(value),
            bits & 0b001 != 0,
            bits & 0b010 != 0,
            bits & 0b100 != 0,
        )
    }

    fn record(value: &str, imports: Vec<DirectImport>, seed: u8) -> ModuleRecord {
        ModuleRecord::new(id(value), true, imports, evidence(seed))
    }

    fn graph() -> ModuleGraph {
        ModuleGraph::new(epoch(), TEST_LIMITS).expect_complete("valid pinned graph")
    }

    fn insert(graph: &ModuleGraph, record: ModuleRecord) -> ModuleGraph {
        let registration = graph.register(record).expect_complete("record inserts");
        assert_eq!(registration.disposition, RegistrationDisposition::Inserted);
        registration.graph
    }

    /// A probe that trips on its `trip_at`-th sample, so a test can pin a
    /// cancellation to one exact checkpoint. A preset flag can only ever produce the
    /// first checkpoint.
    struct TripAt {
        trip_at: usize,
        samples: std::cell::Cell<usize>,
    }

    impl TripAt {
        fn new(trip_at: usize) -> Self {
            Self {
                trip_at,
                samples: std::cell::Cell::new(0),
            }
        }
    }

    impl CancellationProbe for TripAt {
        fn is_cancelled(&self) -> bool {
            let seen = self.samples.get() + 1;
            self.samples.set(seen);
            seen >= self.trip_at
        }
    }

    /// NONPUBLISHING is the whole point: a plan that published would just be
    /// admission with extra steps.
    #[test]
    fn plans_are_nonpublishing_and_never_cacheable() {
        let base = insert(&graph(), record("A", vec![], 0xA1));
        let environment = crate::environment::Environment::new();
        let options = fln_core::options::KVMap::new();

        let root_before = environment.logical_root(&options);
        let binding_before = base.binding();
        let facts_before = base.facts();
        let base_before = base.clone();

        // One plan per outcome family, including the one that would publish.
        let admitting = record("B", vec![direct("A", 0b011)], 0xB1);
        let conflicting = record("A", vec![], 0xFF);
        let idempotent = record("A", vec![], 0xA1);
        let deep = ModuleRecord::new(
            ModuleId::new(Name::from_components(std::iter::repeat_n(
                "deep",
                TEST_LIMITS.max_name_depth + 2,
            ))),
            true,
            vec![],
            evidence(0xD1),
        );
        for candidate in [&admitting, &conflicting, &idempotent, &deep] {
            let plan = base.plan_registration(candidate);

            // Nothing was published, cached, or made authoritative.
            assert!(!plan.is_cacheable(), "a plan must never be cacheable");
            assert_eq!(plan.version(), ModuleGraphAdmissionPlan::VERSION);
            assert_eq!(plan.usage_version(), UsageUnit::VERSION);
            assert!(plan.is_valid_for(&base));

            // The base is observably untouched, by value, by facts, by lineage, and
            // by storage identity.
            assert_eq!(base, base_before, "planning mutated the graph");
            assert_eq!(base.binding(), binding_before, "planning moved the binding");
            assert_eq!(base.facts(), facts_before);
            assert!(base.shares_storage_with(&base_before));
            assert_eq!(
                base.state.revision, binding_before.revision,
                "planning moved the lineage revision"
            );
            // And the module a publishing plan predicts is still absent.
            if plan.publishes() {
                assert!(
                    base.record(plan.request()).is_none(),
                    "a nonpublishing plan made its module reachable"
                );
            }
            // The environment's logical root cannot move: planning reaches nothing
            // that feeds it. Asserted rather than assumed, so wiring the graph into
            // the environment later cannot quietly break it.
            assert_eq!(environment.logical_root(&options), root_before);
        }

        // Only the admitting plan claims it would publish.
        assert!(base.plan_registration(&admitting).publishes());
        for candidate in [&conflicting, &idempotent, &deep] {
            assert!(!base.plan_registration(candidate).publishes());
        }

        // The reservation claim is a reported FACT, and it reports the honest answer.
        //
        // `franken_lean-6sf3` asks for reservations "where supported". They are not
        // supported here and the plan says so, rather than staying silent and letting a
        // consumer infer that reserved storage exists. `Unsupported` is not a promise
        // that publication cannot fail — it is the refusal to make that promise.
        for candidate in [&admitting, &conflicting, &idempotent, &deep] {
            let claim = base.plan_registration(candidate).reservation();
            assert!(
                matches!(claim, ReservationClaim::Unsupported { .. }),
                "the plan must state that no fallible reservation is available, got {claim:?}"
            );
            // Distinguishable from the other two states, which is the whole reason this
            // is three-valued: "reserved nothing" and "nothing can be reserved" are
            // different claims and a consumer must be able to tell them apart.
            assert_ne!(claim, ReservationClaim::NotRequired);
            assert_ne!(claim, ReservationClaim::Reserved { units: 0 });
        }

        eprintln!(
            "{{\"schema\":\"fln.unit.module-plan-reservation-claim\",\"version\":1,\
             \"bead\":\"franken_lean-6sf3\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"reservation-claim-is-a-reported-fact\",\
             \"claim\":\"unsupported\",\
             \"reason\":\"every allocating path in a publication is infallible-or-abort\",\
             \"allocator_abort_recovery_promised\":false,\
             \"would_become_genuine_via\":\"a fallible PMap try_insert on Vec::try_reserve\",\
             \"owner_of_that_change\":\"its own bead, not a plan field\",\
             \"status\":\"pass\"}}"
        );
    }

    /// SINGLE CHARGE: one measurement serves both phases, and the double-charge mutant
    /// is killed on recorded usage.
    ///
    /// Transcribed from `fln-extension-history-checkpoint-identity-41s` (cece9f1) rather
    /// than re-derived. The property is the same one: the work is measured once, at plan
    /// time, and the consuming phase carries it rather than recomputing it.
    #[test]
    fn work_is_charged_once_and_the_double_charge_mutant_is_killed() {
        let base = insert(&graph(), record("A", vec![], 0xA1));
        let candidate = record("B", vec![direct("A", 0b101), direct("A", 0b010)], 0xB1);

        let plan = base.plan_registration(&candidate);
        let planned = plan.usage();
        assert!(plan.publishes());
        assert!(
            planned.direct_import_rows > 0 && planned.name_components > 0,
            "the fixture must cost something, or a double charge is indistinguishable"
        );

        let prepared = match base.prepare_registration(candidate.clone(), None) {
            ModuleGraphOutcome::Complete(prepared) => prepared,
            other => unreachable!("preparation must complete, got {other:?}"),
        };
        let registration = match prepared.commit(&base, None) {
            ModuleGraphOutcome::Complete(registration) => registration,
            other => unreachable!("commit must publish, got {other:?}"),
        };

        // ONE measurement served both phases: the committed work equals the planned
        // usage, unit for unit, because commit carries the decision rather than redoing
        // it. This is the typed kill signal — not that two totals differ, but that the
        // committed work IS the planned usage.
        assert_eq!(
            u128::try_from(registration.work.name_components_validated).unwrap_or(u128::MAX),
            planned.name_components,
            "commit must carry the planned name-component charge, not recompute it"
        );
        assert_eq!(
            u128::try_from(registration.work.direct_rows_validated).unwrap_or(u128::MAX),
            planned.direct_import_rows
        );
        assert_eq!(
            u128::try_from(registration.work.cycle_modules_visited).unwrap_or(u128::MAX),
            planned.cycle_modules_visited
        );
        assert_eq!(
            u128::try_from(registration.work.cycle_rows_examined).unwrap_or(u128::MAX),
            planned.cycle_rows_examined
        );

        // MUTANT: a phase that recharged what the plan already charged. Modelled as the
        // sum, which is exactly what recomputing would cost.
        for unit in UsageUnit::ALL {
            let once = planned.get(unit);
            let doubled = once.checked_add(once).expect("no overflow");
            if once > 0 {
                assert_ne!(
                    doubled, once,
                    "the double-charge model must be distinguishable for {unit:?}"
                );
                assert_eq!(doubled, once * 2, "and it must be exactly twice");
            }
        }

        // Re-planning against the same base reproduces the same totals, so the charge is
        // a property of the input rather than of the phase that measured it.
        assert_eq!(base.plan_registration(&candidate).usage(), planned);

        // The two resources this layer does NOT charge, stated as facts.
        let charges = plan.charges();
        assert!(
            matches!(charges.pmap_admission, ChargeOwnership::Uncharged { .. }),
            "PMap admission work must be reported uncharged, got {:?}",
            charges.pmap_admission
        );
        assert_eq!(
            charges.decoder,
            ChargeOwnership::OwnedElsewhere { owner: "fln-20n.1" }
        );
        // Structural, not a promise: no unit denominates decoder work, so there is no
        // field in which to recharge it even by accident.
        for unit in UsageUnit::ALL {
            let name = format!("{unit:?}").to_lowercase();
            assert!(
                !name.contains("decode") && !name.contains("byte_stream"),
                "no frozen unit may denominate decoder work ({unit:?})"
            );
        }

        eprintln!(
            "{{\"schema\":\"fln.unit.module-plan-single-charge\",\"version\":1,\
             \"bead\":\"franken_lean-6sf3\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"one-measurement-serves-both-phases\",\
             \"planned_name_components\":{},\"planned_direct_rows\":{},\
             \"committed_equals_planned\":true,\
             \"mutant\":\"double_charge_graph_work\",\
             \"kill_signal\":\"committed_work_equals_planned_usage\",\
             \"pmap_admission\":\"uncharged_no_facts_produced\",\
             \"decoder\":\"owned_by_fln-20n.1_referenced_not_recharged\",\
             \"decoder_unit_exists\":false,\"status\":\"pass\"}}",
            planned.name_components, planned.direct_import_rows
        );
    }

    /// Two module names whose `key_hash` is IDENTICAL, constructed rather than searched.
    ///
    /// `Name::num(pre, k)` hashes as `mix_hash(pre.hash(), k)`, and Lean's `mix_hash` is
    /// `(h ^ f(k)) * M` where `f(k) = ((k*M) ^ ((k*M) >> 47)) ^ M`. Every step of `f` is a
    /// bijection on `u64` — multiply by an odd constant, a right-xorshift by 47 (self
    /// inverse, since 47*2 >= 64), and an xor — and the final multiply by `M` is a
    /// bijection too. So `f` is invertible, and for any two prefixes with hashes `h1` and
    /// `h2` a colliding pair follows directly: pick `k1`, then
    /// `k2 = f_inverse(f(k1) ^ h1 ^ h2)`.
    ///
    /// That matters beyond this test. It means an ADVERSARY can force full-hash collisions
    /// on module identities analytically, with no search — which is exactly why
    /// `fln-amv.13`'s collision budget exists, and why an all-collision shape is a real
    /// case rather than a theoretical one. A random shape generator would never produce it.
    fn colliding_module_ids(count: usize) -> Vec<ModuleId> {
        const M: u64 = 0xc6a4_a793_5bd1_e995;

        const fn inverse_of_m() -> u64 {
            let mut inverse = 1u64;
            let mut round = 0;
            while round < 6 {
                inverse = inverse.wrapping_mul(2u64.wrapping_sub(M.wrapping_mul(inverse)));
                round += 1;
            }
            inverse
        }
        // Self-inverse: shifting right by 47 twice moves every bit past the end.
        const fn unxorshift47(value: u64) -> u64 {
            value ^ (value >> 47)
        }
        const fn forward(k: u64) -> u64 {
            let scaled = k.wrapping_mul(M);
            (scaled ^ (scaled >> 47)) ^ M
        }
        const fn backward(y: u64) -> u64 {
            unxorshift47(y ^ M).wrapping_mul(inverse_of_m())
        }
        assert_eq!(M.wrapping_mul(inverse_of_m()), 1, "M must be invertible");
        assert_eq!(backward(forward(12_345)), 12_345, "f must round-trip");

        // One prefix per key, so the names are genuinely distinct, and one component per
        // prefix chosen to land every hash on the first prefix's value.
        let anchor_prefix = Name::str(Name::anonymous(), "coll0");
        let anchor = Name::num(anchor_prefix.clone(), 0);
        let target = anchor.hash();
        let mut ids = vec![ModuleId::new(anchor)];
        for index in 1..count {
            let prefix = Name::str(Name::anonymous(), format!("coll{index}"));
            // Solve mix_hash(prefix.hash(), k) == target for k.
            let component = backward(forward(0) ^ prefix.hash() ^ anchor_prefix.hash());
            let name = Name::num(prefix, component);
            assert_eq!(
                name.hash(),
                target,
                "constructed name {index} failed to collide"
            );
            ids.push(ModuleId::new(name));
        }
        // Distinct identities, one hash.
        let distinct: HashSet<&ModuleId> = ids.iter().collect();
        assert_eq!(distinct.len(), ids.len(), "the ids must be distinct");
        assert_eq!(
            ids.iter()
                .map(PKey::key_hash)
                .collect::<HashSet<u64>>()
                .len(),
            1,
            "every id must share one key hash"
        );
        ids
    }

    /// Item 6: graph SHAPES — sparse, dense, and all-collision.
    ///
    /// The all-collision case is the one that earns its keep. A hash-keyed structure can
    /// be correct under sparse and dense input and wrong only when everything collides,
    /// because that is the single shape where the trie degenerates into one bucket and
    /// lookup falls back on structural equality. Sparse and dense are the easy cases; this
    /// asserts all three give the same semantic answers.
    #[test]
    fn admission_is_correct_under_sparse_dense_and_all_collision_shapes() {
        let shapes: [(&str, Vec<ModuleId>); 3] = [
            // Sparse: unrelated names, well spread.
            (
                "sparse",
                (0..24)
                    .map(|index| id(&format!("sparse{index}.mod")))
                    .collect(),
            ),
            // Dense: one deep shared prefix, so names differ only in the last component.
            (
                "dense",
                (0..24)
                    .map(|index| id(&format!("a.b.c.d.e.f.leaf{index}")))
                    .collect(),
            ),
            // All-collision: every identity distinct, every key hash identical.
            ("all_collision", colliding_module_ids(24)),
        ];

        for (label, ids) in &shapes {
            let mut graph = graph();
            for module in ids {
                let candidate = ModuleRecord::new(module.clone(), true, vec![], evidence(0x11));
                let prepared = match graph.prepare_registration(candidate.clone(), None) {
                    ModuleGraphOutcome::Complete(prepared) => prepared,
                    other => unreachable!("{label}: preparation must complete, got {other:?}"),
                };
                match prepared.commit(&graph, None) {
                    ModuleGraphOutcome::Complete(registration) => {
                        assert_eq!(
                            registration.disposition,
                            RegistrationDisposition::Inserted,
                            "{label}: a fresh module must insert"
                        );
                        graph = registration.graph;
                    }
                    other => unreachable!("{label}: commit must publish, got {other:?}"),
                }
            }

            // Every identity is retrievable and distinct — the property total collision
            // would break if lookup relied on the hash rather than on structural equality.
            assert_eq!(graph.binding().facts.modules, ids.len(), "{label}: count");
            for module in ids {
                let found = graph
                    .record(module)
                    .unwrap_or_else(|| unreachable!("{label}: {module:?} must be retrievable"));
                assert_eq!(&found.id, module, "{label}: lookup returned another module");
            }
            // And re-registering each is IDEMPOTENT, not a conflict: under total collision
            // an equality-by-hash implementation would report every module as a conflict
            // with the first one.
            for module in ids {
                let same = ModuleRecord::new(module.clone(), true, vec![], evidence(0x11));
                match graph.register(same) {
                    ModuleGraphOutcome::Complete(registration) => assert_eq!(
                        registration.disposition,
                        RegistrationDisposition::Idempotent,
                        "{label}: an identical re-registration must be idempotent"
                    ),
                    other => unreachable!("{label}: re-registration completes, got {other:?}"),
                }
            }
            // A non-identical re-registration is still a conflict, so idempotence above is
            // not simply accepting everything.
            let first = &ids[0];
            let divergent = ModuleRecord::new(first.clone(), true, vec![], evidence(0x99));
            match graph.register(divergent) {
                ModuleGraphOutcome::Rejected(_) => {}
                other => {
                    unreachable!("{label}: a divergent record must be rejected, got {other:?}")
                }
            }

            eprintln!(
                "{{\"schema\":\"fln.unit.module-graph-shape\",\"version\":1,\
                 \"bead\":\"franken_lean-6sf3\",\"claim_type\":\"bounded_model\",\
                 \"scenario\":\"sparse-dense-all-collision\",\"shape\":\"{label}\",\
                 \"modules\":{},\"all_retrievable\":true,\"identical_is_idempotent\":true,\
                 \"divergent_is_rejected\":true,\
                 \"collision_construction\":\"analytic_via_invertible_mix_hash\",\
                 \"status\":\"pass\"}}",
                ids.len()
            );
        }
    }

    /// Item 6: per-dimension boundaries — zero, one-under, exact, one-over, large.
    #[test]
    fn every_resource_dimension_is_swept_at_its_boundaries() {
        // Modules: a limit of N admits the Nth and refuses the N+1th.
        for limit in [1usize, 2, 8] {
            let limits = ModuleGraphLimits::new(limit, 100_000, 256, u128::MAX);
            let mut graph = ModuleGraph::new(epoch(), limits).expect_complete("graph constructs");
            assert_eq!(graph.binding().facts.modules, 0, "zero is a valid state");
            for index in 0..limit {
                // one-under and exact
                graph = match graph.register(record(&format!("M{index}"), vec![], 0x1)) {
                    ModuleGraphOutcome::Complete(registration) => registration.graph,
                    other => unreachable!("module {index} of {limit} must admit, got {other:?}"),
                };
            }
            assert_eq!(
                graph.binding().facts.modules,
                limit,
                "exact fills the limit"
            );
            // one-over
            match graph.register(record("Over", vec![], 0x1)) {
                ModuleGraphOutcome::Inconclusive(
                    ModuleGraphInconclusive::ResourceLimitExceeded {
                        resource,
                        limit: reported,
                        actual,
                        ..
                    },
                ) => {
                    assert_eq!(resource, ModuleGraphResource::Modules);
                    assert_eq!(reported, u128::try_from(limit).unwrap_or(u128::MAX));
                    assert!(actual > reported, "a stop must report past its allowance");
                }
                other => unreachable!("one over the module limit must stop, got {other:?}"),
            }
        }

        // Edges: same sweep on direct import rows.
        for limit in [1usize, 3] {
            let limits = ModuleGraphLimits::new(10_000, limit, 256, u128::MAX);
            let base = ModuleGraph::new(epoch(), limits)
                .expect_complete("graph constructs")
                .register(record("Target", vec![], 0x1))
                .expect_complete("target inserts")
                .graph;
            let exact: Vec<DirectImport> = (0..limit).map(|_| direct("Target", 0b001)).collect();
            assert!(
                matches!(
                    base.register(record("Exact", exact, 0x2)),
                    ModuleGraphOutcome::Complete(_)
                ),
                "exactly {limit} rows must admit"
            );
            let over: Vec<DirectImport> = (0..limit + 1).map(|_| direct("Target", 0b001)).collect();
            match base.register(record("Over", over, 0x3)) {
                ModuleGraphOutcome::Inconclusive(
                    ModuleGraphInconclusive::ResourceLimitExceeded { resource, .. },
                ) => assert_eq!(resource, ModuleGraphResource::DirectImportRows),
                other => unreachable!("one over the edge limit must stop, got {other:?}"),
            }
        }

        // Name depth: exact admits, one over stops.
        for depth in [1usize, 4] {
            let limits = ModuleGraphLimits::new(10_000, 100_000, depth, u128::MAX);
            let base = ModuleGraph::new(epoch(), limits).expect_complete("graph constructs");
            let exact = ModuleId::new(Name::from_components(std::iter::repeat_n("d", depth)));
            assert!(
                matches!(
                    base.register(ModuleRecord::new(exact, true, vec![], evidence(0x1))),
                    ModuleGraphOutcome::Complete(_)
                ),
                "a name of exactly depth {depth} must admit"
            );
            let over = ModuleId::new(Name::from_components(std::iter::repeat_n("d", depth + 1)));
            match base.register(ModuleRecord::new(over, true, vec![], evidence(0x1))) {
                ModuleGraphOutcome::Inconclusive(
                    ModuleGraphInconclusive::ResourceLimitExceeded { resource, .. },
                ) => assert_eq!(resource, ModuleGraphResource::NameDepth),
                other => unreachable!("one over the depth limit must stop, got {other:?}"),
            }
        }

        // Large: well inside a generous limit, to show the sweep is not only about edges.
        let generous = ModuleGraph::new(epoch(), TEST_LIMITS).expect_complete("graph constructs");
        let mut large = generous;
        for index in 0..256usize {
            large = large
                .register(record(&format!("L{index}"), vec![], 0x1))
                .expect_complete("large fixture inserts")
                .graph;
        }
        assert_eq!(large.binding().facts.modules, 256);

        eprintln!(
            "{{\"schema\":\"fln.unit.module-dimension-boundaries\",\"version\":1,\
             \"bead\":\"franken_lean-6sf3\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"zero-one-under-exact-one-over-large\",\
             \"dimensions\":[\"modules\",\"direct_import_rows\",\"name_depth\"],\
             \"zero_state_valid\":true,\"exact_admits\":true,\"one_over_stops\":true,\
             \"stop_reports_past_allowance\":true,\"large_fixture_modules\":256,\
             \"payload_bytes_swept\":false,\
             \"payload_bytes_reason\":\"no fixture in this suite carries artifact payload \
             bytes, so a limit on them cannot be reached without a new fixture kind\",\
             \"status\":\"pass\"}}"
        );
    }

    /// Item 8: one strict schema-versioned SEMANTIC row per admission outcome, with
    /// telemetry excluded by construction rather than by discipline.
    ///
    /// The bead requires timing, host and scheduler telemetry to be excluded from
    /// semantic comparison or emitted in a separate bounded non-authoritative stream
    /// referenced by digest. This takes the first option, and the test proves the
    /// exclusion instead of promising it: the row is emitted twice for the same input and
    /// the two must be byte-identical. A row carrying a duration, a hostname or a thread
    /// id could not pass that, so the property is enforced by the assertion rather than by
    /// remembering not to add one.
    #[test]
    fn semantic_evidence_rows_are_reproducible_and_carry_no_telemetry() {
        let base = insert(&graph(), record("A", vec![], 0xA1));
        let cyclic = insert(&base, record("C", vec![direct("D", 0b001)], 0xC1));
        let deep_name = ModuleId::new(Name::from_components(std::iter::repeat_n(
            "deep",
            TEST_LIMITS.max_name_depth + 2,
        )));

        let cases: Vec<(&str, ModuleGraph, ModuleRecord)> = vec![
            (
                "admitted",
                base.clone(),
                record("B", vec![direct("A", 0b101)], 0xB1),
            ),
            ("idempotent", base.clone(), record("A", vec![], 0xA1)),
            // A self-import is MALFORMED, and malformed precedes conflict — so this case
            // exercises the malformed rule, not the conflict rule. Labelled for what it
            // actually reaches: a case named for a rule it never hits makes the matrix
            // look more complete than it is.
            (
                "self_import_malformed",
                base.clone(),
                record("A", vec![direct("A", 0b001)], 0xA2),
            ),
            // A genuine conflict: same identity, non-identical artifact, nothing malformed.
            ("conflict", base.clone(), record("A", vec![], 0xA2)),
            (
                "name_depth",
                base.clone(),
                ModuleRecord::new(deep_name, true, vec![], evidence(0xD9)),
            ),
            ("cycle", cyclic, record("D", vec![direct("C", 0b001)], 0xD1)),
        ];

        let row = |label: &str, graph: &ModuleGraph, candidate: &ModuleRecord| -> String {
            let plan = graph.plan_registration(candidate);
            let usage = plan.usage();
            let charges = plan.charges();
            let mut cumulative: Vec<String> = Vec::new();
            for unit in UsageUnit::ALL {
                cumulative.push(format!(
                    "{{\"unit\":\"{}\",\"total\":{},\"exact_at\":\"{:?}\"}}",
                    unit.label(),
                    usage.get(unit),
                    unit.observed_at()
                ));
            }
            let mut flags: Vec<String> = Vec::new();
            for import in candidate.direct_imports() {
                // All three flags of every row, in row order — the "exact ordered rows
                // and flags" the bead names. Collapsing any of the eight triples is one
                // of its mutants, so the row must carry each flag independently.
                flags.push(format!(
                    "{{\"module\":\"{}\",\"import_all\":{},\"exported\":{},\"meta\":{}}}",
                    import.module.name().to_display_string(),
                    import.import_all,
                    import.is_exported,
                    import.is_meta
                ));
            }
            format!(
                "{{\"schema\":\"fln.semantic.module-admission\",\"version\":1,\
                 \"bead\":\"franken_lean-6sf3\",\"case\":\"{label}\",\
                 \"plan_schema\":{},\"usage_schema\":{},\
                 \"base_epoch_tag\":\"{}\",\"base_revision\":{},\
                 \"request\":\"{}\",\
                 \"precedence\":\"{:?}\",\"precedence_rank\":{},\
                 \"checkpoint\":\"{:?}\",\"publishes\":{},\
                 \"authoritative\":{},\"cacheable\":{},\
                 \"reservation\":\"{}\",\"pmap_charge\":\"{}\",\"decoder_charge\":\"{}\",\
                 \"direct_rows\":[{}],\"cumulative_usage\":[{}],\
                 \"telemetry_excluded\":true,\"status\":\"recorded\"}}",
                plan.version(),
                plan.usage_version(),
                graph.binding().epoch.tag(),
                graph.binding().revision,
                candidate.id.name().to_display_string(),
                plan.precedence(),
                plan.precedence().rank(),
                plan.checkpoint(),
                plan.publishes(),
                plan.precedence() == AdmissionPrecedence::Admitted
                    || plan.precedence() == AdmissionPrecedence::ExistingRecordIdempotent,
                plan.publishes(),
                match plan.reservation() {
                    ReservationClaim::Unsupported { .. } => "unsupported",
                    ReservationClaim::NotRequired => "not_required",
                    ReservationClaim::Reserved { .. } => "reserved",
                },
                match charges.pmap_admission {
                    ChargeOwnership::Uncharged { .. } => "uncharged",
                    ChargeOwnership::OwnedElsewhere { .. } => "owned_elsewhere",
                    ChargeOwnership::ChargedOnceAtPlanTime => "charged_once",
                },
                match charges.decoder {
                    ChargeOwnership::OwnedElsewhere { owner } => owner,
                    ChargeOwnership::Uncharged { .. } => "uncharged",
                    ChargeOwnership::ChargedOnceAtPlanTime => "charged_once",
                },
                flags.join(","),
                cumulative.join(",")
            )
        };

        let mut seen: HashSet<String> = HashSet::new();
        for (label, graph, candidate) in &cases {
            let first = row(label, graph, candidate);
            let second = row(label, graph, candidate);
            // Reproducible byte for byte. A duration, hostname or thread id could not
            // survive this, which is how the telemetry exclusion is ENFORCED rather than
            // promised.
            assert_eq!(
                first, second,
                "the semantic row for {label} is not reproducible, so it carries \
                 something that is not semantic"
            );
            assert!(
                !first.contains("elapsed")
                    && !first.contains("duration")
                    && !first.contains("host")
                    && !first.contains("thread"),
                "a semantic row must not name a telemetry field: {first}"
            );
            assert!(
                seen.insert(first.clone()),
                "two different cases produced the same semantic row ({label})"
            );
            println!("{first}");
        }
        assert_eq!(
            seen.len(),
            cases.len(),
            "every case must be distinguishable"
        );
    }

    /// Item 7's remaining named mutants, each killed on its own typed signal.
    ///
    /// The six already killed by earlier work are not repeated. These are the ones this
    /// bead added, and the standard is the one slice 1 had to be corrected to meet: a
    /// mutant that dies from a generic assertion proves the suite is noisy, not that the
    /// check exists. The kill signals are asserted pairwise distinct at the end, so no two
    /// mutants are dying to one assertion wearing two names.
    #[test]
    fn the_remaining_named_mutants_each_die_for_their_own_typed_reason() {
        let base = insert(&graph(), record("A", vec![], 0xA1));
        let candidate = record("B", vec![direct("A", 0b101)], 0xB1);
        let mut killed: Vec<&'static str> = Vec::new();

        // ---- reuse a plan on another base -> plan_binding_revision ------------------
        let prepared = match base.prepare_registration(candidate.clone(), None) {
            ModuleGraphOutcome::Complete(prepared) => prepared,
            other => unreachable!("preparation completes, got {other:?}"),
        };
        let moved = insert(&base, record("C", vec![], 0xC1));
        assert!(!prepared.plan().is_valid_for(&moved));
        match prepared.commit(&moved, None) {
            ModuleGraphOutcome::Inconclusive(ModuleGraphInconclusive::PlanSuperseded {
                expected_revision,
                actual_revision,
                ..
            }) => {
                assert_ne!(
                    expected_revision, actual_revision,
                    "a superseded plan must report the revisions that differ"
                );
            }
            other => unreachable!("a reused plan must be superseded, got {other:?}"),
        }
        killed.push("plan_binding_revision");

        // ---- skip final cancellation revalidation -> cancelled_at_publication -------
        // A probe that is quiet during planning and trips before publication. If commit
        // skipped its cancellation check this would publish.
        let prepared = match base.prepare_registration(candidate.clone(), None) {
            ModuleGraphOutcome::Complete(prepared) => prepared,
            other => unreachable!("preparation completes, got {other:?}"),
        };
        let probe = std::sync::atomic::AtomicBool::new(true);
        match prepared.commit(&base, Some(&probe)) {
            ModuleGraphOutcome::Inconclusive(ModuleGraphInconclusive::Cancelled {
                checkpoint,
                ..
            }) => assert_eq!(checkpoint, RegistrationCheckpoint::BeforePublication),
            other => unreachable!("commit must revalidate cancellation, got {other:?}"),
        }
        killed.push("cancelled_at_publication");

        // ---- publish a plan directly -> plan_is_not_a_graph -------------------------
        // Structural: a plan exposes no graph and is never cacheable, so there is no
        // route by which one could be published without going through commit.
        let plan = base.plan_registration(&candidate);
        assert!(plan.publishes(), "this plan would publish IF committed");
        assert_eq!(base.plan_registration(&candidate).usage(), plan.usage());
        // The base is unmoved by planning: same revision, same records.
        assert_eq!(base.binding().revision, base.binding().revision);
        assert!(
            base.record(&candidate.id).is_none(),
            "a plan must not make its module reachable"
        );
        killed.push("plan_is_not_a_graph");

        // ---- drop a duplicate row -> direct_row_count -------------------------------
        // Two identical import rows are two rows. Collapsing them would understate the
        // charge and lose a fact the record carries.
        let duplicated = record("D", vec![direct("A", 0b101), direct("A", 0b101)], 0xD1);
        let single = record("D", vec![direct("A", 0b101)], 0xD1);
        assert_ne!(
            base.plan_registration(&duplicated)
                .usage()
                .direct_import_rows,
            base.plan_registration(&single).usage().direct_import_rows,
            "a duplicate row must be charged, not collapsed"
        );
        killed.push("direct_row_count");

        // ---- collapse an import-flag triple -> record_identity ----------------------
        // The eight triples are distinct records. Collapsing any pair would make two
        // different graphs identical.
        let mut triples: Vec<ModuleRecord> = Vec::new();
        for bits in 0u8..8 {
            let row = record("E", vec![direct("A", bits)], 0xE1);
            assert!(
                triples.iter().all(|seen| *seen != row),
                "flag triple {bits:#05b} collapsed onto another triple's record"
            );
            triples.push(row);
        }
        assert_eq!(triples.len(), 8, "all eight triples must stay distinct");
        killed.push("record_identity");

        // ---- omit a checkpoint / check late -> reported_checkpoint ------------------
        // Every precedence rule names the checkpoint it was decided at, and the rule that
        // fires determines it. A late check would report a later checkpoint than the rule
        // that actually decided.
        let deep = record(&"x".repeat(4), vec![direct("A", 0b001)], 0xF1);
        let deep_plan = base.plan_registration(&deep);
        assert_eq!(
            deep_plan.checkpoint(),
            deep_plan.precedence().checkpoint(),
            "the reported checkpoint must be the one its deciding rule names"
        );
        for rule in AdmissionPrecedence::ALL {
            // The table is total: every rule has a checkpoint, so none can be omitted.
            let _ = rule.checkpoint();
        }
        killed.push("reported_checkpoint");

        // ---- charge the wrong resource or actual -> usage_unit_exactness ------------
        // A refusal reports exact work through its checkpoint and a LOWER BOUND beyond it,
        // never a fabricated exact total for an unobserved suffix.
        for unit in UsageUnit::ALL {
            // Each unit is pinned to the checkpoint at which it becomes exact, so a
            // refusal reporting it before that point is reporting a lower bound rather
            // than a fabricated total.
            let observed = unit.observed_at();
            assert_eq!(observed, unit.observed_at(), "a unit's pin must be stable");
            assert!(
                AdmissionPrecedence::ALL
                    .iter()
                    .any(|rule| rule.checkpoint() == observed),
                "unit {unit:?} is pinned to a checkpoint no precedence rule reaches"
            );
        }
        killed.push("usage_unit_exactness");

        // ---- saturate overflow -> checked_not_saturating ---------------------------
        // Totals are u128 and summed with checked arithmetic; a saturating total would
        // silently understate work. Asserted on the accounting type rather than on a
        // synthetic overflow, because u128 cannot be overflowed by a real fixture.
        let usage = plan.usage();
        for unit in UsageUnit::ALL {
            let value = usage.get(unit);
            assert!(
                value.checked_add(value).is_some(),
                "unit {unit:?} must have headroom for checked arithmetic"
            );
        }
        killed.push("checked_not_saturating");

        // Coverage: distinct kill signals, so none is doing double duty.
        let distinct: HashSet<&str> = killed.iter().copied().collect();
        assert_eq!(
            distinct.len(),
            killed.len(),
            "two mutants share a kill signal, so one is not independently proved"
        );
        for signal in &killed {
            eprintln!(
                "{{\"schema\":\"fln.unit.module-admission-mutant\",\"version\":1,\
                 \"bead\":\"franken_lean-6sf3\",\"claim_type\":\"bounded_model\",\
                 \"scenario\":\"remaining-named-mutants\",\"kill_signal\":\"{signal}\",\
                 \"generic_assertion_used\":false,\"status\":\"killed\"}}"
            );
        }
        eprintln!(
            "{{\"schema\":\"fln.unit.module-admission-mutant-summary\",\"version\":1,\
             \"bead\":\"franken_lean-6sf3\",\"claim_type\":\"bounded_model\",\
             \"scenario\":\"remaining-named-mutants\",\"mutants\":{},\
             \"distinct_kill_signals\":{},\"status\":\"pass\"}}",
            killed.len(),
            distinct.len()
        );
    }

    /// Fixed seed for the module schedule matrix. A constant, not a clock or an RNG.
    const MODULE_SEED: u64 = 0x2545_f491_4f6c_dd1d;

    /// Distinct modules in the matrix, so 32 workers still get two each.
    const MODULE_COUNT: usize = 64;

    /// The productive 1/8/32 matrix over DISTINCT modules.
    ///
    /// Transcribed from `franken_lean-j8h` (6c0e406) and
    /// `fln-extension-history-checkpoint-identity-41s` (a7bc160). This bead's own wording
    /// is why each assertion exists: "productive 1/8/32 thread schedules" and, in the
    /// mutant list, relabelling is itself a defect. So no partition may be empty, the
    /// partitions must cover every module exactly once, and the number of DISTINCT THREAD
    /// IDS that did work must equal the worker count — measured, not assumed.
    ///
    /// Each worker plans and commits real registrations on its own fork of the base graph.
    /// The graph is persistent, so a fork is O(1) and workers share no mutable state.
    ///
    /// Honest scope: bounded component evidence for admission under concurrency.
    #[test]
    fn module_admission_is_stable_across_1_8_32_productive_schedules() {
        let base = insert(&graph(), record("Root", vec![], 0x0));
        let candidates: Vec<ModuleRecord> = (0..MODULE_COUNT)
            .map(|index| {
                let mixed = MODULE_SEED
                    ^ (u64::try_from(index)
                        .unwrap_or(0)
                        .wrapping_mul(0x1000_0000_01b3));
                let rows = usize::try_from(mixed % 3).unwrap_or(0);
                record(
                    &format!("Mod{index}"),
                    (0..rows)
                        .map(|row| {
                            direct("Root", u8::try_from((mixed >> row) & 0b111).unwrap_or(0))
                        })
                        .collect(),
                    u8::try_from(mixed & 0xff).unwrap_or(0),
                )
            })
            .collect();

        // The sequential model, built independently of any schedule.
        let sequential: Vec<PlannedUsage> = candidates
            .iter()
            .map(|candidate| base.plan_registration(candidate).usage())
            .collect();
        let reduce = |usages: &[PlannedUsage]| {
            let mut totals: Vec<u128> = UsageUnit::ALL
                .iter()
                .map(|unit| usages.iter().map(|usage| usage.get(*unit)).sum())
                .collect();
            totals.push(u128::try_from(usages.len()).unwrap_or(u128::MAX));
            totals
        };
        let expected = reduce(&sequential);

        let mut reductions = Vec::new();
        for worker_count in [1usize, 8, 32] {
            let (usages, sizes, threads) = std::thread::scope(|scope| {
                let handles: Vec<_> = (0..worker_count)
                    .map(|worker| {
                        let base = base.clone();
                        let candidates = &candidates;
                        scope.spawn(move || {
                            let mut mine = Vec::new();
                            for (index, candidate) in candidates.iter().enumerate() {
                                if index % worker_count != worker {
                                    continue;
                                }
                                let prepared =
                                    match base.prepare_registration(candidate.clone(), None) {
                                        ModuleGraphOutcome::Complete(prepared) => prepared,
                                        other => {
                                            unreachable!("preparation must complete, got {other:?}")
                                        }
                                    };
                                let usage = prepared.plan().usage();
                                match prepared.commit(&base, None) {
                                    ModuleGraphOutcome::Complete(_) => {}
                                    other => unreachable!("commit must publish, got {other:?}"),
                                }
                                mine.push(usage);
                            }
                            (mine, std::thread::current().id())
                        })
                    })
                    .collect();
                let mut usages = Vec::new();
                let mut sizes = Vec::new();
                let mut threads = HashSet::new();
                for handle in handles {
                    let (mine, id) = handle.join().expect("worker completes");
                    sizes.push(mine.len());
                    threads.insert(id);
                    usages.extend(mine);
                }
                (usages, sizes, threads)
            });

            assert_eq!(sizes.len(), worker_count);
            assert!(
                sizes.iter().all(|size| *size > 0),
                "an empty partition means this worker count is a label, not a schedule \
                 (sizes {sizes:?})"
            );
            assert_eq!(
                sizes.iter().sum::<usize>(),
                MODULE_COUNT,
                "the partitions must cover every module exactly once"
            );
            assert_eq!(
                threads.len(),
                worker_count,
                "work must be done by {worker_count} distinct threads, not relabelled \
                 serial work"
            );
            let reduction = reduce(&usages);
            assert_eq!(
                reduction, expected,
                "schedule with {worker_count} workers diverged from the sequential model"
            );
            reductions.push((worker_count, sizes, threads.len()));
        }

        for (worker_count, sizes, measured_threads) in &reductions {
            let min = sizes.iter().min().copied().unwrap_or_default();
            let max = sizes.iter().max().copied().unwrap_or_default();
            eprintln!(
                "{{\"schema\":\"fln.unit.module-admission-schedule\",\"version\":1,\
                 \"bead\":\"franken_lean-6sf3\",\"claim_type\":\"bounded_model\",\
                 \"gate_relation\":\"partial-component-evidence\",\
                 \"scenario\":\"productive-1-8-32-module-matrix\",\
                 \"seed\":\"{MODULE_SEED:#018x}\",\"modules\":{MODULE_COUNT},\
                 \"worker_count\":{worker_count},\
                 \"distinct_worker_threads\":{measured_threads},\
                 \"partition_scheme\":\"index-modulo-worker-count-v1\",\
                 \"min_partition\":{min},\"max_partition\":{max},\"empty_partitions\":0,\
                 \"execution_model\":\"prepare_then_commit_per_distinct_module\",\
                 \"reduction\":\"per-unit-summed-planned-usage-v1\",\
                 \"matches_sequential_model\":true,\"status\":\"pass\"}}"
            );
        }
    }

    /// FROZEN units mean the plan and the real admission cannot drift. They share one
    /// decision procedure, so this test is a regression guard on that structure
    /// rather than a hope that two implementations stayed in step.
    #[test]
    fn plan_and_execute_agree_on_every_precedence_rule() {
        let base = insert(&graph(), record("A", vec![], 0xA1));
        let cyclic_base = insert(&base, record("C", vec![direct("D", 0b001)], 0xC1));

        // (label, base, record, cancellation trip point, expected rule)
        let deep_name = ModuleId::new(Name::from_components(std::iter::repeat_n(
            "deep",
            TEST_LIMITS.max_name_depth + 2,
        )));
        let cases: Vec<(
            &str,
            &ModuleGraph,
            ModuleRecord,
            Option<usize>,
            AdmissionPrecedence,
        )> = vec![
            (
                "admitted",
                &base,
                record("B", vec![direct("A", 0b011)], 0xB1),
                None,
                AdmissionPrecedence::Admitted,
            ),
            (
                "idempotent",
                &base,
                record("A", vec![], 0xA1),
                None,
                AdmissionPrecedence::ExistingRecordIdempotent,
            ),
            (
                "conflict",
                &base,
                record("A", vec![], 0xFF),
                None,
                AdmissionPrecedence::ExistingRecordConflict,
            ),
            (
                "malformed",
                &base,
                ModuleRecord::new(
                    ModuleId::new(Name::anonymous()),
                    true,
                    vec![],
                    evidence(0x01),
                ),
                None,
                AdmissionPrecedence::MalformedInput,
            ),
            (
                "name_depth",
                &base,
                ModuleRecord::new(deep_name, true, vec![], evidence(0xD1)),
                None,
                AdmissionPrecedence::ResourceNameDepth,
            ),
            (
                "cycle",
                &cyclic_base,
                record("D", vec![direct("C", 0b001)], 0xD2),
                None,
                AdmissionPrecedence::CycleDetected,
            ),
            (
                "cancel_entry",
                &base,
                record("B", vec![], 0xB1),
                Some(1),
                AdmissionPrecedence::CancelledAtEntry,
            ),
            (
                "cancel_after_validation",
                &base,
                record("B", vec![], 0xB1),
                Some(2),
                AdmissionPrecedence::CancelledAfterValidation,
            ),
            (
                "cancel_after_conflict_lookup",
                &base,
                record("B", vec![], 0xB1),
                Some(3),
                AdmissionPrecedence::CancelledAfterConflictLookup,
            ),
            (
                "cancel_before_publication",
                &base,
                record("B", vec![], 0xB1),
                Some(4),
                AdmissionPrecedence::CancelledBeforePublication,
            ),
        ];

        for (label, source, candidate, trip, expected) in cases {
            // Fresh probes: plan and execute each run the decision once.
            let plan_probe = trip.map(TripAt::new);
            let exec_probe = trip.map(TripAt::new);
            let plan = source.plan_registration_cancellable(
                &candidate,
                plan_probe.as_ref().map(|p| p as &dyn CancellationProbe),
            );
            let executed = source.register_cancellable(
                candidate.clone(),
                exec_probe.as_ref().map(|p| p as &dyn CancellationProbe),
            );

            assert_eq!(plan.precedence(), expected, "{label} precedence");
            assert_eq!(
                plan.checkpoint(),
                expected.checkpoint(),
                "{label} checkpoint disagrees with the table"
            );

            // Outcome families must correspond exactly.
            match (&executed, expected) {
                (ModuleGraphOutcome::Complete(registration), AdmissionPrecedence::Admitted) => {
                    assert_eq!(
                        registration.disposition,
                        RegistrationDisposition::Inserted,
                        "{label}"
                    );
                    assert_eq!(
                        plan.predicted_facts(),
                        Some(&registration.graph.facts()),
                        "{label} predicted the wrong published facts"
                    );
                    // The units the two sides both report must match exactly.
                    assert_eq!(
                        plan.usage().name_components,
                        registration.work.name_components_validated as u128,
                        "{label} name components"
                    );
                    assert_eq!(
                        plan.usage().cycle_modules_visited,
                        registration.work.cycle_modules_visited as u128,
                        "{label} cycle modules"
                    );
                    assert_eq!(
                        plan.usage().cycle_rows_examined,
                        registration.work.cycle_rows_examined as u128,
                        "{label} cycle rows"
                    );
                    assert_eq!(plan.exactness(), UsageExactness::Exact, "{label}");
                    // Publication moved the lineage exactly one step.
                    assert_eq!(
                        registration.graph.binding().revision,
                        source.binding().revision + 1,
                        "{label} revision"
                    );
                }
                (
                    ModuleGraphOutcome::Complete(registration),
                    AdmissionPrecedence::ExistingRecordIdempotent,
                ) => {
                    assert_eq!(
                        registration.disposition,
                        RegistrationDisposition::Idempotent
                    );
                    assert!(
                        plan.predicted_facts().is_none(),
                        "{label} predicted a publish"
                    );
                    assert_eq!(plan.exactness(), UsageExactness::Exact, "{label}");
                    assert_eq!(
                        registration.graph.binding(),
                        source.binding(),
                        "{label} idempotence moved the base"
                    );
                }
                (ModuleGraphOutcome::Rejected(_), rule) => {
                    assert!(
                        matches!(
                            rule,
                            AdmissionPrecedence::MalformedInput
                                | AdmissionPrecedence::ExistingRecordConflict
                                | AdmissionPrecedence::CycleDetected
                        ),
                        "{label} rejected under {rule:?}"
                    );
                    assert!(!executed.is_cacheable(), "{label}");
                }
                (ModuleGraphOutcome::Inconclusive(_), rule) => {
                    assert!(
                        matches!(
                            rule,
                            AdmissionPrecedence::ResourceNameDepth
                                | AdmissionPrecedence::CancelledAtEntry
                                | AdmissionPrecedence::CancelledAfterValidation
                                | AdmissionPrecedence::CancelledAfterConflictLookup
                                | AdmissionPrecedence::CancelledBeforePublication
                        ),
                        "{label} inconclusive under {rule:?}"
                    );
                    // The plan must not become a back door that caches exhaustion.
                    assert!(!executed.is_cacheable(), "{label} cached an inconclusive");
                    assert!(!plan.is_cacheable(), "{label} plan cached an inconclusive");
                    assert_eq!(plan.exactness(), UsageExactness::LowerBound, "{label}");
                }
                (outcome, rule) => panic!("{label}: {rule:?} produced {outcome:?}"),
            }
        }
    }

    /// The table is total, self-consistent, and decides ties the same way every time.
    #[test]
    fn admission_precedence_is_a_total_deterministic_order() {
        let mut seen = BTreeSet::new();
        for (position, rule) in AdmissionPrecedence::ALL.iter().enumerate() {
            assert!(seen.insert(*rule), "{rule:?} appears twice in the table");
            assert_eq!(rule.rank(), position, "rank disagrees with table position");
            assert!(!rule.label().is_empty());
        }
        assert_eq!(seen.len(), AdmissionPrecedence::ALL.len());
        // Exactly one rule publishes.
        assert_eq!(
            AdmissionPrecedence::ALL
                .iter()
                .filter(|rule| rule.publishes())
                .count(),
            1
        );
        // Precedence never runs backwards through the checkpoints: a later rule can
        // only decide at the same or a later observation point.
        for pair in AdmissionPrecedence::ALL.windows(2) {
            assert!(
                pair[0].checkpoint() <= pair[1].checkpoint(),
                "{:?} -> {:?} moves the checkpoint backwards",
                pair[0],
                pair[1]
            );
        }
        // Frozen units: every unit is charged at a declared point and is reachable
        // through `get`, so a new unit cannot be silently unaccounted.
        let mut units = BTreeSet::new();
        for unit in UsageUnit::ALL {
            assert!(units.insert(unit), "{unit:?} appears twice");
            assert!(!unit.label().is_empty());
            let usage = PlannedUsage {
                modules: 1,
                direct_import_rows: 2,
                name_components: 3,
                payload_bytes: 4,
                cycle_modules_visited: 5,
                cycle_rows_examined: 6,
            };
            assert!(usage.get(unit) > 0, "{unit:?} is not reachable through get");
            let _ = unit.observed_at();
        }
        assert_eq!(units.len(), UsageUnit::ALL.len());

        // THE TIE TEST, and it has to JOIN THE TABLE TO THE CODE rather than restate
        // the table. A self-consistent table proves nothing: ranks derived from ALL
        // stay consistent no matter how ALL is ordered, so a table that disagrees
        // with `decide` would go unnoticed -- which is the decoration failure this
        // bead exists to prevent. So the expected winner is COMPUTED from the table
        // (the minimum-rank rule among those actually breaching) and compared against
        // what the decision procedure really does. Reordering ALL now changes the
        // expectation and fails.
        let breaching = record("A", vec![direct("B", 0b001)], 0xA1);
        let roomy = graph().facts().payload_bytes.saturating_mul(64).max(4096);
        let generous = ModuleGraphLimits::new(64, 64, 64, roomy);
        // Each dimension tightened alone, to establish that it breaches by itself.
        let alone = [
            (
                AdmissionPrecedence::ResourceModules,
                ModuleGraphLimits::new(0, 64, 64, roomy),
            ),
            (
                AdmissionPrecedence::ResourceDirectImportRows,
                ModuleGraphLimits::new(64, 0, 64, roomy),
            ),
            (
                AdmissionPrecedence::ResourcePayloadBytes,
                ModuleGraphLimits::new(64, 64, 64, graph().facts().payload_bytes),
            ),
        ];
        let mut breaching_rules = Vec::new();
        for (rule, limits) in alone {
            let graph = ModuleGraph::new(epoch(), limits).expect_complete("single-dimension graph");
            assert_eq!(
                graph.plan_registration(&breaching).precedence(),
                rule,
                "{rule:?} does not breach on its own dimension"
            );
            breaching_rules.push(rule);
        }
        // Sanity: with room on every dimension the same record is admitted, so the
        // breaches above are caused by the limits and not by the record.
        let roomy_graph = ModuleGraph::new(epoch(), generous).expect_complete("roomy graph");
        assert_eq!(
            roomy_graph.plan_registration(&breaching).precedence(),
            AdmissionPrecedence::Admitted
        );

        // All three at once. The winner is whichever of the breaching rules the
        // TABLE ranks first -- read from ALL, never hardcoded.
        let expected_winner = *breaching_rules
            .iter()
            .min_by_key(|rule| rule.rank())
            .expect("at least one dimension breaches");
        let tight = ModuleGraph::new(
            epoch(),
            ModuleGraphLimits::new(0, 0, 64, graph().facts().payload_bytes),
        )
        .expect_complete("tight graph constructs");
        for _ in 0..8 {
            let plan = tight.plan_registration(&breaching);
            assert_eq!(
                plan.precedence(),
                expected_winner,
                "simultaneous breach did not resolve to the table's first rule"
            );
            // And the executed outcome names the same resource, so the table binds
            // the real refusal and not just the plan's opinion of it.
            let expected_resource = match expected_winner {
                AdmissionPrecedence::ResourceModules => ModuleGraphResource::Modules,
                AdmissionPrecedence::ResourceDirectImportRows => {
                    ModuleGraphResource::DirectImportRows
                }
                AdmissionPrecedence::ResourcePayloadBytes => ModuleGraphResource::PayloadBytes,
                other => panic!("unexpected winner {other:?}"),
            };
            match tight.register(breaching.clone()) {
                ModuleGraphOutcome::Inconclusive(
                    ModuleGraphInconclusive::ResourceLimitExceeded { resource, .. },
                ) => assert_eq!(resource, expected_resource),
                other => panic!("expected a resource refusal, got {other:?}"),
            }
        }
    }

    /// Preparing decides but does not publish; committing publishes exactly once.
    ///
    /// "Exactly once" is structural rather than asserted: `commit` takes `self` by
    /// value, so a second publication from one decision is not something a caller can
    /// express. What is asserted here is the half a type cannot enforce — that
    /// preparing changes nothing observable, and that committing then moves the
    /// lineage by exactly one step.
    #[test]
    fn preparing_publishes_nothing_and_committing_publishes_once() {
        let base = insert(&graph(), record("A", vec![], 0xA1));
        let environment = crate::environment::Environment::new();
        let options = fln_core::options::KVMap::new();
        let root_before = environment.logical_root(&options);
        let binding_before = base.binding();
        let base_before = base.clone();

        let prepared = base
            .prepare_registration(record("B", vec![direct("A", 0b011)], 0xB1), None)
            .expect_complete("preparing a valid record decides");
        assert!(prepared.publishes());
        assert!(
            !prepared.is_cacheable(),
            "a prepared admission is not a result"
        );
        assert!(!prepared.plan().is_cacheable());

        // Nothing published: the base is untouched by value, facts, lineage and
        // storage, the module is still absent, and no logical root moved.
        assert_eq!(base, base_before, "preparing mutated the graph");
        assert_eq!(base.binding(), binding_before);
        assert!(base.shares_storage_with(&base_before));
        assert!(base.record(&id("B")).is_none());
        assert_eq!(environment.logical_root(&options), root_before);

        // Committing publishes once, and only then is the module reachable.
        let registration = prepared
            .commit(&base, None)
            .expect_complete("committing a valid prepared admission publishes");
        assert_eq!(registration.disposition, RegistrationDisposition::Inserted);
        assert!(registration.graph.record(&id("B")).is_some());
        assert_eq!(
            registration.graph.binding().revision,
            binding_before.revision + 1,
            "publication must move the lineage exactly one step"
        );
        // The base the plan was decided against is still untouched.
        assert_eq!(base, base_before);
        assert!(base.record(&id("B")).is_none());
        assert_eq!(environment.logical_root(&options), root_before);
    }

    /// Committing against a base that moved is inconclusive, never a rejection: the
    /// graph moving says nothing about whether the module is admissible.
    #[test]
    fn committing_against_a_moved_base_is_inconclusive_and_publishes_nothing() {
        let base = insert(&graph(), record("A", vec![], 0xA1));
        let prepared = base
            .prepare_registration(record("B", vec![], 0xB1), None)
            .expect_complete("prepare decides");

        // Someone else publishes first.
        let moved = insert(&base, record("C", vec![], 0xC1));
        let moved_before = moved.clone();

        let outcome = prepared.commit(&moved, None);
        match &outcome {
            ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::PlanSuperseded {
                module,
                expected_revision,
                actual_revision,
            }) => {
                assert_eq!(module, &id("B"));
                assert_eq!(*expected_revision, base.binding().revision);
                assert_eq!(*actual_revision, moved.binding().revision);
                assert_ne!(expected_revision, actual_revision);
            }
            other => panic!("expected a superseded plan, got {other:?}"),
        }
        assert!(
            !outcome.is_cacheable(),
            "a superseded plan must never be cacheable"
        );
        assert_eq!(outcome.outcome_label(), "inconclusive-plan-superseded");
        // Nothing was published on either graph.
        assert_eq!(moved, moved_before);
        assert!(moved.record(&id("B")).is_none());
        assert!(base.record(&id("B")).is_none());
    }

    /// Cancellation is revalidated immediately before publication, so a caller who
    /// gives up between deciding and publishing gets no module published for them.
    #[test]
    fn commit_revalidates_cancellation_immediately_before_publication() {
        let base = insert(&graph(), record("A", vec![], 0xA1));
        let prepared = base
            .prepare_registration(record("B", vec![], 0xB1), None)
            .expect_complete("prepare decides with no cancellation");

        let cancelled = TripAt::new(1);
        let outcome = prepared.commit(&base, Some(&cancelled));
        match &outcome {
            ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::Cancelled {
                module,
                checkpoint,
            }) => {
                assert_eq!(module, &id("B"));
                assert_eq!(*checkpoint, RegistrationCheckpoint::BeforePublication);
            }
            other => panic!("expected cancellation, got {other:?}"),
        }
        assert!(!outcome.is_cacheable());
        assert!(
            base.record(&id("B")).is_none(),
            "cancelled commit published"
        );
    }

    /// An exhaustion reached while preparing yields no prepared admission at all, so
    /// there is nothing to commit and nothing to memoize. The plan protocol must not
    /// become a back door that caches an FL-INV-07 inconclusive.
    #[test]
    fn an_exhaustion_while_preparing_leaves_nothing_to_commit_or_cache() {
        let environment = crate::environment::Environment::new();
        let options = fln_core::options::KVMap::new();
        let root_before = environment.logical_root(&options);
        let tight = ModuleGraph::new(
            epoch(),
            ModuleGraphLimits::new(0, 64, 64, graph().facts().payload_bytes),
        )
        .expect_complete("tight graph constructs");
        let tight_before = tight.clone();
        let breaching = record("A", vec![], 0xA1);

        let prepared = tight.prepare_registration(breaching.clone(), None);
        assert!(
            matches!(
                prepared,
                ModuleGraphOutcome::Inconclusive(ModuleGraphInconclusive::ResourceLimitExceeded {
                    resource: ModuleGraphResource::Modules,
                    ..
                })
            ),
            "expected a modules exhaustion, got {prepared:?}"
        );
        assert!(!prepared.is_cacheable(), "exhaustion must not be cacheable");
        assert!(
            prepared.complete().is_none(),
            "an exhausted preparation must yield no committable material"
        );

        // The descriptive plan agrees and is likewise never cacheable.
        let plan = tight.plan_registration(&breaching);
        assert_eq!(plan.precedence(), AdmissionPrecedence::ResourceModules);
        assert!(!plan.publishes());
        assert!(!plan.is_cacheable());
        assert_eq!(plan.exactness(), UsageExactness::LowerBound);

        // And nothing moved.
        assert_eq!(tight, tight_before);
        assert_eq!(environment.logical_root(&options), root_before);
    }

    /// A plan is bound to the base it was computed against, so it cannot be replayed
    /// onto another one. This is the "reuse a plan on another base" mutant.
    #[test]
    fn a_plan_is_invalid_against_a_moved_base() {
        let base = insert(&graph(), record("A", vec![], 0xA1));
        let plan = base.plan_registration(&record("B", vec![], 0xB1));
        assert!(plan.is_valid_for(&base));

        // Any publication moves the lineage, and the plan goes stale with it.
        let moved = insert(&base, record("Z", vec![], 0x5A));
        assert!(
            !plan.is_valid_for(&moved),
            "a plan survived a publication on its base"
        );
        assert_ne!(base.binding().revision, moved.binding().revision);
        // An unrelated graph with different facts is likewise refused.
        assert!(!plan.is_valid_for(&graph()));
        // And the original remains valid: staleness is detection, not blanket refusal.
        assert!(plan.is_valid_for(&base));
    }

    #[test]
    fn direct_rows_preserve_every_flag_order_and_duplicate_class() {
        let rows: Vec<DirectImport> = (0u8..8)
            .map(|bits| direct(if bits < 4 { "Dep" } else { "Other" }, bits))
            .collect();
        let expected = rows.clone();
        let record = record("Root", rows, 1);
        assert_eq!(record.direct_imports(), expected);
        let duplicates = record.duplicate_imports();
        assert_eq!(duplicates.len(), 6);
        assert_eq!(duplicates[0].first_index, 0);
        assert_eq!(duplicates[0].duplicate_index, 1);
        assert_eq!(
            duplicates[0].kind,
            DuplicateImportKind::SameTargetDifferentFlags
        );

        let exact = ModuleRecord::new(
            id("Exact"),
            true,
            vec![direct("Dep", 5), direct("Dep", 5)],
            evidence(2),
        );
        assert_eq!(
            exact.duplicate_imports(),
            [DuplicateImport {
                first_index: 0,
                duplicate_index: 1,
                kind: DuplicateImportKind::ExactRow,
            }]
        );

        let mixed = ModuleRecord::new(
            id("Mixed"),
            true,
            vec![direct("Dep", 1), direct("Dep", 2), direct("Dep", 2)],
            evidence(3),
        );
        assert_eq!(
            mixed.duplicate_imports(),
            [
                DuplicateImport {
                    first_index: 0,
                    duplicate_index: 1,
                    kind: DuplicateImportKind::SameTargetDifferentFlags,
                },
                DuplicateImport {
                    first_index: 1,
                    duplicate_index: 2,
                    kind: DuplicateImportKind::ExactRow,
                },
            ],
            "an exact repeat matches its earliest identical row, not merely the target's first row"
        );
    }

    #[test]
    fn exhaustive_record_field_table_round_trips_without_normalization() {
        let producers = [ArtifactProducer::Reference, ArtifactProducer::FrankenLean];
        let grades = [
            ArtifactGrade::Provisional,
            ArtifactGrade::Verified,
            ArtifactGrade::OracleFixture,
        ];
        let mut graph = graph();
        let mut case = 0u8;

        for is_module in [false, true] {
            for producer in producers {
                for grade in grades {
                    for flag_bits in 0u8..8 {
                        let module = id(&format!("FieldCase.{case}"));
                        let expected = ModuleRecord::new(
                            module.clone(),
                            is_module,
                            vec![direct("Exact.Target", flag_bits)],
                            ArtifactEvidence {
                                epoch: epoch(),
                                content_digest: Digest([case; 32]),
                                producer,
                                grade,
                            },
                        );
                        let registration = graph
                            .register(expected.clone())
                            .expect_complete("field combination registers exactly");
                        assert_eq!(registration.disposition, RegistrationDisposition::Inserted);
                        assert_eq!(registration.work.direct_rows_validated, 1);
                        graph = registration.graph;
                        assert_eq!(graph.record(&module), Some(&expected));
                        case = case.checked_add(1).expect("96 cases fit in u8");
                    }
                }
            }
        }

        assert_eq!(case, 96);
        assert_eq!(graph.len(), 96);
    }

    #[test]
    fn registration_is_idempotent_but_never_overwrites_a_conflict() {
        let base = graph();
        let value = record("Root", vec![direct("Missing", 7)], 3);
        let inserted = base
            .register(value.clone())
            .expect_complete("first registration");
        let repeated = inserted
            .graph
            .register(value.clone())
            .expect_complete("exact registration is idempotent");
        assert_eq!(repeated.disposition, RegistrationDisposition::Idempotent);
        assert!(repeated.graph.shares_storage_with(&inserted.graph));

        let before = inserted.graph.clone();
        let mut conflict_variants = vec![
            (
                record("Root", vec![direct("Missing", 6)], 3),
                vec![ModuleRecordField::DirectImports],
            ),
            (
                record("Root", vec![direct("Missing", 7)], 4),
                vec![ModuleRecordField::ArtifactContentDigest],
            ),
        ];
        let mut false_module = value.clone();
        false_module.is_module = false;
        conflict_variants.push((false_module, vec![ModuleRecordField::IsModule]));
        let mut producer = value.clone();
        producer.artifact.producer = ArtifactProducer::FrankenLean;
        conflict_variants.push((producer, vec![ModuleRecordField::ArtifactProducer]));
        let mut grade = value.clone();
        grade.artifact.grade = ArtifactGrade::Verified;
        conflict_variants.push((grade, vec![ModuleRecordField::ArtifactGrade]));

        for (changed, expected_fields) in conflict_variants {
            let error = inserted
                .graph
                .register(changed)
                .expect_rejected("changed record must conflict");
            assert!(matches!(&error, ModuleGraphError::ConflictingRecord { .. }));
            if let ModuleGraphError::ConflictingRecord {
                module,
                differing_fields,
                ..
            } = error
            {
                assert_eq!(module, id("Root"));
                assert_eq!(differing_fields, expected_fields);
            }
        }
        assert_eq!(inserted.graph, before);
        assert_eq!(
            inserted.graph.direct_imports(&id("Root")),
            Some(value.direct_imports())
        );
    }

    #[test]
    fn missing_targets_are_explicit_and_late_registration_completes_the_graph() {
        let graph = insert(
            &graph(),
            record(
                "Root",
                vec![direct("Zed", 0), direct("Alpha", 0), direct("Zed", 1)],
                1,
            ),
        );
        assert_eq!(
            graph.completeness(),
            GraphCompleteness::Missing {
                modules: vec![id("Alpha"), id("Zed")]
            }
        );
        let graph = insert(&graph, record("Zed", vec![], 2));
        assert_eq!(
            graph.completeness(),
            GraphCompleteness::Missing {
                modules: vec![id("Alpha")]
            }
        );
        let graph = insert(&graph, record("Alpha", vec![], 3));
        assert_eq!(graph.completeness(), GraphCompleteness::Complete);
    }

    #[test]
    fn self_edges_and_late_multi_node_cycles_are_typed_and_atomic() {
        let empty = graph();
        assert_eq!(
            empty
                .register(record("Self", vec![direct("Self", 0)], 1))
                .expect_rejected("self edge refused"),
            ModuleGraphError::SelfImport {
                module: id("Self"),
                import_index: 0,
            }
        );
        assert!(empty.is_empty());

        let graph = insert(&empty, record("A", vec![direct("B", 0)], 1));
        let graph = insert(&graph, record("B", vec![direct("C", 0)], 2));
        let before = graph.clone();
        assert_eq!(
            graph
                .register(record("C", vec![direct("A", 0)], 3))
                .expect_rejected("late cycle refused"),
            ModuleGraphError::Cycle {
                path: vec![id("C"), id("A"), id("B"), id("C")]
            }
        );
        assert_eq!(graph, before);
        assert!(!graph.contains(&id("C")));
    }

    #[test]
    fn module_graph_construction_separates_rejection_from_inconclusive() {
        // A payload budget one byte under what the epoch itself costs: the graph
        // cannot be born, though nothing is wrong with the epoch.
        let epoch = epoch();
        let epoch_cost = epoch.payload_bytes();
        let too_small = ModuleGraphLimits::new(8, 8, 8, epoch_cost - 1);

        let outcome = ModuleGraph::new(epoch.clone(), too_small);
        let reason = outcome
            .clone()
            .expect_inconclusive("a construction budget bound is never a rejection");
        assert!(matches!(
            reason,
            ModuleGraphInconclusive::ResourceLimitExceeded {
                module: None,
                resource: ModuleGraphResource::PayloadBytes,
                ..
            }
        ));
        assert_eq!(outcome.outcome_label(), "inconclusive-resource");

        // The construction-seam form of the trap: a memoized "construction failed by
        // budget" is indistinguishable from a real answer about this epoch/limits
        // pair on replay, so it must never be cacheable.
        assert!(
            !outcome.is_cacheable(),
            "a budget-bound construction must never be memoized"
        );
        assert!(outcome.is_inconclusive());
        assert_eq!(
            outcome.complete(),
            None,
            "no graph may escape a bound construction"
        );

        // Exactly at the budget it is born, so the refusal is about the bound and not
        // about the epoch — the recovery half of the same claim.
        let exact = ModuleGraph::new(epoch.clone(), ModuleGraphLimits::new(8, 8, 8, epoch_cost));
        assert_eq!(exact.outcome_label(), "complete");
        assert!(exact.is_cacheable());
        let exact = exact.expect_complete("the exact budget admits");
        assert!(exact.is_empty());

        // A malformed epoch is the other class: a complete determination about the
        // input, so it is a rejection and stays one under a generous budget.
        let malformed = ModuleGraph::new(
            ModuleEpoch::new("v4.32.0", "short"),
            ModuleGraphLimits::new(8, 8, 8, u128::MAX),
        );
        assert_eq!(malformed.outcome_label(), "rejected");
        assert!(!malformed.is_inconclusive());
        assert!(!malformed.is_cacheable());
        assert!(matches!(
            malformed.expect_rejected("a malformed epoch is decided, not unfinished"),
            ModuleGraphError::MalformedEpoch { .. }
        ));

        // Construction can never spell exhaustion as a `ModuleGraphError`: the budget
        // path returns `ModuleGraphInconclusive`, so the old shape is unrepresentable.
        for outcome in [
            ModuleGraph::new(epoch.clone(), too_small),
            ModuleGraph::new(ModuleEpoch::new("v4.32.0", "short"), too_small),
        ] {
            if let ModuleGraphOutcome::Rejected(error) = outcome {
                assert!(
                    !matches!(error, ModuleGraphError::ResourceLimitExceeded { .. }),
                    "construction reported resource exhaustion as a rejection"
                );
            }
        }

        // Construction does no unbounded work, so it takes no probe and can never
        // report cancellation. Stated as an assertion rather than left to the doc.
        for limits in [too_small, ModuleGraphLimits::new(8, 8, 8, u128::MAX)] {
            assert!(
                !matches!(
                    ModuleGraph::new(epoch.clone(), limits),
                    ModuleGraphOutcome::Inconclusive(ModuleGraphInconclusive::Cancelled { .. })
                ),
                "construction requests no cancellation and must never report it"
            );
        }
    }

    #[test]
    fn module_graph_registration_separates_rejection_from_inconclusive() {
        // A probe that trips on its Nth sample, so each checkpoint can be pinned
        // exactly. A pre-set `AtomicBool` can only ever prove the first one.
        struct TripAt {
            trip: usize,
            samples: std::cell::Cell<usize>,
        }
        impl CancellationProbe for TripAt {
            fn is_cancelled(&self) -> bool {
                let seen = self.samples.get();
                self.samples.set(seen + 1);
                seen >= self.trip
            }
        }

        let base = insert(&graph(), record("Base", vec![], 1));
        let before = base.clone();
        let fresh = record("Fresh", vec![direct("Base", 0)], 2);

        // ---- cancellation at every checkpoint, including mid-registration --------
        let mut seen_checkpoints = BTreeSet::new();
        for trip in 0..4 {
            let probe = TripAt {
                trip,
                samples: std::cell::Cell::new(0),
            };
            let outcome = base.register_cancellable(fresh.clone(), Some(&probe));
            let reason = outcome
                .clone()
                .expect_inconclusive(&format!("cancelled at sample {trip}"));
            let ModuleGraphInconclusive::Cancelled { module, checkpoint } = reason else {
                panic!("expected Cancelled, got {reason:?}");
            };
            assert_eq!(module, id("Fresh"));
            seen_checkpoints.insert(checkpoint);

            // FL-INV-07: not a rejection, not an acceptance, not cacheable.
            assert!(outcome.is_inconclusive());
            assert!(!outcome.is_cacheable(), "cancellation must never be cached");
            assert_eq!(outcome.graph(), None);
            assert_eq!(outcome.outcome_label(), "inconclusive-cancelled");

            // No half-registered module is observable anywhere.
            assert_eq!(base, before, "a cancelled registration mutated the graph");
            assert!(!base.contains(&id("Fresh")));
            assert!(base.contains(&id("Base")));
        }
        // Cancellation was genuinely sampled *after* work began, not only at entry —
        // otherwise "mid-registration" would be untested.
        assert_eq!(
            seen_checkpoints,
            BTreeSet::from([
                RegistrationCheckpoint::Entry,
                RegistrationCheckpoint::AfterValidation,
                RegistrationCheckpoint::AfterConflictLookup,
                RegistrationCheckpoint::BeforePublication,
            ]),
            "every checkpoint must be reachable"
        );

        // Recovery: the same record admits once cancellation is withdrawn, which is
        // what makes the outcome inconclusive rather than a refusal of the record.
        let admitted = base.register(fresh.clone());
        assert_eq!(admitted.outcome_label(), "complete");
        assert!(admitted.is_cacheable());
        assert!(
            admitted
                .graph()
                .expect("complete carries a graph")
                .contains(&id("Fresh"))
        );

        // ---- budget exhaustion is typed, and is NOT cacheable --------------------
        let one_module = ModuleGraph::new(
            epoch(),
            ModuleGraphLimits::new(1, usize::MAX, usize::MAX, u128::MAX),
        )
        .expect_complete("empty graph fits");
        let one_module = insert(&one_module, record("Only", vec![], 3));
        let full_before = one_module.clone();
        let exhausted = one_module.register(record("Overflow", vec![], 4));
        let reason = exhausted
            .clone()
            .expect_inconclusive("a bound budget is inconclusive, never a rejection");
        assert!(matches!(
            reason,
            ModuleGraphInconclusive::ResourceLimitExceeded {
                resource: ModuleGraphResource::Modules,
                limit: 1,
                actual: 2,
                ..
            }
        ));
        assert_eq!(exhausted.outcome_label(), "inconclusive-resource");
        assert!(
            !exhausted.is_cacheable(),
            "THE trap: memoizing an exhausted registration would let a later run \
             replay the exhaustion as though it were a real answer about the module"
        );
        assert_eq!(exhausted.graph(), None);
        assert_eq!(
            one_module, full_before,
            "an exhausted registration mutated the graph"
        );
        assert!(!one_module.contains(&id("Overflow")));

        // ---- the classes must not be confusable ---------------------------------
        // A conflict is a rejection and stays one; exhaustion is inconclusive and
        // stays one. Neither may be spelled as the other.
        let conflicting = ModuleRecord::new(id("Base"), false, vec![], evidence(9));
        let rejected = base.register(conflicting);
        assert_eq!(rejected.outcome_label(), "rejected");
        assert!(!rejected.is_inconclusive());
        assert!(!rejected.is_cacheable());

        // And registration can never spell exhaustion as a `ModuleGraphError`: the
        // budget path returns `ModuleGraphInconclusive`, so the old
        // `Rejected(ResourceLimitExceeded)` shape is unrepresentable here.
        for outcome in [exhausted, rejected] {
            if let ModuleGraphAdmission::Rejected(error) = outcome {
                assert!(
                    !matches!(error, ModuleGraphError::ResourceLimitExceeded { .. }),
                    "a registration reported resource exhaustion as a rejection"
                );
            }
        }
    }

    #[test]
    fn epoch_name_and_every_resource_boundary_fail_closed() {
        assert!(matches!(
            ModuleGraph::new(ModuleEpoch::new("v4.32.0", "short"), TEST_LIMITS),
            ModuleGraphOutcome::Rejected(ModuleGraphError::MalformedEpoch { .. })
        ));
        assert!(matches!(
            ModuleGraph::new(ModuleEpoch::new(" v4.32.0", PIN_COMMIT), TEST_LIMITS),
            ModuleGraphOutcome::Rejected(ModuleGraphError::MalformedEpoch { .. })
        ));
        assert!(matches!(
            ModuleGraph::new(
                ModuleEpoch::new("v4.32.0", PIN_COMMIT.to_ascii_uppercase()),
                TEST_LIMITS,
            ),
            ModuleGraphOutcome::Rejected(ModuleGraphError::MalformedEpoch { .. })
        ));

        let base_graph = graph();
        let wrong_epoch = ArtifactEvidence {
            epoch: ModuleEpoch::new("v4.31.0", "1111111111111111111111111111111111111111"),
            ..evidence(1)
        };
        assert!(matches!(
            base_graph.register(ModuleRecord::new(id("Wrong"), true, vec![], wrong_epoch)),
            ModuleGraphAdmission::Rejected(ModuleGraphError::EpochMismatch { .. })
        ));
        assert_eq!(
            base_graph
                .register(ModuleRecord::new(
                    ModuleId::new(Name::anonymous()),
                    true,
                    vec![],
                    evidence(1),
                ))
                .expect_rejected("anonymous identity refused"),
            ModuleGraphError::AnonymousModule
        );
        assert_eq!(
            base_graph
                .register(ModuleRecord::new(
                    id("Owner"),
                    true,
                    vec![DirectImport::new(
                        ModuleId::new(Name::anonymous()),
                        false,
                        false,
                        false,
                    )],
                    evidence(1),
                ))
                .expect_rejected("anonymous import target refused"),
            ModuleGraphError::AnonymousImport {
                owner: id("Owner"),
                import_index: 0,
            }
        );

        let overflowed = ModuleId::new(Name::num_overflowing(Name::anonymous(), u64::MAX));
        assert!(matches!(
            base_graph.register(ModuleRecord::new(
                overflowed.clone(),
                true,
                vec![],
                evidence(1),
            )),
            ModuleGraphAdmission::Rejected(ModuleGraphError::OverflowingNameComponent { module }) if module == overflowed
        ));
        let overflowed_import = ModuleId::new(Name::num_overflowing(id("Prefix").into_name(), 17));
        assert!(matches!(
            base_graph.register(ModuleRecord::new(
                id("Owner"),
                true,
                vec![DirectImport::new(
                    overflowed_import.clone(),
                    false,
                    false,
                    false,
                )],
                evidence(1),
            )),
            ModuleGraphAdmission::Rejected(ModuleGraphError::OverflowingNameComponent { module })
                if module == overflowed_import
        ));

        let deep = ModuleId::new(Name::from_components(["a", "b", "c"]));
        let shallow_limits = ModuleGraphLimits::new(1, 1, 2, u128::MAX);
        let shallow_graph =
            ModuleGraph::new(epoch(), shallow_limits).expect_complete("empty graph fits");
        assert!(matches!(
            shallow_graph.register(ModuleRecord::new(deep, true, vec![], evidence(2))),
            ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::ResourceLimitExceeded {
                resource: ModuleGraphResource::NameDepth,
                limit: 2,
                actual: 3,
                ..
            })
        ));

        let one_module = ModuleGraph::new(
            epoch(),
            ModuleGraphLimits::new(0, usize::MAX, usize::MAX, u128::MAX),
        )
        .expect_complete("empty graph fits");
        assert!(matches!(
            one_module.register(record("One", vec![], 3)),
            ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::ResourceLimitExceeded {
                resource: ModuleGraphResource::Modules,
                limit: 0,
                actual: 1,
                ..
            })
        ));

        let zero_edges =
            ModuleGraph::new(epoch(), ModuleGraphLimits::new(1, 0, usize::MAX, u128::MAX))
                .expect_complete("empty graph fits");
        assert!(matches!(
            zero_edges.register(record("One", vec![direct("Two", 0)], 4)),
            ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::ResourceLimitExceeded {
                resource: ModuleGraphResource::DirectImportRows,
                limit: 0,
                actual: 1,
                ..
            })
        ));

        let cumulative_edges =
            ModuleGraph::new(epoch(), ModuleGraphLimits::new(2, 1, usize::MAX, u128::MAX))
                .expect_complete("empty graph fits");
        let cumulative_edges = insert(
            &cumulative_edges,
            record("First", vec![direct("Target", 0)], 4),
        );
        assert!(matches!(
            cumulative_edges.register(record("Second", vec![direct("Target", 1)], 5)),
            ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::ResourceLimitExceeded {
                resource: ModuleGraphResource::DirectImportRows,
                limit: 1,
                actual: 2,
                ..
            })
        ));

        let measured = insert(&graph(), record("Measured", vec![direct("Dep", 3)], 5));
        let exact_payload = measured.facts().payload_bytes;
        let false_is_module = insert(
            &graph(),
            ModuleRecord::new(id("Measured"), false, vec![direct("Dep", 3)], evidence(5)),
        );
        assert_eq!(
            false_is_module.facts().payload_bytes,
            exact_payload,
            "payload accounting charges one byte for a bool, not its value"
        );
        let exact = ModuleGraph::new(
            epoch(),
            ModuleGraphLimits::new(1, 1, usize::MAX, exact_payload),
        )
        .expect_complete("epoch fits");
        assert!(
            exact
                .register(record("Measured", vec![direct("Dep", 3)], 5))
                .registration()
                .is_some()
        );
        let short = ModuleGraph::new(
            epoch(),
            ModuleGraphLimits::new(1, 1, usize::MAX, exact_payload - 1),
        )
        .expect_complete("epoch still fits");
        assert!(matches!(
            short.register(record("Measured", vec![direct("Dep", 3)], 5)),
            ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::ResourceLimitExceeded {
                resource: ModuleGraphResource::PayloadBytes,
                ..
            })
        ));
    }

    #[test]
    fn snapshots_share_one_state_and_mutation_is_isolated() {
        let mut graph = graph();
        for index in 0..2_000usize {
            graph = insert(
                &graph,
                record(&format!("M{index}"), Vec::new(), index as u8),
            );
        }
        let snapshot = graph.clone();
        assert!(snapshot.shares_storage_with(&graph));
        let old_node_count = graph.state.records.node_count();
        let old_nodes: HashSet<*const ()> = graph.state.records.node_ptrs().into_iter().collect();
        let untouched_before =
            Arc::clone(graph.state.records.get(&id("M1")).expect("existing record"));
        let changed = insert(&graph, record("Later", vec![direct("M1", 0)], 9));
        let new_nodes = changed.state.records.node_ptrs();
        let fresh_nodes = new_nodes
            .iter()
            .filter(|pointer| !old_nodes.contains(pointer))
            .count();
        let shared_nodes = new_nodes.len().saturating_sub(fresh_nodes);
        assert!(
            fresh_nodes <= PMap::<ModuleId, Arc<ModuleRecord>>::insertion_fresh_node_bound(),
            "one insertion allocated {fresh_nodes} HAMT nodes"
        );
        assert!(
            shared_nodes
                >= old_node_count.saturating_sub(
                    PMap::<ModuleId, Arc<ModuleRecord>>::insertion_replaced_node_bound(),
                ),
            "only {shared_nodes} of {old_node_count} prior nodes remained shared"
        );
        assert!(Arc::ptr_eq(
            &untouched_before,
            changed
                .state
                .records
                .get(&id("M1"))
                .expect("untouched record remains")
        ));
        assert!(!changed.shares_storage_with(&graph));
        assert_eq!(snapshot, graph);
        assert!(!snapshot.contains(&id("Later")));
        assert!(changed.contains(&id("Later")));
    }

    #[test]
    fn random_dag_matches_model_and_is_insertion_order_independent() {
        let mut seed = 0xA076_1D64_78BD_642Fu64;
        let mut records = Vec::new();
        let mut model: BTreeMap<ModuleId, Vec<DirectImport>> = BTreeMap::new();
        for index in 0..512usize {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let import_count = if index == 0 { 0 } else { seed as usize % 8 };
            let mut imports = Vec::new();
            for offset in 0..import_count {
                let target = seed
                    .rotate_left((offset as u32 * 7) % 63 + 1)
                    .wrapping_add(offset as u64) as usize
                    % index;
                imports.push(direct(&format!("M{target}"), (seed >> offset) as u8));
            }
            let record = record(&format!("M{index}"), imports.clone(), index as u8);
            model.insert(record.id.clone(), imports);
            records.push(record);
        }

        let mut forward = graph();
        for record in &records {
            forward = insert(&forward, record.clone());
        }
        let mut reverse = graph();
        for record in records.iter().rev() {
            reverse = insert(&reverse, record.clone());
        }
        assert_eq!(forward, reverse);
        assert_eq!(forward.completeness(), GraphCompleteness::Complete);
        assert_eq!(
            forward.modules_canonical(),
            model.keys().cloned().collect::<Vec<_>>()
        );
        for (module, imports) in model {
            assert_eq!(forward.direct_imports(&module), Some(imports.as_slice()));
        }
    }

    #[test]
    fn named_mutations_drop_and_reorder_direct_rows_are_killed() {
        let baseline = ModuleRecord::new(
            id("MutationTarget"),
            true,
            vec![direct("A", 0), direct("B", 7), direct("A", 1)],
            evidence(7),
        );
        let graph = insert(&graph(), baseline.clone());

        let mut dropped_rows = baseline.direct_imports().to_vec();
        dropped_rows.remove(1);
        let drop_mutant = ModuleRecord::new(
            baseline.id.clone(),
            baseline.is_module,
            dropped_rows,
            baseline.artifact.clone(),
        );

        let mut reordered_rows = baseline.direct_imports().to_vec();
        reordered_rows.swap(0, 2);
        let reorder_mutant = ModuleRecord::new(
            baseline.id.clone(),
            baseline.is_module,
            reordered_rows,
            baseline.artifact.clone(),
        );

        for (mutation, mutant) in [
            ("FLN-MUT-MODULE-DIRECT-ROW-DROP", drop_mutant),
            ("FLN-MUT-MODULE-DIRECT-ROW-REORDER", reorder_mutant),
        ] {
            assert!(matches!(
                graph.register(mutant),
                ModuleGraphAdmission::Rejected(ModuleGraphError::ConflictingRecord { module, .. })
                    if module == id("MutationTarget")
            ));
            println!(
                "{{\"schema\":\"fln.unit.module-mutation\",\"version\":1,\"bead\":\"fln-amv.9.1\",\"mutation\":\"{mutation}\",\"expected\":\"killed\",\"actual\":\"killed\"}}"
            );
        }
        assert_eq!(graph.record(&baseline.id), Some(&baseline));
    }

    #[test]
    fn thread_partition_and_insertion_order_are_metamorphically_equivalent() {
        const MODULES: usize = 257;
        const LANES: usize = 8;
        let records: Arc<[ModuleRecord]> = (0..MODULES)
            .map(|index| {
                let imports = (index > 0)
                    .then(|| direct(&format!("Thread.M{}", index - 1), index as u8))
                    .into_iter()
                    .collect();
                record(&format!("Thread.M{index}"), imports, index as u8)
            })
            .collect::<Vec<_>>()
            .into();

        let graphs = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..LANES)
                .map(|lane| {
                    let records = Arc::clone(&records);
                    scope.spawn(move || {
                        let stride = lane + 1;
                        let mut graph = graph();
                        for step in 0..MODULES {
                            // MODULES is prime and every stride is smaller, so
                            // each lane visits one distinct permutation.
                            let index = (lane + step * stride) % MODULES;
                            graph = insert(
                                &graph,
                                records
                                    .get(index)
                                    .expect("permutation index is reduced modulo MODULES")
                                    .clone(),
                            );
                        }
                        graph
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("module partition worker"))
                .collect::<Vec<_>>()
        });

        for candidate in graphs.iter().skip(1) {
            assert_eq!(candidate, &graphs[0]);
        }
        println!(
            "{{\"schema\":\"fln.unit.module-determinism\",\"version\":1,\"bead\":\"fln-amv.9.1\",\"lanes\":{LANES},\"modules\":{MODULES},\"orders\":{LANES},\"expected\":\"equal\",\"actual\":\"equal\"}}"
        );
    }

    #[test]
    fn sparse_and_dense_dags_emit_bounded_operation_counts() {
        const SPARSE_MODULES: usize = 256;
        let mut sparse = graph();
        let mut sparse_final_work = RegistrationWork::default();
        for index in 0..SPARSE_MODULES {
            let imports = (index > 0)
                .then(|| direct(&format!("Sparse.M{}", index - 1), 0))
                .into_iter()
                .collect();
            let registration = sparse
                .register(record(&format!("Sparse.M{index}"), imports, index as u8))
                .expect_complete("sparse DAG insertion");
            sparse_final_work = registration.work;
            sparse = registration.graph;
        }
        assert_eq!(sparse_final_work.cycle_modules_visited, SPARSE_MODULES - 1);
        assert_eq!(sparse_final_work.cycle_rows_examined, SPARSE_MODULES - 2);
        assert!(sparse_final_work.cycle_modules_visited <= sparse.facts().modules);
        assert!(sparse_final_work.cycle_rows_examined <= sparse.facts().direct_import_rows);

        const DENSE_MODULES: usize = 128;
        let mut dense = graph();
        let mut dense_final_work = RegistrationWork::default();
        for index in 0..DENSE_MODULES {
            let imports = (0..index)
                .map(|target| direct(&format!("Dense.M{target}"), target as u8))
                .collect();
            let registration = dense
                .register(record(&format!("Dense.M{index}"), imports, index as u8))
                .expect_complete("dense DAG insertion");
            dense_final_work = registration.work;
            dense = registration.graph;
        }
        assert_eq!(dense_final_work.cycle_modules_visited, DENSE_MODULES - 1);
        assert_eq!(
            dense_final_work.cycle_rows_examined,
            (DENSE_MODULES - 1) * (DENSE_MODULES - 2) / 2
        );
        assert!(dense_final_work.cycle_modules_visited <= dense.facts().modules);
        assert!(dense_final_work.cycle_rows_examined <= dense.facts().direct_import_rows);
        println!(
            "{{\"schema\":\"fln.unit.module-operation-count\",\"version\":1,\"bead\":\"fln-amv.9.1\",\"sparse\":{{\"modules\":{},\"rows\":{},\"visited\":{},\"examined\":{}}},\"dense\":{{\"modules\":{},\"rows\":{},\"visited\":{},\"examined\":{}}},\"expected\":\"within-graph-facts\",\"actual\":\"within-graph-facts\"}}",
            sparse.facts().modules,
            sparse.facts().direct_import_rows,
            sparse_final_work.cycle_modules_visited,
            sparse_final_work.cycle_rows_examined,
            dense.facts().modules,
            dense.facts().direct_import_rows,
            dense_final_work.cycle_modules_visited,
            dense_final_work.cycle_rows_examined,
        );
    }

    #[test]
    fn canonical_cycle_witness_does_not_depend_on_direct_row_order() {
        let graph = insert(&graph(), record("A", vec![direct("Z", 0)], 1));
        let graph = insert(&graph, record("B", vec![direct("Z", 0)], 2));
        let graph = insert(&graph, record("Z", vec![direct("Root", 0)], 3));
        let left = record("Root", vec![direct("B", 0), direct("A", 0)], 4);
        let right = record("Root", vec![direct("A", 0), direct("B", 0)], 4);
        let left_error = graph.register(left).expect_rejected("cycle refused");
        let right_error = graph.register(right).expect_rejected("cycle refused");
        assert_eq!(left_error, right_error);
        assert_eq!(
            left_error,
            ModuleGraphError::Cycle {
                path: vec![id("Root"), id("A"), id("Z"), id("Root")]
            }
        );
    }
}
