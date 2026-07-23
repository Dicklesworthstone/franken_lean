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
}

/// Immutable module DAG. Clone is one bounded `Arc` increment.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGraph {
    epoch: ModuleEpoch,
    limits: ModuleGraphLimits,
    state: Arc<ModuleGraphState>,
}

impl ModuleGraph {
    pub fn new(epoch: ModuleEpoch, limits: ModuleGraphLimits) -> Result<Self, ModuleGraphError> {
        if !epoch.is_well_formed() {
            return Err(ModuleGraphError::MalformedEpoch {
                tag: Arc::clone(&epoch.tag),
                commit: Arc::clone(&epoch.commit),
            });
        }
        let payload_bytes = epoch.payload_bytes();
        if payload_bytes > limits.max_payload_bytes {
            return Err(ModuleGraphError::ResourceLimitExceeded {
                module: None,
                resource: ModuleGraphResource::PayloadBytes,
                limit: limits.max_payload_bytes,
                actual: payload_bytes,
            });
        }
        Ok(Self {
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
    pub fn register(&self, record: ModuleRecord) -> Result<Registration, ModuleGraphError> {
        let record_facts = self.validate_record(&record)?;
        let direct_rows_validated = record.direct_imports().len();
        if let Some(existing) = self.state.records.get(&record.id) {
            if existing.as_ref() == &record {
                return Ok(Registration {
                    graph: self.clone(),
                    disposition: RegistrationDisposition::Idempotent,
                    work: RegistrationWork {
                        name_components_validated: record_facts.name_components,
                        direct_rows_validated,
                        ..RegistrationWork::default()
                    },
                });
            }
            let differing_fields = differing_record_fields(existing, &record);
            debug_assert!(!differing_fields.is_empty());
            return Err(ModuleGraphError::ConflictingRecord {
                module: record.id,
                differing_fields,
                existing_artifact: Box::new(existing.artifact.clone()),
                incoming_artifact: Box::new(record.artifact),
            });
        }

        let modules = self.state.facts.modules.saturating_add(1);
        enforce_limit(
            Some(&record.id),
            ModuleGraphResource::Modules,
            self.limits.max_modules as u128,
            modules as u128,
        )?;
        let direct_import_rows = self
            .state
            .facts
            .direct_import_rows
            .saturating_add(record.direct_imports().len());
        enforce_limit(
            Some(&record.id),
            ModuleGraphResource::DirectImportRows,
            self.limits.max_edges as u128,
            direct_import_rows as u128,
        )?;
        let payload_bytes = self
            .state
            .facts
            .payload_bytes
            .saturating_add(record_facts.payload_bytes);
        enforce_limit(
            Some(&record.id),
            ModuleGraphResource::PayloadBytes,
            self.limits.max_payload_bytes,
            payload_bytes,
        )?;

        let module = record.id.clone();
        let records = self.state.records.insert(module.clone(), Arc::new(record));
        let cycle_scan = cycle_through(&records, &module);
        if let Some(path) = cycle_scan.path {
            return Err(ModuleGraphError::Cycle { path });
        }

        Ok(Registration {
            graph: Self {
                epoch: self.epoch.clone(),
                limits: self.limits,
                state: Arc::new(ModuleGraphState {
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
                }),
            },
            disposition: RegistrationDisposition::Inserted,
            work: RegistrationWork {
                name_components_validated: record_facts.name_components,
                direct_rows_validated,
                cycle_modules_visited: cycle_scan.modules_visited,
                cycle_rows_examined: cycle_scan.rows_examined,
            },
        })
    }

    /// Pointer-identity probe for snapshot/sharing evidence.
    pub fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.state, &other.state)
    }

    fn validate_record(&self, record: &ModuleRecord) -> Result<RecordFacts, ModuleGraphError> {
        if record.id.name().is_anonymous() {
            return Err(ModuleGraphError::AnonymousModule);
        }
        if record.artifact.epoch != self.epoch {
            return Err(ModuleGraphError::EpochMismatch {
                module: record.id.clone(),
                expected: self.epoch.clone(),
                actual: record.artifact.epoch.clone(),
            });
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
                return Err(ModuleGraphError::AnonymousImport {
                    owner: record.id.clone(),
                    import_index: position - 1,
                });
            }
            let stats = name_stats(module.name());
            if stats.overflowing_component {
                return Err(ModuleGraphError::OverflowingNameComponent {
                    module: module.clone(),
                });
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
                return Err(ModuleGraphError::SelfImport {
                    module: record.id.clone(),
                    import_index,
                });
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

fn enforce_limit(
    module: Option<&ModuleId>,
    resource: ModuleGraphResource,
    limit: u128,
    actual: u128,
) -> Result<(), ModuleGraphError> {
    if actual > limit {
        return Err(ModuleGraphError::ResourceLimitExceeded {
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
        ModuleGraph::new(epoch(), TEST_LIMITS).expect("valid pinned graph")
    }

    fn insert(graph: &ModuleGraph, record: ModuleRecord) -> ModuleGraph {
        let registration = graph.register(record).expect("record inserts");
        assert_eq!(registration.disposition, RegistrationDisposition::Inserted);
        registration.graph
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
                            .expect("field combination registers exactly");
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
        let inserted = base.register(value.clone()).expect("first registration");
        let repeated = inserted
            .graph
            .register(value.clone())
            .expect("exact registration is idempotent");
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
                .expect_err("changed record must conflict");
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
                .expect_err("self edge refused"),
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
                .expect_err("late cycle refused"),
            ModuleGraphError::Cycle {
                path: vec![id("C"), id("A"), id("B"), id("C")]
            }
        );
        assert_eq!(graph, before);
        assert!(!graph.contains(&id("C")));
    }

    #[test]
    fn epoch_name_and_every_resource_boundary_fail_closed() {
        assert!(matches!(
            ModuleGraph::new(ModuleEpoch::new("v4.32.0", "short"), TEST_LIMITS),
            Err(ModuleGraphError::MalformedEpoch { .. })
        ));
        assert!(matches!(
            ModuleGraph::new(ModuleEpoch::new(" v4.32.0", PIN_COMMIT), TEST_LIMITS),
            Err(ModuleGraphError::MalformedEpoch { .. })
        ));
        assert!(matches!(
            ModuleGraph::new(
                ModuleEpoch::new("v4.32.0", PIN_COMMIT.to_ascii_uppercase()),
                TEST_LIMITS,
            ),
            Err(ModuleGraphError::MalformedEpoch { .. })
        ));

        let base_graph = graph();
        let wrong_epoch = ArtifactEvidence {
            epoch: ModuleEpoch::new("v4.31.0", "1111111111111111111111111111111111111111"),
            ..evidence(1)
        };
        assert!(matches!(
            base_graph.register(ModuleRecord::new(id("Wrong"), true, vec![], wrong_epoch)),
            Err(ModuleGraphError::EpochMismatch { .. })
        ));
        assert_eq!(
            base_graph
                .register(ModuleRecord::new(
                    ModuleId::new(Name::anonymous()),
                    true,
                    vec![],
                    evidence(1),
                ))
                .expect_err("anonymous identity refused"),
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
                .expect_err("anonymous import target refused"),
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
            Err(ModuleGraphError::OverflowingNameComponent { module }) if module == overflowed
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
            Err(ModuleGraphError::OverflowingNameComponent { module })
                if module == overflowed_import
        ));

        let deep = ModuleId::new(Name::from_components(["a", "b", "c"]));
        let shallow_limits = ModuleGraphLimits::new(1, 1, 2, u128::MAX);
        let shallow_graph = ModuleGraph::new(epoch(), shallow_limits).expect("empty graph fits");
        assert!(matches!(
            shallow_graph.register(ModuleRecord::new(deep, true, vec![], evidence(2))),
            Err(ModuleGraphError::ResourceLimitExceeded {
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
        .expect("empty graph fits");
        assert!(matches!(
            one_module.register(record("One", vec![], 3)),
            Err(ModuleGraphError::ResourceLimitExceeded {
                resource: ModuleGraphResource::Modules,
                limit: 0,
                actual: 1,
                ..
            })
        ));

        let zero_edges =
            ModuleGraph::new(epoch(), ModuleGraphLimits::new(1, 0, usize::MAX, u128::MAX))
                .expect("empty graph fits");
        assert!(matches!(
            zero_edges.register(record("One", vec![direct("Two", 0)], 4)),
            Err(ModuleGraphError::ResourceLimitExceeded {
                resource: ModuleGraphResource::DirectImportRows,
                limit: 0,
                actual: 1,
                ..
            })
        ));

        let cumulative_edges =
            ModuleGraph::new(epoch(), ModuleGraphLimits::new(2, 1, usize::MAX, u128::MAX))
                .expect("empty graph fits");
        let cumulative_edges = insert(
            &cumulative_edges,
            record("First", vec![direct("Target", 0)], 4),
        );
        assert!(matches!(
            cumulative_edges.register(record("Second", vec![direct("Target", 1)], 5)),
            Err(ModuleGraphError::ResourceLimitExceeded {
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
        .expect("epoch fits");
        assert!(
            exact
                .register(record("Measured", vec![direct("Dep", 3)], 5))
                .is_ok()
        );
        let short = ModuleGraph::new(
            epoch(),
            ModuleGraphLimits::new(1, 1, usize::MAX, exact_payload - 1),
        )
        .expect("epoch still fits");
        assert!(matches!(
            short.register(record("Measured", vec![direct("Dep", 3)], 5)),
            Err(ModuleGraphError::ResourceLimitExceeded {
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
                Err(ModuleGraphError::ConflictingRecord { module, .. })
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
                .expect("sparse DAG insertion");
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
                .expect("dense DAG insertion");
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
        let left_error = graph.register(left).expect_err("cycle refused");
        let right_error = graph.register(right).expect_err("cycle refused");
        assert_eq!(left_error, right_error);
        assert_eq!(
            left_error,
            ModuleGraphError::Cycle {
                path: vec![id("Root"), id("A"), id("Z"), id("Root")]
            }
        );
    }
}
