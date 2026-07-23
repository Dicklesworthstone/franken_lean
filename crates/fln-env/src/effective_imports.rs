//! Pinned Lean v4.32.0 effective-import fixed point.
//!
//! This is the environment-side, artifact-independent form of
//! `Lean.importModulesCore` (`Lean/Environment.lean:2057-2187`). It preserves
//! Reference direct-row order, recursive postorder discovery, monotone upgrades,
//! and the deliberately separate data, transitive-IR, IR-load, and phase facts.
//! Artifact loading is supplied later by `fln-amv.9.4`; missing graph records are
//! therefore honest partial results, never fabricated leaves.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::modules::{DirectImport, ModuleGraph, ModuleId};

/// The three Reference `.olean` loading profiles.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GlobalOLeanLevel {
    Exported,
    Server,
    Private,
}

impl GlobalOLeanLevel {
    fn is_module_mode(self) -> bool {
        self != Self::Private
    }

    fn root_is_exported(self) -> bool {
        self != Self::Private
    }

    fn globally_requests_ir(self) -> bool {
        self != Self::Exported
    }
}

/// Reference IR availability phases and their exact upgrade join.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IrPhases {
    Runtime,
    Comptime,
    All,
}

impl IrPhases {
    fn join(self, other: Self) -> Self {
        if self == other { self } else { Self::All }
    }
}

/// Data-visibility lattice. `Public` and `PrivateAll` are incomparable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ImportExposure {
    None,
    Private,
    PrivateAll,
    Public,
    All,
}

impl ImportExposure {
    pub fn join(self, other: Self) -> Self {
        let (left_data, left_exported, left_all) = self.components();
        let (right_data, right_exported, right_all) = other.components();
        Self::from_components(
            left_data || right_data,
            left_exported || right_exported,
            left_all || right_all,
        )
    }

    fn components(self) -> (bool, bool, bool) {
        match self {
            Self::None => (false, false, false),
            Self::Private => (true, false, false),
            Self::PrivateAll => (true, false, true),
            Self::Public => (true, true, false),
            Self::All => (true, true, true),
        }
    }

    fn from_components(has_data: bool, is_exported: bool, import_all: bool) -> Self {
        if !has_data {
            Self::None
        } else {
            match (is_exported, import_all) {
                (false, false) => Self::Private,
                (false, true) => Self::PrivateAll,
                (true, false) => Self::Public,
                (true, true) => Self::All,
            }
        }
    }
}

/// One exact edge in an explanation. `source = None` denotes the root request.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImportWitnessStep {
    pub source: Option<ModuleId>,
    pub direct_row_index: usize,
    pub import: DirectImport,
}

/// A root-to-module path; multiple paths may be required to justify a joined
/// conjunction such as `hasData(A) && importAll(A)`.
#[derive(Debug, Clone, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct ImportWitnessPath {
    pub steps: Arc<[ImportWitnessStep]>,
}

impl ImportWitnessPath {
    fn appended(&self, step: &ImportWitnessStep) -> Self {
        let mut steps = Vec::with_capacity(self.steps.len().saturating_add(1));
        steps.extend(self.steps.iter().cloned());
        steps.push(step.clone());
        Self {
            steps: steps.into(),
        }
    }
}

/// Minimal deterministic path set explaining one monotone component.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ComponentWitness {
    pub paths: Arc<[ImportWitnessPath]>,
}

impl ComponentWitness {
    fn root() -> Self {
        Self {
            paths: vec![ImportWitnessPath::default()].into(),
        }
    }

    fn append(&self, step: &ImportWitnessStep, facts: &mut ClosureFacts) -> Self {
        let mut paths: Vec<_> = self
            .paths
            .iter()
            .map(|path| {
                let path = path.appended(step);
                facts.witness_steps_materialized = facts
                    .witness_steps_materialized
                    .saturating_add(path.steps.len());
                path
            })
            .collect();
        paths.sort();
        paths.dedup();
        Self {
            paths: paths.into(),
        }
    }

    fn conjoin(
        left: &Self,
        right: &Self,
        step: &ImportWitnessStep,
        facts: &mut ClosureFacts,
    ) -> Self {
        let mut paths = Vec::with_capacity(left.paths.len().saturating_add(right.paths.len()));
        for path in left.paths.iter().chain(right.paths.iter()) {
            let path = path.appended(step);
            facts.witness_steps_materialized = facts
                .witness_steps_materialized
                .saturating_add(path.steps.len());
            paths.push(path);
        }
        paths.sort();
        paths.dedup();
        Self {
            paths: paths.into(),
        }
    }
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EffectiveImportWitnesses {
    /// The exact row path that first created the Reference `EffectiveImport`,
    /// and therefore owns its retained `is_meta` value.
    pub first_discovery: ImportWitnessPath,
    pub data: Option<ComponentWitness>,
    pub import_all: Option<ComponentWitness>,
    pub exported: Option<ComponentWitness>,
    pub ir_transitive: Option<ComponentWitness>,
    pub ir_runtime: Option<ComponentWitness>,
    pub ir_comptime: Option<ComponentWitness>,
    pub ir_requested: Option<ComponentWitness>,
}

/// Exact effective state for one discovered module.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectiveImportState {
    pub module: ModuleId,
    pub import_all: bool,
    pub is_exported: bool,
    /// Retained from the first-discovery row, exactly as in the Reference.
    pub is_meta: bool,
    pub ir_phases: IrPhases,
    pub has_data: bool,
    pub needs_ir_transitive: bool,
    /// Whether this profile requested an IR artifact. In server mode this may
    /// be true while `ir_phases == Runtime`.
    pub ir_requested: bool,
    pub witnesses: EffectiveImportWitnesses,
}

impl EffectiveImportState {
    pub fn exposure(&self) -> ImportExposure {
        ImportExposure::from_components(self.has_data, self.is_exported, self.import_all)
    }

    fn propagation_context(&self) -> PropagationContext {
        PropagationContext {
            import_all: self.import_all,
            is_exported: self.is_exported,
            needs_data: self.has_data,
            needs_ir_transitive: self.needs_ir_transitive,
            import_all_witness: self.witnesses.import_all.clone(),
            exported_witness: self.witnesses.exported.clone(),
            data_witness: self.witnesses.data.clone(),
            ir_transitive_witness: self.witnesses.ir_transitive.clone(),
            route_witness: first_witness(&self.witnesses),
        }
    }
}

fn first_witness(witnesses: &EffectiveImportWitnesses) -> ComponentWitness {
    witnesses
        .data
        .as_ref()
        .or(witnesses.ir_transitive.as_ref())
        .or(witnesses.import_all.as_ref())
        .or(witnesses.exported.as_ref())
        .or(witnesses.ir_requested.as_ref())
        .cloned()
        .unwrap_or_else(ComponentWitness::root)
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum ImportSource {
    Root,
    Module(ModuleId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReverseImportRow {
    pub source: ImportSource,
    pub direct_row_index: usize,
    pub import: DirectImport,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MissingModuleFinding {
    pub module: ModuleId,
    pub witness: ImportWitnessPath,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClosureResource {
    RootImportRows,
    PendingItems,
    WorkItems,
    StateUpgrades,
    WitnessSteps,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InconclusiveReason {
    Cancelled {
        at_work_item: usize,
    },
    ResourceLimitExceeded {
        resource: ClosureResource,
        limit: usize,
        actual: usize,
        module: Option<ModuleId>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidImportRequest {
    AnonymousRootImport {
        direct_row_index: usize,
    },
    OverflowingRootModule {
        module: ModuleId,
        direct_row_index: usize,
    },
    NonModuleDirectImport {
        module: ModuleId,
        direct_row_index: usize,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WitnessComponent {
    Data,
    ImportAll,
    Exported,
    IrTransitive,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosureInternalFault {
    MissingComponentWitness {
        component: WitnessComponent,
        source: ImportSource,
        direct_row_index: usize,
        target: ModuleId,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClosureStatus {
    Complete,
    Incomplete { missing: Vec<MissingModuleFinding> },
    Inconclusive { reason: InconclusiveReason },
    Invalid { reason: InvalidImportRequest },
    InternalFault { fault: ClosureInternalFault },
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ClosureFacts {
    pub work_items: usize,
    pub direct_rows_examined: usize,
    pub first_discoveries: usize,
    pub state_upgrades: usize,
    pub closure_replays: usize,
    pub maximum_pending_items: usize,
    pub witness_steps_materialized: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ClosureLimits {
    pub max_root_import_rows: usize,
    pub max_pending_items: usize,
    pub max_work_items: usize,
    pub max_state_upgrades: usize,
    pub max_witness_steps: usize,
}

impl Default for ClosureLimits {
    fn default() -> Self {
        Self {
            max_root_import_rows: 1_000_000,
            max_pending_items: 20_000_000,
            max_work_items: 100_000_000,
            max_state_upgrades: 8_000_000,
            max_witness_steps: 100_000_000,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectiveImportRequest {
    pub direct_imports: Arc<[DirectImport]>,
    pub global_level: GlobalOLeanLevel,
    /// Explicit `importModulesCore` root override. [`Self::new`] uses the
    /// Reference default `global_level < private`.
    pub root_is_exported: bool,
    pub limits: ClosureLimits,
}

impl EffectiveImportRequest {
    pub fn new(direct_imports: Vec<DirectImport>, global_level: GlobalOLeanLevel) -> Self {
        Self {
            direct_imports: direct_imports.into(),
            global_level,
            root_is_exported: global_level.root_is_exported(),
            limits: ClosureLimits::default(),
        }
    }

    pub fn with_root_is_exported(mut self, root_is_exported: bool) -> Self {
        self.root_is_exported = root_is_exported;
        self
    }
}

/// Queryable fixed-point result. Maps use canonical `Name.cmp` order; the
/// separate discovery array retains Reference postorder.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EffectiveImportClosure {
    states: BTreeMap<ModuleId, EffectiveImportState>,
    discovery: Vec<ModuleId>,
    reverse_rows: BTreeMap<ModuleId, Vec<ReverseImportRow>>,
}

impl EffectiveImportClosure {
    pub fn state(&self, module: &ModuleId) -> Option<&EffectiveImportState> {
        self.states.get(module)
    }

    pub fn canonical_modules(&self) -> Vec<ModuleId> {
        self.states.keys().cloned().collect()
    }

    pub fn reference_discovery(&self) -> &[ModuleId] {
        &self.discovery
    }

    pub fn reverse_rows(&self, module: &ModuleId) -> &[ReverseImportRow] {
        self.reverse_rows.get(module).map_or(&[], Vec::as_slice)
    }

    pub fn canonical_reverse_importers(&self, module: &ModuleId) -> Vec<ImportSource> {
        let mut importers: Vec<_> = self
            .reverse_rows(module)
            .iter()
            .map(|row| row.source.clone())
            .collect();
        importers.sort();
        importers.dedup();
        importers
    }

    pub fn len(&self) -> usize {
        self.states.len()
    }

    pub fn is_empty(&self) -> bool {
        self.states.is_empty()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EffectiveImportReport {
    pub closure: EffectiveImportClosure,
    pub status: ClosureStatus,
    pub facts: ClosureFacts,
}

#[derive(Debug, Clone)]
struct PropagationContext {
    import_all: bool,
    is_exported: bool,
    needs_data: bool,
    needs_ir_transitive: bool,
    import_all_witness: Option<ComponentWitness>,
    exported_witness: Option<ComponentWitness>,
    data_witness: Option<ComponentWitness>,
    ir_transitive_witness: Option<ComponentWitness>,
    route_witness: ComponentWitness,
}

impl PropagationContext {
    fn root(root_is_exported: bool) -> Self {
        Self {
            import_all: true,
            is_exported: root_is_exported,
            needs_data: true,
            needs_ir_transitive: false,
            import_all_witness: Some(ComponentWitness::root()),
            exported_witness: root_is_exported.then(ComponentWitness::root),
            data_witness: Some(ComponentWitness::root()),
            ir_transitive_witness: None,
            route_witness: ComponentWitness::root(),
        }
    }
}

#[derive(Debug)]
struct Candidate {
    state: EffectiveImportState,
    first_path: ImportWitnessPath,
}

#[derive(Debug)]
enum WorkItem {
    Visit {
        source: ImportSource,
        row_index: usize,
        import: DirectImport,
        parent: PropagationContext,
    },
    FinishDiscovery(ModuleId),
}

/// Compute the pinned fixed point. A cancellation flag is sampled at each work
/// item; it is intentionally not part of the deterministic semantic result.
pub fn compute_effective_imports(
    graph: &ModuleGraph,
    request: &EffectiveImportRequest,
    cancellation: Option<&AtomicBool>,
) -> EffectiveImportReport {
    let mut closure = EffectiveImportClosure::default();
    let mut facts = ClosureFacts::default();
    let mut missing = Vec::new();
    let mut seen_reverse_rows = BTreeSet::new();

    if request.direct_imports.len() > request.limits.max_root_import_rows {
        return report_inconclusive(
            closure,
            facts,
            ClosureResource::RootImportRows,
            request.limits.max_root_import_rows,
            request.direct_imports.len(),
            None,
        );
    }

    for (direct_row_index, import) in request.direct_imports.iter().enumerate() {
        if import.module.name().is_anonymous() {
            return EffectiveImportReport {
                closure,
                status: ClosureStatus::Invalid {
                    reason: InvalidImportRequest::AnonymousRootImport { direct_row_index },
                },
                facts,
            };
        }
        if name_has_overflow(import.module.name()) {
            return EffectiveImportReport {
                closure,
                status: ClosureStatus::Invalid {
                    reason: InvalidImportRequest::OverflowingRootModule {
                        module: import.module.clone(),
                        direct_row_index,
                    },
                },
                facts,
            };
        }
    }

    let mut stack = Vec::new();
    let root = PropagationContext::root(request.root_is_exported);
    if let Some(report) = push_rows(
        &mut stack,
        ImportSource::Root,
        &request.direct_imports,
        &root,
        &request.limits,
        &mut facts,
        &closure,
    ) {
        return report;
    }

    while let Some(item) = stack.pop() {
        if cancellation.is_some_and(|flag| flag.load(Ordering::Relaxed)) {
            return EffectiveImportReport {
                closure,
                status: ClosureStatus::Inconclusive {
                    reason: InconclusiveReason::Cancelled {
                        at_work_item: facts.work_items,
                    },
                },
                facts,
            };
        }
        facts.work_items = facts.work_items.saturating_add(1);
        if facts.work_items > request.limits.max_work_items {
            return report_inconclusive(
                closure,
                facts,
                ClosureResource::WorkItems,
                request.limits.max_work_items,
                facts.work_items,
                None,
            );
        }

        match item {
            WorkItem::FinishDiscovery(module) => closure.discovery.push(module),
            WorkItem::Visit {
                source,
                row_index,
                import,
                parent,
            } => {
                facts.direct_rows_examined = facts.direct_rows_examined.saturating_add(1);
                if seen_reverse_rows.insert((source.clone(), row_index, import.module.clone())) {
                    closure
                        .reverse_rows
                        .entry(import.module.clone())
                        .or_default()
                        .push(ReverseImportRow {
                            source: source.clone(),
                            direct_row_index: row_index,
                            import: import.clone(),
                        });
                }

                let candidate = match propagate_candidate(
                    request.global_level,
                    source,
                    row_index,
                    &import,
                    &parent,
                    &mut facts,
                ) {
                    Ok(Some(candidate)) => candidate,
                    Ok(None) => continue,
                    Err(fault) => {
                        return EffectiveImportReport {
                            closure,
                            status: ClosureStatus::InternalFault { fault },
                            facts,
                        };
                    }
                };
                if facts.witness_steps_materialized > request.limits.max_witness_steps {
                    return report_inconclusive(
                        closure,
                        facts,
                        ClosureResource::WitnessSteps,
                        request.limits.max_witness_steps,
                        facts.witness_steps_materialized,
                        Some(import.module),
                    );
                }

                if let Some(existing) = closure.states.get_mut(&import.module) {
                    let mut merged = existing.clone();
                    let upgraded = merge_state(&mut merged, candidate.state);
                    if !upgraded {
                        continue;
                    }
                    let next_upgrade_count = facts.state_upgrades.saturating_add(1);
                    if next_upgrade_count > request.limits.max_state_upgrades {
                        return report_inconclusive(
                            closure,
                            facts,
                            ClosureResource::StateUpgrades,
                            request.limits.max_state_upgrades,
                            next_upgrade_count,
                            Some(import.module),
                        );
                    }
                    facts.state_upgrades = next_upgrade_count;
                    *existing = merged;
                    if let Some(record) = graph.record(&import.module) {
                        facts.closure_replays = facts.closure_replays.saturating_add(1);
                        let context = existing.propagation_context();
                        if let Some(report) = push_rows(
                            &mut stack,
                            ImportSource::Module(import.module.clone()),
                            &record.direct_imports_arc(),
                            &context,
                            &request.limits,
                            &mut facts,
                            &closure,
                        ) {
                            return report;
                        }
                    }
                    continue;
                }

                facts.first_discoveries = facts.first_discoveries.saturating_add(1);
                let Candidate { state, first_path } = candidate;
                let context = state.propagation_context();
                closure.states.insert(import.module.clone(), state);
                if let Some(record) = graph.record(&import.module) {
                    stack.push(WorkItem::FinishDiscovery(import.module.clone()));
                    if let Some(report) = push_rows(
                        &mut stack,
                        ImportSource::Module(import.module.clone()),
                        &record.direct_imports_arc(),
                        &context,
                        &request.limits,
                        &mut facts,
                        &closure,
                    ) {
                        return report;
                    }
                } else {
                    closure.discovery.push(import.module.clone());
                    missing.push(MissingModuleFinding {
                        module: import.module,
                        witness: first_path,
                    });
                }
            }
        }
    }

    if request.global_level.is_module_mode() {
        for (direct_row_index, import) in request.direct_imports.iter().enumerate() {
            if graph
                .record(&import.module)
                .is_some_and(|record| !record.is_module)
            {
                return EffectiveImportReport {
                    closure,
                    status: ClosureStatus::Invalid {
                        reason: InvalidImportRequest::NonModuleDirectImport {
                            module: import.module.clone(),
                            direct_row_index,
                        },
                    },
                    facts,
                };
            }
        }
    }

    missing.sort_by(|left, right| {
        left.module
            .cmp(&right.module)
            .then_with(|| left.witness.cmp(&right.witness))
    });
    let status = if missing.is_empty() {
        ClosureStatus::Complete
    } else {
        ClosureStatus::Incomplete { missing }
    };
    EffectiveImportReport {
        closure,
        status,
        facts,
    }
}

fn name_has_overflow(name: &fln_core::name::Name) -> bool {
    let mut cursor = name.clone();
    while !cursor.is_anonymous() {
        if cursor.component_overflowed() {
            return true;
        }
        cursor = cursor.parent();
    }
    false
}

fn push_rows(
    stack: &mut Vec<WorkItem>,
    source: ImportSource,
    rows: &[DirectImport],
    parent: &PropagationContext,
    limits: &ClosureLimits,
    facts: &mut ClosureFacts,
    closure: &EffectiveImportClosure,
) -> Option<EffectiveImportReport> {
    let pending = stack.len().saturating_add(rows.len());
    if pending > limits.max_pending_items {
        return Some(report_inconclusive(
            closure.clone(),
            *facts,
            ClosureResource::PendingItems,
            limits.max_pending_items,
            pending,
            match &source {
                ImportSource::Root => None,
                ImportSource::Module(module) => Some(module.clone()),
            },
        ));
    }
    for (row_index, import) in rows.iter().enumerate().rev() {
        stack.push(WorkItem::Visit {
            source: source.clone(),
            row_index,
            import: import.clone(),
            parent: parent.clone(),
        });
    }
    facts.maximum_pending_items = facts.maximum_pending_items.max(stack.len());
    None
}

fn propagate_candidate(
    global_level: GlobalOLeanLevel,
    source: ImportSource,
    row_index: usize,
    import: &DirectImport,
    parent: &PropagationContext,
    facts: &mut ClosureFacts,
) -> Result<Option<Candidate>, ClosureInternalFault> {
    let step = ImportWitnessStep {
        source: match &source {
            ImportSource::Root => None,
            ImportSource::Module(module) => Some(module.clone()),
        },
        direct_row_index: row_index,
        import: import.clone(),
    };

    let needs_data = parent.needs_data && (import.is_exported || parent.import_all);
    let import_all =
        global_level == GlobalOLeanLevel::Private || parent.import_all && import.import_all;
    let is_exported = parent.is_exported && import.is_exported;
    let needs_ir_transitive = parent.needs_ir_transitive || needs_data && import.is_meta;
    let ir_requested = needs_ir_transitive || import_all || global_level.globally_requests_ir();
    if !needs_data && !ir_requested {
        return Ok(None);
    }

    let fault = |component| ClosureInternalFault::MissingComponentWitness {
        component,
        source: source.clone(),
        direct_row_index: row_index,
        target: import.module.clone(),
    };
    let data_witness = if needs_data {
        let data = parent
            .data_witness
            .as_ref()
            .ok_or_else(|| fault(WitnessComponent::Data))?;
        Some(if import.is_exported {
            data.append(&step, facts)
        } else {
            ComponentWitness::conjoin(
                data,
                parent
                    .import_all_witness
                    .as_ref()
                    .ok_or_else(|| fault(WitnessComponent::ImportAll))?,
                &step,
                facts,
            )
        })
    } else {
        None
    };
    let import_all_witness = if import_all {
        Some(if global_level == GlobalOLeanLevel::Private {
            parent.route_witness.append(&step, facts)
        } else {
            parent
                .import_all_witness
                .as_ref()
                .ok_or_else(|| fault(WitnessComponent::ImportAll))?
                .append(&step, facts)
        })
    } else {
        None
    };
    let exported_witness = if is_exported {
        Some(
            parent
                .exported_witness
                .as_ref()
                .ok_or_else(|| fault(WitnessComponent::Exported))?
                .append(&step, facts),
        )
    } else {
        None
    };
    let ir_transitive_witness = if needs_ir_transitive {
        Some(if parent.needs_ir_transitive {
            parent
                .ir_transitive_witness
                .as_ref()
                .ok_or_else(|| fault(WitnessComponent::IrTransitive))?
                .append(&step, facts)
        } else {
            data_witness
                .as_ref()
                .ok_or_else(|| fault(WitnessComponent::Data))?
                .clone()
        })
    } else {
        None
    };

    let route_witness = data_witness
        .as_ref()
        .or(ir_transitive_witness.as_ref())
        .or(import_all_witness.as_ref())
        .or(exported_witness.as_ref())
        .cloned()
        .unwrap_or_else(|| parent.route_witness.append(&step, facts));
    let ir_phases = if import_all {
        IrPhases::All
    } else if needs_ir_transitive {
        IrPhases::Comptime
    } else {
        IrPhases::Runtime
    };
    let (ir_runtime, ir_comptime) = match ir_phases {
        IrPhases::Runtime => (Some(route_witness.clone()), None),
        IrPhases::Comptime => (None, ir_transitive_witness.clone()),
        IrPhases::All => (import_all_witness.clone(), import_all_witness.clone()),
    };
    let ir_requested_witness = ir_requested.then(|| {
        ir_transitive_witness
            .as_ref()
            .or(import_all_witness.as_ref())
            .cloned()
            .unwrap_or_else(|| route_witness.clone())
    });
    let first_path = route_witness.paths.first().cloned().unwrap_or_default();

    Ok(Some(Candidate {
        state: EffectiveImportState {
            module: import.module.clone(),
            import_all,
            is_exported,
            is_meta: import.is_meta,
            ir_phases,
            has_data: needs_data,
            needs_ir_transitive,
            ir_requested,
            witnesses: EffectiveImportWitnesses {
                first_discovery: first_path.clone(),
                data: data_witness,
                import_all: import_all_witness,
                exported: exported_witness,
                ir_transitive: ir_transitive_witness,
                ir_runtime,
                ir_comptime,
                ir_requested: ir_requested_witness,
            },
        },
        first_path,
    }))
}

/// Returns exactly the Reference five-field update condition. `is_meta` and
/// `ir_requested` are retained/accumulated but never independently trigger a replay.
fn merge_state(existing: &mut EffectiveImportState, incoming: EffectiveImportState) -> bool {
    let import_all = existing.import_all || incoming.import_all;
    let is_exported = existing.is_exported || incoming.is_exported;
    let has_data = existing.has_data || incoming.has_data;
    let needs_ir_transitive = existing.needs_ir_transitive || incoming.needs_ir_transitive;
    let ir_phases = existing.ir_phases.join(incoming.ir_phases);
    let changed = import_all != existing.import_all
        || is_exported != existing.is_exported
        || has_data != existing.has_data
        || needs_ir_transitive != existing.needs_ir_transitive
        || ir_phases != existing.ir_phases;

    retain_first_witness(&mut existing.witnesses.data, incoming.witnesses.data);
    retain_first_witness(
        &mut existing.witnesses.import_all,
        incoming.witnesses.import_all,
    );
    retain_first_witness(
        &mut existing.witnesses.exported,
        incoming.witnesses.exported,
    );
    retain_first_witness(
        &mut existing.witnesses.ir_transitive,
        incoming.witnesses.ir_transitive,
    );
    retain_first_witness(
        &mut existing.witnesses.ir_runtime,
        incoming.witnesses.ir_runtime,
    );
    retain_first_witness(
        &mut existing.witnesses.ir_comptime,
        incoming.witnesses.ir_comptime,
    );
    retain_first_witness(
        &mut existing.witnesses.ir_requested,
        incoming.witnesses.ir_requested,
    );
    existing.import_all = import_all;
    existing.is_exported = is_exported;
    existing.has_data = has_data;
    existing.needs_ir_transitive = needs_ir_transitive;
    existing.ir_phases = ir_phases;
    existing.ir_requested |= incoming.ir_requested;
    changed
}

fn retain_first_witness(
    existing: &mut Option<ComponentWitness>,
    incoming: Option<ComponentWitness>,
) {
    if existing.is_none() {
        *existing = incoming;
    }
}

fn report_inconclusive(
    closure: EffectiveImportClosure,
    facts: ClosureFacts,
    resource: ClosureResource,
    limit: usize,
    actual: usize,
    module: Option<ModuleId>,
) -> EffectiveImportReport {
    EffectiveImportReport {
        closure,
        status: ClosureStatus::Inconclusive {
            reason: InconclusiveReason::ResourceLimitExceeded {
                resource,
                limit,
                actual,
                module,
            },
        },
        facts,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::name::Name;
    use fln_hash::domain::Digest;

    use crate::modules::{
        ArtifactEvidence, ArtifactGrade, ArtifactProducer, ModuleEpoch, ModuleGraphLimits,
        ModuleRecord,
    };

    const PIN_COMMIT: &str = "8c9756b28d64dab099da31a4c09229a9e6a2ef35";

    fn id(value: &str) -> ModuleId {
        ModuleId::new(Name::from_components(value.split('.')))
    }

    fn direct(value: &str, bits: u8) -> DirectImport {
        DirectImport::new(id(value), bits & 1 != 0, bits & 2 != 0, bits & 4 != 0)
    }

    fn graph(records: Vec<(&str, bool, Vec<DirectImport>)>) -> ModuleGraph {
        let epoch = ModuleEpoch::new("v4.32.0", PIN_COMMIT);
        let mut graph = ModuleGraph::new(
            epoch.clone(),
            ModuleGraphLimits::new(10_000, 100_000, 1_000, u128::MAX),
        )
        .expect("test epoch");
        for (index, (module, is_module, imports)) in records.into_iter().enumerate() {
            graph = graph
                .register(ModuleRecord::new(
                    id(module),
                    is_module,
                    imports,
                    ArtifactEvidence {
                        epoch: epoch.clone(),
                        content_digest: Digest([index as u8; 32]),
                        producer: ArtifactProducer::Reference,
                        grade: ArtifactGrade::OracleFixture,
                    },
                ))
                .expect("test module registers")
                .graph;
        }
        graph
    }

    #[derive(Debug, Clone, PartialEq, Eq)]
    struct ModelState {
        module: ModuleId,
        import_all: bool,
        is_exported: bool,
        is_meta: bool,
        ir_phases: IrPhases,
        has_data: bool,
        needs_ir_transitive: bool,
        ir_requested: bool,
    }

    #[derive(Debug, Clone, Copy)]
    struct ModelContext {
        import_all: bool,
        is_exported: bool,
        needs_data: bool,
        needs_ir_transitive: bool,
    }

    impl ModelContext {
        fn root(root_is_exported: bool) -> Self {
            Self {
                import_all: true,
                is_exported: root_is_exported,
                needs_data: true,
                needs_ir_transitive: false,
            }
        }

        fn from_state(state: &ModelState) -> Self {
            Self {
                import_all: state.import_all,
                is_exported: state.is_exported,
                needs_data: state.has_data,
                needs_ir_transitive: state.needs_ir_transitive,
            }
        }
    }

    fn model_candidate(
        level: GlobalOLeanLevel,
        parent: ModelContext,
        import: &DirectImport,
    ) -> Option<ModelState> {
        let has_data = parent.needs_data && (import.is_exported || parent.import_all);
        let import_all =
            level == GlobalOLeanLevel::Private || parent.import_all && import.import_all;
        let is_exported = parent.is_exported && import.is_exported;
        let needs_ir_transitive = parent.needs_ir_transitive || has_data && import.is_meta;
        let ir_requested = needs_ir_transitive || import_all || level.globally_requests_ir();
        if !has_data && !ir_requested {
            return None;
        }
        Some(ModelState {
            module: import.module.clone(),
            import_all,
            is_exported,
            is_meta: import.is_meta,
            ir_phases: if import_all {
                IrPhases::All
            } else if needs_ir_transitive {
                IrPhases::Comptime
            } else {
                IrPhases::Runtime
            },
            has_data,
            needs_ir_transitive,
            ir_requested,
        })
    }

    fn model_merge(existing: &ModelState, incoming: ModelState) -> (ModelState, bool) {
        let merged = ModelState {
            module: existing.module.clone(),
            import_all: existing.import_all || incoming.import_all,
            is_exported: existing.is_exported || incoming.is_exported,
            is_meta: existing.is_meta,
            ir_phases: existing.ir_phases.join(incoming.ir_phases),
            has_data: existing.has_data || incoming.has_data,
            needs_ir_transitive: existing.needs_ir_transitive || incoming.needs_ir_transitive,
            ir_requested: existing.ir_requested || incoming.ir_requested,
        };
        let changed = merged.import_all != existing.import_all
            || merged.is_exported != existing.is_exported
            || merged.ir_phases != existing.ir_phases
            || merged.has_data != existing.has_data
            || merged.needs_ir_transitive != existing.needs_ir_transitive;
        (merged, changed)
    }

    fn model_compute(
        graph: &ModuleGraph,
        request: &EffectiveImportRequest,
    ) -> (BTreeMap<ModuleId, ModelState>, Vec<ModuleId>) {
        fn visit_rows(
            graph: &ModuleGraph,
            level: GlobalOLeanLevel,
            rows: &[DirectImport],
            parent: ModelContext,
            states: &mut BTreeMap<ModuleId, ModelState>,
            discovery: &mut Vec<ModuleId>,
        ) {
            for import in rows {
                let Some(candidate) = model_candidate(level, parent, import) else {
                    continue;
                };
                if let Some(existing) = states.get(&import.module).cloned() {
                    let (merged, changed) = model_merge(&existing, candidate);
                    states.insert(import.module.clone(), merged.clone());
                    if changed && let Some(record) = graph.record(&import.module) {
                        visit_rows(
                            graph,
                            level,
                            record.direct_imports(),
                            ModelContext::from_state(&merged),
                            states,
                            discovery,
                        );
                    }
                } else {
                    states.insert(import.module.clone(), candidate.clone());
                    if let Some(record) = graph.record(&import.module) {
                        visit_rows(
                            graph,
                            level,
                            record.direct_imports(),
                            ModelContext::from_state(&candidate),
                            states,
                            discovery,
                        );
                    }
                    discovery.push(import.module.clone());
                }
            }
        }

        let mut states = BTreeMap::new();
        let mut discovery = Vec::new();
        visit_rows(
            graph,
            request.global_level,
            &request.direct_imports,
            ModelContext::root(request.root_is_exported),
            &mut states,
            &mut discovery,
        );
        (states, discovery)
    }

    fn scalar(state: &EffectiveImportState) -> ModelState {
        ModelState {
            module: state.module.clone(),
            import_all: state.import_all,
            is_exported: state.is_exported,
            is_meta: state.is_meta,
            ir_phases: state.ir_phases,
            has_data: state.has_data,
            needs_ir_transitive: state.needs_ir_transitive,
            ir_requested: state.ir_requested,
        }
    }

    fn assert_witness_path_valid(
        graph: &ModuleGraph,
        request: &EffectiveImportRequest,
        target: &ModuleId,
        path: &ImportWitnessPath,
    ) {
        assert!(!path.steps.is_empty(), "module witness must leave the root");
        let mut expected_source = None;
        for step in path.steps.iter() {
            assert_eq!(step.source, expected_source);
            let expected_row = match &step.source {
                None => request.direct_imports.get(step.direct_row_index),
                Some(source) => graph
                    .record(source)
                    .and_then(|record| record.direct_imports().get(step.direct_row_index)),
            }
            .expect("witness row exists in its named source");
            assert_eq!(expected_row, &step.import);
            expected_source = Some(step.import.module.clone());
        }
        assert_eq!(expected_source.as_ref(), Some(target));
    }

    fn assert_state_witnesses_valid(
        graph: &ModuleGraph,
        request: &EffectiveImportRequest,
        state: &EffectiveImportState,
    ) {
        assert_witness_path_valid(
            graph,
            request,
            &state.module,
            &state.witnesses.first_discovery,
        );
        let components = [
            state.witnesses.data.as_ref(),
            state.witnesses.import_all.as_ref(),
            state.witnesses.exported.as_ref(),
            state.witnesses.ir_transitive.as_ref(),
            state.witnesses.ir_runtime.as_ref(),
            state.witnesses.ir_comptime.as_ref(),
            state.witnesses.ir_requested.as_ref(),
        ];
        for component in components.into_iter().flatten() {
            assert!(!component.paths.is_empty());
            for path in component.paths.iter() {
                assert_witness_path_valid(graph, request, &state.module, path);
            }
        }
    }

    #[test]
    fn all_flag_combinations_match_pinned_direct_equations() {
        let records = (0u8..8)
            .map(|bits| (format!("M{bits}"), true, Vec::new()))
            .collect::<Vec<_>>();
        let graph = graph(
            records
                .iter()
                .map(|(name, is_module, rows)| (name.as_str(), *is_module, rows.clone()))
                .collect(),
        );
        let request = EffectiveImportRequest::new(
            (0u8..8)
                .map(|bits| direct(&format!("M{bits}"), bits))
                .collect(),
            GlobalOLeanLevel::Exported,
        );
        let report = compute_effective_imports(&graph, &request, None);
        assert_eq!(report.status, ClosureStatus::Complete);
        for bits in 0u8..8 {
            let state = report.closure.state(&id(&format!("M{bits}"))).unwrap();
            assert!(state.has_data);
            assert_eq!(state.import_all, bits & 1 != 0);
            assert_eq!(state.is_exported, bits & 2 != 0);
            assert_eq!(state.is_meta, bits & 4 != 0);
            assert_eq!(state.needs_ir_transitive, bits & 4 != 0);
            assert_eq!(
                state.ir_phases,
                if bits & 1 != 0 {
                    IrPhases::All
                } else if bits & 4 != 0 {
                    IrPhases::Comptime
                } else {
                    IrPhases::Runtime
                }
            );
        }
    }

    #[test]
    fn discovery_is_postorder_and_reverse_rows_preserve_duplicates() {
        let graph = graph(vec![
            ("A", true, vec![direct("C", 2)]),
            ("B", true, vec![direct("C", 2), direct("C", 6)]),
            ("C", true, vec![]),
        ]);
        let request = EffectiveImportRequest::new(
            vec![direct("A", 2), direct("B", 2)],
            GlobalOLeanLevel::Exported,
        );
        let report = compute_effective_imports(&graph, &request, None);
        assert_eq!(
            report.closure.reference_discovery(),
            [id("C"), id("A"), id("B")]
        );
        assert_eq!(report.closure.reverse_rows(&id("C")).len(), 3);
        assert_eq!(
            report.closure.canonical_reverse_importers(&id("C")),
            [ImportSource::Module(id("A")), ImportSource::Module(id("B"))]
        );
    }

    #[test]
    fn direct_row_permutation_changes_only_reference_ordered_surfaces() {
        let graph = graph(vec![
            ("A", true, vec![direct("C", 2)]),
            ("B", true, vec![direct("D", 2)]),
            ("C", true, vec![]),
            ("D", true, vec![]),
        ]);
        let left = compute_effective_imports(
            &graph,
            &EffectiveImportRequest::new(
                vec![direct("A", 2), direct("B", 2)],
                GlobalOLeanLevel::Exported,
            ),
            None,
        );
        let right = compute_effective_imports(
            &graph,
            &EffectiveImportRequest::new(
                vec![direct("B", 2), direct("A", 2)],
                GlobalOLeanLevel::Exported,
            ),
            None,
        );
        assert_eq!(
            left.closure.canonical_modules(),
            right.closure.canonical_modules()
        );
        assert_ne!(
            left.closure.reference_discovery(),
            right.closure.reference_discovery()
        );
        assert_eq!(
            left.closure.reference_discovery(),
            [id("C"), id("A"), id("D"), id("B")]
        );
        assert_eq!(
            right.closure.reference_discovery(),
            [id("D"), id("B"), id("C"), id("A")]
        );
    }

    #[test]
    fn late_upgrade_replays_closure_but_retains_first_is_meta() {
        let graph = graph(vec![
            ("A", true, vec![direct("C", 3)]),
            ("B", true, vec![direct("A", 7)]),
            ("C", true, vec![]),
        ]);
        let request = EffectiveImportRequest::new(
            vec![direct("A", 2), direct("B", 3), direct("A", 6)],
            GlobalOLeanLevel::Exported,
        );
        let report = compute_effective_imports(&graph, &request, None);
        let a = report.closure.state(&id("A")).unwrap();
        assert!(a.import_all);
        assert!(a.is_exported);
        assert!(
            !a.is_meta,
            "first discovery edge owns EffectiveImport.isMeta"
        );
        let first_step = a
            .witnesses
            .first_discovery
            .steps
            .first()
            .expect("direct first discovery has one step");
        assert_eq!(first_step.source, None);
        assert_eq!(first_step.direct_row_index, 0);
        assert_eq!(first_step.import, direct("A", 2));
        assert!(report.facts.state_upgrades >= 1);
        assert!(report.facts.closure_replays >= 1);
        assert_eq!(report.closure.reverse_rows(&id("C")).len(), 1);
        assert_eq!(
            report.closure.state(&id("C")).unwrap().exposure(),
            ImportExposure::All
        );
    }

    #[test]
    fn server_ir_request_does_not_invent_comptime_phase() {
        let graph = graph(vec![("A", true, vec![])]);
        let request = EffectiveImportRequest::new(vec![direct("A", 2)], GlobalOLeanLevel::Server);
        let report = compute_effective_imports(&graph, &request, None);
        let state = report.closure.state(&id("A")).unwrap();
        assert!(state.ir_requested);
        assert_eq!(state.ir_phases, IrPhases::Runtime);
        assert!(!state.needs_ir_transitive);
    }

    #[test]
    fn every_exposure_and_phase_join_is_explicit() {
        let levels = [
            ImportExposure::None,
            ImportExposure::Private,
            ImportExposure::PrivateAll,
            ImportExposure::Public,
            ImportExposure::All,
        ];
        for left in levels {
            assert_eq!(left.join(ImportExposure::None), left);
            assert_eq!(left.join(ImportExposure::All), ImportExposure::All);
            for right in levels {
                assert_eq!(left.join(right), right.join(left));
            }
        }
        assert_eq!(
            ImportExposure::Public.join(ImportExposure::PrivateAll),
            ImportExposure::All
        );
        assert_eq!(IrPhases::Runtime.join(IrPhases::Comptime), IrPhases::All);

        let graph = graph(vec![("A", true, vec![])]);
        let report = compute_effective_imports(
            &graph,
            &EffectiveImportRequest::new(
                vec![direct("A", 2), direct("A", 1)],
                GlobalOLeanLevel::Exported,
            ),
            None,
        );
        let state = report.closure.state(&id("A")).unwrap();
        assert_eq!(state.exposure(), ImportExposure::All);
        assert!(!state.is_meta);

        let phase_join = compute_effective_imports(
            &graph,
            &EffectiveImportRequest::new(
                vec![direct("A", 2), direct("A", 6)],
                GlobalOLeanLevel::Exported,
            ),
            None,
        );
        let state = phase_join.closure.state(&id("A")).unwrap();
        assert!(!state.import_all);
        assert_eq!(state.ir_phases, IrPhases::All);
        assert!(state.needs_ir_transitive);
        assert!(!state.is_meta, "phase join must not join first-edge isMeta");
    }

    #[test]
    fn transitive_meta_context_can_reach_ir_only_modules() {
        let graph = graph(vec![
            ("A", true, vec![direct("B", 0), direct("Skipped", 0)]),
            ("B", true, vec![direct("C", 0)]),
            ("C", true, vec![]),
            ("Skipped", true, vec![]),
        ]);
        let report = compute_effective_imports(
            &graph,
            &EffectiveImportRequest::new(vec![direct("A", 6)], GlobalOLeanLevel::Exported),
            None,
        );
        for module in ["B", "C", "Skipped"] {
            let state = report.closure.state(&id(module)).unwrap();
            assert!(!state.has_data);
            assert!(state.needs_ir_transitive);
            assert!(state.ir_requested);
            assert_eq!(state.ir_phases, IrPhases::Comptime);
        }

        let no_meta = compute_effective_imports(
            &graph,
            &EffectiveImportRequest::new(vec![direct("A", 2)], GlobalOLeanLevel::Exported),
            None,
        );
        assert!(no_meta.closure.state(&id("B")).is_none());
        assert!(no_meta.closure.state(&id("Skipped")).is_none());
    }

    #[test]
    fn generated_dags_match_independent_recursive_model_and_build_order() {
        let mut seed = 0xD1B5_4A32_D192_ED03u64;
        let mut records = Vec::new();
        for index in 0..96usize {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            let mut imports = Vec::new();
            if index > 0 {
                for offset in 0..(seed as usize % 5) {
                    let target = seed
                        .rotate_left((offset as u32 * 11 + 1) % 64)
                        .wrapping_add(offset as u64) as usize
                        % index;
                    imports.push(direct(&format!("R{target}"), (seed >> (offset * 3)) as u8));
                }
            }
            records.push((format!("R{index}"), true, imports));
        }

        let forward = graph(
            records
                .iter()
                .map(|(name, is_module, imports)| (name.as_str(), *is_module, imports.clone()))
                .collect(),
        );
        let reverse = graph(
            records
                .iter()
                .rev()
                .map(|(name, is_module, imports)| (name.as_str(), *is_module, imports.clone()))
                .collect(),
        );

        for level in [
            GlobalOLeanLevel::Exported,
            GlobalOLeanLevel::Server,
            GlobalOLeanLevel::Private,
        ] {
            let mut roots = Vec::new();
            for index in 88..96usize {
                roots.push(direct(&format!("R{index}"), (seed >> (index % 17)) as u8));
            }
            roots.push(direct("R95", 7));
            roots.push(direct("R94", 0));
            let request = EffectiveImportRequest::new(roots, level);
            let expected = model_compute(&forward, &request);
            let actual = compute_effective_imports(&forward, &request, None);
            let reordered = compute_effective_imports(&reverse, &request, None);
            assert_eq!(actual.status, ClosureStatus::Complete);
            assert_eq!(actual, reordered);
            assert_eq!(actual.closure.reference_discovery(), expected.1);
            assert_eq!(actual.closure.len(), expected.0.len());
            for (module, expected_state) in expected.0 {
                let actual_state = actual
                    .closure
                    .state(&module)
                    .expect("model module exists in closure");
                assert_eq!(
                    scalar(actual_state),
                    expected_state,
                    "model mismatch at {} under {level:?}",
                    module.name().to_display_string()
                );
                assert_state_witnesses_valid(&forward, &request, actual_state);
            }
        }
    }

    #[test]
    fn thread_partitioned_graph_construction_cannot_change_the_report() {
        const MODULES: usize = 67;
        const LANES: usize = 8;
        let records: Arc<Vec<(String, bool, Vec<DirectImport>)>> = Arc::new(
            (0..MODULES)
                .map(|index| {
                    let imports = if index > 0 {
                        vec![
                            direct(&format!("T{}", index - 1), index as u8),
                            direct(&format!("T{}", index / 2), (index >> 1) as u8),
                        ]
                    } else {
                        Vec::new()
                    };
                    (format!("T{index}"), true, imports)
                })
                .collect(),
        );
        let request = Arc::new(EffectiveImportRequest::new(
            vec![direct(&format!("T{}", MODULES - 1), 7)],
            GlobalOLeanLevel::Server,
        ));

        let reports = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..LANES)
                .map(|lane| {
                    let records = Arc::clone(&records);
                    let request = Arc::clone(&request);
                    scope.spawn(move || {
                        let stride = lane + 1;
                        let ordered: Vec<_> = (0..MODULES)
                            .map(|step| {
                                let index = (lane + step * stride) % MODULES;
                                let (name, is_module, imports) = records
                                    .get(index)
                                    .expect("prime permutation index is in range");
                                (name.as_str(), *is_module, imports.clone())
                            })
                            .collect();
                        compute_effective_imports(&graph(ordered), &request, None)
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("effective import worker"))
                .collect::<Vec<_>>()
        });

        let baseline = reports.first().expect("at least one determinism lane");
        for report in reports.iter().skip(1) {
            assert_eq!(report, baseline);
        }
        println!(
            "{{\"schema\":\"fln.unit.effective-import-determinism\",\"version\":1,\"bead\":\"fln-amv.9.2\",\"lanes\":{LANES},\"modules\":{MODULES},\"orders\":{LANES},\"expected\":\"equal\",\"actual\":\"equal\"}}"
        );
    }

    #[test]
    fn large_dense_dag_work_is_bounded_by_rows_and_monotone_upgrades() {
        const MODULES: usize = 72;
        let mut records = Vec::new();
        let mut edge_rows = 0usize;
        for index in 0..MODULES {
            let start = index.saturating_sub(12);
            let imports: Vec<_> = (start..index)
                .map(|target| direct(&format!("Dense{target}"), (index + target) as u8))
                .collect();
            edge_rows = edge_rows.saturating_add(imports.len());
            records.push((format!("Dense{index}"), true, imports));
        }
        let graph = graph(
            records
                .iter()
                .map(|(name, is_module, imports)| (name.as_str(), *is_module, imports.clone()))
                .collect(),
        );
        let roots: Vec<_> = (MODULES - 8..MODULES)
            .flat_map(|index| {
                [
                    direct(&format!("Dense{index}"), 2),
                    direct(&format!("Dense{index}"), 7),
                ]
            })
            .collect();
        let root_rows = roots.len();
        let report = compute_effective_imports(
            &graph,
            &EffectiveImportRequest::new(roots, GlobalOLeanLevel::Exported),
            None,
        );
        assert_eq!(report.status, ClosureStatus::Complete);
        assert!(report.facts.state_upgrades <= report.closure.len().saturating_mul(5));
        assert!(
            report.facts.direct_rows_examined
                <= root_rows.saturating_add(edge_rows.saturating_mul(6))
        );
        assert!(
            report.facts.work_items
                <= report
                    .facts
                    .direct_rows_examined
                    .saturating_add(report.closure.len())
        );
        println!(
            "{{\"schema\":\"fln.unit.effective-import-operation-count\",\"version\":1,\"bead\":\"fln-amv.9.2\",\"modules\":{},\"graph_rows\":{edge_rows},\"root_rows\":{root_rows},\"examined_rows\":{},\"state_upgrades\":{},\"closure_replays\":{},\"work_items\":{},\"expected\":\"bounded\",\"actual\":\"bounded\"}}",
            report.closure.len(),
            report.facts.direct_rows_examined,
            report.facts.state_upgrades,
            report.facts.closure_replays,
            report.facts.work_items,
        );
    }

    #[test]
    fn incomplete_witness_names_the_exact_root_row_and_flags() {
        let graph = graph(vec![]);
        let request = EffectiveImportRequest::new(
            vec![direct("PresentOnlyInResolver", 0), direct("Missing", 7)],
            GlobalOLeanLevel::Exported,
        );
        let report = compute_effective_imports(&graph, &request, None);
        assert!(matches!(&report.status, ClosureStatus::Incomplete { .. }));
        let missing = if let ClosureStatus::Incomplete { missing } = report.status {
            missing
        } else {
            Vec::new()
        };
        assert_eq!(missing.len(), 2);
        let finding = missing
            .iter()
            .find(|finding| finding.module == id("Missing"))
            .expect("named missing module has a finding");
        assert_eq!(finding.module, id("Missing"));
        assert_eq!(finding.witness.steps.len(), 1);
        let step = finding
            .witness
            .steps
            .first()
            .expect("direct missing witness has one step");
        assert_eq!(step.source, None);
        assert_eq!(step.direct_row_index, 1);
        assert_eq!(step.import, direct("Missing", 7));
    }

    #[test]
    fn root_export_override_and_malformed_root_names_are_not_lost() {
        let graph = graph(vec![("A", true, vec![])]);
        let overridden = compute_effective_imports(
            &graph,
            &EffectiveImportRequest::new(vec![direct("A", 2)], GlobalOLeanLevel::Exported)
                .with_root_is_exported(false),
            None,
        );
        assert_eq!(overridden.status, ClosureStatus::Complete);
        assert!(!overridden.closure.state(&id("A")).unwrap().is_exported);

        let anonymous = EffectiveImportRequest::new(
            vec![DirectImport::new(
                ModuleId::new(Name::anonymous()),
                false,
                true,
                false,
            )],
            GlobalOLeanLevel::Exported,
        );
        assert_eq!(
            compute_effective_imports(&graph, &anonymous, None).status,
            ClosureStatus::Invalid {
                reason: InvalidImportRequest::AnonymousRootImport {
                    direct_row_index: 0,
                }
            }
        );

        let overflowed = ModuleId::new(Name::num_overflowing(Name::anonymous(), u64::MAX));
        let overflow = EffectiveImportRequest::new(
            vec![DirectImport::new(overflowed.clone(), false, true, false)],
            GlobalOLeanLevel::Exported,
        );
        assert_eq!(
            compute_effective_imports(&graph, &overflow, None).status,
            ClosureStatus::Invalid {
                reason: InvalidImportRequest::OverflowingRootModule {
                    module: overflowed,
                    direct_row_index: 0,
                }
            }
        );
    }

    #[test]
    fn impossible_witness_invariant_is_a_typed_internal_fault() {
        let broken_parent = PropagationContext {
            import_all: true,
            is_exported: true,
            needs_data: true,
            needs_ir_transitive: false,
            import_all_witness: Some(ComponentWitness::root()),
            exported_witness: Some(ComponentWitness::root()),
            data_witness: None,
            ir_transitive_witness: None,
            route_witness: ComponentWitness::root(),
        };
        let mut facts = ClosureFacts::default();
        assert_eq!(
            propagate_candidate(
                GlobalOLeanLevel::Exported,
                ImportSource::Root,
                0,
                &direct("A", 2),
                &broken_parent,
                &mut facts,
            )
            .expect_err("missing internal evidence is not a user diagnostic"),
            ClosureInternalFault::MissingComponentWitness {
                component: WitnessComponent::Data,
                source: ImportSource::Root,
                direct_row_index: 0,
                target: id("A"),
            }
        );
    }

    #[test]
    fn every_limit_is_typed_and_stops_before_over_budget_semantic_work() {
        let graph = graph(vec![
            ("A", true, vec![direct("C", 3)]),
            ("B", true, vec![direct("A", 7)]),
            ("C", true, vec![]),
        ]);
        let base = EffectiveImportRequest::new(
            vec![direct("A", 2), direct("B", 3)],
            GlobalOLeanLevel::Exported,
        );
        let resources = [
            ClosureResource::RootImportRows,
            ClosureResource::PendingItems,
            ClosureResource::WorkItems,
            ClosureResource::StateUpgrades,
            ClosureResource::WitnessSteps,
        ];
        for resource in resources {
            let mut request = base.clone();
            match resource {
                ClosureResource::RootImportRows => {
                    request.limits.max_root_import_rows = 0;
                }
                ClosureResource::PendingItems => request.limits.max_pending_items = 0,
                ClosureResource::WorkItems => request.limits.max_work_items = 0,
                ClosureResource::StateUpgrades => request.limits.max_state_upgrades = 0,
                ClosureResource::WitnessSteps => request.limits.max_witness_steps = 0,
            }
            let report = compute_effective_imports(&graph, &request, None);
            assert!(matches!(
                report.status,
                ClosureStatus::Inconclusive {
                    reason: InconclusiveReason::ResourceLimitExceeded {
                        resource: actual,
                        ..
                    }
                } if actual == resource
            ));
            if resource == ClosureResource::StateUpgrades {
                assert_eq!(report.facts.state_upgrades, 0);
                assert!(!report.closure.state(&id("A")).unwrap().import_all);
            }
        }
    }

    #[test]
    fn named_pinned_rule_mutations_are_killed_with_structured_evidence() {
        let main_graph = graph(vec![
            ("A", true, vec![direct("C", 3), direct("D", 0)]),
            ("B", true, vec![direct("A", 7)]),
            ("C", true, vec![]),
            ("D", true, vec![]),
        ]);
        let report = compute_effective_imports(
            &main_graph,
            &EffectiveImportRequest::new(
                vec![direct("A", 2), direct("B", 3), direct("A", 6)],
                GlobalOLeanLevel::Server,
            ),
            None,
        );
        assert_eq!(report.status, ClosureStatus::Complete);
        let a = report.closure.state(&id("A")).unwrap();
        let c = report.closure.state(&id("C")).unwrap();
        assert!(a.has_data && a.import_all && a.is_exported);
        assert!(!a.is_meta);
        assert_eq!(a.ir_phases, IrPhases::All);
        assert_eq!(c.exposure(), ImportExposure::All);
        assert_eq!(report.closure.reference_discovery().first(), Some(&id("C")));
        assert!(report.facts.closure_replays > 0);

        let conjunction_graph = graph(vec![
            (
                "P",
                true,
                vec![
                    direct("Private", 0),
                    direct("PrivateMeta", 4),
                    direct("EdgeAll", 1),
                ],
            ),
            ("Private", true, vec![]),
            ("PrivateMeta", true, vec![]),
            ("EdgeAll", true, vec![]),
        ]);
        let conjunction = compute_effective_imports(
            &conjunction_graph,
            &EffectiveImportRequest::new(
                vec![direct("P", 2), direct("DirectPrivate", 0)],
                GlobalOLeanLevel::Exported,
            ),
            None,
        );
        let direct_private = conjunction.closure.state(&id("DirectPrivate")).unwrap();

        let server_graph = graph(vec![("Runtime", true, vec![])]);
        let server = compute_effective_imports(
            &server_graph,
            &EffectiveImportRequest::new(vec![direct("Runtime", 2)], GlobalOLeanLevel::Server),
            None,
        );
        let runtime = server.closure.state(&id("Runtime")).unwrap();

        let mutation_results = [
            (
                "FLN-MUT-IMPORT-NEEDS-DATA-OR",
                conjunction.closure.state(&id("Private")).is_none(),
            ),
            (
                "FLN-MUT-IMPORT-ALL-OR",
                conjunction.closure.state(&id("EdgeAll")).is_none(),
            ),
            ("FLN-MUT-IMPORT-EXPORTED-OR", !direct_private.is_exported),
            (
                "FLN-MUT-IMPORT-META-WITHOUT-DATA",
                conjunction.closure.state(&id("PrivateMeta")).is_none(),
            ),
            ("FLN-MUT-IMPORT-IR-OMIT-GLOBAL", runtime.ir_requested),
            (
                "FLN-MUT-IMPORT-APPEND-BEFORE-RECURSE",
                report.closure.reference_discovery().first() == Some(&id("C")),
            ),
            ("FLN-MUT-IMPORT-JOIN-IS-META", !a.is_meta),
            (
                "FLN-MUT-IMPORT-SUPPRESS-UPGRADE-REPLAY",
                c.exposure() == ImportExposure::All,
            ),
            (
                "FLN-MUT-IMPORT-SERVER-PHASE-CONFLATION",
                runtime.ir_phases == IrPhases::Runtime,
            ),
        ];
        for (mutation, killed) in mutation_results {
            assert!(killed, "named mutation survived: {mutation}");
            println!(
                "{{\"schema\":\"fln.unit.effective-import-mutation\",\"version\":1,\"bead\":\"fln-amv.9.2\",\"mutation\":\"{mutation}\",\"expected\":\"killed\",\"actual\":\"killed\"}}"
            );
        }
    }

    #[test]
    fn missing_cancel_resource_and_nonmodule_outcomes_never_collapse() {
        let empty = graph(vec![]);
        let request =
            EffectiveImportRequest::new(vec![direct("Missing", 2)], GlobalOLeanLevel::Exported);
        let missing = compute_effective_imports(&empty, &request, None);
        assert!(matches!(missing.status, ClosureStatus::Incomplete { .. }));
        assert_eq!(missing.closure.reference_discovery(), [id("Missing")]);

        let cancelled = AtomicBool::new(true);
        let cancelled_report = compute_effective_imports(&empty, &request, Some(&cancelled));
        assert!(matches!(
            cancelled_report.status,
            ClosureStatus::Inconclusive {
                reason: InconclusiveReason::Cancelled { .. }
            }
        ));

        let mut limited_request = request.clone();
        limited_request.limits.max_work_items = 0;
        let limited = compute_effective_imports(&empty, &limited_request, None);
        assert!(matches!(
            limited.status,
            ClosureStatus::Inconclusive {
                reason: InconclusiveReason::ResourceLimitExceeded {
                    resource: ClosureResource::WorkItems,
                    ..
                }
            }
        ));

        let nonmodule = graph(vec![("Legacy", false, vec![])]);
        let invalid = compute_effective_imports(
            &nonmodule,
            &EffectiveImportRequest::new(vec![direct("Legacy", 2)], GlobalOLeanLevel::Exported),
            None,
        );
        assert_eq!(
            invalid.status,
            ClosureStatus::Invalid {
                reason: InvalidImportRequest::NonModuleDirectImport {
                    module: id("Legacy"),
                    direct_row_index: 0,
                }
            }
        );

        let private = compute_effective_imports(
            &nonmodule,
            &EffectiveImportRequest::new(vec![direct("Legacy", 0)], GlobalOLeanLevel::Private),
            None,
        );
        assert_eq!(private.status, ClosureStatus::Complete);
        assert_eq!(
            private.closure.state(&id("Legacy")).unwrap().exposure(),
            ImportExposure::PrivateAll
        );
    }
}
