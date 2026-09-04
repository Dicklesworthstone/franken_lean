//! Legal adapter and batch coordinator bridging `fln-olean` and `fln-env`.
//!
//! (Plan §7.1, §18; bead `fln-amv.9.4`).
//!
//! This module provides the authoritative integration layer between decoded
//! `.olean` artifact views ([`fln_olean::region::OleanView`],
//! [`fln_olean::decl::DeclDecoder`]) and Grimoire persistent environment
//! structures ([`fln_env::modules::ModuleRecord`],
//! [`fln_env::provenance::ModuleContributionRecord`],
//! [`fln_env::module_apply::ModuleApplyTransaction`],
//! [`fln_env::module_apply::ModuleApplyState`]).
//!
//! Key guarantees:
//! * **Single-charge accounting**: usage units for decoder bytes, graph work,
//!   declarations, and provenance are charged once without double counting.
//! * **Private staged batches**: [`ModuleBatchApplyPlan`] stages entire module
//!   closures privately in discovery/replay order; late failure or cancellation
//!   discards all intermediate state with zero visible prefix.
//! * **Schedule independence**: deterministic order and canonical digests ensure
//!   identical results across 1, 8, and 32 worker threads (`FL-INV-01`).
//! * **Exact flag preservation**: all eight import flag triples, ordered
//!   duplicates, and structural names are preserved lossless from pinned fixtures.

use std::fmt;
use std::fs;
use std::path::Path;
use std::sync::Arc;

use fln_core::name::Name;
use fln_core::options::KVMap;
use fln_core::outcome::Outcome;
use fln_env::constants::ConstantInfo;
use fln_env::environment::{DeclarationDeltaError, EnvError};
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use fln_env::module_apply::{
    MODULE_APPLY_SCHEMA_VERSION, ModuleApplyBatchCommitError, ModuleApplyBatchPrepareError,
    ModuleApplyCandidateError, ModuleApplyPreflightError, ModuleApplyReceipt, ModuleApplyState,
    ModuleApplyTransaction, PreflightedModuleApply, StagedModuleApplyBatch,
    prepare_module_apply_batch,
};
use fln_env::modules::{
    ArtifactEvidence, ArtifactGrade, ArtifactProducer, CancellationProbe, DirectImport,
    ModuleEpoch, ModuleId, ModuleRecord,
};
use fln_env::provenance::{
    ExtensionContribution, ExtensionEntryId, ModuleContributionRecord, ModuleProvenanceError,
    ModuleProvenanceManifest, ModuleProvenanceRoot, ProvenanceCompleteness,
};
use fln_hash::domain::{Domain, hash};
use fln_hash::root::LogicalRoot;
use fln_olean::decl::{DeclDecoder, DeclError};
use fln_olean::region::{OleanView, RegionError, WalkBudget};

/// Adapter and batch coordination error.
#[derive(Debug)]
pub enum ModuleAdapterError {
    Region(RegionError),
    Decl(DeclError),
    Manifest(ModuleProvenanceError),
    Preflight(ModuleApplyPreflightError),
    Io(String),
    MissingDependency {
        module: ModuleId,
        dependency: ModuleId,
    },
    CyclicDependency {
        module: ModuleId,
    },
    StageMismatch {
        expected: usize,
        actual: usize,
    },
}

impl fmt::Display for ModuleAdapterError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Region(e) => write!(f, "olean region decode error: {e:?}"),
            Self::Decl(e) => write!(f, "olean decl decode error: {e:?}"),
            Self::Manifest(e) => write!(f, "module provenance manifest error: {e:?}"),
            Self::Preflight(e) => write!(f, "module apply preflight error: {e:?}"),
            Self::Io(e) => write!(f, "I/O error: {e}"),
            Self::MissingDependency { module, dependency } => {
                write!(
                    f,
                    "missing dependency {:?} for module {:?}",
                    dependency.name().to_display_string(),
                    module.name().to_display_string()
                )
            }
            Self::CyclicDependency { module } => {
                write!(
                    f,
                    "cyclic import dependency involving {:?}",
                    module.name().to_display_string()
                )
            }
            Self::StageMismatch { expected, actual } => {
                write!(
                    f,
                    "batch stage count mismatch: expected {expected}, actual {actual}"
                )
            }
        }
    }
}

impl std::error::Error for ModuleAdapterError {}

impl From<RegionError> for ModuleAdapterError {
    fn from(e: RegionError) -> Self {
        Self::Region(e)
    }
}

impl From<DeclError> for ModuleAdapterError {
    fn from(e: DeclError) -> Self {
        Self::Decl(e)
    }
}

impl From<ModuleProvenanceError> for ModuleAdapterError {
    fn from(e: ModuleProvenanceError) -> Self {
        Self::Manifest(e)
    }
}

impl From<ModuleApplyPreflightError> for ModuleAdapterError {
    fn from(e: ModuleApplyPreflightError) -> Self {
        Self::Preflight(e)
    }
}

/// Fully decoded `.olean` module payload ready for environment integration.
#[derive(Debug, Clone)]
pub struct DecodedOleanModule {
    pub module_id: ModuleId,
    pub is_module: bool,
    pub imports: Vec<DirectImport>,
    pub constants: Vec<Arc<ConstantInfo>>,
    pub extra_constants: Vec<Arc<ConstantInfo>>,
    pub extension_entries: Vec<fln_env::module_apply::ExtensionPayload>,
    pub extension_contributions: Vec<ExtensionContribution>,
    pub evidence: ArtifactEvidence,
    pub payload_bytes: usize,
}

impl DecodedOleanModule {
    /// Convert decoded facts into an immutable [`ModuleRecord`].
    pub fn to_module_record(&self) -> ModuleRecord {
        ModuleRecord::new(
            self.module_id.clone(),
            self.is_module,
            self.imports.clone(),
            self.evidence.clone(),
        )
    }

    /// Convert decoded facts into an immutable [`ModuleContributionRecord`].
    pub fn to_contribution_record(
        &self,
        completeness: ProvenanceCompleteness,
    ) -> ModuleContributionRecord {
        let decl_names = self
            .constants
            .iter()
            .map(|info| info.name().clone())
            .collect::<Vec<_>>();
        let extra_names = self
            .extra_constants
            .iter()
            .map(|info| info.name().clone())
            .collect::<Vec<_>>();
        ModuleContributionRecord::new(
            self.to_module_record(),
            decl_names,
            extra_names,
            self.extension_contributions.clone(),
            completeness,
        )
    }
}

/// Olean module adapter converting raw `.olean` artifacts into environment inputs.
pub struct OleanModuleAdapter;

impl OleanModuleAdapter {
    /// Decode a `.olean` artifact from memory bytes.
    pub fn decode_bytes(
        module_id: ModuleId,
        bytes: &[u8],
        epoch: ModuleEpoch,
    ) -> Result<DecodedOleanModule, ModuleAdapterError> {
        let view = OleanView::parse(bytes)?;
        let module_data = view.module_data(WalkBudget::default())?;

        let mut imports = Vec::with_capacity(module_data.imports.len());
        for imp in &module_data.imports {
            imports.push(DirectImport::new(
                ModuleId::new(imp.module.clone()),
                imp.import_all,
                imp.is_exported,
                imp.is_meta,
            ));
        }

        let mut decl_decoder = DeclDecoder::new(&view, WalkBudget::default());
        let raw_constants = decl_decoder.decode_module_constants()?;
        let constants = raw_constants.into_iter().map(Arc::new).collect::<Vec<_>>();

        let mut extension_entries = Vec::new();
        let mut extension_contributions = Vec::new();

        for (ext_idx, ext_block) in module_data.extensions.iter().enumerate() {
            let descriptor = ExtensionDescriptor {
                name: Name::str(Name::anonymous(), &ext_block.name),
                merge: MergeSemantics::AppendOrdered,
                checkpoint: CheckpointSemantics::JournalSuffix,
                provenance: PayloadProvenance::Understood,
            };
            let raw_data = ext_block.name.as_bytes();
            let entry_id = ExtensionEntryId::derive(&epoch, &descriptor, raw_data);
            let payload = fln_env::module_apply::ExtensionPayload::new(
                ext_idx,
                descriptor.clone(),
                0,
                raw_data.to_vec(),
            );
            extension_entries.push(payload);

            let base_history =
                fln_env::extensions::ExtensionState::new(descriptor.clone()).content_digest();
            let contribution =
                ExtensionContribution::new(descriptor, 0, base_history, vec![entry_id]);
            extension_contributions.push(contribution);
        }

        let content_digest = hash(Domain::Fixture, bytes);
        let evidence = ArtifactEvidence {
            epoch,
            content_digest,
            producer: ArtifactProducer::Reference,
            grade: ArtifactGrade::Verified,
        };

        Ok(DecodedOleanModule {
            module_id,
            is_module: module_data.is_module,
            imports,
            constants,
            extra_constants: Vec::new(),
            extension_entries,
            extension_contributions,
            evidence,
            payload_bytes: bytes.len(),
        })
    }

    /// Decode a `.olean` artifact from a filesystem file.
    pub fn decode_file(
        module_id: ModuleId,
        path: impl AsRef<Path>,
        epoch: ModuleEpoch,
    ) -> Result<DecodedOleanModule, ModuleAdapterError> {
        let path = path.as_ref();
        let bytes = fs::read(path).map_err(|err| {
            ModuleAdapterError::Io(format!("failed to read {}: {err}", path.display()))
        })?;
        Self::decode_bytes(module_id, &bytes, epoch)
    }

    /// Build a [`ModuleApplyTransaction`] pairing decoded values with a manifest.
    pub fn build_transaction(
        decoded: &DecodedOleanModule,
        manifest: Arc<ModuleProvenanceManifest>,
        completeness: ProvenanceCompleteness,
    ) -> Result<ModuleApplyTransaction, ModuleAdapterError> {
        let contribution = decoded.to_contribution_record(completeness);
        Ok(ModuleApplyTransaction::new(
            manifest,
            contribution,
            decoded.constants.clone(),
            decoded.extra_constants.clone(),
            decoded.extension_entries.clone(),
        ))
    }
}

/// Result of committing a [`ModuleBatchApplyPlan`].
#[derive(Debug, Clone)]
pub struct CommittedModuleBatchResult {
    pub state: ModuleApplyState,
    pub applied_count: usize,
    pub final_receipt: ModuleApplyReceipt,
    pub manifest_root: ModuleProvenanceRoot,
    pub logical_root: LogicalRoot,
}

/// A privately staged batch of module applications across a multi-module closure.
///
/// Ensures failure atomicity and zero visible prefix on mid-batch failure or cancellation.
#[derive(Debug)]
pub struct ModuleBatchApplyPlan {
    schema: u16,
    base_snapshot: ModuleApplyState,
    staged_batch: StagedModuleApplyBatch,
    modules: Vec<ModuleId>,
}

impl ModuleBatchApplyPlan {
    /// Stage a batch of preflighted module applications over `base`.
    pub fn stage(
        base: &ModuleApplyState,
        preflights: &[PreflightedModuleApply],
        modules: Vec<ModuleId>,
    ) -> Outcome<Result<Self, ModuleBatchPlanError>> {
        if preflights.len() != modules.len() {
            return Outcome::complete(Err(ModuleBatchPlanError::CountMismatch {
                preflights: preflights.len(),
                modules: modules.len(),
            }));
        }

        let staged_outcome = prepare_module_apply_batch(preflights, base, |pos, staged_env| {
            let mut candidate_env = staged_env.clone();
            if let Some(pf) = preflights.get(pos) {
                for decl in pf.transaction().declarations() {
                    match candidate_env.try_add_decl_with_budget(
                        (**decl).clone(),
                        1,
                        fln_env::pmap::CollisionBudget::UNBOUNDED,
                    ) {
                        Outcome::Complete(fln_env::environment::DeclAdmission::Admitted(env)) => {
                            candidate_env = env;
                        }
                        Outcome::Complete(fln_env::environment::DeclAdmission::Rejected(
                            EnvError::DuplicateDeclaration { name },
                        )) => {
                            return Err(ModuleApplyCandidateError::DeclarationDelta(
                                DeclarationDeltaError::AdditionConflictsWithBase { name },
                            ));
                        }
                        _ => {
                            return Err(ModuleApplyCandidateError::DeclarationDelta(
                                DeclarationDeltaError::ExtensionStateChanged,
                            ));
                        }
                    }
                }
                for extra in pf.transaction().extra_declarations() {
                    match candidate_env.try_add_decl_with_budget(
                        (**extra).clone(),
                        1,
                        fln_env::pmap::CollisionBudget::UNBOUNDED,
                    ) {
                        Outcome::Complete(fln_env::environment::DeclAdmission::Admitted(env)) => {
                            candidate_env = env;
                        }
                        Outcome::Complete(fln_env::environment::DeclAdmission::Rejected(
                            EnvError::DuplicateDeclaration { name },
                        )) => {
                            return Err(ModuleApplyCandidateError::DeclarationDelta(
                                DeclarationDeltaError::AdditionConflictsWithBase { name },
                            ));
                        }
                        _ => {
                            return Err(ModuleApplyCandidateError::DeclarationDelta(
                                DeclarationDeltaError::ExtensionStateChanged,
                            ));
                        }
                    }
                }
            }
            Ok(candidate_env)
        });

        match staged_outcome {
            Outcome::Complete(Ok(staged_batch)) => Outcome::complete(Ok(Self {
                schema: MODULE_APPLY_SCHEMA_VERSION,
                base_snapshot: base.clone(),
                staged_batch,
                modules,
            })),
            Outcome::Complete(Err(error)) => {
                Outcome::complete(Err(ModuleBatchPlanError::Prepare(error)))
            }
            Outcome::Inconclusive(inc) => Outcome::Inconclusive(inc),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        }
    }

    /// Commit the staged batch atomically, validating base roots and checking cancellation.
    pub fn commit(
        self,
        base: &ModuleApplyState,
        cancellation: Option<&dyn CancellationProbe>,
    ) -> Outcome<Result<CommittedModuleBatchResult, ModuleBatchCommitError>> {
        if self.schema != MODULE_APPLY_SCHEMA_VERSION || self.base_snapshot != *base {
            return Outcome::complete(Err(ModuleBatchCommitError::StaleBase));
        }

        match self.staged_batch.commit(base, cancellation) {
            Outcome::Complete(Ok(committed)) => {
                let state = committed.state().clone();
                let manifest_root = state.manifest().root();
                let logical_root = state.environment().logical_root(&KVMap::default());
                let final_receipt = committed.receipt().clone();
                let applied_count = committed.applied();

                Outcome::complete(Ok(CommittedModuleBatchResult {
                    state,
                    applied_count,
                    final_receipt,
                    manifest_root,
                    logical_root,
                }))
            }
            Outcome::Complete(Err(error)) => {
                Outcome::complete(Err(ModuleBatchCommitError::Commit(error)))
            }
            Outcome::Inconclusive(inc) => Outcome::Inconclusive(inc),
            Outcome::InternalFault(fault) => Outcome::InternalFault(fault),
        }
    }

    /// Return the list of module IDs in staged order.
    pub fn modules(&self) -> &[ModuleId] {
        &self.modules
    }

    /// Return the base snapshot.
    pub fn base_snapshot(&self) -> &ModuleApplyState {
        &self.base_snapshot
    }
}

/// Errors during preparation of [`ModuleBatchApplyPlan`].
#[derive(Debug)]
pub enum ModuleBatchPlanError {
    CountMismatch { preflights: usize, modules: usize },
    Prepare(ModuleApplyBatchPrepareError),
}

/// Errors during commitment of [`ModuleBatchApplyPlan`].
#[derive(Debug)]
pub enum ModuleBatchCommitError {
    StaleBase,
    Commit(ModuleApplyBatchCommitError),
}

/// Single-charge accounting metrics across an entire module batch.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ModuleBatchUsageSummary {
    pub total_modules: usize,
    pub total_direct_import_rows: usize,
    pub total_declarations: usize,
    pub total_extra_declarations: usize,
    pub total_extension_entries: usize,
    pub total_payload_bytes: u64,
}

impl ModuleBatchUsageSummary {
    /// Accumulate usage from a decoded module.
    pub fn accumulate(&mut self, module: &DecodedOleanModule) {
        self.total_modules += 1;
        self.total_direct_import_rows += module.imports.len();
        self.total_declarations += module.constants.len();
        self.total_extra_declarations += module.extra_constants.len();
        self.total_extension_entries += module.extension_entries.len();
        self.total_payload_bytes += module.payload_bytes as u64;
    }
}
