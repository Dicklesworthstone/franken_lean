//! Atomic module-application input binding.
//!
//! The provenance manifest deliberately retains contribution *identity* rather than a
//! second copy of declarations or extension bytes.  This module is the boundary where
//! those `Arc`-backed values are paired with the validated manifest before later apply
//! phases can build an immutable committed environment state.

use std::sync::Arc;

use fln_core::name::Name;
use fln_hash::domain::Digest;

use crate::constants::ConstantInfo;
use crate::environment::{DeclarationDeltaError, Environment};
use crate::extensions::ExtensionDescriptor;
use crate::modules::{ModuleGraph, ModuleId};
use crate::provenance::{
    DeclarationClass, ExtensionEntryId, ModuleContributionRecord, ModuleProvenanceError,
    ModuleProvenanceIndexes, ModuleProvenanceManifest, ModuleProvenanceRoot,
};

/// Schema for the ephemeral payload envelope.  Bumping it invalidates every prepared
/// input: a plan must never be consumed under a payload-binding interpretation it was
/// not checked against.
pub const MODULE_APPLY_SCHEMA_VERSION: u16 = 1;

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

/// A completed, non-authoritative payload-binding check.
#[derive(Debug, Clone)]
pub struct PreflightedModuleApply {
    schema: u16,
    transaction: ModuleApplyTransaction,
    manifest_root: ModuleProvenanceRoot,
    declaration_identities: Arc<[Digest]>,
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
    graph: ModuleGraph,
    manifest: Arc<ModuleProvenanceManifest>,
    indexes: ModuleProvenanceIndexes,
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
        for record in manifest.records() {
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
            graph,
            manifest,
            indexes,
        })
    }

    pub fn environment(&self) -> &Environment {
        &self.environment
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

    /// Recheck the single-state invariant before a later apply plan consumes it.
    pub fn verify(&self) -> Result<(), ModuleApplyStateError> {
        let rebuilt = Self::from_parts(
            self.environment.clone(),
            self.graph.clone(),
            Arc::clone(&self.manifest),
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

/// Bind every actual payload to the validated contribution record.
///
/// This operation is read-only.  In particular, it does not register a module, add a
/// declaration, append an extension entry, derive a second provenance store, or hand
/// a provisional identity to a cache.  The subsequent prepare/commit slice consumes
/// this exact checked envelope.
pub fn preflight_module_apply(
    transaction: ModuleApplyTransaction,
) -> Result<PreflightedModuleApply, ModuleApplyPreflightError> {
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

    let declaration_identities = transaction
        .declarations
        .iter()
        .chain(transaction.extra_declarations.iter())
        .map(|info| crate::environment::Environment::decl_content_digest(info))
        .collect();
    Ok(PreflightedModuleApply {
        schema: MODULE_APPLY_SCHEMA_VERSION,
        manifest_root: transaction.manifest.root(),
        transaction,
        declaration_identities,
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::{AxiomVal, ConstantVal};
    use crate::extensions::{CheckpointSemantics, MergeSemantics, PayloadProvenance};
    use crate::modules::{
        ArtifactEvidence, ArtifactGrade, ArtifactProducer, ModuleEpoch, ModuleGraphLimits,
        ModuleId, ModuleRecord,
    };
    use crate::provenance::{
        CaptureStatus, ExtensionContribution, ModuleProvenanceLimits, PayloadTransparency,
        ProvenanceCompleteness,
    };
    use fln_core::expr::Expr;
    use fln_core::level::Level;

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
        let epoch = epoch();
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
            vec![name("fixture.decl")],
            vec![name("fixture.extra")],
            contributions,
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![],
            ),
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
        let checked = preflight_module_apply(transaction).expect("exact payload binding");

        assert!(!checked.is_cacheable());
        assert_eq!(checked.schema(), MODULE_APPLY_SCHEMA_VERSION);
        assert_eq!(checked.declaration_identities().len(), 2);
        assert!(Arc::ptr_eq(
            &declaration,
            &checked.transaction().declarations()[0]
        ));
        assert!(
            checked.transaction().extension_payloads()[0]
                .shares_payload_with(&ExtensionPayload::new(0, descriptor.clone(), 0, payload))
        );
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
            preflight_module_apply(transaction),
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
            preflight_module_apply(wrong_bytes),
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
            preflight_module_apply(reordered),
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
            descriptor,
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
        let state = ModuleApplyState::from_parts(
            environment_with_extension(Some(b"payload")),
            graph_with(&contribution),
            manifest,
        )
        .expect("joined state is coherent");

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
            descriptor,
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

        assert!(matches!(
            ModuleApplyState::from_parts(environment.clone(), graph.clone(), manifest),
            Err(ModuleApplyStateError::ExtensionRange { .. })
        ));
        assert_eq!(environment.len(), 2);
        assert_eq!(graph.len(), 1);
    }

    #[test]
    fn kernel_candidate_must_be_the_exact_declaration_delta_and_nothing_else() {
        let transaction = transaction(record(vec![]), vec![]);
        let checked = preflight_module_apply(transaction).expect("payloads preflight");
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
}
