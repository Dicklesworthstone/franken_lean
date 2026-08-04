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
use crate::extensions::ExtensionDescriptor;
use crate::provenance::{
    DeclarationClass, ExtensionEntryId, ModuleContributionRecord, ModuleProvenanceError,
    ModuleProvenanceManifest, ModuleProvenanceRoot,
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
        ArtifactEvidence, ArtifactGrade, ArtifactProducer, ModuleEpoch, ModuleId, ModuleRecord,
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
}
