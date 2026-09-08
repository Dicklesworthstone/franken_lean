//! Fail-closed `.olean` → environment adapter boundary.
//!
//! Extension entries retain their complete compacted object graphs, with only
//! addresses relocated into standalone regions. Their schemas remain opaque.
//!
//! This facade checks that every nonempty extension block has payload-bearing
//! entries before exposing the decoded module to the batch coordinator.

use std::fmt;
use std::fs;
use std::path::Path;
use std::sync::Arc;

use fln_env::attribute::{
    Assignment, AttributeFamily, AttributeKind, AttributeState, AttributeStatePlan, HandlerClass,
    Payload,
};
use fln_env::module_apply::{ModuleApplyPreflightError, ModuleApplyTransaction};
use fln_env::modules::{ArtifactEvidence, ModuleEpoch, ModuleId};
use fln_env::provenance::{
    ModuleProvenanceError, ModuleProvenanceManifest, ProvenanceCompleteness,
};
use fln_hash::domain::{Digest, Domain, DomainHasher, hash};
use fln_olean::decl::{ChainLimits, DeclError};
use fln_olean::region::{
    CapturedNameError, ExtensionBlock, OleanView, RegionError, WalkBudget, decode_captured_names,
};

mod legacy;

pub use legacy::{
    CommittedModuleBatchResult, DecodedOleanModule, ModuleBatchApplyPlan, ModuleBatchCommitError,
    ModuleBatchPlanError, ModuleBatchUsageSummary,
};

/// Adapter and batch-coordination failure.
///
/// Existing variants preserve the previous public error surface. The extension
/// variant is a typed non-answer: the artifact may be valid, but importing bytes
/// the decoder did not actually recover would be unsound.
#[derive(Debug)]
pub enum ModuleAdapterError {
    Region(RegionError),
    Decl(DeclError),
    Manifest(ModuleProvenanceError),
    Preflight(ModuleApplyPreflightError),
    Io(String),
    CapturedName(CapturedNameError),
    UnboundAttributeCensus,
    AttributeCensusEpochMismatch {
        artifact: ModuleEpoch,
        census: ModuleEpoch,
    },
    AttributePayloadMismatch {
        extension: fln_core::name::Name,
        ordinal: u64,
    },
    MissingAttributeTarget {
        attribute: fln_core::name::Name,
        target: fln_core::name::Name,
    },
    ArtifactDigestMismatch {
        expected: Digest,
        actual: Digest,
    },
    ArtifactEpochMismatch {
        part: &'static str,
        expected: ModuleEpoch,
        actual: ModuleEpoch,
    },
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
    OpaqueExtensionPayloadUnavailable {
        extension: String,
        entries: u64,
    },
}

impl fmt::Display for ModuleAdapterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Region(error) => write!(formatter, "olean region decode error: {error:?}"),
            Self::Decl(error) => write!(formatter, "olean decl decode error: {error:?}"),
            Self::Manifest(error) => {
                write!(formatter, "module provenance manifest error: {error:?}")
            }
            Self::Preflight(error) => write!(formatter, "module apply preflight error: {error:?}"),
            Self::Io(error) => write!(formatter, "I/O error: {error}"),
            Self::CapturedName(error) => write!(formatter, "attribute payload: {error}"),
            Self::UnboundAttributeCensus => write!(
                formatter,
                "tag import requires a census with a declared epoch"
            ),
            Self::AttributeCensusEpochMismatch { artifact, census } => write!(
                formatter,
                "attribute census epoch {census:?} differs from module artifact epoch {artifact:?}"
            ),
            Self::AttributePayloadMismatch { extension, ordinal } => write!(
                formatter,
                "tag payload {extension:?} entry {ordinal} disagrees with its decoded contribution"
            ),
            Self::MissingAttributeTarget { attribute, target } => write!(
                formatter,
                "tag attribute {attribute:?} names absent module declaration {target:?}"
            ),
            Self::ArtifactDigestMismatch { expected, actual } => write!(
                formatter,
                "artifact digest mismatch: expected {expected:?}, actual {actual:?}"
            ),
            Self::ArtifactEpochMismatch {
                part,
                expected,
                actual,
            } => write!(
                formatter,
                "{part} artifact epoch mismatch: expected {expected:?}, actual {actual:?}"
            ),
            Self::MissingDependency { module, dependency } => write!(
                formatter,
                "missing dependency {:?} for module {:?}",
                dependency.name().to_display_string(),
                module.name().to_display_string()
            ),
            Self::CyclicDependency { module } => write!(
                formatter,
                "cyclic import dependency involving {:?}",
                module.name().to_display_string()
            ),
            Self::StageMismatch { expected, actual } => write!(
                formatter,
                "batch stage count mismatch: expected {expected}, actual {actual}"
            ),
            Self::OpaqueExtensionPayloadUnavailable { extension, entries } => write!(
                formatter,
                "olean extension {extension:?} contains {entries} opaque entries without matching captured payloads; refusing to fabricate environment payload bytes"
            ),
        }
    }
}

impl std::error::Error for ModuleAdapterError {}

impl From<RegionError> for ModuleAdapterError {
    fn from(error: RegionError) -> Self {
        Self::Region(error)
    }
}

impl From<DeclError> for ModuleAdapterError {
    fn from(error: DeclError) -> Self {
        Self::Decl(error)
    }
}

impl From<ModuleProvenanceError> for ModuleAdapterError {
    fn from(error: ModuleProvenanceError) -> Self {
        Self::Manifest(error)
    }
}

impl From<ModuleApplyPreflightError> for ModuleAdapterError {
    fn from(error: ModuleApplyPreflightError) -> Self {
        Self::Preflight(error)
    }
}

impl From<legacy::ModuleAdapterError> for ModuleAdapterError {
    fn from(error: legacy::ModuleAdapterError) -> Self {
        match error {
            legacy::ModuleAdapterError::Region(error) => Self::Region(error),
            legacy::ModuleAdapterError::Decl(error) => Self::Decl(error),
            legacy::ModuleAdapterError::Manifest(error) => Self::Manifest(error),
            legacy::ModuleAdapterError::Preflight(error) => Self::Preflight(error),
            legacy::ModuleAdapterError::Io(error) => Self::Io(error),
            legacy::ModuleAdapterError::MissingDependency { module, dependency } => {
                Self::MissingDependency { module, dependency }
            }
            legacy::ModuleAdapterError::CyclicDependency { module } => {
                Self::CyclicDependency { module }
            }
            legacy::ModuleAdapterError::StageMismatch { expected, actual } => {
                Self::StageMismatch { expected, actual }
            }
        }
    }
}

fn require_lossless_extension_payloads(
    extensions: &[ExtensionBlock],
    contributions: &[fln_env::provenance::ExtensionContribution],
) -> Result<(), ModuleAdapterError> {
    if let Some(extension) = extensions.iter().find(|extension| {
        extension.entries != 0
            && !contributions.iter().any(|contribution| {
                contribution.descriptor().name.to_display_string() == extension.name
                    && contribution.entries().len() as u64 == extension.entries
            })
    }) {
        return Err(ModuleAdapterError::OpaqueExtensionPayloadUnavailable {
            extension: extension.name.clone(),
            entries: extension.entries,
        });
    }
    Ok(())
}

/// Olean module adapter converting raw `.olean` artifacts into environment inputs.
///
/// Unknown extension state is captured losslessly, with opaque provenance.
pub struct OleanModuleAdapter;

impl DecodedOleanModule {
    /// Interpret only census-bound tag entries and prepare their native state
    /// update. Other schemas retain their original opaque extension payloads.
    /// This imports stored data; it does not run an attribute's source-side
    /// validation callback or grant declaration admission authority.
    pub fn tag_attribute_plan(
        &self,
        base: &AttributeState,
        budget: WalkBudget,
        max_payload_bytes: usize,
    ) -> Result<AttributeStatePlan, ModuleAdapterError> {
        let census = base
            .census_epoch()
            .ok_or(ModuleAdapterError::UnboundAttributeCensus)?;
        let artifact = &self.evidence.epoch;
        fn epoch_tag(epoch: &ModuleEpoch) -> &str {
            epoch.tag().strip_prefix('v').unwrap_or(epoch.tag())
        }
        if epoch_tag(census) != epoch_tag(artifact) || census.commit() != artifact.commit() {
            return Err(ModuleAdapterError::AttributeCensusEpochMismatch {
                artifact: artifact.clone(),
                census: census.clone(),
            });
        }
        let bindings: std::collections::BTreeMap<_, _> = base
            .definitions()
            .iter()
            .filter(|(_, definition)| {
                definition.family == AttributeFamily::Tag
                    && definition.handler_class == HandlerClass::DataOnly
            })
            .filter_map(|(_, definition)| {
                definition
                    .serialized_extension
                    .as_ref()
                    .map(|key| (key, definition))
            })
            .collect();
        let selected: Vec<_> = self
            .extension_entries
            .iter()
            .filter_map(|entry| {
                bindings
                    .get(&entry.descriptor().name)
                    .map(|definition| (*definition, entry))
            })
            .collect();
        let payloads: Vec<_> = selected.iter().map(|(_, entry)| entry.payload()).collect();
        for (_, entry) in &selected {
            let expected = self
                .extension_contributions
                .get(entry.contribution_index())
                .filter(|contribution| contribution.descriptor() == entry.descriptor())
                .and_then(|contribution| {
                    usize::try_from(entry.source_ordinal())
                        .ok()
                        .and_then(|ordinal| contribution.entries().get(ordinal))
                });
            let actual = fln_env::provenance::ExtensionEntryId::derive(
                &self.evidence.epoch,
                entry.descriptor(),
                entry.payload(),
            );
            if expected != Some(&actual) {
                return Err(ModuleAdapterError::AttributePayloadMismatch {
                    extension: entry.descriptor().name.clone(),
                    ordinal: entry.source_ordinal(),
                });
            }
        }
        let names = decode_captured_names(&payloads, budget, max_payload_bytes)
            .map_err(ModuleAdapterError::CapturedName)?;
        let declarations: std::collections::BTreeSet<_> = self
            .constants
            .iter()
            .chain(&self.extra_constants)
            .map(|info| info.name())
            .collect();
        let mut assignments = Vec::new();
        for ((definition, entry), target) in selected.into_iter().zip(names) {
            if !declarations.contains(&target) {
                return Err(ModuleAdapterError::MissingAttributeTarget {
                    attribute: definition.name.clone(),
                    target,
                });
            }
            assignments.push(Assignment {
                attribute: definition.name.clone(),
                target,
                payload: Payload::Unit,
                kind: AttributeKind::Global,
                provenance: format!(
                    "module-tag:{}:{}:{}",
                    self.module_id.name().to_display_string(),
                    definition.row_id,
                    entry.source_ordinal()
                ),
            });
        }
        Ok(AttributeStatePlan::cut(base, assignments))
    }
}

fn require_artifact_digest(
    evidence: &ArtifactEvidence,
    actual: Digest,
) -> Result<(), ModuleAdapterError> {
    if evidence.content_digest != actual {
        return Err(ModuleAdapterError::ArtifactDigestMismatch {
            expected: evidence.content_digest,
            actual,
        });
    }
    Ok(())
}

fn require_artifact_epoch(
    evidence: &ArtifactEvidence,
    view: &OleanView<'_>,
    part: &'static str,
) -> Result<(), ModuleAdapterError> {
    let header = &view.header;
    // Release tags conventionally carry a leading `v`; the wire version may
    // omit it. No other version or commit normalization is permitted.
    let expected_version = evidence
        .epoch
        .tag()
        .strip_prefix('v')
        .unwrap_or(evidence.epoch.tag());
    let actual_version = header
        .lean_version
        .strip_prefix('v')
        .unwrap_or(&header.lean_version);
    if expected_version != actual_version || evidence.epoch.commit() != header.githash {
        return Err(ModuleAdapterError::ArtifactEpochMismatch {
            part,
            expected: evidence.epoch.clone(),
            actual: ModuleEpoch::new(header.lean_version.as_str(), header.githash.as_str()),
        });
    }
    Ok(())
}

impl OleanModuleAdapter {
    /// Digest a complete chain in exported/server/private role order.
    /// Length framing binds part boundaries, including otherwise ignored bytes.
    /// This computes identity only; it does not establish producer or grade.
    pub fn chain_content_digest(exported: &[u8], server: &[u8], private: &[u8]) -> Digest {
        let mut digest = DomainHasher::new(Domain::Fixture);
        digest.update(b"fln-module-chain-v1\0");
        for part in [exported, server, private] {
            digest.update(&(part.len() as u64).to_le_bytes());
            digest.update(part);
        }
        digest.finalize()
    }

    /// Decode a `.olean` artifact from memory bytes without fabricating extension data.
    ///
    /// The resolver supplies provenance. Its digest must be `hash(Domain::Fixture,
    /// bytes)` and its epoch must match the header. Producer and grade are retained
    /// as supplied assertions, never authenticated or promoted by decoding.
    pub fn decode_bytes(
        module_id: ModuleId,
        bytes: &[u8],
        evidence: ArtifactEvidence,
    ) -> Result<DecodedOleanModule, ModuleAdapterError> {
        require_artifact_digest(&evidence, hash(Domain::Fixture, bytes))?;
        let view = OleanView::parse(bytes)?;
        require_artifact_epoch(&evidence, &view, "standalone")?;
        let module_data = view.module_data(WalkBudget::default())?;
        let decoded = legacy::OleanModuleAdapter::decode_bytes(module_id, bytes, evidence)
            .map_err(ModuleAdapterError::from)?;
        require_lossless_extension_payloads(
            &module_data.extensions,
            &decoded.extension_contributions,
        )?;
        Ok(decoded)
    }

    /// Decode a complete exported/server/private chain at private import level.
    ///
    /// Shared declarations use their full private bodies, and declarations
    /// found only in the private companion become `extra_constants`. Extension
    /// entries come from the private level, retaining references to earlier
    /// parts; IR-only names remain metadata. No kernel checking is implied.
    /// The supplied evidence must bind [`Self::chain_content_digest`] and the
    /// epoch of every part. Its producer and grade remain resolver assertions.
    pub fn decode_chain_bytes(
        module_id: ModuleId,
        exported: &[u8],
        server: &[u8],
        private: &[u8],
        evidence: ArtifactEvidence,
        limits: ChainLimits,
    ) -> Result<DecodedOleanModule, ModuleAdapterError> {
        // Refuse oversized input before hashing or parsing any part, matching
        // the codec's byte-budget precedence. Graph work remains codec-owned.
        let total = exported
            .len()
            .checked_add(server.len())
            .and_then(|total| total.checked_add(private.len()))
            .ok_or(DeclError::ChainTooLarge {
                bytes: usize::MAX,
                limit: limits.max_bytes,
            })?;
        if total > limits.max_bytes {
            return Err(DeclError::ChainTooLarge {
                bytes: total,
                limit: limits.max_bytes,
            }
            .into());
        }
        require_artifact_digest(
            &evidence,
            Self::chain_content_digest(exported, server, private),
        )?;
        for (part, bytes, dependencies) in [
            ("exported", exported, &[][..]),
            ("server", server, &[exported][..]),
            ("private", private, &[exported, server][..]),
        ] {
            let view = OleanView::parse_with_dependencies(bytes, dependencies)?;
            require_artifact_epoch(&evidence, &view, part)?;
        }
        let decoded = legacy::OleanModuleAdapter::decode_chain_bytes(
            module_id, exported, server, private, evidence, limits,
        )?;
        let view = OleanView::parse_with_dependencies(private, &[exported, server])?;
        require_lossless_extension_payloads(
            &view.module_data(limits.graph)?.extensions,
            &decoded.extension_contributions,
        )?;
        Ok(decoded)
    }

    /// Decode a `.olean` artifact from a filesystem file.
    /// The resolver's expected digest is checked against the bytes actually read.
    pub fn decode_file(
        module_id: ModuleId,
        path: impl AsRef<Path>,
        evidence: ArtifactEvidence,
    ) -> Result<DecodedOleanModule, ModuleAdapterError> {
        let path = path.as_ref();
        let bytes = fs::read(path).map_err(|error| {
            ModuleAdapterError::Io(format!("failed to read {}: {error}", path.display()))
        })?;
        Self::decode_bytes(module_id, &bytes, evidence)
    }

    /// Build a transaction from an already fail-closed decoded module.
    pub fn build_transaction(
        decoded: &DecodedOleanModule,
        manifest: Arc<ModuleProvenanceManifest>,
        completeness: ProvenanceCompleteness,
    ) -> Result<ModuleApplyTransaction, ModuleAdapterError> {
        legacy::OleanModuleAdapter::build_transaction(decoded, manifest, completeness)
            .map_err(ModuleAdapterError::from)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::name::Name;
    use fln_env::modules::{ArtifactGrade, ArtifactProducer};
    use fln_olean::format;
    use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};

    fn native_evidence(content_digest: Digest) -> ArtifactEvidence {
        ArtifactEvidence {
            epoch: ModuleEpoch::new(format::PIN_TAG, format::PIN_COMMIT),
            content_digest,
            producer: ArtifactProducer::FrankenLean,
            grade: ArtifactGrade::Provisional,
        }
    }

    #[test]
    fn counts_without_opaque_payloads_are_typed_refusals() {
        let error = require_lossless_extension_payloads(
            &[ExtensionBlock {
                name: "Lean.Parser.Extension".to_owned(),
                entries: 3,
            }],
            &[],
        )
        .expect_err("opaque payload counts are not payload bytes");
        assert!(matches!(
            &error,
            ModuleAdapterError::OpaqueExtensionPayloadUnavailable { extension, entries }
                if extension == "Lean.Parser.Extension" && *entries == 3
        ));
        assert!(error.to_string().contains("refusing to fabricate"));
    }

    #[test]
    fn zero_entry_extension_blocks_require_no_synthetic_payload() {
        require_lossless_extension_payloads(
            &[
                ExtensionBlock {
                    name: "Empty.First".to_owned(),
                    entries: 0,
                },
                ExtensionBlock {
                    name: "Empty.Second".to_owned(),
                    entries: 0,
                },
            ],
            &[],
        )
        .expect("empty extension arrays carry no environment delta");
    }

    #[test]
    fn chain_adapter_routes_declarations_and_binds_every_part_without_promoting_ir_names() {
        use fln_core::expr::Expr;
        use fln_core::level::Level;
        use fln_env::constants::{
            AxiomVal, ConstantInfo, ConstantVal, DefinitionSafety, DefinitionVal, ReducibilityHints,
        };
        let name = |label| Name::str(Name::anonymous(), label);
        let shared_name = Name::str(name("_private"), "Shared");
        let extra_name = name("CompanionOnly");
        let definition = |name: Name| {
            ConstantInfo::Defn(DefinitionVal {
                base: ConstantVal {
                    name: name.clone(),
                    level_params: vec![],
                    type_: Expr::sort(Level::succ(Level::zero()).unwrap()),
                },
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Opaque,
                safety: DefinitionSafety::Safe,
                all: vec![name],
            })
        };
        let shared = definition(shared_name);
        let extra = definition(extra_name.clone());
        let axiom = ConstantInfo::Axiom(AxiomVal {
            base: shared.constant_val().clone(),
            is_unsafe: false,
        });
        let exported_ir = name("ExportedIR");
        let private_ir = name("PrivateIR");
        let encode = |constants: &[ConstantInfo], ir_names: &[Name], base| {
            encode_module(
                ModuleWriteInput {
                    is_module: true,
                    imports: &[],
                    constants,
                    extra_const_names: ir_names,
                },
                OleanWriteHeader {
                    version: 2,
                    flags: 1,
                    lean_version: format::PIN_TAG,
                    githash: format::PIN_COMMIT,
                    base_addr: base,
                },
                WriteBudget::default(),
            )
            .unwrap()
            .bytes
        };
        let parts = [
            encode(
                std::slice::from_ref(&axiom),
                std::slice::from_ref(&exported_ir),
                format::REGION_ALIGN as u64,
            ),
            encode(&[axiom], &[], 2 * format::REGION_ALIGN as u64),
            encode(
                &[shared.clone(), extra.clone()],
                &[private_ir.clone(), extra_name.clone()],
                3 * format::REGION_ALIGN as u64,
            ),
        ];
        let total = parts.iter().map(Vec::len).sum();
        let module = ModuleId::new(name("Chain"));
        let evidence_for = |parts: &[Vec<u8>; 3]| {
            native_evidence(OleanModuleAdapter::chain_content_digest(
                &parts[0], &parts[1], &parts[2],
            ))
        };
        let decode = |parts: &[Vec<u8>; 3], limits| {
            OleanModuleAdapter::decode_chain_bytes(
                module.clone(),
                &parts[0],
                &parts[1],
                &parts[2],
                evidence_for(parts),
                limits,
            )
        };
        let decoded = decode(&parts, ChainLimits::new(total)).unwrap();
        assert_eq!(decoded.evidence, evidence_for(&parts));
        assert_eq!(decoded.to_module_record().artifact, evidence_for(&parts));
        assert_eq!(decoded.constants, vec![Arc::new(shared)]);
        assert_eq!(decoded.extra_constants, vec![Arc::new(extra)]);
        assert_eq!(
            decoded.ir_extra_const_names,
            vec![exported_ir.clone(), private_ir, extra_name]
        );
        assert_eq!(decoded.payload_bytes, total);
        assert!(decoded.extension_entries.is_empty());
        let exported_only = OleanModuleAdapter::decode_bytes(
            module.clone(),
            &parts[0],
            native_evidence(hash(Domain::Fixture, &parts[0])),
        )
        .unwrap();
        assert_eq!(exported_only.ir_extra_const_names, vec![exported_ir]);
        assert!(matches!(
            exported_only.constants[0].as_ref(),
            ConstantInfo::Axiom(_)
        ));

        // Ignored bytes after the version string's NUL affect artifact identity
        // without changing decoded declarations or the chain identity stamp.
        let version_field = format::OLEAN_HEADER_FIELDS
            .iter()
            .find(|field| field.name == "lean_version")
            .unwrap();
        let padding = version_field.offset + version_field.size - 1;
        for role in 0..parts.len() {
            let mut changed = parts.clone();
            assert_eq!(changed[role][padding], 0);
            changed[role][padding] = 0xAB;
            assert!(matches!(
                OleanModuleAdapter::decode_chain_bytes(
                    module.clone(), &changed[0], &changed[1], &changed[2],
                    decoded.evidence.clone(), ChainLimits::new(total)
                ),
                Err(ModuleAdapterError::ArtifactDigestMismatch { expected, actual })
                    if expected == decoded.evidence.content_digest && actual == evidence_for(&changed).content_digest
            ));
            let changed = decode(&changed, ChainLimits::new(total)).unwrap();
            assert_ne!(
                changed.evidence.content_digest, decoded.evidence.content_digest,
                "part {role} must affect the digest"
            );
            assert_eq!(changed.constants, decoded.constants);
            assert_eq!(changed.extra_constants, decoded.extra_constants);
            assert_eq!(changed.ir_extra_const_names, decoded.ir_extra_const_names);
        }
        // A freshly bound digest does not excuse a stale header in any part.
        let commit_offset = format::OLEAN_HEADER_FIELDS
            .iter()
            .find(|field| field.name == "githash")
            .unwrap()
            .offset;
        for (role, part_name) in ["exported", "server", "private"].into_iter().enumerate() {
            let mut changed = parts.clone();
            changed[role][commit_offset] = b'0';
            assert!(matches!(
                decode(&changed, ChainLimits::new(total)),
                Err(ModuleAdapterError::ArtifactEpochMismatch { part, expected, actual })
                    if part == part_name && expected == decoded.evidence.epoch && actual.commit() != expected.commit()
            ));
        }
        assert_ne!(
            OleanModuleAdapter::chain_content_digest(b"a", b"bc", b"d"),
            OleanModuleAdapter::chain_content_digest(b"ab", b"c", b"d"),
            "part boundaries are included in identity",
        );
        assert!(matches!(
            decode(&parts, ChainLimits::new(total - 1)),
            Err(ModuleAdapterError::Decl(DeclError::ChainTooLarge { .. }))
        ));
        assert!(matches!(
            decode(
                &parts,
                ChainLimits {
                    max_bytes: total,
                    graph: WalkBudget { max_objects: 0 }
                }
            ),
            Err(ModuleAdapterError::Decl(DeclError::Region(
                RegionError::BudgetExhausted { .. }
            )))
        ));
        assert_eq!(
            decode(&parts, ChainLimits::new(total)).unwrap().evidence,
            decoded.evidence
        );
    }

    #[test]
    fn extension_free_olean_decodes_without_synthetic_entries() {
        let encoded = encode_module(
            ModuleWriteInput {
                is_module: true,
                imports: &[],
                constants: &[],
                extra_const_names: &[],
            },
            OleanWriteHeader {
                version: 2,
                flags: 1,
                lean_version: format::PIN_TAG,
                githash: format::PIN_COMMIT,
                base_addr: format::REGION_ALIGN as u64,
            },
            WriteBudget::default(),
        )
        .expect("empty module encodes");
        let decoded = OleanModuleAdapter::decode_bytes(
            ModuleId::new(Name::str(Name::anonymous(), "Empty")),
            &encoded.bytes,
            native_evidence(hash(Domain::Fixture, &encoded.bytes)),
        )
        .expect("extension-free module remains decodable");
        assert!(decoded.extension_entries.is_empty());
        assert!(decoded.extension_contributions.is_empty());
        assert_eq!(
            decoded.evidence,
            native_evidence(hash(Domain::Fixture, &encoded.bytes))
        );
        // These are caller-asserted grades, not proof that this native fixture
        // is verified or oracle-produced. Decoding must preserve each assertion.
        for grade in [
            ArtifactGrade::Provisional,
            ArtifactGrade::Verified,
            ArtifactGrade::OracleFixture,
        ] {
            let mut evidence = decoded.evidence.clone();
            evidence.grade = grade;
            let replay = OleanModuleAdapter::decode_bytes(
                decoded.module_id.clone(),
                &encoded.bytes,
                evidence.clone(),
            )
            .unwrap();
            assert_eq!(replay.evidence, evidence);
            assert_eq!(replay.to_module_record().artifact, evidence);
        }
        for epoch in [
            ModuleEpoch::new("v0.0.0", format::PIN_COMMIT),
            ModuleEpoch::new(format::PIN_TAG, "0000000000000000000000000000000000000000"),
        ] {
            let mut evidence = decoded.evidence.clone();
            evidence.epoch = epoch.clone();
            assert!(matches!(
                OleanModuleAdapter::decode_bytes(
                    decoded.module_id.clone(), &encoded.bytes, evidence,
                ),
                Err(ModuleAdapterError::ArtifactEpochMismatch { part: "standalone", expected, .. }) if expected == epoch
            ));
        }
        let mut stale = decoded.evidence.clone();
        stale.content_digest = hash(Domain::Fixture, b"different bytes");
        assert!(matches!(
            OleanModuleAdapter::decode_bytes(decoded.module_id.clone(), &encoded.bytes, stale.clone()),
            Err(ModuleAdapterError::ArtifactDigestMismatch { expected, actual })
                if expected == stale.content_digest && actual == decoded.evidence.content_digest
        ));
    }
}
