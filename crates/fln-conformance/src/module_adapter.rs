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

use fln_env::module_apply::{ModuleApplyPreflightError, ModuleApplyTransaction};
use fln_env::modules::{ModuleEpoch, ModuleId};
use fln_env::provenance::{
    ModuleProvenanceError, ModuleProvenanceManifest, ProvenanceCompleteness,
};
use fln_olean::decl::{ChainLimits, DeclError};
use fln_olean::region::{ExtensionBlock, OleanView, RegionError, WalkBudget};

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

impl OleanModuleAdapter {
    /// Decode a `.olean` artifact from memory bytes without fabricating extension data.
    pub fn decode_bytes(
        module_id: ModuleId,
        bytes: &[u8],
        epoch: ModuleEpoch,
    ) -> Result<DecodedOleanModule, ModuleAdapterError> {
        let view = OleanView::parse(bytes)?;
        let module_data = view.module_data(WalkBudget::default())?;
        let decoded = legacy::OleanModuleAdapter::decode_bytes(module_id, bytes, epoch)
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
    pub fn decode_chain_bytes(
        module_id: ModuleId,
        exported: &[u8],
        server: &[u8],
        private: &[u8],
        epoch: ModuleEpoch,
        limits: ChainLimits,
    ) -> Result<DecodedOleanModule, ModuleAdapterError> {
        let decoded = legacy::OleanModuleAdapter::decode_chain_bytes(
            module_id, exported, server, private, epoch, limits,
        )?;
        let view = OleanView::parse_with_dependencies(private, &[exported, server])?;
        require_lossless_extension_payloads(
            &view.module_data(limits.graph)?.extensions,
            &decoded.extension_contributions,
        )?;
        Ok(decoded)
    }

    /// Decode a `.olean` artifact from a filesystem file.
    pub fn decode_file(
        module_id: ModuleId,
        path: impl AsRef<Path>,
        epoch: ModuleEpoch,
    ) -> Result<DecodedOleanModule, ModuleAdapterError> {
        let path = path.as_ref();
        let bytes = fs::read(path).map_err(|error| {
            ModuleAdapterError::Io(format!("failed to read {}: {error}", path.display()))
        })?;
        Self::decode_bytes(module_id, &bytes, epoch)
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
    use fln_olean::format;
    use fln_olean::write::{ModuleWriteInput, OleanWriteHeader, WriteBudget, encode_module};

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
        let epoch = ModuleEpoch::new(format::PIN_TAG, format::PIN_COMMIT);
        let decode = |parts: &[Vec<u8>; 3], limits| {
            OleanModuleAdapter::decode_chain_bytes(
                module.clone(),
                &parts[0],
                &parts[1],
                &parts[2],
                epoch.clone(),
                limits,
            )
        };
        let decoded = decode(&parts, ChainLimits::new(total)).unwrap();
        assert_eq!(decoded.constants, vec![Arc::new(shared)]);
        assert_eq!(decoded.extra_constants, vec![Arc::new(extra)]);
        assert_eq!(
            decoded.ir_extra_const_names,
            vec![exported_ir.clone(), private_ir, extra_name]
        );
        assert_eq!(decoded.payload_bytes, total);
        assert!(decoded.extension_entries.is_empty());
        let exported_only =
            OleanModuleAdapter::decode_bytes(module.clone(), &parts[0], epoch.clone()).unwrap();
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
            let changed = decode(&changed, ChainLimits::new(total)).unwrap();
            assert_ne!(
                changed.evidence.content_digest, decoded.evidence.content_digest,
                "part {role} must affect the digest"
            );
            assert_eq!(changed.constants, decoded.constants);
            assert_eq!(changed.extra_constants, decoded.extra_constants);
            assert_eq!(changed.ir_extra_const_names, decoded.ir_extra_const_names);
        }
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
            ModuleEpoch::new(format::PIN_TAG, format::PIN_COMMIT),
        )
        .expect("extension-free module remains decodable");
        assert!(decoded.extension_entries.is_empty());
        assert!(decoded.extension_contributions.is_empty());
    }
}
