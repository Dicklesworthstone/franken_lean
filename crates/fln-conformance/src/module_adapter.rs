//! Fail-closed `.olean` → environment adapter boundary.
//!
//! The compacted-region reader currently proves the integrity and cardinality of
//! environment-extension entry arrays, but it does not expose the opaque entry
//! roots or a lossless serialization of their payloads. The former adapter
//! incorrectly substituted the extension name bytes for every payload and marked
//! those bytes as understood provenance. That silently changed module semantics.
//!
//! This facade preserves the existing batch-coordinator implementation and public
//! types while refusing nonempty extension blocks until the region layer can
//! provide lossless payload bytes. Zero-entry blocks contribute no state and are
//! stripped rather than converted into synthetic payloads.

use std::fmt;
use std::fs;
use std::path::Path;
use std::sync::Arc;

use fln_env::module_apply::{ModuleApplyPreflightError, ModuleApplyTransaction};
use fln_env::modules::{ModuleEpoch, ModuleId};
use fln_env::provenance::{
    ModuleProvenanceError, ModuleProvenanceManifest, ProvenanceCompleteness,
};
use fln_olean::decl::DeclError;
use fln_olean::region::{ExtensionBlock, OleanView, RegionError, WalkBudget};

mod legacy;

pub use legacy::{
    CommittedModuleBatchResult, DecodedOleanModule, ModuleBatchApplyPlan,
    ModuleBatchCommitError, ModuleBatchPlanError, ModuleBatchUsageSummary,
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
            Self::Manifest(error) => write!(formatter, "module provenance manifest error: {error:?}"),
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
                "olean extension {extension:?} contains {entries} opaque entries, but the region decoder exposes only their count; refusing to fabricate environment payload bytes"
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
) -> Result<(), ModuleAdapterError> {
    if let Some(extension) = extensions.iter().find(|extension| extension.entries != 0) {
        return Err(ModuleAdapterError::OpaqueExtensionPayloadUnavailable {
            extension: extension.name.clone(),
            entries: extension.entries,
        });
    }
    Ok(())
}

/// Olean module adapter converting raw `.olean` artifacts into environment inputs.
///
/// Declaration and import decoding retain the existing implementation. Extension
/// state is admitted only when it is semantically empty; nonempty opaque blocks
/// are a typed refusal until their exact payloads are recoverable.
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
        require_lossless_extension_payloads(&module_data.extensions)?;

        let mut decoded = legacy::OleanModuleAdapter::decode_bytes(module_id, bytes, epoch)
            .map_err(ModuleAdapterError::from)?;
        // The legacy implementation synthesized one name-byte payload even for
        // an empty entry array. Empty arrays carry no environment delta.
        decoded.extension_entries.clear();
        decoded.extension_contributions.clear();
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
    fn nonempty_opaque_extension_blocks_are_typed_refusals() {
        let error = require_lossless_extension_payloads(&[ExtensionBlock {
            name: "Lean.Parser.Extension".to_owned(),
            entries: 3,
        }])
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
        require_lossless_extension_payloads(&[
            ExtensionBlock {
                name: "Empty.First".to_owned(),
                entries: 0,
            },
            ExtensionBlock {
                name: "Empty.Second".to_owned(),
                entries: 0,
            },
        ])
        .expect("empty extension arrays carry no environment delta");
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
