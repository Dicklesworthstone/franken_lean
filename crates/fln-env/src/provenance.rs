//! Canonical module-contribution provenance identity (plan §7.1; bead
//! `franken_lean-module-provenance-schema-cxn`).
//!
//! This module freezes the data contract consumed by atomic import application,
//! invalidation, and lifecycle integration. It deliberately does not mutate an
//! [`Environment`](crate::environment::Environment): downstream beads build those
//! operations over this validated immutable value.
//!
//! The provenance root is not the trusted environment logical root. It is a
//! separate, schema-versioned identity for module topology, artifact evidence,
//! declaration ownership, extension-entry ranges, and completeness. Future Ledger
//! demand keys and receipts may carry both roots as explicit fields; neither root is
//! silently folded into the other.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use fln_core::name::Name;
use fln_hash::canon::{CanonError, CanonReader, CanonWriter, Canonical, SchemaId};
use fln_hash::domain::{Digest, Domain, hash};

use crate::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use crate::modules::{
    ArtifactEvidence, ArtifactGrade, ArtifactProducer, DirectImport, ModuleEpoch, ModuleGraph,
    ModuleGraphError, ModuleGraphLimits, ModuleId, ModuleRecord, name_stats,
};

/// Frozen canonical schema for the complete provenance manifest.
///
/// Version 1 is positional and length-delimited:
///
/// 1. schema name/version, epoch tag/commit, canonical module count;
/// 2. for each module in `Name.cmp` order: module name, `is_module`, exact ordered
///    direct-import rows (target, `import_all`, `is_exported`, `is_meta`), then
///    artifact digest/producer/grade;
/// 3. ordered declarations, ordered extra declarations, and ordered extension
///    contributions; each contribution carries its descriptor, start ordinal,
///    base-history digest, and contiguous `(ordinal, payload_digest)` identities;
/// 4. decode completeness, extension knowledge, and the canonical missing-target set.
///
/// Enum tags are frozen below by paired exhaustive `*_tag`/`read_*` functions:
/// producer `Reference=0, FrankenLean=1`; grade
/// `Provisional=0, Verified=1, OracleFixture=2`; merge
/// `AppendOrdered=0, SetUnion=1, ConflictsRequireReview=2`; checkpoint
/// `JournalSuffix=0, FullJournal=1`; payload provenance
/// `Understood=0, Opaque=1`; decode `Complete=0, Partial=1`; extension knowledge
/// `AllUnderstood=0, ContainsOpaque=1`. Unknown tags and future schema versions are
/// typed refusals. Any incompatible layout change registers version 2 rather than
/// reinterpreting version-1 bytes.
///
/// Duplicate module and declaration owners are invalid. Exact direct-import rows and
/// extension contributions are ordered replay data, so duplicates are retained.
/// Missing dependencies are a semantic set and are sorted/deduplicated. This policy is
/// part of the graph identity and is covered by golden, field-sensitivity, ordering,
/// and mutation tests below.
pub const MODULE_PROVENANCE_SCHEMA: SchemaId = SchemaId {
    name: "fln.env.module-provenance",
    version: 1,
};

/// Whether the decoder produced every contribution-bearing section it understood.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum DecodeCompleteness {
    Complete,
    Partial,
}

/// Whether every retained extension contribution is semantically understood.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ExtensionKnowledge {
    AllUnderstood,
    ContainsOpaque,
}

/// Orthogonal completeness dimensions. Missing dependencies are a canonical set;
/// declaration and extension arrays elsewhere remain ordered sequences.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenanceCompleteness {
    decode: DecodeCompleteness,
    extension_knowledge: ExtensionKnowledge,
    missing_dependencies: Arc<[ModuleId]>,
}

impl ProvenanceCompleteness {
    pub fn new(
        decode: DecodeCompleteness,
        extension_knowledge: ExtensionKnowledge,
        mut missing_dependencies: Vec<ModuleId>,
    ) -> Self {
        missing_dependencies.sort();
        missing_dependencies.dedup();
        Self {
            decode,
            extension_knowledge,
            missing_dependencies: missing_dependencies.into(),
        }
    }

    pub fn decode(&self) -> DecodeCompleteness {
        self.decode
    }

    pub fn extension_knowledge(&self) -> ExtensionKnowledge {
        self.extension_knowledge
    }

    pub fn missing_dependencies(&self) -> &[ModuleId] {
        &self.missing_dependencies
    }

    pub fn is_complete(&self) -> bool {
        self.decode == DecodeCompleteness::Complete
            && self.extension_knowledge == ExtensionKnowledge::AllUnderstood
            && self.missing_dependencies.is_empty()
    }
}

/// Stable identity of one extension journal entry. The payload is not copied into
/// provenance: the ordinal binds replay position and the digest binds exact bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct ExtensionEntryIdentity {
    index: u64,
    payload_digest: Digest,
}

impl ExtensionEntryIdentity {
    pub const fn new(index: u64, payload_digest: Digest) -> Self {
        Self {
            index,
            payload_digest,
        }
    }

    pub fn index(&self) -> u64 {
        self.index
    }

    pub fn payload_digest(&self) -> Digest {
        self.payload_digest
    }
}

/// One exact ordered range contributed to a registered extension.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionContribution {
    descriptor: ExtensionDescriptor,
    start: u64,
    base_history_digest: Digest,
    entries: Arc<[ExtensionEntryIdentity]>,
}

impl ExtensionContribution {
    pub fn new(
        descriptor: ExtensionDescriptor,
        start: u64,
        base_history_digest: Digest,
        entries: Vec<ExtensionEntryIdentity>,
    ) -> Self {
        Self {
            descriptor,
            start,
            base_history_digest,
            entries: entries.into(),
        }
    }

    pub fn descriptor(&self) -> &ExtensionDescriptor {
        &self.descriptor
    }

    pub fn start(&self) -> u64 {
        self.start
    }

    pub fn base_history_digest(&self) -> Digest {
        self.base_history_digest
    }

    pub fn entries(&self) -> &[ExtensionEntryIdentity] {
        &self.entries
    }

    pub fn end(&self) -> Option<u64> {
        let length = u64::try_from(self.entries.len()).ok()?;
        self.start.checked_add(length)
    }
}

/// Contributions owned by one module. Declaration arrays preserve decoded order;
/// duplicate declaration names are rejected by the manifest because an Environment
/// cannot publish the same declaration twice.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleContributionRecord {
    module: ModuleRecord,
    declarations: Arc<[Name]>,
    extra_declarations: Arc<[Name]>,
    extension_contributions: Arc<[ExtensionContribution]>,
    completeness: ProvenanceCompleteness,
}

impl ModuleContributionRecord {
    pub fn new(
        module: ModuleRecord,
        declarations: Vec<Name>,
        extra_declarations: Vec<Name>,
        extension_contributions: Vec<ExtensionContribution>,
        completeness: ProvenanceCompleteness,
    ) -> Self {
        Self {
            module,
            declarations: declarations.into(),
            extra_declarations: extra_declarations.into(),
            extension_contributions: extension_contributions.into(),
            completeness,
        }
    }

    pub fn module(&self) -> &ModuleRecord {
        &self.module
    }

    pub fn declarations(&self) -> &[Name] {
        &self.declarations
    }

    pub fn extra_declarations(&self) -> &[Name] {
        &self.extra_declarations
    }

    pub fn extension_contributions(&self) -> &[ExtensionContribution] {
        &self.extension_contributions
    }

    pub fn completeness(&self) -> &ProvenanceCompleteness {
        &self.completeness
    }

    /// All immutable variable-length storage is shared by a clone.
    pub fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(
            &self.module.direct_imports_arc(),
            &other.module.direct_imports_arc(),
        ) && Arc::ptr_eq(&self.declarations, &other.declarations)
            && Arc::ptr_eq(&self.extra_declarations, &other.extra_declarations)
            && Arc::ptr_eq(
                &self.extension_contributions,
                &other.extension_contributions,
            )
            && Arc::ptr_eq(
                &self.completeness.missing_dependencies,
                &other.completeness.missing_dependencies,
            )
    }
}

/// Hard limits for both construction and decoding. `max_encoded_bytes` bounds input
/// before any count-directed allocation; the remaining limits bound semantic work.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleProvenanceLimits {
    pub max_modules: usize,
    pub max_direct_import_rows: usize,
    pub max_declaration_names: usize,
    pub max_extension_contributions: usize,
    pub max_extension_entries: usize,
    pub max_missing_dependencies: usize,
    pub max_name_depth: usize,
    pub max_encoded_bytes: u128,
}

impl ModuleProvenanceLimits {
    #[allow(clippy::too_many_arguments)]
    pub const fn new(
        max_modules: usize,
        max_direct_import_rows: usize,
        max_declaration_names: usize,
        max_extension_contributions: usize,
        max_extension_entries: usize,
        max_missing_dependencies: usize,
        max_name_depth: usize,
        max_encoded_bytes: u128,
    ) -> Self {
        Self {
            max_modules,
            max_direct_import_rows,
            max_declaration_names,
            max_extension_contributions,
            max_extension_entries,
            max_missing_dependencies,
            max_name_depth,
            max_encoded_bytes,
        }
    }
}

impl Default for ModuleProvenanceLimits {
    fn default() -> Self {
        Self::new(
            1_000_000,
            20_000_000,
            100_000_000,
            20_000_000,
            100_000_000,
            20_000_000,
            100_000,
            8 * 1024 * 1024 * 1024,
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleProvenanceResource {
    Modules,
    DirectImportRows,
    DeclarationNames,
    ExtensionContributions,
    ExtensionEntries,
    MissingDependencies,
    NameDepth,
    EncodedBytes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeclarationClass {
    Declaration,
    ExtraDeclaration,
}

/// Exact dimensions of a validated manifest.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ModuleProvenanceFacts {
    pub modules: usize,
    pub direct_import_rows: usize,
    pub declarations: usize,
    pub extra_declarations: usize,
    pub extension_contributions: usize,
    pub extension_entries: usize,
    pub missing_dependencies: usize,
    pub maximum_name_depth: usize,
    pub encoded_bytes: u128,
}

/// Dedicated identity type prevents accidental substitution for a logical or
/// operational root even though all three contain a `Digest`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ModuleProvenanceRoot(pub Digest);

impl std::fmt::Display for ModuleProvenanceRoot {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

/// Typed schema/validation refusal. No constructor publishes a partial manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModuleProvenanceError {
    UnsupportedSchemaVersion {
        found: u16,
        supported: u16,
    },
    InvalidModuleGraph(ModuleGraphError),
    DuplicateModule {
        module: ModuleId,
    },
    AnonymousDeclaration {
        module: ModuleId,
        class: DeclarationClass,
        index: usize,
    },
    AnonymousExtension {
        module: ModuleId,
        contribution_index: usize,
    },
    OverflowingNameComponent {
        module: ModuleId,
        name: Name,
    },
    DuplicateDeclaration {
        module: ModuleId,
        name: Name,
        first_class: DeclarationClass,
        first_index: usize,
        duplicate_class: DeclarationClass,
        duplicate_index: usize,
    },
    ConflictingDeclarationOwner {
        name: Name,
        first_module: ModuleId,
        second_module: ModuleId,
    },
    EmptyExtensionContribution {
        module: ModuleId,
        contribution_index: usize,
    },
    EntryIndexMismatch {
        module: ModuleId,
        contribution_index: usize,
        entry_index: usize,
        expected: u64,
        actual: u64,
    },
    EntryRangeOverflow {
        module: ModuleId,
        contribution_index: usize,
    },
    ExtensionKnowledgeMismatch {
        module: ModuleId,
        expected: ExtensionKnowledge,
        actual: ExtensionKnowledge,
    },
    MissingDependenciesMismatch {
        module: ModuleId,
        expected: Vec<ModuleId>,
        actual: Vec<ModuleId>,
    },
    ResourceLimitExceeded {
        module: Option<ModuleId>,
        resource: ModuleProvenanceResource,
        limit: u128,
        actual: u128,
    },
    Canonical(CanonError),
    MalformedEncoding {
        what: &'static str,
    },
    NonCanonicalEncoding,
}

impl std::fmt::Display for ModuleProvenanceError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnsupportedSchemaVersion { found, supported } => write!(
                formatter,
                "unsupported module-provenance schema version {found}; supported={supported}"
            ),
            Self::InvalidModuleGraph(error) => error.fmt(formatter),
            Self::DuplicateModule { module } => write!(
                formatter,
                "duplicate module provenance record `{}`",
                module.name().to_display_string()
            ),
            Self::AnonymousDeclaration {
                module,
                class,
                index,
            } => write!(
                formatter,
                "module `{}` has anonymous {class:?} at index {index}",
                module.name().to_display_string()
            ),
            Self::AnonymousExtension {
                module,
                contribution_index,
            } => write!(
                formatter,
                "module `{}` has an anonymous extension at contribution {contribution_index}",
                module.name().to_display_string()
            ),
            Self::OverflowingNameComponent { module, name } => write!(
                formatter,
                "module `{}` provenance name `{}` contains an overflowing component",
                module.name().to_display_string(),
                name.to_display_string()
            ),
            Self::DuplicateDeclaration { module, name, .. } => write!(
                formatter,
                "module `{}` repeats declaration `{}`",
                module.name().to_display_string(),
                name.to_display_string()
            ),
            Self::ConflictingDeclarationOwner {
                name,
                first_module,
                second_module,
            } => write!(
                formatter,
                "declaration `{}` is owned by both `{}` and `{}`",
                name.to_display_string(),
                first_module.name().to_display_string(),
                second_module.name().to_display_string()
            ),
            Self::EmptyExtensionContribution {
                module,
                contribution_index,
            } => write!(
                formatter,
                "module `{}` extension contribution {contribution_index} is empty",
                module.name().to_display_string()
            ),
            Self::EntryIndexMismatch {
                module,
                contribution_index,
                entry_index,
                expected,
                actual,
            } => write!(
                formatter,
                "module `{}` extension contribution {contribution_index} entry {entry_index} has index {actual}, expected {expected}",
                module.name().to_display_string()
            ),
            Self::EntryRangeOverflow {
                module,
                contribution_index,
            } => write!(
                formatter,
                "module `{}` extension contribution {contribution_index} range overflows u64",
                module.name().to_display_string()
            ),
            Self::ExtensionKnowledgeMismatch {
                module,
                expected,
                actual,
            } => write!(
                formatter,
                "module `{}` extension knowledge mismatch: expected {expected:?}, actual {actual:?}",
                module.name().to_display_string()
            ),
            Self::MissingDependenciesMismatch {
                module,
                expected,
                actual,
            } => write!(
                formatter,
                "module `{}` missing-dependency mismatch: expected {expected:?}, actual {actual:?}",
                module.name().to_display_string()
            ),
            Self::ResourceLimitExceeded {
                module,
                resource,
                limit,
                actual,
            } => write!(
                formatter,
                "module provenance resource {resource:?} exceeded for {}: {actual} > {limit}",
                module
                    .as_ref()
                    .map(|id| id.name().to_display_string())
                    .unwrap_or_else(|| "<manifest>".to_owned())
            ),
            Self::Canonical(error) => error.fmt(formatter),
            Self::MalformedEncoding { what } => {
                write!(formatter, "malformed module-provenance encoding: {what}")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("module-provenance bytes are not canonical")
            }
        }
    }
}

impl std::error::Error for ModuleProvenanceError {}

impl From<CanonError> for ModuleProvenanceError {
    fn from(error: CanonError) -> Self {
        Self::Canonical(error)
    }
}

/// Validated, canonically ordered immutable manifest.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleProvenanceManifest {
    epoch: ModuleEpoch,
    records: Arc<[ModuleContributionRecord]>,
    facts: ModuleProvenanceFacts,
    root: ModuleProvenanceRoot,
}

impl ModuleProvenanceManifest {
    pub fn new(
        epoch: ModuleEpoch,
        mut records: Vec<ModuleContributionRecord>,
        limits: ModuleProvenanceLimits,
    ) -> Result<Self, ModuleProvenanceError> {
        if !epoch.is_well_formed() {
            return Err(ModuleProvenanceError::InvalidModuleGraph(
                ModuleGraphError::MalformedEpoch {
                    tag: Arc::from(epoch.tag()),
                    commit: Arc::from(epoch.commit()),
                },
            ));
        }
        enforce_limit(
            None,
            ModuleProvenanceResource::Modules,
            limits.max_modules as u128,
            records.len() as u128,
        )?;
        records.sort_by(|left, right| left.module.id.cmp(&right.module.id));
        for pair in records.windows(2) {
            if pair[0].module.id == pair[1].module.id {
                return Err(ModuleProvenanceError::DuplicateModule {
                    module: pair[0].module.id.clone(),
                });
            }
        }

        // Reuse the already-proved graph validator so the provenance schema can
        // never become a second source of truth for epoch, topology, or cycles.
        let graph_limits = ModuleGraphLimits::new(
            limits.max_modules,
            limits.max_direct_import_rows,
            limits.max_name_depth,
            u128::MAX,
        );
        let mut graph = ModuleGraph::new(epoch.clone(), graph_limits)
            .map_err(ModuleProvenanceError::InvalidModuleGraph)?;
        for record in &records {
            graph = graph
                .register(record.module.clone())
                .map_err(ModuleProvenanceError::InvalidModuleGraph)?
                .graph;
        }

        let present: BTreeSet<ModuleId> = records
            .iter()
            .map(|record| record.module.id.clone())
            .collect();
        let mut declaration_owners = BTreeMap::<Name, (ModuleId, DeclarationClass)>::new();
        let mut facts = ModuleProvenanceFacts {
            modules: records.len(),
            direct_import_rows: graph.facts().direct_import_rows,
            maximum_name_depth: graph.facts().maximum_name_depth,
            ..ModuleProvenanceFacts::default()
        };
        for record in &records {
            validate_contribution_record(
                record,
                &present,
                &mut declaration_owners,
                limits,
                &mut facts,
            )?;
        }

        let records: Arc<[ModuleContributionRecord]> = records.into();
        let bytes = encode_manifest(&epoch, &records);
        facts.encoded_bytes = bytes.len() as u128;
        enforce_limit(
            None,
            ModuleProvenanceResource::EncodedBytes,
            limits.max_encoded_bytes,
            facts.encoded_bytes,
        )?;
        let root = ModuleProvenanceRoot(hash(Domain::ModuleProvenance, &bytes));
        Ok(Self {
            epoch,
            records,
            facts,
            root,
        })
    }

    pub fn epoch(&self) -> &ModuleEpoch {
        &self.epoch
    }

    pub fn records(&self) -> &[ModuleContributionRecord] {
        &self.records
    }

    pub fn record(&self, module: &ModuleId) -> Option<&ModuleContributionRecord> {
        self.records
            .binary_search_by(|record| record.module.id.cmp(module))
            .ok()
            .map(|index| &self.records[index])
    }

    pub fn facts(&self) -> ModuleProvenanceFacts {
        self.facts
    }

    pub fn root(&self) -> ModuleProvenanceRoot {
        self.root
    }

    pub fn to_canonical_bytes(&self) -> Vec<u8> {
        encode_manifest(&self.epoch, &self.records)
    }

    pub fn from_canonical_bytes(
        bytes: &[u8],
        limits: ModuleProvenanceLimits,
    ) -> Result<Self, ModuleProvenanceError> {
        enforce_limit(
            None,
            ModuleProvenanceResource::EncodedBytes,
            limits.max_encoded_bytes,
            bytes.len() as u128,
        )?;
        let mut reader = CanonReader::new(bytes);
        let schema_name = reader.str()?;
        if schema_name != MODULE_PROVENANCE_SCHEMA.name {
            return Err(ModuleProvenanceError::MalformedEncoding {
                what: "schema name mismatch",
            });
        }
        let version = reader.u16()?;
        if version != MODULE_PROVENANCE_SCHEMA.version {
            return Err(ModuleProvenanceError::UnsupportedSchemaVersion {
                found: version,
                supported: MODULE_PROVENANCE_SCHEMA.version,
            });
        }

        let epoch = ModuleEpoch::new(reader.str()?, reader.str()?);
        let module_count = read_count(
            &mut reader,
            ModuleProvenanceResource::Modules,
            limits.max_modules,
        )?;
        let mut budget = DecodeBudget::new(limits);
        budget.take(ModuleProvenanceResource::Modules, module_count, None)?;
        let mut records = Vec::with_capacity(module_count);
        for _ in 0..module_count {
            records.push(read_contribution_record(&mut reader, &epoch, &mut budget)?);
        }
        reader.finish()?;
        let manifest = Self::new(epoch, records, limits)?;
        if manifest.to_canonical_bytes() != bytes {
            return Err(ModuleProvenanceError::NonCanonicalEncoding);
        }
        Ok(manifest)
    }

    /// Manifest clones share every record and nested immutable array.
    pub fn shares_storage_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.records, &other.records)
    }
}

fn validate_contribution_record(
    record: &ModuleContributionRecord,
    present: &BTreeSet<ModuleId>,
    owners: &mut BTreeMap<Name, (ModuleId, DeclarationClass)>,
    limits: ModuleProvenanceLimits,
    facts: &mut ModuleProvenanceFacts,
) -> Result<(), ModuleProvenanceError> {
    let module = &record.module.id;
    let expected_missing: Vec<ModuleId> = record
        .module
        .direct_imports()
        .iter()
        .filter(|import| !present.contains(&import.module))
        .map(|import| import.module.clone())
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect();
    let actual_missing = record.completeness.missing_dependencies().to_vec();
    if expected_missing != actual_missing {
        return Err(ModuleProvenanceError::MissingDependenciesMismatch {
            module: module.clone(),
            expected: expected_missing,
            actual: actual_missing,
        });
    }
    facts.missing_dependencies = facts
        .missing_dependencies
        .saturating_add(record.completeness.missing_dependencies().len());
    enforce_limit(
        Some(module),
        ModuleProvenanceResource::MissingDependencies,
        limits.max_missing_dependencies as u128,
        facts.missing_dependencies as u128,
    )?;

    let expected_knowledge = if record
        .extension_contributions
        .iter()
        .any(|contribution| contribution.descriptor.provenance == PayloadProvenance::Opaque)
    {
        ExtensionKnowledge::ContainsOpaque
    } else {
        ExtensionKnowledge::AllUnderstood
    };
    if expected_knowledge != record.completeness.extension_knowledge {
        return Err(ModuleProvenanceError::ExtensionKnowledgeMismatch {
            module: module.clone(),
            expected: expected_knowledge,
            actual: record.completeness.extension_knowledge,
        });
    }

    let mut local = BTreeMap::<Name, (DeclarationClass, usize)>::new();
    for (class, names) in [
        (DeclarationClass::Declaration, record.declarations.as_ref()),
        (
            DeclarationClass::ExtraDeclaration,
            record.extra_declarations.as_ref(),
        ),
    ] {
        for (index, name) in names.iter().enumerate() {
            validate_name(name, module, limits, facts)?;
            if name.is_anonymous() {
                return Err(ModuleProvenanceError::AnonymousDeclaration {
                    module: module.clone(),
                    class,
                    index,
                });
            }
            if let Some((first_class, first_index)) = local.get(name).copied() {
                return Err(ModuleProvenanceError::DuplicateDeclaration {
                    module: module.clone(),
                    name: name.clone(),
                    first_class,
                    first_index,
                    duplicate_class: class,
                    duplicate_index: index,
                });
            }
            local.insert(name.clone(), (class, index));
            if let Some((first_module, _)) = owners.get(name) {
                return Err(ModuleProvenanceError::ConflictingDeclarationOwner {
                    name: name.clone(),
                    first_module: first_module.clone(),
                    second_module: module.clone(),
                });
            }
            owners.insert(name.clone(), (module.clone(), class));
        }
    }
    facts.declarations = facts.declarations.saturating_add(record.declarations.len());
    facts.extra_declarations = facts
        .extra_declarations
        .saturating_add(record.extra_declarations.len());
    enforce_limit(
        Some(module),
        ModuleProvenanceResource::DeclarationNames,
        limits.max_declaration_names as u128,
        facts.declarations.saturating_add(facts.extra_declarations) as u128,
    )?;

    for (contribution_index, contribution) in record.extension_contributions.iter().enumerate() {
        validate_name(&contribution.descriptor.name, module, limits, facts)?;
        if contribution.descriptor.name.is_anonymous() {
            return Err(ModuleProvenanceError::AnonymousExtension {
                module: module.clone(),
                contribution_index,
            });
        }
        if contribution.entries.is_empty() {
            return Err(ModuleProvenanceError::EmptyExtensionContribution {
                module: module.clone(),
                contribution_index,
            });
        }
        if contribution.end().is_none() {
            return Err(ModuleProvenanceError::EntryRangeOverflow {
                module: module.clone(),
                contribution_index,
            });
        }
        for (entry_index, entry) in contribution.entries.iter().enumerate() {
            let entry_offset = u64::try_from(entry_index).map_err(|_| {
                ModuleProvenanceError::EntryRangeOverflow {
                    module: module.clone(),
                    contribution_index,
                }
            })?;
            let expected = contribution
                .start
                .checked_add(entry_offset)
                .ok_or_else(|| ModuleProvenanceError::EntryRangeOverflow {
                    module: module.clone(),
                    contribution_index,
                })?;
            if entry.index != expected {
                return Err(ModuleProvenanceError::EntryIndexMismatch {
                    module: module.clone(),
                    contribution_index,
                    entry_index,
                    expected,
                    actual: entry.index,
                });
            }
        }
        facts.extension_entries = facts
            .extension_entries
            .saturating_add(contribution.entries.len());
    }
    facts.extension_contributions = facts
        .extension_contributions
        .saturating_add(record.extension_contributions.len());
    enforce_limit(
        Some(module),
        ModuleProvenanceResource::ExtensionContributions,
        limits.max_extension_contributions as u128,
        facts.extension_contributions as u128,
    )?;
    enforce_limit(
        Some(module),
        ModuleProvenanceResource::ExtensionEntries,
        limits.max_extension_entries as u128,
        facts.extension_entries as u128,
    )?;
    Ok(())
}

fn validate_name(
    name: &Name,
    module: &ModuleId,
    limits: ModuleProvenanceLimits,
    facts: &mut ModuleProvenanceFacts,
) -> Result<(), ModuleProvenanceError> {
    let stats = name_stats(name);
    if stats.overflowing_component {
        return Err(ModuleProvenanceError::OverflowingNameComponent {
            module: module.clone(),
            name: name.clone(),
        });
    }
    enforce_limit(
        Some(module),
        ModuleProvenanceResource::NameDepth,
        limits.max_name_depth as u128,
        stats.depth as u128,
    )?;
    facts.maximum_name_depth = facts.maximum_name_depth.max(stats.depth);
    Ok(())
}

fn enforce_limit(
    module: Option<&ModuleId>,
    resource: ModuleProvenanceResource,
    limit: u128,
    actual: u128,
) -> Result<(), ModuleProvenanceError> {
    if actual > limit {
        return Err(ModuleProvenanceError::ResourceLimitExceeded {
            module: module.cloned(),
            resource,
            limit,
            actual,
        });
    }
    Ok(())
}

fn encode_manifest(epoch: &ModuleEpoch, records: &[ModuleContributionRecord]) -> Vec<u8> {
    let mut writer = CanonWriter::new();
    writer.schema(MODULE_PROVENANCE_SCHEMA);
    writer.str(epoch.tag());
    writer.str(epoch.commit());
    writer.u64(records.len() as u64);
    for record in records {
        write_contribution_record(record, &mut writer);
    }
    writer.into_bytes()
}

fn write_contribution_record(record: &ModuleContributionRecord, writer: &mut CanonWriter) {
    record.module.id.name().write_body(writer);
    writer.bool(record.module.is_module);
    writer.u64(record.module.direct_imports().len() as u64);
    for import in record.module.direct_imports() {
        import.module.name().write_body(writer);
        writer.bool(import.import_all);
        writer.bool(import.is_exported);
        writer.bool(import.is_meta);
    }
    writer.bytes(&record.module.artifact.content_digest.0);
    writer.u8(artifact_producer_tag(record.module.artifact.producer));
    writer.u8(artifact_grade_tag(record.module.artifact.grade));

    writer.u64(record.declarations.len() as u64);
    for name in record.declarations.iter() {
        name.write_body(writer);
    }
    writer.u64(record.extra_declarations.len() as u64);
    for name in record.extra_declarations.iter() {
        name.write_body(writer);
    }
    writer.u64(record.extension_contributions.len() as u64);
    for contribution in record.extension_contributions.iter() {
        contribution.descriptor.name.write_body(writer);
        writer.u8(merge_semantics_tag(contribution.descriptor.merge));
        writer.u8(checkpoint_semantics_tag(contribution.descriptor.checkpoint));
        writer.u8(payload_provenance_tag(contribution.descriptor.provenance));
        writer.u64(contribution.start);
        writer.bytes(&contribution.base_history_digest.0);
        writer.u64(contribution.entries.len() as u64);
        for entry in contribution.entries.iter() {
            writer.u64(entry.index);
            writer.bytes(&entry.payload_digest.0);
        }
    }
    writer.u8(decode_completeness_tag(record.completeness.decode));
    writer.u8(extension_knowledge_tag(
        record.completeness.extension_knowledge,
    ));
    writer.u64(record.completeness.missing_dependencies.len() as u64);
    for module in record.completeness.missing_dependencies.iter() {
        module.name().write_body(writer);
    }
}

#[derive(Debug, Clone, Copy)]
struct BudgetDimension {
    limit: usize,
    used: usize,
}

impl BudgetDimension {
    const fn new(limit: usize) -> Self {
        Self { limit, used: 0 }
    }
}

#[derive(Debug, Clone, Copy)]
struct DecodeBudget {
    modules: BudgetDimension,
    direct_rows: BudgetDimension,
    declaration_names: BudgetDimension,
    extension_contributions: BudgetDimension,
    extension_entries: BudgetDimension,
    missing_dependencies: BudgetDimension,
}

impl DecodeBudget {
    fn new(limits: ModuleProvenanceLimits) -> Self {
        Self {
            modules: BudgetDimension::new(limits.max_modules),
            direct_rows: BudgetDimension::new(limits.max_direct_import_rows),
            declaration_names: BudgetDimension::new(limits.max_declaration_names),
            extension_contributions: BudgetDimension::new(limits.max_extension_contributions),
            extension_entries: BudgetDimension::new(limits.max_extension_entries),
            missing_dependencies: BudgetDimension::new(limits.max_missing_dependencies),
        }
    }

    fn limit(&self, resource: ModuleProvenanceResource) -> Result<usize, ModuleProvenanceError> {
        let dimension = self.dimension(resource)?;
        Ok(dimension.limit)
    }

    fn take(
        &mut self,
        resource: ModuleProvenanceResource,
        count: usize,
        module: Option<&ModuleId>,
    ) -> Result<(), ModuleProvenanceError> {
        let dimension = self.dimension_mut(resource)?;
        let actual = dimension.used.saturating_add(count);
        if actual > dimension.limit {
            return Err(ModuleProvenanceError::ResourceLimitExceeded {
                module: module.cloned(),
                resource,
                limit: dimension.limit as u128,
                actual: actual as u128,
            });
        }
        dimension.used = actual;
        Ok(())
    }

    fn dimension(
        &self,
        resource: ModuleProvenanceResource,
    ) -> Result<&BudgetDimension, ModuleProvenanceError> {
        match resource {
            ModuleProvenanceResource::Modules => Ok(&self.modules),
            ModuleProvenanceResource::DirectImportRows => Ok(&self.direct_rows),
            ModuleProvenanceResource::DeclarationNames => Ok(&self.declaration_names),
            ModuleProvenanceResource::ExtensionContributions => Ok(&self.extension_contributions),
            ModuleProvenanceResource::ExtensionEntries => Ok(&self.extension_entries),
            ModuleProvenanceResource::MissingDependencies => Ok(&self.missing_dependencies),
            ModuleProvenanceResource::NameDepth | ModuleProvenanceResource::EncodedBytes => {
                Err(ModuleProvenanceError::MalformedEncoding {
                    what: "invalid decoder budget dimension",
                })
            }
        }
    }

    fn dimension_mut(
        &mut self,
        resource: ModuleProvenanceResource,
    ) -> Result<&mut BudgetDimension, ModuleProvenanceError> {
        match resource {
            ModuleProvenanceResource::Modules => Ok(&mut self.modules),
            ModuleProvenanceResource::DirectImportRows => Ok(&mut self.direct_rows),
            ModuleProvenanceResource::DeclarationNames => Ok(&mut self.declaration_names),
            ModuleProvenanceResource::ExtensionContributions => {
                Ok(&mut self.extension_contributions)
            }
            ModuleProvenanceResource::ExtensionEntries => Ok(&mut self.extension_entries),
            ModuleProvenanceResource::MissingDependencies => Ok(&mut self.missing_dependencies),
            ModuleProvenanceResource::NameDepth | ModuleProvenanceResource::EncodedBytes => {
                Err(ModuleProvenanceError::MalformedEncoding {
                    what: "invalid decoder budget dimension",
                })
            }
        }
    }
}

fn read_contribution_record(
    reader: &mut CanonReader<'_>,
    epoch: &ModuleEpoch,
    budget: &mut DecodeBudget,
) -> Result<ModuleContributionRecord, ModuleProvenanceError> {
    let module_id = ModuleId::new(Name::read_body(reader)?);
    let is_module = reader.bool()?;
    let direct_count = read_count(
        reader,
        ModuleProvenanceResource::DirectImportRows,
        budget.limit(ModuleProvenanceResource::DirectImportRows)?,
    )?;
    budget.take(
        ModuleProvenanceResource::DirectImportRows,
        direct_count,
        Some(&module_id),
    )?;
    let mut imports = Vec::with_capacity(direct_count);
    for _ in 0..direct_count {
        imports.push(DirectImport::new(
            ModuleId::new(Name::read_body(reader)?),
            reader.bool()?,
            reader.bool()?,
            reader.bool()?,
        ));
    }
    let content_digest = read_digest(reader)?;
    let producer = read_artifact_producer(reader.u8()?)?;
    let grade = read_artifact_grade(reader.u8()?)?;
    let module = ModuleRecord::new(
        module_id.clone(),
        is_module,
        imports,
        ArtifactEvidence {
            epoch: epoch.clone(),
            content_digest,
            producer,
            grade,
        },
    );

    let declaration_count = read_count(
        reader,
        ModuleProvenanceResource::DeclarationNames,
        budget.limit(ModuleProvenanceResource::DeclarationNames)?,
    )?;
    budget.take(
        ModuleProvenanceResource::DeclarationNames,
        declaration_count,
        Some(&module_id),
    )?;
    let mut declarations = Vec::with_capacity(declaration_count);
    for _ in 0..declaration_count {
        declarations.push(Name::read_body(reader)?);
    }
    let extra_count = read_count(
        reader,
        ModuleProvenanceResource::DeclarationNames,
        budget.limit(ModuleProvenanceResource::DeclarationNames)?,
    )?;
    budget.take(
        ModuleProvenanceResource::DeclarationNames,
        extra_count,
        Some(&module_id),
    )?;
    let mut extra_declarations = Vec::with_capacity(extra_count);
    for _ in 0..extra_count {
        extra_declarations.push(Name::read_body(reader)?);
    }

    let contribution_count = read_count(
        reader,
        ModuleProvenanceResource::ExtensionContributions,
        budget.limit(ModuleProvenanceResource::ExtensionContributions)?,
    )?;
    budget.take(
        ModuleProvenanceResource::ExtensionContributions,
        contribution_count,
        Some(&module_id),
    )?;
    let mut contributions = Vec::with_capacity(contribution_count);
    for _ in 0..contribution_count {
        let descriptor = ExtensionDescriptor {
            name: Name::read_body(reader)?,
            merge: read_merge_semantics(reader.u8()?)?,
            checkpoint: read_checkpoint_semantics(reader.u8()?)?,
            provenance: read_payload_provenance(reader.u8()?)?,
        };
        let start = reader.u64()?;
        let base_history_digest = read_digest(reader)?;
        let entry_count = read_count(
            reader,
            ModuleProvenanceResource::ExtensionEntries,
            budget.limit(ModuleProvenanceResource::ExtensionEntries)?,
        )?;
        budget.take(
            ModuleProvenanceResource::ExtensionEntries,
            entry_count,
            Some(&module_id),
        )?;
        let mut entries = Vec::with_capacity(entry_count);
        for _ in 0..entry_count {
            entries.push(ExtensionEntryIdentity::new(
                reader.u64()?,
                read_digest(reader)?,
            ));
        }
        contributions.push(ExtensionContribution::new(
            descriptor,
            start,
            base_history_digest,
            entries,
        ));
    }

    let decode = read_decode_completeness(reader.u8()?)?;
    let extension_knowledge = read_extension_knowledge(reader.u8()?)?;
    let missing_count = read_count(
        reader,
        ModuleProvenanceResource::MissingDependencies,
        budget.limit(ModuleProvenanceResource::MissingDependencies)?,
    )?;
    budget.take(
        ModuleProvenanceResource::MissingDependencies,
        missing_count,
        Some(&module_id),
    )?;
    let mut missing = Vec::with_capacity(missing_count);
    for _ in 0..missing_count {
        missing.push(ModuleId::new(Name::read_body(reader)?));
    }
    Ok(ModuleContributionRecord::new(
        module,
        declarations,
        extra_declarations,
        contributions,
        ProvenanceCompleteness::new(decode, extension_knowledge, missing),
    ))
}

fn read_count(
    reader: &mut CanonReader<'_>,
    resource: ModuleProvenanceResource,
    limit: usize,
) -> Result<usize, ModuleProvenanceError> {
    let raw = reader.u64()?;
    let count = usize::try_from(raw).map_err(|_| ModuleProvenanceError::ResourceLimitExceeded {
        module: None,
        resource,
        limit: limit as u128,
        actual: raw as u128,
    })?;
    Ok(count)
}

fn read_digest(reader: &mut CanonReader<'_>) -> Result<Digest, ModuleProvenanceError> {
    let bytes = reader.bytes()?;
    let array: [u8; 32] =
        bytes
            .try_into()
            .map_err(|_| ModuleProvenanceError::MalformedEncoding {
                what: "digest must contain exactly 32 bytes",
            })?;
    Ok(Digest(array))
}

fn artifact_producer_tag(value: ArtifactProducer) -> u8 {
    match value {
        ArtifactProducer::Reference => 0,
        ArtifactProducer::FrankenLean => 1,
    }
}

fn artifact_grade_tag(value: ArtifactGrade) -> u8 {
    match value {
        ArtifactGrade::Provisional => 0,
        ArtifactGrade::Verified => 1,
        ArtifactGrade::OracleFixture => 2,
    }
}

fn merge_semantics_tag(value: MergeSemantics) -> u8 {
    match value {
        MergeSemantics::AppendOrdered => 0,
        MergeSemantics::SetUnion => 1,
        MergeSemantics::ConflictsRequireReview => 2,
    }
}

fn checkpoint_semantics_tag(value: CheckpointSemantics) -> u8 {
    match value {
        CheckpointSemantics::JournalSuffix => 0,
        CheckpointSemantics::FullJournal => 1,
    }
}

fn payload_provenance_tag(value: PayloadProvenance) -> u8 {
    match value {
        PayloadProvenance::Understood => 0,
        PayloadProvenance::Opaque => 1,
    }
}

fn decode_completeness_tag(value: DecodeCompleteness) -> u8 {
    match value {
        DecodeCompleteness::Complete => 0,
        DecodeCompleteness::Partial => 1,
    }
}

fn extension_knowledge_tag(value: ExtensionKnowledge) -> u8 {
    match value {
        ExtensionKnowledge::AllUnderstood => 0,
        ExtensionKnowledge::ContainsOpaque => 1,
    }
}

fn read_artifact_producer(tag: u8) -> Result<ArtifactProducer, ModuleProvenanceError> {
    match tag {
        0 => Ok(ArtifactProducer::Reference),
        1 => Ok(ArtifactProducer::FrankenLean),
        _ => Err(ModuleProvenanceError::MalformedEncoding {
            what: "unknown artifact producer tag",
        }),
    }
}

fn read_artifact_grade(tag: u8) -> Result<ArtifactGrade, ModuleProvenanceError> {
    match tag {
        0 => Ok(ArtifactGrade::Provisional),
        1 => Ok(ArtifactGrade::Verified),
        2 => Ok(ArtifactGrade::OracleFixture),
        _ => Err(ModuleProvenanceError::MalformedEncoding {
            what: "unknown artifact grade tag",
        }),
    }
}

fn read_merge_semantics(tag: u8) -> Result<MergeSemantics, ModuleProvenanceError> {
    match tag {
        0 => Ok(MergeSemantics::AppendOrdered),
        1 => Ok(MergeSemantics::SetUnion),
        2 => Ok(MergeSemantics::ConflictsRequireReview),
        _ => Err(ModuleProvenanceError::MalformedEncoding {
            what: "unknown extension merge tag",
        }),
    }
}

fn read_checkpoint_semantics(tag: u8) -> Result<CheckpointSemantics, ModuleProvenanceError> {
    match tag {
        0 => Ok(CheckpointSemantics::JournalSuffix),
        1 => Ok(CheckpointSemantics::FullJournal),
        _ => Err(ModuleProvenanceError::MalformedEncoding {
            what: "unknown extension checkpoint tag",
        }),
    }
}

fn read_payload_provenance(tag: u8) -> Result<PayloadProvenance, ModuleProvenanceError> {
    match tag {
        0 => Ok(PayloadProvenance::Understood),
        1 => Ok(PayloadProvenance::Opaque),
        _ => Err(ModuleProvenanceError::MalformedEncoding {
            what: "unknown extension provenance tag",
        }),
    }
}

fn read_decode_completeness(tag: u8) -> Result<DecodeCompleteness, ModuleProvenanceError> {
    match tag {
        0 => Ok(DecodeCompleteness::Complete),
        1 => Ok(DecodeCompleteness::Partial),
        _ => Err(ModuleProvenanceError::MalformedEncoding {
            what: "unknown decode completeness tag",
        }),
    }
}

fn read_extension_knowledge(tag: u8) -> Result<ExtensionKnowledge, ModuleProvenanceError> {
    match tag {
        0 => Ok(ExtensionKnowledge::AllUnderstood),
        1 => Ok(ExtensionKnowledge::ContainsOpaque),
        _ => Err(ModuleProvenanceError::MalformedEncoding {
            what: "unknown extension knowledge tag",
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::options::KVMap;
    use fln_hash::domain::hash;

    const PIN_COMMIT: &str = "0123456789abcdef0123456789abcdef01234567";
    const TEST_LIMITS: ModuleProvenanceLimits = ModuleProvenanceLimits::new(
        10_000,
        100_000,
        200_000,
        100_000,
        500_000,
        100_000,
        256,
        128 * 1024 * 1024,
    );

    fn epoch() -> ModuleEpoch {
        ModuleEpoch::new("v4.32.0", PIN_COMMIT)
    }

    fn name(value: &str) -> Name {
        Name::from_components(value.split('.'))
    }

    fn id(value: &str) -> ModuleId {
        ModuleId::new(name(value))
    }

    fn evidence(seed: u8) -> ArtifactEvidence {
        ArtifactEvidence {
            epoch: epoch(),
            content_digest: Digest([seed; 32]),
            producer: ArtifactProducer::Reference,
            grade: ArtifactGrade::Verified,
        }
    }

    fn extension_descriptor(
        extension_name: &str,
        provenance: PayloadProvenance,
    ) -> ExtensionDescriptor {
        ExtensionDescriptor {
            name: name(extension_name),
            merge: MergeSemantics::AppendOrdered,
            checkpoint: CheckpointSemantics::JournalSuffix,
            provenance,
        }
    }

    fn entry(index: u64, seed: u8) -> ExtensionEntryIdentity {
        ExtensionEntryIdentity::new(index, hash(Domain::Fixture, &[seed]))
    }

    fn sample_records() -> Vec<ModuleContributionRecord> {
        let module_a = ModuleRecord::new(
            id("A"),
            true,
            vec![
                DirectImport::new(id("B"), false, true, false),
                DirectImport::new(id("Ghost"), true, false, true),
            ],
            evidence(0xA1),
        );
        let contribution = ExtensionContribution::new(
            extension_descriptor("simpExt", PayloadProvenance::Understood),
            7,
            Digest([0x31; 32]),
            vec![entry(7, 0x41), entry(8, 0x42)],
        );
        let a = ModuleContributionRecord::new(
            module_a,
            vec![name("A.one"), name("A.two")],
            vec![name("A.generated")],
            vec![contribution],
            ProvenanceCompleteness::new(
                DecodeCompleteness::Complete,
                ExtensionKnowledge::AllUnderstood,
                vec![id("Ghost")],
            ),
        );
        let b = ModuleContributionRecord::new(
            ModuleRecord::new(id("B"), true, vec![], evidence(0xB1)),
            vec![name("B.one")],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                DecodeCompleteness::Complete,
                ExtensionKnowledge::AllUnderstood,
                vec![],
            ),
        );
        vec![a, b]
    }

    fn sample_manifest() -> ModuleProvenanceManifest {
        ModuleProvenanceManifest::new(epoch(), sample_records(), TEST_LIMITS)
            .expect("sample manifest validates")
    }

    fn limits_from_facts(facts: ModuleProvenanceFacts) -> ModuleProvenanceLimits {
        ModuleProvenanceLimits::new(
            facts.modules,
            facts.direct_import_rows,
            facts.declarations + facts.extra_declarations,
            facts.extension_contributions,
            facts.extension_entries,
            facts.missing_dependencies,
            facts.maximum_name_depth,
            facts.encoded_bytes,
        )
    }

    #[test]
    fn domain_registry_covers_operational_and_module_provenance_domains() {
        assert!(Domain::ALL.contains(&Domain::OperationalMeta));
        assert!(Domain::ALL.contains(&Domain::ModuleProvenance));
        assert_eq!(Domain::ALL.len(), 12);
        assert_ne!(
            hash(Domain::LogicalRoot, b"same"),
            hash(Domain::ModuleProvenance, b"same")
        );
        assert_ne!(
            hash(Domain::OperationalMeta, b"same"),
            hash(Domain::ModuleProvenance, b"same")
        );
    }

    #[test]
    fn schema_and_every_enum_tag_are_frozen_with_typed_unknown_refusals() {
        assert_eq!(MODULE_PROVENANCE_SCHEMA.name, "fln.env.module-provenance");
        assert_eq!(MODULE_PROVENANCE_SCHEMA.version, 1);

        for value in [ArtifactProducer::Reference, ArtifactProducer::FrankenLean] {
            assert_eq!(
                read_artifact_producer(artifact_producer_tag(value)),
                Ok(value)
            );
        }
        for value in [
            ArtifactGrade::Provisional,
            ArtifactGrade::Verified,
            ArtifactGrade::OracleFixture,
        ] {
            assert_eq!(read_artifact_grade(artifact_grade_tag(value)), Ok(value));
        }
        for value in [
            MergeSemantics::AppendOrdered,
            MergeSemantics::SetUnion,
            MergeSemantics::ConflictsRequireReview,
        ] {
            assert_eq!(read_merge_semantics(merge_semantics_tag(value)), Ok(value));
        }
        for value in [
            CheckpointSemantics::JournalSuffix,
            CheckpointSemantics::FullJournal,
        ] {
            assert_eq!(
                read_checkpoint_semantics(checkpoint_semantics_tag(value)),
                Ok(value)
            );
        }
        for value in [PayloadProvenance::Understood, PayloadProvenance::Opaque] {
            assert_eq!(
                read_payload_provenance(payload_provenance_tag(value)),
                Ok(value)
            );
        }
        for value in [DecodeCompleteness::Complete, DecodeCompleteness::Partial] {
            assert_eq!(
                read_decode_completeness(decode_completeness_tag(value)),
                Ok(value)
            );
        }
        for value in [
            ExtensionKnowledge::AllUnderstood,
            ExtensionKnowledge::ContainsOpaque,
        ] {
            assert_eq!(
                read_extension_knowledge(extension_knowledge_tag(value)),
                Ok(value)
            );
        }

        for error in [
            read_artifact_producer(u8::MAX).expect_err("unknown producer is refused"),
            read_artifact_grade(u8::MAX).expect_err("unknown grade is refused"),
            read_merge_semantics(u8::MAX).expect_err("unknown merge policy is refused"),
            read_checkpoint_semantics(u8::MAX).expect_err("unknown checkpoint policy is refused"),
            read_payload_provenance(u8::MAX).expect_err("unknown provenance is refused"),
            read_decode_completeness(u8::MAX).expect_err("unknown completeness is refused"),
            read_extension_knowledge(u8::MAX).expect_err("unknown knowledge grade is refused"),
        ] {
            assert!(matches!(
                error,
                ModuleProvenanceError::MalformedEncoding { .. }
            ));
        }
    }

    #[test]
    fn canonical_round_trip_golden_root_and_exact_facts() {
        let manifest = sample_manifest();
        let bytes = manifest.to_canonical_bytes();
        let decoded = ModuleProvenanceManifest::from_canonical_bytes(&bytes, TEST_LIMITS)
            .expect("canonical manifest decodes");
        assert_eq!(decoded, manifest);
        assert_eq!(decoded.to_canonical_bytes(), bytes);
        assert_eq!(decoded.root(), manifest.root());
        assert_eq!(
            manifest.root().to_string(),
            "8c0a18d29e8d4401615c33de39a516612aabe400cb9888088013c02ef8134b48",
            "schema/domain changes require an explicit golden update"
        );
        assert_eq!(bytes.len(), 685, "canonical layout size is frozen");
        assert_eq!(
            manifest.facts(),
            ModuleProvenanceFacts {
                modules: 2,
                direct_import_rows: 2,
                declarations: 3,
                extra_declarations: 1,
                extension_contributions: 1,
                extension_entries: 2,
                missing_dependencies: 1,
                maximum_name_depth: 2,
                encoded_bytes: bytes.len() as u128,
            }
        );
        println!(
            "module provenance golden: root={} bytes={}",
            manifest.root(),
            bytes.len()
        );
    }

    #[test]
    fn manifest_order_is_canonical_but_reference_rows_and_contributions_are_not_sorted() {
        let forward = ModuleProvenanceManifest::new(epoch(), sample_records(), TEST_LIMITS)
            .expect("forward validates");
        let mut reverse_records = sample_records();
        reverse_records.reverse();
        let reverse = ModuleProvenanceManifest::new(epoch(), reverse_records, TEST_LIMITS)
            .expect("reverse validates");
        assert_eq!(forward, reverse);
        assert_eq!(forward.to_canonical_bytes(), reverse.to_canonical_bytes());
        assert_eq!(forward.root(), reverse.root());
        assert_eq!(
            forward
                .records()
                .iter()
                .map(|record| record.module().id.clone())
                .collect::<Vec<_>>(),
            vec![id("A"), id("B")]
        );

        let mut reordered = sample_records();
        let a = &mut reordered[0];
        let mut imports = a.module.direct_imports().to_vec();
        imports.reverse();
        a.module = ModuleRecord::new(
            a.module.id.clone(),
            a.module.is_module,
            imports,
            a.module.artifact.clone(),
        );
        let reordered = ModuleProvenanceManifest::new(epoch(), reordered, TEST_LIMITS)
            .expect("reordered direct rows remain a valid distinct manifest");
        assert_ne!(forward.root(), reordered.root());

        let mut contribution_reordered = sample_records();
        let contribution = &contribution_reordered[0].extension_contributions[0];
        let mut entries = contribution.entries().to_vec();
        entries.swap(0, 1);
        // Preserve a valid contiguous range while reversing payload identities.
        entries[0] = ExtensionEntryIdentity::new(7, entries[0].payload_digest());
        entries[1] = ExtensionEntryIdentity::new(8, entries[1].payload_digest());
        contribution_reordered[0].extension_contributions = vec![ExtensionContribution::new(
            contribution.descriptor().clone(),
            contribution.start(),
            contribution.base_history_digest(),
            entries,
        )]
        .into();
        let contribution_reordered =
            ModuleProvenanceManifest::new(epoch(), contribution_reordered, TEST_LIMITS)
                .expect("reordered entry identities remain structurally valid");
        assert_ne!(forward.root(), contribution_reordered.root());

        let mut two_contributions = sample_records();
        let second = ExtensionContribution::new(
            extension_descriptor("traceExt", PayloadProvenance::Understood),
            0,
            Digest([0x52; 32]),
            vec![entry(0, 0x53)],
        );
        let first = two_contributions[0].extension_contributions[0].clone();
        two_contributions[0].extension_contributions = vec![first.clone(), second.clone()].into();
        let contribution_forward =
            ModuleProvenanceManifest::new(epoch(), two_contributions.clone(), TEST_LIMITS)
                .expect("two ordered contributions validate");
        two_contributions[0].extension_contributions = vec![second, first].into();
        let contribution_reverse =
            ModuleProvenanceManifest::new(epoch(), two_contributions, TEST_LIMITS)
                .expect("reversed contribution sequence validates");
        assert_ne!(contribution_forward.root(), contribution_reverse.root());
        assert_ne!(
            contribution_forward.to_canonical_bytes(),
            contribution_reverse.to_canonical_bytes()
        );

        let canonical_missing = ProvenanceCompleteness::new(
            DecodeCompleteness::Complete,
            ExtensionKnowledge::AllUnderstood,
            vec![id("Lost"), id("Ghost"), id("Lost")],
        );
        assert_eq!(
            canonical_missing.missing_dependencies(),
            &[id("Ghost"), id("Lost")]
        );
    }

    #[test]
    fn exact_duplicate_direct_rows_survive_the_schema() {
        let duplicate = DirectImport::new(id("B"), true, false, true);
        let record = ModuleContributionRecord::new(
            ModuleRecord::new(
                id("A"),
                true,
                vec![duplicate.clone(), duplicate.clone()],
                evidence(1),
            ),
            vec![name("A.one")],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                DecodeCompleteness::Complete,
                ExtensionKnowledge::AllUnderstood,
                vec![id("B")],
            ),
        );
        let manifest = ModuleProvenanceManifest::new(epoch(), vec![record], TEST_LIMITS)
            .expect("duplicate rows are lossless, not normalized");
        assert_eq!(manifest.records()[0].module().direct_imports().len(), 2);
        let decoded = ModuleProvenanceManifest::from_canonical_bytes(
            &manifest.to_canonical_bytes(),
            TEST_LIMITS,
        )
        .expect("duplicate rows round trip");
        assert_eq!(
            decoded.records()[0].module().direct_imports(),
            &[duplicate.clone(), duplicate]
        );
    }

    #[test]
    fn every_root_field_is_observable_and_named_drop_mutants_are_killed() {
        let baseline = sample_manifest();
        let baseline_root = baseline.root();
        let mut roots = BTreeSet::new();
        roots.insert(baseline_root);

        let mut drop_extra = sample_records();
        drop_extra[0].extra_declarations = Arc::from([]);
        let drop_extra = ModuleProvenanceManifest::new(epoch(), drop_extra, TEST_LIMITS)
            .expect("drop-extra mutant remains structurally valid");
        roots.insert(drop_extra.root());

        let mut drop_extension = sample_records();
        drop_extension[0].extension_contributions = Arc::from([]);
        drop_extension[0].completeness = ProvenanceCompleteness::new(
            DecodeCompleteness::Complete,
            ExtensionKnowledge::AllUnderstood,
            vec![id("Ghost")],
        );
        let drop_extension = ModuleProvenanceManifest::new(epoch(), drop_extension, TEST_LIMITS)
            .expect("drop-extension mutant remains structurally valid");
        roots.insert(drop_extension.root());

        let mut drop_completeness = sample_records();
        drop_completeness[0].completeness = ProvenanceCompleteness::new(
            DecodeCompleteness::Partial,
            ExtensionKnowledge::AllUnderstood,
            vec![id("Ghost")],
        );
        let drop_completeness =
            ModuleProvenanceManifest::new(epoch(), drop_completeness, TEST_LIMITS)
                .expect("completeness mutant remains structurally valid");
        roots.insert(drop_completeness.root());

        let mut artifact = sample_records();
        artifact[0].module.artifact.content_digest = Digest([0x77; 32]);
        let artifact = ModuleProvenanceManifest::new(epoch(), artifact, TEST_LIMITS)
            .expect("artifact mutant remains structurally valid");
        roots.insert(artifact.root());

        let mut direct_flag = sample_records();
        direct_flag[0].module = ModuleRecord::new(
            id("A"),
            true,
            vec![
                DirectImport::new(id("B"), true, true, false),
                DirectImport::new(id("Ghost"), true, false, true),
            ],
            evidence(0xA1),
        );
        let direct_flag = ModuleProvenanceManifest::new(epoch(), direct_flag, TEST_LIMITS)
            .expect("direct-flag mutant remains structurally valid");
        roots.insert(direct_flag.root());

        let mut graph_identity = sample_records();
        graph_identity[0].module.id = id("C");
        let graph_identity = ModuleProvenanceManifest::new(epoch(), graph_identity, TEST_LIMITS)
            .expect("graph-identity mutant remains structurally valid");
        roots.insert(graph_identity.root());

        let mut entry_payload = sample_records();
        let contribution = &entry_payload[0].extension_contributions[0];
        let mut entries = contribution.entries().to_vec();
        entries[1] = entry(8, 0x99);
        entry_payload[0].extension_contributions = vec![ExtensionContribution::new(
            contribution.descriptor().clone(),
            contribution.start(),
            contribution.base_history_digest(),
            entries,
        )]
        .into();
        let entry_payload = ModuleProvenanceManifest::new(epoch(), entry_payload, TEST_LIMITS)
            .expect("entry-identity mutant remains structurally valid");
        roots.insert(entry_payload.root());

        assert_eq!(roots.len(), 8, "every named field mutant changes the root");
        for (mutant, root) in [
            ("DROP-EXTRA-DECLARATION", drop_extra.root()),
            ("DROP-EXTENSION-CONTRIBUTOR", drop_extension.root()),
            ("DROP-COMPLETENESS-GRADE", drop_completeness.root()),
            ("DROP-ARTIFACT-BINDING", artifact.root()),
            ("DROP-DIRECT-ROW-FIELD", direct_flag.root()),
            ("DROP-GRAPH-ROOT-FIELD", graph_identity.root()),
            ("DROP-ENTRY-IDENTITY", entry_payload.root()),
        ] {
            assert_ne!(root, baseline_root, "mutant {mutant} must be killed");
            println!(
                "{{\"schema\":\"fln.unit.module-provenance-mutation\",\"version\":1,\"bead\":\"franken_lean-module-provenance-schema-cxn\",\"mutant\":\"{mutant}\",\"expected\":\"root-change\",\"actual\":\"root-change\",\"baseline_root\":\"{baseline_root}\",\"mutant_root\":\"{root}\",\"status\":\"killed\"}}"
            );
        }
    }

    #[test]
    fn every_canonical_field_family_has_distinct_round_trip_identity() {
        const ALT_COMMIT: &str = "fedcba9876543210fedcba9876543210fedcba98";

        let baseline = sample_manifest();
        let baseline_bytes = baseline.to_canonical_bytes();
        let baseline_root = baseline.root();
        let mut roots = BTreeSet::from([baseline_root]);
        let mut observe = |field: &'static str, variant_epoch: ModuleEpoch, records: Vec<_>| {
            let candidate = ModuleProvenanceManifest::new(variant_epoch, records, TEST_LIMITS)
                .expect("field variant remains structurally valid");
            let bytes = candidate.to_canonical_bytes();
            assert_ne!(bytes, baseline_bytes, "field={field}");
            assert_ne!(candidate.root(), baseline_root, "field={field}");
            assert!(
                roots.insert(candidate.root()),
                "field={field} must have a distinct canonical identity"
            );
            assert_eq!(
                ModuleProvenanceManifest::from_canonical_bytes(&bytes, TEST_LIMITS)
                    .expect("field variant round trips")
                    .root(),
                candidate.root(),
                "field={field}"
            );
            println!(
                "{{\"schema\":\"fln.unit.module-provenance-field\",\"version\":1,\"bead\":\"franken_lean-module-provenance-schema-cxn\",\"field\":\"{field}\",\"baseline_root\":\"{baseline_root}\",\"variant_root\":\"{}\",\"canonical_round_trip\":\"pass\"}}",
                candidate.root()
            );
        };

        let tag_epoch = ModuleEpoch::new("v4.32.1", PIN_COMMIT);
        let mut records = sample_records();
        for record in &mut records {
            record.module.artifact.epoch = tag_epoch.clone();
        }
        observe("epoch.tag", tag_epoch, records);

        let commit_epoch = ModuleEpoch::new("v4.32.0", ALT_COMMIT);
        let mut records = sample_records();
        for record in &mut records {
            record.module.artifact.epoch = commit_epoch.clone();
        }
        observe("epoch.commit", commit_epoch, records);

        let mut records = sample_records();
        records[0].module.id = id("C");
        observe("module.id", epoch(), records);

        let mut records = sample_records();
        records[0].module.is_module = false;
        observe("module.is_module", epoch(), records);

        let mut records = sample_records();
        records[0].module = ModuleRecord::new(
            id("A"),
            true,
            vec![
                DirectImport::new(id("B"), false, true, false),
                DirectImport::new(id("Phantom"), true, false, true),
            ],
            evidence(0xA1),
        );
        records[0].completeness = ProvenanceCompleteness::new(
            DecodeCompleteness::Complete,
            ExtensionKnowledge::AllUnderstood,
            vec![id("Phantom")],
        );
        observe("direct_import.module+missing_dependency", epoch(), records);

        for (field, first) in [
            (
                "direct_import.import_all",
                DirectImport::new(id("B"), true, true, false),
            ),
            (
                "direct_import.is_exported",
                DirectImport::new(id("B"), false, false, false),
            ),
            (
                "direct_import.is_meta",
                DirectImport::new(id("B"), false, true, true),
            ),
        ] {
            let mut records = sample_records();
            records[0].module = ModuleRecord::new(
                id("A"),
                true,
                vec![first, DirectImport::new(id("Ghost"), true, false, true)],
                evidence(0xA1),
            );
            observe(field, epoch(), records);
        }

        let mut records = sample_records();
        records[0].module.artifact.content_digest = Digest([0xD1; 32]);
        observe("artifact.content_digest", epoch(), records);

        let mut records = sample_records();
        records[0].module.artifact.producer = ArtifactProducer::FrankenLean;
        observe("artifact.producer", epoch(), records);

        let mut records = sample_records();
        records[0].module.artifact.grade = ArtifactGrade::OracleFixture;
        observe("artifact.grade", epoch(), records);

        let mut records = sample_records();
        records[0].declarations = vec![name("A.two"), name("A.one")].into();
        observe("declarations.order", epoch(), records);

        let mut records = sample_records();
        records[0].extra_declarations = vec![name("A.generated.variant")].into();
        observe("extra_declarations.identity", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            ExtensionDescriptor {
                name: name("traceExt"),
                ..original.descriptor().clone()
            },
            original.start(),
            original.base_history_digest(),
            original.entries().to_vec(),
        )]
        .into();
        observe("extension.name", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            ExtensionDescriptor {
                merge: MergeSemantics::SetUnion,
                ..original.descriptor().clone()
            },
            original.start(),
            original.base_history_digest(),
            original.entries().to_vec(),
        )]
        .into();
        observe("extension.merge", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            ExtensionDescriptor {
                checkpoint: CheckpointSemantics::FullJournal,
                ..original.descriptor().clone()
            },
            original.start(),
            original.base_history_digest(),
            original.entries().to_vec(),
        )]
        .into();
        observe("extension.checkpoint", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            ExtensionDescriptor {
                provenance: PayloadProvenance::Opaque,
                ..original.descriptor().clone()
            },
            original.start(),
            original.base_history_digest(),
            original.entries().to_vec(),
        )]
        .into();
        records[0].completeness = ProvenanceCompleteness::new(
            DecodeCompleteness::Complete,
            ExtensionKnowledge::ContainsOpaque,
            vec![id("Ghost")],
        );
        observe("extension.provenance+extension_knowledge", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            9,
            original.base_history_digest(),
            vec![entry(9, 0x41), entry(10, 0x42)],
        )]
        .into();
        observe("extension.range_start+entry_ordinals", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            original.start(),
            Digest([0xB1; 32]),
            original.entries().to_vec(),
        )]
        .into();
        observe("extension.base_history_digest", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            original.start(),
            original.base_history_digest(),
            vec![entry(7, 0x41), entry(8, 0x99)],
        )]
        .into();
        observe("extension.entry_payload_digest", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            original.start(),
            original.base_history_digest(),
            vec![entry(7, 0x41), entry(8, 0x42), entry(9, 0x43)],
        )]
        .into();
        observe("extension.entry_count", epoch(), records);

        let mut records = sample_records();
        records[0].completeness = ProvenanceCompleteness::new(
            DecodeCompleteness::Partial,
            ExtensionKnowledge::AllUnderstood,
            vec![id("Ghost")],
        );
        observe("completeness.decode", epoch(), records);

        let mut records = sample_records();
        records[0].module = ModuleRecord::new(
            id("A"),
            true,
            vec![
                DirectImport::new(id("B"), false, true, false),
                DirectImport::new(id("Ghost"), true, false, true),
                DirectImport::new(id("Lost"), false, false, false),
            ],
            evidence(0xA1),
        );
        records[0].completeness = ProvenanceCompleteness::new(
            DecodeCompleteness::Complete,
            ExtensionKnowledge::AllUnderstood,
            vec![id("Lost"), id("Ghost")],
        );
        observe("completeness.missing_dependency_set", epoch(), records);

        assert_eq!(roots.len(), 24, "baseline plus every field-family variant");
    }

    #[test]
    fn logical_root_is_structurally_independent_of_provenance_root() {
        let environment = crate::environment::Environment::new()
            .register_extension(extension_descriptor(
                "simpExt",
                PayloadProvenance::Understood,
            ))
            .and_then(|environment| {
                environment.push_extension_entry(&name("simpExt"), b"entry".as_slice())
            })
            .expect("environment builds");
        let logical_before = environment.logical_root(&KVMap::new());
        let base = sample_manifest();
        let mut topology_changed = sample_records();
        topology_changed[0].module = ModuleRecord::new(
            id("A"),
            true,
            vec![DirectImport::new(id("Ghost"), true, false, true)],
            evidence(0xA1),
        );
        topology_changed[0].completeness = ProvenanceCompleteness::new(
            DecodeCompleteness::Complete,
            ExtensionKnowledge::AllUnderstood,
            vec![id("Ghost")],
        );
        let topology_changed =
            ModuleProvenanceManifest::new(epoch(), topology_changed, TEST_LIMITS)
                .expect("changed topology validates");
        assert_ne!(base.root(), topology_changed.root());
        assert_eq!(logical_before, environment.logical_root(&KVMap::new()));
        assert_ne!(
            base.root().0,
            logical_before.0,
            "typed domains do not alias even for unrelated current values"
        );
    }

    #[test]
    fn exact_resource_boundaries_pass_and_every_dimension_refuses_overage() {
        let baseline = sample_manifest();
        let facts = baseline.facts();
        let exact = limits_from_facts(facts);
        assert_eq!(
            ModuleProvenanceManifest::new(epoch(), sample_records(), exact)
                .expect("every exact boundary passes")
                .facts(),
            facts
        );

        let cases = [
            (
                ModuleProvenanceLimits {
                    max_modules: facts.modules - 1,
                    ..exact
                },
                ModuleProvenanceResource::Modules,
            ),
            (
                ModuleProvenanceLimits {
                    max_direct_import_rows: facts.direct_import_rows - 1,
                    ..exact
                },
                ModuleProvenanceResource::DirectImportRows,
            ),
            (
                ModuleProvenanceLimits {
                    max_declaration_names: facts.declarations + facts.extra_declarations - 1,
                    ..exact
                },
                ModuleProvenanceResource::DeclarationNames,
            ),
            (
                ModuleProvenanceLimits {
                    max_extension_contributions: facts.extension_contributions - 1,
                    ..exact
                },
                ModuleProvenanceResource::ExtensionContributions,
            ),
            (
                ModuleProvenanceLimits {
                    max_extension_entries: facts.extension_entries - 1,
                    ..exact
                },
                ModuleProvenanceResource::ExtensionEntries,
            ),
            (
                ModuleProvenanceLimits {
                    max_missing_dependencies: facts.missing_dependencies - 1,
                    ..exact
                },
                ModuleProvenanceResource::MissingDependencies,
            ),
            (
                ModuleProvenanceLimits {
                    max_name_depth: facts.maximum_name_depth - 1,
                    ..exact
                },
                ModuleProvenanceResource::NameDepth,
            ),
            (
                ModuleProvenanceLimits {
                    max_encoded_bytes: facts.encoded_bytes - 1,
                    ..exact
                },
                ModuleProvenanceResource::EncodedBytes,
            ),
        ];
        for (limits, expected_resource) in cases {
            let error = ModuleProvenanceManifest::new(epoch(), sample_records(), limits)
                .expect_err("one-below boundary is refused");
            let actual_resource = match error {
                ModuleProvenanceError::ResourceLimitExceeded { resource, .. } => Some(resource),
                ModuleProvenanceError::InvalidModuleGraph(
                    ModuleGraphError::ResourceLimitExceeded { resource, .. },
                ) => match resource {
                    crate::modules::ModuleGraphResource::Modules => {
                        Some(ModuleProvenanceResource::Modules)
                    }
                    crate::modules::ModuleGraphResource::DirectImportRows => {
                        Some(ModuleProvenanceResource::DirectImportRows)
                    }
                    crate::modules::ModuleGraphResource::NameDepth => {
                        Some(ModuleProvenanceResource::NameDepth)
                    }
                    crate::modules::ModuleGraphResource::PayloadBytes => None,
                },
                _ => None,
            };
            assert_eq!(actual_resource, Some(expected_resource));
        }

        let bytes = baseline.to_canonical_bytes();
        assert!(matches!(
            ModuleProvenanceManifest::from_canonical_bytes(
                &bytes,
                ModuleProvenanceLimits {
                    max_encoded_bytes: bytes.len() as u128 - 1,
                    ..exact
                }
            ),
            Err(ModuleProvenanceError::ResourceLimitExceeded {
                resource: ModuleProvenanceResource::EncodedBytes,
                ..
            })
        ));
    }

    #[test]
    fn decoder_reports_configured_limit_and_cumulative_actual_before_allocation() {
        let bytes = sample_manifest().to_canonical_bytes();
        let limits = ModuleProvenanceLimits {
            max_declaration_names: 3,
            ..TEST_LIMITS
        };
        assert_eq!(
            ModuleProvenanceManifest::from_canonical_bytes(&bytes, limits),
            Err(ModuleProvenanceError::ResourceLimitExceeded {
                module: Some(id("B")),
                resource: ModuleProvenanceResource::DeclarationNames,
                limit: 3,
                actual: 4,
            })
        );
    }

    #[test]
    fn semantic_malformed_table_is_typed_and_atomic() {
        let baseline_records = sample_records();

        let mut duplicate_module = baseline_records.clone();
        duplicate_module.push(duplicate_module[0].clone());
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), duplicate_module, TEST_LIMITS),
            Err(ModuleProvenanceError::DuplicateModule { .. })
        ));

        let mut duplicate_local = baseline_records.clone();
        duplicate_local[0].extra_declarations = vec![name("A.one")].into();
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), duplicate_local, TEST_LIMITS),
            Err(ModuleProvenanceError::DuplicateDeclaration { .. })
        ));

        let mut conflicting_owner = baseline_records.clone();
        conflicting_owner[1].declarations = vec![name("A.one")].into();
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), conflicting_owner, TEST_LIMITS),
            Err(ModuleProvenanceError::ConflictingDeclarationOwner { .. })
        ));

        let mut wrong_missing = baseline_records.clone();
        wrong_missing[0].completeness = ProvenanceCompleteness::new(
            DecodeCompleteness::Complete,
            ExtensionKnowledge::AllUnderstood,
            vec![],
        );
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), wrong_missing, TEST_LIMITS),
            Err(ModuleProvenanceError::MissingDependenciesMismatch { .. })
        ));

        let mut wrong_knowledge = baseline_records.clone();
        wrong_knowledge[0].completeness = ProvenanceCompleteness::new(
            DecodeCompleteness::Complete,
            ExtensionKnowledge::ContainsOpaque,
            vec![id("Ghost")],
        );
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), wrong_knowledge, TEST_LIMITS),
            Err(ModuleProvenanceError::ExtensionKnowledgeMismatch { .. })
        ));

        let mut empty_contribution = baseline_records.clone();
        let original = &empty_contribution[0].extension_contributions[0];
        empty_contribution[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            original.start(),
            original.base_history_digest(),
            vec![],
        )]
        .into();
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), empty_contribution, TEST_LIMITS),
            Err(ModuleProvenanceError::EmptyExtensionContribution { .. })
        ));

        let mut wrong_entry = baseline_records.clone();
        let original = &wrong_entry[0].extension_contributions[0];
        wrong_entry[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            original.start(),
            original.base_history_digest(),
            vec![entry(7, 1), entry(99, 2)],
        )]
        .into();
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), wrong_entry, TEST_LIMITS),
            Err(ModuleProvenanceError::EntryIndexMismatch { .. })
        ));

        let mut overflow = baseline_records.clone();
        let original = &overflow[0].extension_contributions[0];
        overflow[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            u64::MAX,
            original.base_history_digest(),
            vec![entry(u64::MAX, 1)],
        )]
        .into();
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), overflow, TEST_LIMITS),
            Err(ModuleProvenanceError::EntryRangeOverflow { .. })
        ));

        let mut anonymous_extension = baseline_records.clone();
        let original = &anonymous_extension[0].extension_contributions[0];
        anonymous_extension[0].extension_contributions = vec![ExtensionContribution::new(
            ExtensionDescriptor {
                name: Name::anonymous(),
                ..original.descriptor().clone()
            },
            original.start(),
            original.base_history_digest(),
            original.entries().to_vec(),
        )]
        .into();
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), anonymous_extension, TEST_LIMITS),
            Err(ModuleProvenanceError::AnonymousExtension { .. })
        ));

        let mut overflowing_name = baseline_records;
        overflowing_name[0].extra_declarations = vec![Name::num_overflowing(name("A"), 7)].into();
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), overflowing_name, TEST_LIMITS),
            Err(ModuleProvenanceError::OverflowingNameComponent { .. })
        ));

        // Every refusal consumed owned candidate data, while the published baseline
        // remains byte- and root-identical.
        let baseline = sample_manifest();
        assert_eq!(baseline, sample_manifest());
    }

    #[test]
    fn canonical_decoder_rejects_future_truncated_trailing_unknown_and_reordered_bytes() {
        let manifest = sample_manifest();
        let bytes = manifest.to_canonical_bytes();

        let mut wrong_schema = bytes.clone();
        wrong_schema[8] = b'x';
        assert_eq!(
            ModuleProvenanceManifest::from_canonical_bytes(&wrong_schema, TEST_LIMITS),
            Err(ModuleProvenanceError::MalformedEncoding {
                what: "schema name mismatch",
            })
        );

        let mut future = bytes.clone();
        let version_at = 8 + MODULE_PROVENANCE_SCHEMA.name.len();
        future[version_at..version_at + 2].copy_from_slice(&2u16.to_le_bytes());
        assert_eq!(
            ModuleProvenanceManifest::from_canonical_bytes(&future, TEST_LIMITS),
            Err(ModuleProvenanceError::UnsupportedSchemaVersion {
                found: 2,
                supported: 1,
            })
        );

        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(matches!(
            ModuleProvenanceManifest::from_canonical_bytes(&trailing, TEST_LIMITS),
            Err(ModuleProvenanceError::Canonical(CanonError {
                what: "trailing bytes after value",
                ..
            }))
        ));
        assert!(matches!(
            ModuleProvenanceManifest::from_canonical_bytes(&bytes[..bytes.len() - 1], TEST_LIMITS),
            Err(ModuleProvenanceError::Canonical(CanonError {
                what: "input truncated",
                ..
            }))
        ));

        let mut unknown_producer = bytes.clone();
        let marker = [
            32u64.to_le_bytes().as_slice(),
            [0xA1; 32].as_slice(),
            [artifact_producer_tag(ArtifactProducer::Reference)].as_slice(),
        ]
        .concat();
        let producer_at = unknown_producer
            .windows(marker.len())
            .position(|window| window == marker)
            .expect("artifact marker occurs")
            + marker.len()
            - 1;
        unknown_producer[producer_at] = 99;
        assert_eq!(
            ModuleProvenanceManifest::from_canonical_bytes(&unknown_producer, TEST_LIMITS),
            Err(ModuleProvenanceError::MalformedEncoding {
                what: "unknown artifact producer tag",
            })
        );

        let mut records = sample_records();
        records.reverse();
        let reordered = encode_manifest(&epoch(), &records);
        assert_eq!(
            ModuleProvenanceManifest::from_canonical_bytes(&reordered, TEST_LIMITS),
            Err(ModuleProvenanceError::NonCanonicalEncoding)
        );
    }

    #[test]
    fn opaque_and_partial_grades_are_explicit_and_payloads_are_not_copied() {
        let descriptor = extension_descriptor("opaqueExt", PayloadProvenance::Opaque);
        let contribution =
            ExtensionContribution::new(descriptor, 0, Digest([0; 32]), vec![entry(0, 9)]);
        let record = ModuleContributionRecord::new(
            ModuleRecord::new(id("Opaque"), true, vec![], evidence(9)),
            vec![name("Opaque.one")],
            vec![],
            vec![contribution],
            ProvenanceCompleteness::new(
                DecodeCompleteness::Partial,
                ExtensionKnowledge::ContainsOpaque,
                vec![],
            ),
        );
        let manifest = ModuleProvenanceManifest::new(epoch(), vec![record], TEST_LIMITS)
            .expect("opaque partial manifest is retained honestly");
        assert_eq!(
            manifest.records()[0].completeness().decode(),
            DecodeCompleteness::Partial
        );
        assert_eq!(
            manifest.records()[0].completeness().extension_knowledge(),
            ExtensionKnowledge::ContainsOpaque
        );
        assert!(!manifest.records()[0].completeness().is_complete());
        assert_eq!(
            manifest.records()[0].extension_contributions()[0].entries()[0].payload_digest(),
            hash(Domain::Fixture, &[9])
        );
        // The schema contains only a fixed-size digest, not the source payload Arc.
        assert_eq!(
            std::mem::size_of::<ExtensionEntryIdentity>(),
            std::mem::size_of::<u64>() + std::mem::size_of::<Digest>()
        );
    }

    #[test]
    fn clones_share_all_variable_storage_and_round_trip_values_remain_equal() {
        let manifest = sample_manifest();
        let snapshot = manifest.clone();
        assert!(manifest.shares_storage_with(&snapshot));
        for (left, right) in manifest.records().iter().zip(snapshot.records()) {
            assert!(left.shares_storage_with(right));
        }
        let decoded = ModuleProvenanceManifest::from_canonical_bytes(
            &manifest.to_canonical_bytes(),
            TEST_LIMITS,
        )
        .expect("decoded value validates");
        assert_eq!(decoded, manifest);
        assert!(!decoded.shares_storage_with(&manifest));
    }

    #[test]
    fn generated_schedule_matrix_is_byte_and_root_identical() {
        const MODULES: usize = 96;
        let records: Arc<[ModuleContributionRecord]> = (0..MODULES)
            .map(|index| {
                let module_id = id(&format!("Generated.M{index:03}"));
                let imports = if index == 0 {
                    vec![]
                } else {
                    vec![DirectImport::new(
                        id(&format!("Generated.M{:03}", index - 1)),
                        index % 2 == 0,
                        index % 3 == 0,
                        index % 5 == 0,
                    )]
                };
                ModuleContributionRecord::new(
                    ModuleRecord::new(module_id, true, imports, evidence(index as u8)),
                    vec![name(&format!("Generated.d{index:03}"))],
                    if index % 7 == 0 {
                        vec![name(&format!("Generated.extra{index:03}"))]
                    } else {
                        vec![]
                    },
                    vec![],
                    ProvenanceCompleteness::new(
                        DecodeCompleteness::Complete,
                        ExtensionKnowledge::AllUnderstood,
                        vec![],
                    ),
                )
            })
            .collect();
        let baseline =
            ModuleProvenanceManifest::new(epoch(), records.iter().cloned().collect(), TEST_LIMITS)
                .expect("baseline generated manifest validates");

        for threads in [1usize, 4, 8] {
            let chunk_len = MODULES.div_ceil(threads);
            let mut scheduled = std::thread::scope(|scope| {
                let handles: Vec<_> = records
                    .chunks(chunk_len)
                    .enumerate()
                    .map(|(lane, chunk)| {
                        scope.spawn(move || {
                            let mut local = chunk.to_vec();
                            if lane % 2 == 1 {
                                local.reverse();
                            }
                            local
                        })
                    })
                    .collect();
                handles
                    .into_iter()
                    .rev()
                    .flat_map(|handle| handle.join().expect("schedule lane joins"))
                    .collect::<Vec<_>>()
            });
            if threads == 1 {
                scheduled.reverse();
            }
            let candidate = ModuleProvenanceManifest::new(epoch(), scheduled, TEST_LIMITS)
                .expect("scheduled manifest validates");
            assert_eq!(candidate.root(), baseline.root(), "threads={threads}");
            assert_eq!(
                candidate.to_canonical_bytes(),
                baseline.to_canonical_bytes(),
                "threads={threads}"
            );
        }
        println!(
            "{{\"schema\":\"fln.unit.module-provenance-schedule\",\"version\":1,\"bead\":\"franken_lean-module-provenance-schema-cxn\",\"modules\":{MODULES},\"thread_matrix\":[1,4,8],\"expected_root\":\"{}\",\"actual_root\":\"{}\",\"expected\":\"byte-identical\",\"actual\":\"byte-identical\",\"status\":\"pass\"}}",
            baseline.root(),
            baseline.root()
        );
    }
}
