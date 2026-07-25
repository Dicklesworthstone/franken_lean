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
    ModuleGraphAdmission, ModuleGraphError, ModuleGraphInconclusive, ModuleGraphLimits,
    ModuleGraphOutcome, ModuleGraphResource, ModuleId, ModuleRecord, name_stats,
};

// ---------------------------------------------------------------------------------
// The normative V1 contribution table (bead `franken_lean-3ldh`).
//
// The schema layout used to live only in prose plus a set of sensitivity tests. Prose
// cannot be joined against the encoder, so a field could be added, moved, or silently
// dropped from the root without any artifact disagreeing. This table is the normative
// statement, in data, and the tests below hold it to the standard the design set:
// **missing, duplicate, stale, or unclassified rows block closure.**
// ---------------------------------------------------------------------------------

/// Whether a field is a scalar, an ordered replay sequence, a canonical set, or a
/// count derived from the sequence it introduces.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum V1SequenceLaw {
    Scalar,
    /// Order is semantic replay data and duplicates are retained.
    OrderedSequence,
    /// Order is canonical (sorted) and duplicates are removed.
    CanonicalSet,
    /// A length introducing the sequence that follows it.
    DerivedCount,
}

/// The ordinal namespace a row's position belongs to. Separate namespaces are what
/// keep an ordinary declaration and an extra generated declaration from sharing a
/// coordinate.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum V1OrdinalNamespace {
    None,
    DirectImport,
    OrdinaryContribution,
    ExtraContribution,
    ExtensionSource,
    MissingDependency,
}

/// What happens when the same value appears twice.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum V1DuplicatePolicy {
    NotApplicable,
    /// Retained verbatim — this is ordered replay data.
    Retained,
    /// A typed refusal: the same declaration cannot be published twice.
    RefusedAsConflict,
    /// Sorted and deduplicated as part of canonicalization.
    DedupedCanonically,
}

/// Whether a row carries identity or points at payload owned elsewhere. The schema is
/// identity-only by design: values and raw bytes stay `Arc`-backed in the Environment
/// and the extension journal.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum V1Ownership {
    /// The row *is* identity — a name, tag, count, or digest.
    Identity,
    /// The row names payload owned by another layer and never copied here.
    PayloadOwnedElsewhere,
}

/// How a row reaches [`ModuleProvenanceRoot`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum V1RootParticipation {
    /// Written into the canonical bytes; changing it changes the root.
    Direct,
    /// Not written, because validation pins it to a value that is written. Omitting
    /// it is safe *only* while that validation exists — the join is the evidence.
    ViaValidation,
    /// Deliberately excluded from the canonical bytes.
    Excluded,
}

/// Which completeness axis a row feeds.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum V1CompletenessAxis {
    None,
    Capture,
    Transparency,
    MissingDependencies,
}

/// Exact canonical width, so the table can predict a manifest's byte length.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum V1Width {
    /// A fixed number of bytes (`u8`/`bool` = 1, `u64` = 8, …).
    Fixed(usize),
    /// `CanonWriter::bytes`: an 8-byte length prefix plus the payload.
    LengthPrefixed(usize),
    /// A `Name` body, whose width depends on the name and is measured from the
    /// fixture rather than guessed.
    NameBody,
    /// `CanonWriter::schema`: a length-prefixed name plus a `u16` version.
    SchemaHeader,
}

/// How many times a row occurs in a manifest, so the width prediction can be scaled
/// by the manifest's own facts instead of a hand-counted constant.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum V1Multiplicity {
    Once,
    PerModule,
    PerDirectImportRow,
    PerDeclaration,
    PerExtraDeclaration,
    PerExtensionContribution,
    PerExtensionEntry,
    PerMissingDependency,
    /// Present in the value but not in the canonical bytes.
    NotEncoded,
}

/// One row of the normative V1 contribution table.
#[derive(Debug, Clone, Copy)]
pub struct V1FieldRow {
    /// Stable field tag. Unique across the table — duplicates block closure.
    pub tag: &'static str,
    /// The decoder source field this row is pinned to.
    pub decoder_source: &'static str,
    pub value_type: &'static str,
    pub sequence_law: V1SequenceLaw,
    pub ordinal_namespace: V1OrdinalNamespace,
    /// Ordinal width in bits, where the row has an ordinal.
    pub ordinal_width_bits: Option<u32>,
    pub duplicate_policy: V1DuplicatePolicy,
    /// The canonical inputs that decide this row's identity.
    pub identity_inputs: &'static str,
    pub ownership: V1Ownership,
    pub root_participation: V1RootParticipation,
    pub completeness_axis: V1CompletenessAxis,
    /// The typed outcome a malformed value earns.
    pub malformed_outcome: &'static str,
    /// The resource this row is charged against, if any.
    pub resource_charge: Option<ModuleProvenanceResource>,
    pub width: V1Width,
    pub multiplicity: V1Multiplicity,
    /// The label of the field-family sensitivity observation that witnesses this
    /// row's root participation, where one exists. Every `Direct` row must either
    /// carry a witness or be a `DerivedCount` (whose sensitivity is witnessed by the
    /// sequence it introduces).
    pub sensitivity_witness: Option<&'static str>,
}

/// The normative V1 contribution table. One row per field of the canonical
/// encoding, in encoder order, plus the rows that are deliberately *not* encoded.
///
/// This is the artifact the design asked for: per row, the field tag, its pinned
/// decoder source, value type, ordered-sequence versus canonical-set law, ordinal
/// namespace and width, duplicate policy, canonical identity inputs,
/// payload-versus-identity ownership, root participation, completeness-axis effect,
/// malformed outcome, and resource charge.
pub const MODULE_PROVENANCE_V1_TABLE: &[V1FieldRow] = &[
    V1FieldRow {
        tag: "schema",
        decoder_source: "MODULE_PROVENANCE_SCHEMA",
        value_type: "SchemaId",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "schema name and version",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding / UnsupportedSchemaVersion",
        resource_charge: Some(ModuleProvenanceResource::EncodedBytes),
        width: V1Width::SchemaHeader,
        multiplicity: V1Multiplicity::Once,
        sensitivity_witness: None,
    },
    V1FieldRow {
        tag: "epoch.tag",
        decoder_source: "ModuleEpoch::tag",
        value_type: "str",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "exact tag bytes",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "InvalidModuleGraph(MalformedEpoch)",
        resource_charge: Some(ModuleProvenanceResource::EncodedBytes),
        width: V1Width::LengthPrefixed(0),
        multiplicity: V1Multiplicity::Once,
        sensitivity_witness: Some("epoch.tag"),
    },
    V1FieldRow {
        tag: "epoch.commit",
        decoder_source: "ModuleEpoch::commit",
        value_type: "str",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "exact commit bytes",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "InvalidModuleGraph(MalformedEpoch)",
        resource_charge: Some(ModuleProvenanceResource::EncodedBytes),
        width: V1Width::LengthPrefixed(0),
        multiplicity: V1Multiplicity::Once,
        sensitivity_witness: Some("epoch.commit"),
    },
    V1FieldRow {
        tag: "records.count",
        decoder_source: "records.len()",
        value_type: "u64",
        sequence_law: V1SequenceLaw::DerivedCount,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "module-record cardinality",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "ResourceLimitExceeded(Modules) / MalformedEncoding",
        resource_charge: Some(ModuleProvenanceResource::Modules),
        width: V1Width::Fixed(8),
        multiplicity: V1Multiplicity::Once,
        sensitivity_witness: None,
    },
    V1FieldRow {
        tag: "module.id",
        decoder_source: "ModuleRecord::id",
        value_type: "Name",
        sequence_law: V1SequenceLaw::CanonicalSet,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::RefusedAsConflict,
        identity_inputs: "structural Name",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "DuplicateModule / InvalidModuleGraph(AnonymousModule)",
        resource_charge: Some(ModuleProvenanceResource::NameDepth),
        width: V1Width::NameBody,
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: Some("module.id"),
    },
    V1FieldRow {
        tag: "module.is_module",
        decoder_source: "ModuleRecord::is_module",
        value_type: "bool",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "flag value",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: Some("module.is_module"),
    },
    V1FieldRow {
        tag: "module.direct_imports.count",
        decoder_source: "ModuleRecord::direct_imports().len()",
        value_type: "u64",
        sequence_law: V1SequenceLaw::DerivedCount,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "direct-row cardinality",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "ResourceLimitExceeded(DirectImportRows)",
        resource_charge: Some(ModuleProvenanceResource::DirectImportRows),
        width: V1Width::Fixed(8),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: None,
    },
    V1FieldRow {
        tag: "direct_import.module",
        decoder_source: "DirectImport::module",
        value_type: "Name",
        sequence_law: V1SequenceLaw::OrderedSequence,
        ordinal_namespace: V1OrdinalNamespace::DirectImport,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::Retained,
        identity_inputs: "structural Name at this ordinal",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::MissingDependencies,
        malformed_outcome: "InvalidModuleGraph(AnonymousImport)",
        resource_charge: Some(ModuleProvenanceResource::DirectImportRows),
        width: V1Width::NameBody,
        multiplicity: V1Multiplicity::PerDirectImportRow,
        sensitivity_witness: Some("direct_import.module+missing_dependency"),
    },
    V1FieldRow {
        tag: "direct_import.import_all",
        decoder_source: "DirectImport::import_all",
        value_type: "bool",
        sequence_law: V1SequenceLaw::OrderedSequence,
        ordinal_namespace: V1OrdinalNamespace::DirectImport,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::Retained,
        identity_inputs: "flag value at this ordinal",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerDirectImportRow,
        sensitivity_witness: Some("direct_import.import_all"),
    },
    V1FieldRow {
        tag: "direct_import.is_exported",
        decoder_source: "DirectImport::is_exported",
        value_type: "bool",
        sequence_law: V1SequenceLaw::OrderedSequence,
        ordinal_namespace: V1OrdinalNamespace::DirectImport,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::Retained,
        identity_inputs: "flag value at this ordinal",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerDirectImportRow,
        sensitivity_witness: Some("direct_import.is_exported"),
    },
    V1FieldRow {
        tag: "direct_import.is_meta",
        decoder_source: "DirectImport::is_meta",
        value_type: "bool",
        sequence_law: V1SequenceLaw::OrderedSequence,
        ordinal_namespace: V1OrdinalNamespace::DirectImport,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::Retained,
        identity_inputs: "flag value at this ordinal",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerDirectImportRow,
        sensitivity_witness: Some("direct_import.is_meta"),
    },
    V1FieldRow {
        tag: "artifact.content_digest",
        decoder_source: "ArtifactEvidence::content_digest",
        value_type: "Digest",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "exact 32 digest bytes",
        ownership: V1Ownership::PayloadOwnedElsewhere,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding",
        resource_charge: Some(ModuleProvenanceResource::EncodedBytes),
        width: V1Width::LengthPrefixed(32),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: Some("artifact.content_digest"),
    },
    V1FieldRow {
        tag: "artifact.producer",
        decoder_source: "ArtifactEvidence::producer",
        value_type: "ArtifactProducer tag",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "frozen enum tag",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding(unknown artifact producer tag)",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: Some("artifact.producer"),
    },
    V1FieldRow {
        tag: "artifact.grade",
        decoder_source: "ArtifactEvidence::grade",
        value_type: "ArtifactGrade tag",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "frozen enum tag",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding(unknown artifact grade tag)",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: Some("artifact.grade"),
    },
    V1FieldRow {
        tag: "artifact.epoch",
        decoder_source: "ArtifactEvidence::epoch",
        value_type: "ModuleEpoch",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "pinned equal to the manifest epoch by validation",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::ViaValidation,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "InvalidModuleGraph(EpochMismatch)",
        resource_charge: None,
        width: V1Width::Fixed(0),
        multiplicity: V1Multiplicity::NotEncoded,
        sensitivity_witness: None,
    },
    V1FieldRow {
        tag: "declarations.count",
        decoder_source: "ModuleContributionRecord::declarations.len()",
        value_type: "u64",
        sequence_law: V1SequenceLaw::DerivedCount,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "ordinary-contribution cardinality",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "ResourceLimitExceeded(DeclarationNames)",
        resource_charge: Some(ModuleProvenanceResource::DeclarationNames),
        width: V1Width::Fixed(8),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: None,
    },
    V1FieldRow {
        tag: "declarations.name",
        decoder_source: "ModuleContributionRecord::declarations[i]",
        value_type: "Name",
        sequence_law: V1SequenceLaw::OrderedSequence,
        ordinal_namespace: V1OrdinalNamespace::OrdinaryContribution,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::RefusedAsConflict,
        identity_inputs: "structural Name at this ordinal",
        ownership: V1Ownership::PayloadOwnedElsewhere,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "DuplicateDeclaration / ConflictingDeclarationOwner / AnonymousDeclaration",
        resource_charge: Some(ModuleProvenanceResource::DeclarationNames),
        width: V1Width::NameBody,
        multiplicity: V1Multiplicity::PerDeclaration,
        sensitivity_witness: Some("declarations.order"),
    },
    V1FieldRow {
        tag: "extra_declarations.count",
        decoder_source: "ModuleContributionRecord::extra_declarations.len()",
        value_type: "u64",
        sequence_law: V1SequenceLaw::DerivedCount,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "extra-contribution cardinality",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "ResourceLimitExceeded(DeclarationNames)",
        resource_charge: Some(ModuleProvenanceResource::DeclarationNames),
        width: V1Width::Fixed(8),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: None,
    },
    V1FieldRow {
        tag: "extra_declarations.name",
        decoder_source: "ModuleContributionRecord::extra_declarations[i]",
        value_type: "Name",
        sequence_law: V1SequenceLaw::OrderedSequence,
        ordinal_namespace: V1OrdinalNamespace::ExtraContribution,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::RefusedAsConflict,
        identity_inputs: "structural Name at this ordinal, in its own namespace",
        ownership: V1Ownership::PayloadOwnedElsewhere,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "DuplicateDeclaration / ConflictingDeclarationOwner",
        resource_charge: Some(ModuleProvenanceResource::DeclarationNames),
        width: V1Width::NameBody,
        multiplicity: V1Multiplicity::PerExtraDeclaration,
        sensitivity_witness: Some("extra_declarations.identity"),
    },
    V1FieldRow {
        tag: "extension_contributions.count",
        decoder_source: "ModuleContributionRecord::extension_contributions.len()",
        value_type: "u64",
        sequence_law: V1SequenceLaw::DerivedCount,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "contribution cardinality",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "ResourceLimitExceeded(ExtensionContributions)",
        resource_charge: Some(ModuleProvenanceResource::ExtensionContributions),
        width: V1Width::Fixed(8),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: None,
    },
    V1FieldRow {
        tag: "extension.descriptor.name",
        decoder_source: "ExtensionDescriptor::name",
        value_type: "Name",
        sequence_law: V1SequenceLaw::OrderedSequence,
        ordinal_namespace: V1OrdinalNamespace::ExtensionSource,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::Retained,
        identity_inputs: "structural Name",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "AnonymousExtension",
        resource_charge: Some(ModuleProvenanceResource::NameDepth),
        width: V1Width::NameBody,
        multiplicity: V1Multiplicity::PerExtensionContribution,
        sensitivity_witness: Some("extension.name"),
    },
    V1FieldRow {
        tag: "extension.descriptor.merge",
        decoder_source: "ExtensionDescriptor::merge",
        value_type: "MergeSemantics tag",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "frozen enum tag",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding(unknown merge policy tag)",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerExtensionContribution,
        sensitivity_witness: Some("extension.merge"),
    },
    V1FieldRow {
        tag: "extension.descriptor.checkpoint",
        decoder_source: "ExtensionDescriptor::checkpoint",
        value_type: "CheckpointSemantics tag",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "frozen enum tag",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding(unknown checkpoint policy tag)",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerExtensionContribution,
        sensitivity_witness: Some("extension.checkpoint"),
    },
    V1FieldRow {
        tag: "extension.descriptor.provenance",
        decoder_source: "ExtensionDescriptor::provenance",
        value_type: "PayloadProvenance tag",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "frozen enum tag",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::Transparency,
        malformed_outcome: "MalformedEncoding / PayloadTransparencyMismatch",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerExtensionContribution,
        sensitivity_witness: Some("extension.provenance+transparency"),
    },
    V1FieldRow {
        tag: "extension.range_start",
        decoder_source: "ExtensionContribution::start",
        value_type: "u64",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "target-journal start; scoped to one root and extension, NOT stable content identity",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "EntryRangeOverflow",
        resource_charge: None,
        width: V1Width::Fixed(8),
        multiplicity: V1Multiplicity::PerExtensionContribution,
        sensitivity_witness: Some("extension.range_start"),
    },
    V1FieldRow {
        tag: "extension.base_history_digest",
        decoder_source: "ExtensionContribution::base_history_digest",
        value_type: "Digest",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "exact 32 digest bytes",
        ownership: V1Ownership::PayloadOwnedElsewhere,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding",
        resource_charge: Some(ModuleProvenanceResource::EncodedBytes),
        width: V1Width::LengthPrefixed(32),
        multiplicity: V1Multiplicity::PerExtensionContribution,
        sensitivity_witness: Some("extension.base_history_digest"),
    },
    V1FieldRow {
        tag: "extension.entries.count",
        decoder_source: "ExtensionContribution::entries.len()",
        value_type: "u64",
        sequence_law: V1SequenceLaw::DerivedCount,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "occurrence cardinality; also the applied range length",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "EmptyExtensionContribution / ResourceLimitExceeded(ExtensionEntries)",
        resource_charge: Some(ModuleProvenanceResource::ExtensionEntries),
        width: V1Width::Fixed(8),
        multiplicity: V1Multiplicity::PerExtensionContribution,
        sensitivity_witness: Some("extension.entry_count"),
    },
    V1FieldRow {
        tag: "extension.entry_id",
        decoder_source: "ExtensionContribution::entries[j]",
        value_type: "ExtensionEntryId",
        sequence_law: V1SequenceLaw::OrderedSequence,
        ordinal_namespace: V1OrdinalNamespace::ExtensionSource,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::Retained,
        identity_inputs: "entry schema, epoch, descriptor identity, exact payload bytes",
        ownership: V1Ownership::PayloadOwnedElsewhere,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "MalformedEncoding",
        resource_charge: Some(ModuleProvenanceResource::ExtensionEntries),
        width: V1Width::LengthPrefixed(32),
        multiplicity: V1Multiplicity::PerExtensionEntry,
        sensitivity_witness: Some("extension.entry_id"),
    },
    V1FieldRow {
        tag: "extension.target_position",
        decoder_source: "derived: start + source ordinal",
        value_type: "u64",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::ExtensionSource,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "none: a derived coordinate, never an identity input",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Excluded,
        completeness_axis: V1CompletenessAxis::None,
        malformed_outcome: "EntryRangeOverflow",
        resource_charge: None,
        width: V1Width::Fixed(0),
        multiplicity: V1Multiplicity::NotEncoded,
        sensitivity_witness: None,
    },
    V1FieldRow {
        tag: "completeness.capture",
        decoder_source: "ProvenanceCompleteness::capture",
        value_type: "CaptureStatus tag",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "frozen enum tag",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::Capture,
        malformed_outcome: "MalformedEncoding / CaptureStatusContradicted",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: Some("completeness.capture"),
    },
    V1FieldRow {
        tag: "completeness.transparency",
        decoder_source: "ProvenanceCompleteness::transparency",
        value_type: "PayloadTransparency tag",
        sequence_law: V1SequenceLaw::Scalar,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "frozen enum tag, recomputed from descriptors",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::Transparency,
        malformed_outcome: "MalformedEncoding / PayloadTransparencyMismatch",
        resource_charge: None,
        width: V1Width::Fixed(1),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: Some("completeness.transparency"),
    },
    V1FieldRow {
        tag: "completeness.missing_dependencies.count",
        decoder_source: "ProvenanceCompleteness::missing_dependencies.len()",
        value_type: "u64",
        sequence_law: V1SequenceLaw::DerivedCount,
        ordinal_namespace: V1OrdinalNamespace::None,
        ordinal_width_bits: None,
        duplicate_policy: V1DuplicatePolicy::NotApplicable,
        identity_inputs: "missing-target cardinality",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::MissingDependencies,
        malformed_outcome: "ResourceLimitExceeded(MissingDependencies)",
        resource_charge: Some(ModuleProvenanceResource::MissingDependencies),
        width: V1Width::Fixed(8),
        multiplicity: V1Multiplicity::PerModule,
        sensitivity_witness: None,
    },
    V1FieldRow {
        tag: "completeness.missing_dependencies.name",
        decoder_source: "ProvenanceCompleteness::missing_dependencies[i]",
        value_type: "Name",
        sequence_law: V1SequenceLaw::CanonicalSet,
        ordinal_namespace: V1OrdinalNamespace::MissingDependency,
        ordinal_width_bits: Some(64),
        duplicate_policy: V1DuplicatePolicy::DedupedCanonically,
        identity_inputs: "structural Name, sorted and deduplicated",
        ownership: V1Ownership::Identity,
        root_participation: V1RootParticipation::Direct,
        completeness_axis: V1CompletenessAxis::MissingDependencies,
        malformed_outcome: "MissingDependenciesMismatch",
        resource_charge: Some(ModuleProvenanceResource::MissingDependencies),
        width: V1Width::NameBody,
        multiplicity: V1Multiplicity::PerMissingDependency,
        sensitivity_witness: Some("completeness.missing_dependency_set"),
    },
];

/// Frozen canonical schema for the complete provenance manifest.
///
/// Version 1 is positional and length-delimited:
///
/// 1. schema name/version, epoch tag/commit, canonical module count;
/// 2. for each module in `Name.cmp` order: module name, `is_module`, exact ordered
///    direct-import rows (target, `import_all`, `is_exported`, `is_meta`), then
///    artifact digest/producer/grade;
/// 3. ordered declarations, ordered extra declarations, and ordered extension
///    contributions; each contribution carries its descriptor, target-journal start,
///    base-history digest, and its module-local source sequence of
///    [`ExtensionEntryId`] content identities — the source ordinal is the position in
///    that sequence and the target position is `start + ordinal`, so no rebasable
///    journal coordinate is stored per entry;
/// 4. the capture-status and payload-transparency axes, and the canonical
///    missing-target set. The authority axis is derived from that tuple and is
///    deliberately absent from the bytes, so no record can assert a capability it has
///    not earned.
///
/// Enum tags are frozen below by paired exhaustive `*_tag`/`read_*` functions:
/// producer `Reference=0, FrankenLean=1`; grade
/// `Provisional=0, Verified=1, OracleFixture=2`; merge
/// `AppendOrdered=0, SetUnion=1, ConflictsRequireReview=2`; checkpoint
/// `JournalSuffix=0, FullJournal=1`; payload provenance
/// `Understood=0, Opaque=1`; capture status `Complete=0, Partial=1, Missing=2`;
/// payload transparency
/// `Understood=0, Mixed=1, Opaque=2`. Unknown tags and future schema versions are
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

/// **Capture axis** — how much of this module's contribution the decoder obtained.
///
/// This says nothing about whether the captured bytes are understood; that is the
/// independent [`PayloadTransparency`] axis. `Missing` is not "empty": a module that
/// genuinely contributes nothing is `Complete` with zero contributions, whereas
/// `Missing` records that the contributions could not be captured at all. The two
/// encode the same empty content and make opposite claims about it, which is precisely
/// why the axis is explicit.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum CaptureStatus {
    Complete,
    Partial,
    Missing,
}

/// **Transparency axis** — whether the captured extension payloads are semantically
/// understood.
///
/// Orthogonal to [`CaptureStatus`]: an opaque payload can be byte-complete, and an
/// understood one can be partially captured. `Mixed` is a real state, not a rounding
/// of `Opaque` — it is what keeps an opaque boundary *localized* and addressable
/// instead of condemning the whole module.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PayloadTransparency {
    Understood,
    Mixed,
    Opaque,
}

/// **Authority axis** — one capability a consumer may exercise over a record.
///
/// Authority is *derived*, never stored: it is a pure function of the capture and
/// transparency axes plus the missing-dependency set (see
/// [`ProvenanceCompleteness::authority`]). Because the manifest carries no authority
/// field, a record cannot assert a capability it has not earned — unjustified
/// authority is unrepresentable rather than merely rejected on decode, and every
/// decode recomputes it by construction.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum ProvenanceAuthority {
    /// Read what was recorded. Requires only that something was captured.
    Inspection,
    /// Replay this module's exact ordered extension entries. Opacity is irrelevant —
    /// opaque bytes replay verbatim — so this needs capture alone.
    ExactReplay,
    /// Enumerate every declaration and contribution the module owns.
    CompleteInventory,
    /// Serve as an authoritative cache identity. Opacity is tolerable because entry
    /// identity is byte-exact, but an unresolved import means the recorded closure is
    /// not the real one.
    AuthoritativeCache,
    /// Compute a precise invalidation cone. The strictest capability: it is the only
    /// one that needs semantic attribution, so an opaque or mixed payload withholds it.
    FineInvalidation,
}

impl ProvenanceAuthority {
    /// Every capability, in strengthening order. Iterating this rather than a
    /// hand-written list is what makes "omit an axis" detectable in the tests.
    pub const ALL: [ProvenanceAuthority; 5] = [
        ProvenanceAuthority::Inspection,
        ProvenanceAuthority::ExactReplay,
        ProvenanceAuthority::CompleteInventory,
        ProvenanceAuthority::AuthoritativeCache,
        ProvenanceAuthority::FineInvalidation,
    ];
}

/// The three independent completeness axes.
///
/// They are deliberately *not* reducible to one another and there is no boolean
/// "complete" accessor: a single flag would have to pick an axis to privilege, and
/// every caller that asked it would silently inherit that choice. Ask the axis you
/// actually mean — [`capture`](Self::capture), [`transparency`](Self::transparency),
/// [`missing_dependencies`](Self::missing_dependencies) — or ask what you are allowed
/// to do, via [`authority`](Self::authority).
///
/// Missing dependencies are a canonical set; declaration and extension arrays
/// elsewhere remain ordered sequences.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProvenanceCompleteness {
    capture: CaptureStatus,
    transparency: PayloadTransparency,
    missing_dependencies: Arc<[ModuleId]>,
}

impl ProvenanceCompleteness {
    pub fn new(
        capture: CaptureStatus,
        transparency: PayloadTransparency,
        mut missing_dependencies: Vec<ModuleId>,
    ) -> Self {
        missing_dependencies.sort();
        missing_dependencies.dedup();
        Self {
            capture,
            transparency,
            missing_dependencies: missing_dependencies.into(),
        }
    }

    pub fn capture(&self) -> CaptureStatus {
        self.capture
    }

    pub fn transparency(&self) -> PayloadTransparency {
        self.transparency
    }

    pub fn missing_dependencies(&self) -> &[ModuleId] {
        &self.missing_dependencies
    }

    /// Whether the full axis tuple justifies one capability.
    ///
    /// Each arm names the axes it consults and ignores the rest. `Complete + Opaque`
    /// and `Partial + Understood` are both legal here and both yield a *reduced* set
    /// rather than nothing — that is the whole point of keeping the axes apart.
    pub fn grants(&self, authority: ProvenanceAuthority) -> bool {
        let captured_everything = self.capture == CaptureStatus::Complete;
        let closure_is_known = self.missing_dependencies.is_empty();
        let semantics_are_attributable = self.transparency == PayloadTransparency::Understood;
        match authority {
            ProvenanceAuthority::Inspection => self.capture != CaptureStatus::Missing,
            ProvenanceAuthority::ExactReplay | ProvenanceAuthority::CompleteInventory => {
                captured_everything
            }
            ProvenanceAuthority::AuthoritativeCache => captured_everything && closure_is_known,
            ProvenanceAuthority::FineInvalidation => {
                captured_everything && closure_is_known && semantics_are_attributable
            }
        }
    }

    /// The complete derived capability set, in strengthening order.
    pub fn authority(&self) -> Vec<ProvenanceAuthority> {
        ProvenanceAuthority::ALL
            .into_iter()
            .filter(|candidate| self.grants(*candidate))
            .collect()
    }
}

/// Dedicated versioned derivation for extension-entry content identity.
///
/// It shares [`Domain::ModuleProvenance`] with the manifest root but is separated from
/// it by this canonical schema prefix, so an entry-id preimage can never coincide with
/// a manifest preimage.
pub const EXTENSION_ENTRY_ID_SCHEMA: SchemaId = SchemaId {
    name: "fln.env.module-provenance.entry-id",
    version: 1,
};

/// Stable content identity of one extension journal entry.
///
/// Derived from the versioned entry schema, the module epoch, the exact extension
/// descriptor identity, and the exact raw payload bytes — and from nothing else. The
/// contributing module, the module-local source ordinal, the target journal position,
/// the applied range, the journal branch, and every allocation or `Arc` fact are
/// deliberately excluded, so the identity survives journal rebasing, replay, restore,
/// and merge. Two occurrences carrying the same descriptor and payload therefore share
/// this id by construction; they remain distinguishable *as occurrences* by the
/// contributing [`ModuleId`] plus the module-local source ordinal
/// ([`ExtensionContribution::source_ordinal`]).
///
/// The id is a locator and a fast inequality check. Digest collision resistance is a
/// HYPOTHESIS of the selected digest, never an injectivity proof: wherever equality or
/// ownership is load-bearing, the exact canonical fields decide.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ExtensionEntryId(Digest);

impl ExtensionEntryId {
    /// Derive the identity from the only inputs it is permitted to depend on. The
    /// payload is hashed, never retained: provenance stores identity, and the bytes
    /// themselves stay `Arc`-backed in the extension journal.
    pub fn derive(epoch: &ModuleEpoch, descriptor: &ExtensionDescriptor, payload: &[u8]) -> Self {
        let mut writer = CanonWriter::new();
        writer.schema(EXTENSION_ENTRY_ID_SCHEMA);
        writer.str(epoch.tag());
        writer.str(epoch.commit());
        descriptor.name.write_body(&mut writer);
        writer.u8(merge_semantics_tag(descriptor.merge));
        writer.u8(checkpoint_semantics_tag(descriptor.checkpoint));
        writer.u8(payload_provenance_tag(descriptor.provenance));
        writer.bytes(payload);
        Self(hash(Domain::ModuleProvenance, &writer.into_bytes()))
    }

    /// Reconstruct from canonical bytes. Crate-internal on purpose: an external caller
    /// must [`derive`](Self::derive) the id from the payload rather than assert one,
    /// so no fabricated identity can enter a manifest.
    pub(crate) const fn from_digest(digest: Digest) -> Self {
        Self(digest)
    }

    pub fn digest(&self) -> Digest {
        self.0
    }
}

impl std::fmt::Display for ExtensionEntryId {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(formatter)
    }
}

/// One exact ordered range contributed to a registered extension.
///
/// `entries` is the module-local source sequence: the array index *is* the entry's
/// `ExtensionSourceOrdinal` (zero-based), and empty or repeated occurrences are
/// retained rather than deduplicated, because this is ordered replay data.
///
/// `start` is the target journal position the range was applied at. It is scoped to
/// one committed provenance root and one extension, may change after replay, restore,
/// or merge, and is never an input to any [`ExtensionEntryId`]. Source ordinal and
/// target position are therefore two different coordinates and never aliases.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExtensionContribution {
    descriptor: ExtensionDescriptor,
    start: u64,
    base_history_digest: Digest,
    entries: Arc<[ExtensionEntryId]>,
}

impl ExtensionContribution {
    pub fn new(
        descriptor: ExtensionDescriptor,
        start: u64,
        base_history_digest: Digest,
        entries: Vec<ExtensionEntryId>,
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

    /// Target-journal start of the applied range. Not stable content identity.
    pub fn start(&self) -> u64 {
        self.start
    }

    pub fn base_history_digest(&self) -> Digest {
        self.base_history_digest
    }

    pub fn entries(&self) -> &[ExtensionEntryId] {
        &self.entries
    }

    /// Module-local source ordinal of the occurrence at `index` — the coordinate that,
    /// with the contributing module and the entry id, identifies an occurrence.
    pub fn source_ordinal(&self, index: usize) -> Option<u64> {
        if index >= self.entries.len() {
            return None;
        }
        u64::try_from(index).ok()
    }

    /// Current target-journal position of the occurrence at `index`. Scoped to one
    /// committed root and extension; it may differ after replay, restore, or merge.
    pub fn target_position(&self, index: usize) -> Option<u64> {
        self.start.checked_add(self.source_ordinal(index)?)
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

/// How an untrusted candidate that claims an identity relates to one already held.
///
/// The whole point of this type is that [`IdentityVerdict::Collision`] is a *reported
/// outcome*, never a resolution. Nothing here picks a winner, merges, or falls back to
/// the digest: an equal root over unequal canonical values is handed upward as a
/// candidate for atomic application to adjudicate.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IdentityVerdict {
    /// Same root, same canonical bytes. Safe to treat as the same object, which is what
    /// makes cache hits and re-imports idempotent.
    Idempotent,
    /// Different roots. Unrelated objects; the digest's inequality is conclusive because
    /// a hash never reports different for equal inputs.
    Distinct,
    /// Same root, **different** canonical bytes.
    Collision(IdentityCollision),
}

/// Evidence for an equal-digest/unequal-value pair, carrying enough to diagnose it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdentityCollision {
    pub root: ModuleProvenanceRoot,
    pub held_len: usize,
    pub candidate_len: usize,
    /// Byte offset of the first disagreement, or the shorter length when one canonical
    /// value is a strict prefix of the other.
    pub first_divergence: usize,
}

/// Classify a candidate against a held object by claimed root, then by exact canonical
/// value.
///
/// This is the schema's **bounded-model collision seam**. It takes roots and bytes as
/// separate inputs rather than reading them off two manifests, precisely so a test can
/// *inject* the digest equality that a real collision would produce. Injecting that
/// equality is a bounded model: it assumes, counterfactually and only inside the model,
/// that two distinct canonical values digest alike. **No cryptographic collision is
/// claimed, searched for, or found**, and this seam must never be cited as evidence
/// that one exists.
///
/// What the seam does establish is the property that matters if collision resistance
/// ever fails: equal digest plus unequal canonical identity stays *distinguishable*,
/// because equality is decided by the exact bytes and the digest is only ever a fast
/// inequality check. Collision resistance is a HYPOTHESIS of the selected digest
/// (claim type `bounded_model`), never an injectivity proof.
pub fn classify_identity(
    held: (ModuleProvenanceRoot, &[u8]),
    candidate: (ModuleProvenanceRoot, &[u8]),
) -> IdentityVerdict {
    let (held_root, held_bytes) = held;
    let (candidate_root, candidate_bytes) = candidate;
    if held_root != candidate_root {
        return IdentityVerdict::Distinct;
    }
    if held_bytes == candidate_bytes {
        return IdentityVerdict::Idempotent;
    }
    let first_divergence = held_bytes
        .iter()
        .zip(candidate_bytes.iter())
        .position(|(left, right)| left != right)
        .unwrap_or_else(|| held_bytes.len().min(candidate_bytes.len()));
    IdentityVerdict::Collision(IdentityCollision {
        root: held_root,
        held_len: held_bytes.len(),
        candidate_len: candidate_bytes.len(),
        first_divergence,
    })
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
    EntryRangeOverflow {
        module: ModuleId,
        contribution_index: usize,
    },
    PayloadTransparencyMismatch {
        module: ModuleId,
        expected: PayloadTransparency,
        actual: PayloadTransparency,
    },
    /// A record claims its contributions were not captured while carrying some. The
    /// axes are independent, but each still has to describe the same record.
    CaptureStatusContradicted {
        module: ModuleId,
        capture: CaptureStatus,
        declarations: usize,
        extra_declarations: usize,
        extension_contributions: usize,
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
    /// A layer below reported an outcome this construction path cannot request.
    /// An invariant failure, never a verdict about a module (FL-INV-07).
    GraphAdmissionFault {
        what: &'static str,
    },
    Canonical(CanonError),
    MalformedEncoding {
        what: &'static str,
    },
    NonCanonicalEncoding,
    /// An inconsistency inside already-validated state. This is an invariant failure,
    /// never a verdict about a module and never a diagnostic a user caused: the same
    /// shape arriving from outside is an [`IdentityVerdict::Collision`] instead
    /// (FL-INV-07 — inconclusive and faulted outcomes are not rejections).
    InternalFault {
        what: &'static str,
        held: ModuleProvenanceRoot,
        recomputed: ModuleProvenanceRoot,
    },
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
            Self::EntryRangeOverflow {
                module,
                contribution_index,
            } => write!(
                formatter,
                "module `{}` extension contribution {contribution_index} range overflows u64",
                module.name().to_display_string()
            ),
            Self::CaptureStatusContradicted {
                module,
                capture,
                declarations,
                extra_declarations,
                extension_contributions,
            } => write!(
                formatter,
                "module `{}` claims capture {capture:?} while carrying {declarations} declaration(s), {extra_declarations} extra declaration(s), and {extension_contributions} extension contribution(s)",
                module.name().to_display_string()
            ),
            Self::PayloadTransparencyMismatch {
                module,
                expected,
                actual,
            } => write!(
                formatter,
                "module `{}` payload transparency mismatch: expected {expected:?}, actual {actual:?}",
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
            Self::GraphAdmissionFault { what } => {
                write!(formatter, "module-provenance internal fault: {what}")
            }
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
            Self::InternalFault {
                what,
                held,
                recomputed,
            } => write!(
                formatter,
                "module-provenance internal fault: {what} (held {held}, recomputed {recomputed})"
            ),
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
        // Construction splits the same way registration does: a malformed epoch is a
        // rejection, a bound payload budget is inconclusive. This path sets the
        // graph's payload budget to `u128::MAX`, so only the rejection arm is
        // reachable — but it is matched explicitly rather than assumed away.
        let mut graph = match ModuleGraph::new(epoch.clone(), graph_limits) {
            ModuleGraphOutcome::Complete(graph) => graph,
            ModuleGraphOutcome::Rejected(error) => {
                return Err(ModuleProvenanceError::InvalidModuleGraph(error));
            }
            ModuleGraphOutcome::Inconclusive(reason) => {
                return Err(ModuleProvenanceError::GraphAdmissionFault {
                    what: match reason {
                        ModuleGraphInconclusive::ResourceLimitExceeded { .. } => {
                            "module-graph construction bound a budget this path sets to u128::MAX"
                        }
                        ModuleGraphInconclusive::Cancelled { .. } => {
                            "module-graph construction reported cancellation without a request"
                        }
                    },
                });
            }
        };
        for record in &records {
            // The three arms are kept apart deliberately. A rejection is a real
            // determination about the record; an exhausted budget is not, and folding
            // it into `InvalidModuleGraph` would report "this graph is invalid" for
            // what is only "we ran out of room" (FL-INV-07, bead
            // franken_lean-module-graph-resource-outcomes-46b).
            graph = match graph.register(record.module.clone()) {
                ModuleGraphAdmission::Complete(registration) => registration.graph,
                ModuleGraphAdmission::Rejected(error) => {
                    return Err(ModuleProvenanceError::InvalidModuleGraph(error));
                }
                ModuleGraphAdmission::Inconclusive(
                    ModuleGraphInconclusive::ResourceLimitExceeded {
                        module,
                        resource,
                        limit,
                        actual,
                    },
                ) => {
                    return Err(ModuleProvenanceError::ResourceLimitExceeded {
                        module,
                        resource: match resource {
                            ModuleGraphResource::Modules => ModuleProvenanceResource::Modules,
                            ModuleGraphResource::DirectImportRows => {
                                ModuleProvenanceResource::DirectImportRows
                            }
                            ModuleGraphResource::NameDepth => ModuleProvenanceResource::NameDepth,
                            // Unreachable here: this path sets the graph's payload
                            // budget to `u128::MAX`, so only the three above can bind.
                            ModuleGraphResource::PayloadBytes => {
                                ModuleProvenanceResource::EncodedBytes
                            }
                        },
                        limit,
                        actual,
                    });
                }
                ModuleGraphAdmission::Inconclusive(ModuleGraphInconclusive::Cancelled {
                    ..
                }) => {
                    // This path requests no cancellation, so a cancelled outcome is an
                    // invariant failure of the layer below — never a verdict about the
                    // module, and never a user-facing diagnostic.
                    return Err(ModuleProvenanceError::GraphAdmissionFault {
                        what: "module-graph registration reported cancellation without a request",
                    });
                }
            };
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

    /// Classify an **untrusted** candidate against this manifest.
    ///
    /// Equality is decided by the exact canonical value; the root is only the fast
    /// inequality check that lets the common case skip the comparison. A candidate that
    /// shares this manifest's root but not its bytes yields
    /// [`IdentityVerdict::Collision`] — reported for atomic application to adjudicate,
    /// never silently resolved in either direction.
    ///
    /// Both arguments here are validated manifests, so the collision arm is unreachable
    /// in practice; [`classify_identity`] is the seam where a bounded model can exercise
    /// it without claiming a real collision.
    pub fn classify_candidate(&self, candidate: &ModuleProvenanceManifest) -> IdentityVerdict {
        classify_identity(
            (self.root, &self.to_canonical_bytes()),
            (candidate.root(), &candidate.to_canonical_bytes()),
        )
    }

    /// Re-derive this manifest's root from its own records and confirm it still matches.
    ///
    /// The same equal-digest/unequal-value inconsistency means two different things
    /// depending on where it is found. Arriving from outside it is an
    /// [`IdentityVerdict::Collision`] — untrusted input, a normal thing to receive and
    /// refuse. Found *inside* validated state it is an invariant failure: this manifest
    /// was checked at construction, so a disagreement now means the value or the
    /// derivation was corrupted, and the typed answer is `InternalFault`, never a
    /// verdict about the module (FL-INV-07).
    pub fn verify_self_consistency(&self) -> Result<(), ModuleProvenanceError> {
        let recomputed =
            ModuleProvenanceRoot(hash(Domain::ModuleProvenance, &self.to_canonical_bytes()));
        if recomputed == self.root {
            return Ok(());
        }
        Err(ModuleProvenanceError::InternalFault {
            what: "validated manifest root disagrees with its canonical value",
            held: self.root,
            recomputed,
        })
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

    // The transparency axis is recomputed from the descriptors rather than trusted, and
    // it resolves to three states, not two: a module with both understood and opaque
    // contributions is `Mixed`, which keeps the opaque boundary localized instead of
    // condemning the module wholesale.
    let opaque = record
        .extension_contributions
        .iter()
        .filter(|contribution| contribution.descriptor.provenance == PayloadProvenance::Opaque)
        .count();
    let expected_transparency = if opaque == 0 {
        PayloadTransparency::Understood
    } else if opaque == record.extension_contributions.len() {
        PayloadTransparency::Opaque
    } else {
        PayloadTransparency::Mixed
    };
    if expected_transparency != record.completeness.transparency {
        return Err(ModuleProvenanceError::PayloadTransparencyMismatch {
            module: module.clone(),
            expected: expected_transparency,
            actual: record.completeness.transparency,
        });
    }

    // Capture cannot be recomputed — whether the decoder obtained everything it should
    // have is knowledge from outside the record. Exactly one cross-check is available
    // and is therefore mandatory: a record cannot claim it captured nothing while
    // carrying contributions. This is the only coupling between the axes, and it is a
    // consistency obligation, not a collapse: it never lets one axis *derive* another.
    if record.completeness.capture == CaptureStatus::Missing
        && !(record.declarations.is_empty()
            && record.extra_declarations.is_empty()
            && record.extension_contributions.is_empty())
    {
        return Err(ModuleProvenanceError::CaptureStatusContradicted {
            module: module.clone(),
            capture: record.completeness.capture,
            declarations: record.declarations.len(),
            extra_declarations: record.extra_declarations.len(),
            extension_contributions: record.extension_contributions.len(),
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
        // Source ordinal and target position are both derived from the array index and
        // `start`, so neither can disagree with the range by construction — the
        // `EntryIndexMismatch` this loop used to raise is unrepresentable now that no
        // entry carries a journal coordinate of its own. `end()` above already proved
        // the whole range fits, which is the only remaining arithmetic obligation.
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
            // The occurrence's source ordinal is its position in this sequence and its
            // target position is `start + ordinal`; writing either again would put a
            // rebasable journal coordinate inside the entry identity.
            writer.bytes(&entry.digest().0);
        }
    }
    writer.u8(capture_status_tag(record.completeness.capture));
    writer.u8(payload_transparency_tag(record.completeness.transparency));
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
            entries.push(ExtensionEntryId::from_digest(read_digest(reader)?));
        }
        contributions.push(ExtensionContribution::new(
            descriptor,
            start,
            base_history_digest,
            entries,
        ));
    }

    let capture = read_capture_status(reader.u8()?)?;
    let transparency = read_payload_transparency(reader.u8()?)?;
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
        ProvenanceCompleteness::new(capture, transparency, missing),
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

fn capture_status_tag(value: CaptureStatus) -> u8 {
    match value {
        CaptureStatus::Complete => 0,
        CaptureStatus::Partial => 1,
        CaptureStatus::Missing => 2,
    }
}

fn payload_transparency_tag(value: PayloadTransparency) -> u8 {
    match value {
        PayloadTransparency::Understood => 0,
        PayloadTransparency::Mixed => 1,
        PayloadTransparency::Opaque => 2,
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

fn read_capture_status(tag: u8) -> Result<CaptureStatus, ModuleProvenanceError> {
    match tag {
        0 => Ok(CaptureStatus::Complete),
        1 => Ok(CaptureStatus::Partial),
        2 => Ok(CaptureStatus::Missing),
        _ => Err(ModuleProvenanceError::MalformedEncoding {
            what: "unknown capture status tag",
        }),
    }
}

fn read_payload_transparency(tag: u8) -> Result<PayloadTransparency, ModuleProvenanceError> {
    match tag {
        0 => Ok(PayloadTransparency::Understood),
        1 => Ok(PayloadTransparency::Mixed),
        2 => Ok(PayloadTransparency::Opaque),
        _ => Err(ModuleProvenanceError::MalformedEncoding {
            what: "unknown payload transparency tag",
        }),
    }
}

/// Where one extension entry occurrence lives: the contributing module, its
/// contribution index, and the module-local source ordinal within that contribution.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct EntryOccurrence {
    pub module: ModuleId,
    pub contribution_index: usize,
    pub source_ordinal: u64,
}

/// Derived forward and reverse indexes over a validated manifest.
///
/// **These are projections, not truth.** The manifest's records are the committed
/// state and [`ModuleProvenanceRoot`] is the sole authoritative aggregate identity.
/// An index is a rebuildable cache: it carries the root it was derived from so it can
/// be checked against the records, and it never contributes to that root. Persisting
/// one and later disagreeing with the records is an invariant failure, not a second
/// opinion — [`verify`](Self::verify) reports that as `InternalFault`.
///
/// Index layout, ordering, and sharing are deliberately outside the canonical bytes:
/// building, dropping, or rebuilding indexes cannot move the aggregate root, and a
/// test asserts exactly that.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleProvenanceIndexes {
    /// Reverse: declaration name -> its owning module and contribution class.
    owners: BTreeMap<Name, (ModuleId, DeclarationClass)>,
    /// Forward: module -> the declaration names it owns, in canonical order.
    declarations_by_module: BTreeMap<ModuleId, Vec<Name>>,
    /// Reverse: entry identity -> every occurrence of it, canonically ordered.
    entry_occurrences: BTreeMap<ExtensionEntryId, Vec<EntryOccurrence>>,
    /// The aggregate root these projections were derived from. Carried for checking,
    /// never as an identity of its own.
    derived_from: ModuleProvenanceRoot,
}

impl ModuleProvenanceIndexes {
    /// Derive both indexes from the manifest's primary records.
    ///
    /// Deterministic and total: every input row lands in both directions, so a
    /// rebuild from the same records is byte-for-byte the same projection.
    pub fn derive(manifest: &ModuleProvenanceManifest) -> Self {
        let mut owners = BTreeMap::new();
        let mut declarations_by_module = BTreeMap::new();
        let mut entry_occurrences: BTreeMap<ExtensionEntryId, Vec<EntryOccurrence>> =
            BTreeMap::new();
        for record in manifest.records() {
            let module = record.module().id.clone();
            let mut owned =
                Vec::with_capacity(record.declarations().len() + record.extra_declarations().len());
            for (class, names) in [
                (DeclarationClass::Declaration, record.declarations()),
                (
                    DeclarationClass::ExtraDeclaration,
                    record.extra_declarations(),
                ),
            ] {
                for name in names {
                    owners.insert(name.clone(), (module.clone(), class));
                    owned.push(name.clone());
                }
            }
            owned.sort();
            declarations_by_module.insert(module.clone(), owned);
            for (contribution_index, contribution) in
                record.extension_contributions().iter().enumerate()
            {
                for (offset, entry) in contribution.entries().iter().enumerate() {
                    let Some(source_ordinal) = contribution.source_ordinal(offset) else {
                        continue;
                    };
                    entry_occurrences
                        .entry(*entry)
                        .or_default()
                        .push(EntryOccurrence {
                            module: module.clone(),
                            contribution_index,
                            source_ordinal,
                        });
                }
            }
        }
        for occurrences in entry_occurrences.values_mut() {
            occurrences.sort();
        }
        Self {
            owners,
            declarations_by_module,
            entry_occurrences,
            derived_from: manifest.root(),
        }
    }

    /// The aggregate root these projections were derived from. This is a *back
    /// reference*, not an identity: two different index layouts over the same records
    /// report the same value because the records decide it.
    pub fn derived_from(&self) -> ModuleProvenanceRoot {
        self.derived_from
    }

    /// Reverse query: which module owns this declaration, and in which class.
    pub fn owner_of(&self, name: &Name) -> Option<&(ModuleId, DeclarationClass)> {
        self.owners.get(name)
    }

    /// Forward query: the declarations this module owns, canonically ordered.
    pub fn declarations_of(&self, module: &ModuleId) -> Option<&[Name]> {
        self.declarations_by_module
            .get(module)
            .map(|names| names.as_slice())
    }

    /// Reverse query: every occurrence of one entry identity.
    pub fn occurrences_of(&self, entry: &ExtensionEntryId) -> Option<&[EntryOccurrence]> {
        self.entry_occurrences
            .get(entry)
            .map(|occurrences| occurrences.as_slice())
    }

    /// Re-derive from `manifest` and confirm this projection still agrees with it.
    ///
    /// Any disagreement — a stale root, a missing row, an extra row, or a
    /// contradictory one — is an [`InternalFault`](ModuleProvenanceError::InternalFault)
    /// or a [`GraphAdmissionFault`](ModuleProvenanceError::GraphAdmissionFault),
    /// never a verdict about a module. Validated state that disagrees with itself is
    /// an invariant failure by definition (FL-INV-07).
    pub fn verify(&self, manifest: &ModuleProvenanceManifest) -> Result<(), ModuleProvenanceError> {
        if self.derived_from != manifest.root() {
            return Err(ModuleProvenanceError::InternalFault {
                what: "index projection was derived from a different committed root",
                held: self.derived_from,
                recomputed: manifest.root(),
            });
        }
        let rebuilt = Self::derive(manifest);
        if rebuilt.owners != self.owners {
            return Err(ModuleProvenanceError::GraphAdmissionFault {
                what: "declaration-owner projection disagrees with the committed records",
            });
        }
        if rebuilt.declarations_by_module != self.declarations_by_module {
            return Err(ModuleProvenanceError::GraphAdmissionFault {
                what: "forward declaration projection disagrees with the committed records",
            });
        }
        if rebuilt.entry_occurrences != self.entry_occurrences {
            return Err(ModuleProvenanceError::GraphAdmissionFault {
                what: "entry-occurrence projection disagrees with the committed records",
            });
        }
        // Bidirectional coverage: the forward and reverse declaration indexes must be
        // exact inverses. A one-way index is how a projection quietly becomes a second
        // source of truth.
        for (name, (module, _)) in &self.owners {
            let owned =
                self.declarations_of(module)
                    .ok_or(ModuleProvenanceError::GraphAdmissionFault {
                        what: "reverse index names a module the forward index does not carry",
                    })?;
            if !owned.contains(name) {
                return Err(ModuleProvenanceError::GraphAdmissionFault {
                    what: "reverse index maps a declaration to a module that does not own it",
                });
            }
        }
        for (module, names) in &self.declarations_by_module {
            for name in names {
                match self.owner_of(name) {
                    Some((owner, _)) if owner == module => {}
                    _ => {
                        return Err(ModuleProvenanceError::GraphAdmissionFault {
                            what: "forward index owns a declaration the reverse index does not",
                        });
                    }
                }
            }
        }
        Ok(())
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

    /// Fixture entries are derived exactly as production entries are — from the epoch,
    /// the descriptor, and raw payload bytes. No test may assert an id it fabricated,
    /// or the derivation law would be tested against itself.
    fn entry_for(descriptor: &ExtensionDescriptor, payload: &[u8]) -> ExtensionEntryId {
        ExtensionEntryId::derive(&epoch(), descriptor, payload)
    }

    /// The common case: an entry under the `simpExt`/Understood descriptor that
    /// `sample_records` uses.
    fn entry(seed: u8) -> ExtensionEntryId {
        entry_for(
            &extension_descriptor("simpExt", PayloadProvenance::Understood),
            &[seed],
        )
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
            vec![entry(0x41), entry(0x42)],
        );
        let a = ModuleContributionRecord::new(
            module_a,
            vec![name("A.one"), name("A.two")],
            vec![name("A.generated")],
            vec![contribution],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
                vec![id("Ghost")],
            ),
        );
        let b = ModuleContributionRecord::new(
            ModuleRecord::new(id("B"), true, vec![], evidence(0xB1)),
            vec![name("B.one")],
            vec![],
            vec![],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
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
        // Every variant of both axes round-trips, including the two states added when
        // the axes were separated: an axis whose new variant had no tag would be an
        // "omit a completeness axis" mutant that only shows up on real data.
        for value in [
            CaptureStatus::Complete,
            CaptureStatus::Partial,
            CaptureStatus::Missing,
        ] {
            assert_eq!(read_capture_status(capture_status_tag(value)), Ok(value));
        }
        for value in [
            PayloadTransparency::Understood,
            PayloadTransparency::Mixed,
            PayloadTransparency::Opaque,
        ] {
            assert_eq!(
                read_payload_transparency(payload_transparency_tag(value)),
                Ok(value)
            );
        }

        for error in [
            read_artifact_producer(u8::MAX).expect_err("unknown producer is refused"),
            read_artifact_grade(u8::MAX).expect_err("unknown grade is refused"),
            read_merge_semantics(u8::MAX).expect_err("unknown merge policy is refused"),
            read_checkpoint_semantics(u8::MAX).expect_err("unknown checkpoint policy is refused"),
            read_payload_provenance(u8::MAX).expect_err("unknown provenance is refused"),
            read_capture_status(u8::MAX).expect_err("unknown completeness is refused"),
            read_payload_transparency(u8::MAX).expect_err("unknown knowledge grade is refused"),
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
            "9af861837929fcff05062054d8a328377d5bfd2bf55a23ab7b3009dc5067146f",
            "schema/domain changes require an explicit golden update"
        );
        // Re-pinned when per-entry journal ordinals left the encoding: each occurrence
        // is now a bare content id, so the two sample entries shed one `u64` each.
        assert_eq!(bytes.len(), 669, "canonical layout size is frozen");
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
        // Source order is the array order, so a swap is the whole mutation: no journal
        // coordinate has to be rewritten to keep the applied range valid.
        entries.swap(0, 1);
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
            vec![entry_for(
                &extension_descriptor("traceExt", PayloadProvenance::Understood),
                &[0x53],
            )],
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
            CaptureStatus::Complete,
            PayloadTransparency::Understood,
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
                CaptureStatus::Complete,
                PayloadTransparency::Understood,
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
            CaptureStatus::Complete,
            PayloadTransparency::Understood,
            vec![id("Ghost")],
        );
        let drop_extension = ModuleProvenanceManifest::new(epoch(), drop_extension, TEST_LIMITS)
            .expect("drop-extension mutant remains structurally valid");
        roots.insert(drop_extension.root());

        let mut drop_completeness = sample_records();
        drop_completeness[0].completeness = ProvenanceCompleteness::new(
            CaptureStatus::Partial,
            PayloadTransparency::Understood,
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
        entries[1] = entry(0x99);
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
        // Collected so the normative V1 table can be joined against what was actually
        // witnessed: a table row claiming root participation with no observation is
        // stale, and an observation with no row means the table is missing one.
        let mut witnessed: BTreeSet<&'static str> = BTreeSet::new();
        let mut observe = |field: &'static str, variant_epoch: ModuleEpoch, records: Vec<_>| {
            witnessed.insert(field);
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
            CaptureStatus::Complete,
            PayloadTransparency::Understood,
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
            CaptureStatus::Complete,
            PayloadTransparency::Opaque,
            vec![id("Ghost")],
        );
        observe("extension.provenance+transparency", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            9,
            original.base_history_digest(),
            vec![entry(0x41), entry(0x42)],
        )]
        .into();
        // Only the applied range start moves here: entry ordinals are positions in the
        // source sequence now, not stored fields, so they cannot vary independently.
        observe("extension.range_start", epoch(), records);

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
            vec![entry(0x41), entry(0x99)],
        )]
        .into();
        observe("extension.entry_id", epoch(), records);

        let mut records = sample_records();
        let original = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            original.start(),
            original.base_history_digest(),
            vec![entry(0x41), entry(0x42), entry(0x43)],
        )]
        .into();
        observe("extension.entry_count", epoch(), records);

        let mut records = sample_records();
        records[0].completeness = ProvenanceCompleteness::new(
            CaptureStatus::Partial,
            PayloadTransparency::Understood,
            vec![id("Ghost")],
        );
        observe("completeness.capture", epoch(), records);

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
            CaptureStatus::Complete,
            PayloadTransparency::Understood,
            vec![id("Lost"), id("Ghost")],
        );
        observe("completeness.missing_dependency_set", epoch(), records);

        // One gap the normative V1 table exposed: transparency was only ever
        // witnessed together with the descriptor's provenance, so it was never known
        // to reach the root on its own. (The three import flags turned out to be
        // witnessed already, by the loop above — the table's job is to make that
        // checkable either way.)

        let mut records = sample_records();
        let contribution = records[0].extension_contributions[0].clone();
        records[0].extension_contributions = vec![
            contribution.clone(),
            ExtensionContribution::new(
                extension_descriptor("opaqueExt", PayloadProvenance::Opaque),
                0,
                Digest([0x77; 32]),
                vec![entry_for(
                    &extension_descriptor("opaqueExt", PayloadProvenance::Opaque),
                    &[0x5A],
                )],
            ),
        ]
        .into();
        records[0].completeness = ProvenanceCompleteness::new(
            CaptureStatus::Complete,
            PayloadTransparency::Mixed,
            vec![id("Ghost")],
        );
        observe("completeness.transparency", epoch(), records);

        assert_eq!(roots.len(), 25, "baseline plus every field-family variant");

        // ---- the join: the table and the witnesses must agree exactly -----------
        let claimed: BTreeSet<&'static str> = MODULE_PROVENANCE_V1_TABLE
            .iter()
            .filter_map(|row| row.sensitivity_witness)
            .collect();
        assert_eq!(
            claimed.difference(&witnessed).copied().collect::<Vec<_>>(),
            Vec::<&str>::new(),
            "a V1 table row claims a sensitivity witness that was never observed (stale row)"
        );
        assert_eq!(
            witnessed.difference(&claimed).copied().collect::<Vec<_>>(),
            Vec::<&str>::new(),
            "a field family was observed with no V1 table row (missing row)"
        );
    }

    /// Canonical width of one `Name` body, measured rather than guessed.
    fn name_body_len(name: &Name) -> usize {
        let mut writer = CanonWriter::new();
        name.write_body(&mut writer);
        writer.into_bytes().len()
    }

    /// The V1 table is normative, so it must be well formed on its own terms:
    /// unique tags, and every row classified on every axis the design requires.
    /// An unclassified row is exactly as bad as a missing one — it looks specified.
    #[test]
    fn the_v1_table_has_unique_and_fully_classified_rows() {
        let mut tags = BTreeSet::new();
        for row in MODULE_PROVENANCE_V1_TABLE {
            assert!(
                tags.insert(row.tag),
                "duplicate V1 table row for tag `{}`",
                row.tag
            );
            for (column, value) in [
                ("decoder_source", row.decoder_source),
                ("value_type", row.value_type),
                ("identity_inputs", row.identity_inputs),
                ("malformed_outcome", row.malformed_outcome),
            ] {
                assert!(
                    !value.is_empty(),
                    "row `{}` leaves `{column}` unclassified",
                    row.tag
                );
            }
            // An ordinal namespace and an ordinal width are one fact in two halves;
            // declaring either alone leaves the coordinate ambiguous.
            assert_eq!(
                row.ordinal_namespace != V1OrdinalNamespace::None,
                row.ordinal_width_bits.is_some(),
                "row `{}` declares an ordinal namespace without a width, or vice versa",
                row.tag
            );
            // Ordered replay data and canonical sets must state a duplicate policy.
            if matches!(
                row.sequence_law,
                V1SequenceLaw::OrderedSequence | V1SequenceLaw::CanonicalSet
            ) {
                assert_ne!(
                    row.duplicate_policy,
                    V1DuplicatePolicy::NotApplicable,
                    "row `{}` is a sequence or set but declares no duplicate policy",
                    row.tag
                );
            }
            // Encoded rows must have a width; unencoded rows must not claim one.
            let encoded = row.multiplicity != V1Multiplicity::NotEncoded;
            assert_eq!(
                encoded,
                row.root_participation == V1RootParticipation::Direct,
                "row `{}`: only directly-encoded rows may claim Direct root participation",
                row.tag
            );
            if !encoded {
                assert_eq!(
                    row.width,
                    V1Width::Fixed(0),
                    "row `{}` is not encoded yet claims a width",
                    row.tag
                );
            }
        }
        // The two deliberately-unencoded rows are the ones this schema reasons about
        // most: the artifact epoch (pinned by validation) and the target journal
        // position (derived, and excluded from entry identity on purpose).
        let unencoded: Vec<_> = MODULE_PROVENANCE_V1_TABLE
            .iter()
            .filter(|row| row.multiplicity == V1Multiplicity::NotEncoded)
            .map(|row| row.tag)
            .collect();
        assert_eq!(
            unencoded,
            vec!["artifact.epoch", "extension.target_position"],
            "the set of deliberately-unencoded fields changed without a table update"
        );
    }

    /// **Completeness, mechanically.** The table predicts the exact canonical byte
    /// length of a manifest from its own rows plus that manifest's facts. If the
    /// encoder writes a field the table does not list — or stops writing one it does
    /// — the totals disagree. This is what makes "missing rows block closure"
    /// enforceable instead of aspirational.
    #[test]
    fn the_v1_table_predicts_the_exact_canonical_byte_length() {
        let manifest = sample_manifest();
        let facts = manifest.facts();
        let actual = manifest.to_canonical_bytes().len();

        // Data-dependent widths are measured from the fixture; the table supplies
        // which fields exist and how each is framed.
        let sum_names = |names: Vec<&Name>| names.iter().map(|n| name_body_len(n)).sum::<usize>();
        let module_ids: Vec<&Name> = manifest
            .records()
            .iter()
            .map(|r| r.module().id.name())
            .collect();
        let import_names: Vec<&Name> = manifest
            .records()
            .iter()
            .flat_map(|r| r.module().direct_imports().iter().map(|i| i.module.name()))
            .collect();
        let declaration_names: Vec<&Name> = manifest
            .records()
            .iter()
            .flat_map(|r| r.declarations().iter())
            .collect();
        let extra_names: Vec<&Name> = manifest
            .records()
            .iter()
            .flat_map(|r| r.extra_declarations().iter())
            .collect();
        let extension_names: Vec<&Name> = manifest
            .records()
            .iter()
            .flat_map(|r| {
                r.extension_contributions()
                    .iter()
                    .map(|c| &c.descriptor().name)
            })
            .collect();
        let missing_names: Vec<&Name> = manifest
            .records()
            .iter()
            .flat_map(|r| r.completeness().missing_dependencies().iter())
            .map(|m| m.name())
            .collect();

        let mut predicted = 0usize;
        for row in MODULE_PROVENANCE_V1_TABLE {
            let occurrences = match row.multiplicity {
                V1Multiplicity::Once => 1,
                V1Multiplicity::PerModule => facts.modules,
                V1Multiplicity::PerDirectImportRow => facts.direct_import_rows,
                V1Multiplicity::PerDeclaration => facts.declarations,
                V1Multiplicity::PerExtraDeclaration => facts.extra_declarations,
                V1Multiplicity::PerExtensionContribution => facts.extension_contributions,
                V1Multiplicity::PerExtensionEntry => facts.extension_entries,
                V1Multiplicity::PerMissingDependency => facts.missing_dependencies,
                V1Multiplicity::NotEncoded => 0,
            };
            predicted += match (row.width, row.tag) {
                (V1Width::Fixed(width), _) => width * occurrences,
                (V1Width::LengthPrefixed(_), "epoch.tag") => 8 + manifest.epoch().tag().len(),
                (V1Width::LengthPrefixed(_), "epoch.commit") => 8 + manifest.epoch().commit().len(),
                (V1Width::LengthPrefixed(payload), _) => (8 + payload) * occurrences,
                (V1Width::SchemaHeader, _) => 8 + MODULE_PROVENANCE_SCHEMA.name.len() + 2,
                (V1Width::NameBody, "module.id") => sum_names(module_ids.clone()),
                (V1Width::NameBody, "direct_import.module") => sum_names(import_names.clone()),
                (V1Width::NameBody, "declarations.name") => sum_names(declaration_names.clone()),
                (V1Width::NameBody, "extra_declarations.name") => sum_names(extra_names.clone()),
                (V1Width::NameBody, "extension.descriptor.name") => {
                    sum_names(extension_names.clone())
                }
                (V1Width::NameBody, "completeness.missing_dependencies.name") => {
                    sum_names(missing_names.clone())
                }
                (width, tag) => panic!("unhandled V1 width {width:?} for row `{tag}`"),
            };
        }
        assert_eq!(
            predicted, actual,
            "the V1 table no longer accounts for every canonical byte — a field was \
             added to or removed from the encoder without a table row"
        );
        assert_eq!(actual, 669, "the pinned canonical size is unchanged");
    }

    /// **Identity-only, proved rather than asserted.** Declaration values and raw
    /// extension payload bytes stay `Arc`-backed in the Environment and the journal;
    /// this schema stores names, tags, counts and digests. A second copy of semantic
    /// payload state here would be a durability and divergence hazard, so the table
    /// records ownership per row and this test holds the encoding to it.
    #[test]
    fn the_v1_schema_is_identity_only_and_copies_no_payload() {
        // Payload bytes that exist only inside the extension journal, never here.
        const SECRET_PAYLOAD: &[u8] = b"PAYLOAD-BYTES-THAT-MUST-NOT-BE-COPIED";
        let descriptor = extension_descriptor("simpExt", PayloadProvenance::Understood);
        let mut records = sample_records();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            descriptor.clone(),
            7,
            Digest([0x31; 32]),
            vec![ExtensionEntryId::derive(
                &epoch(),
                &descriptor,
                SECRET_PAYLOAD,
            )],
        )]
        .into();
        let manifest = ModuleProvenanceManifest::new(epoch(), records, TEST_LIMITS)
            .expect("the payload-bearing fixture validates");
        let bytes = manifest.to_canonical_bytes();

        assert!(
            !bytes
                .windows(SECRET_PAYLOAD.len())
                .any(|window| window == SECRET_PAYLOAD),
            "raw extension payload bytes leaked into the canonical provenance encoding"
        );
        // The entry is still fully identified — identity-only is not identity-poor.
        assert_eq!(
            manifest.records()[0].extension_contributions()[0].entries()[0],
            ExtensionEntryId::derive(&epoch(), &descriptor, SECRET_PAYLOAD)
        );

        // Every row that names payload owned elsewhere stores a fixed-width digest or
        // a name, never the payload itself.
        for row in MODULE_PROVENANCE_V1_TABLE
            .iter()
            .filter(|row| row.ownership == V1Ownership::PayloadOwnedElsewhere)
        {
            assert!(
                matches!(row.width, V1Width::LengthPrefixed(32) | V1Width::NameBody),
                "row `{}` claims to own payload elsewhere but is not a digest or a name",
                row.tag
            );
        }
    }

    /// Projections are rebuildable caches, never truth. The properties that make
    /// that claim real: they are exactly derivable from the primary records, they
    /// cover both directions, and their existence cannot move the aggregate root.
    #[test]
    fn index_projections_are_derivable_bidirectional_and_never_authoritative() {
        let manifest = sample_manifest();
        let root_before = manifest.root();
        let indexes = ModuleProvenanceIndexes::derive(&manifest);

        // Derivable: a rebuild from the same records is the same projection, and it
        // verifies against the manifest it came from.
        assert_eq!(indexes, ModuleProvenanceIndexes::derive(&manifest));
        assert_eq!(indexes.verify(&manifest), Ok(()));
        assert_eq!(indexes.derived_from(), root_before);

        // NEVER AUTHORITATIVE: deriving, holding, cloning, and dropping projections
        // leaves the aggregate root and the canonical bytes untouched. Index layout
        // is outside the identity by construction, and this is the assertion that
        // keeps it there.
        let bytes_before = manifest.to_canonical_bytes();
        let _clone = indexes.clone();
        drop(ModuleProvenanceIndexes::derive(&manifest));
        assert_eq!(
            manifest.root(),
            root_before,
            "an index moved the aggregate root"
        );
        assert_eq!(manifest.to_canonical_bytes(), bytes_before);

        // Bidirectional coverage over real data: every owned declaration resolves
        // back to its owner, and every owner's list is exactly its declarations.
        let mut seen = 0usize;
        for record in manifest.records() {
            let module = &record.module().id;
            let owned = indexes
                .declarations_of(module)
                .expect("every module is in the forward index");
            let mut expected: Vec<Name> = record
                .declarations()
                .iter()
                .chain(record.extra_declarations().iter())
                .cloned()
                .collect();
            expected.sort();
            assert_eq!(owned, expected.as_slice(), "forward index disagrees");
            for name in &expected {
                let (owner, class) = indexes
                    .owner_of(name)
                    .expect("every declaration is in the reverse index");
                assert_eq!(owner, module);
                // The class distinction survives the projection: an ordinary and an
                // extra generated declaration are not interchangeable.
                let expected_class = if record.declarations().contains(name) {
                    DeclarationClass::Declaration
                } else {
                    DeclarationClass::ExtraDeclaration
                };
                assert_eq!(*class, expected_class, "declaration class was flattened");
                seen += 1;
            }
        }
        assert_eq!(
            seen,
            manifest.facts().declarations + manifest.facts().extra_declarations,
            "bidirectional walk did not cover every declaration"
        );

        // Reverse entry index: occurrences resolve to real coordinates.
        for record in manifest.records() {
            for (contribution_index, contribution) in
                record.extension_contributions().iter().enumerate()
            {
                for (offset, entry) in contribution.entries().iter().enumerate() {
                    let occurrences = indexes
                        .occurrences_of(entry)
                        .expect("every entry occurrence is indexed");
                    assert!(
                        occurrences.contains(&EntryOccurrence {
                            module: record.module().id.clone(),
                            contribution_index,
                            source_ordinal: contribution
                                .source_ordinal(offset)
                                .expect("offset is in range"),
                        })
                    );
                }
            }
        }
    }

    /// The named mutants: a projection that disagrees with the committed records, or
    /// one carried across to a different manifest, must fault rather than answer.
    #[test]
    fn a_disagreeing_index_projection_is_a_fault_not_a_second_opinion() {
        let manifest = sample_manifest();
        let other = other_manifest();

        // Carried across to a different committed root: caught by the back reference
        // before any row is compared.
        let stale = ModuleProvenanceIndexes::derive(&manifest);
        assert!(matches!(
            stale.verify(&other),
            Err(ModuleProvenanceError::InternalFault {
                what: "index projection was derived from a different committed root",
                ..
            })
        ));

        // Tampered rows, with the root reference left intact so the row comparison is
        // what has to catch it. Each is a distinct way a cache can rot.
        let mut dropped_owner = ModuleProvenanceIndexes::derive(&manifest);
        let victim = manifest.records()[0].declarations()[0].clone();
        dropped_owner.owners.remove(&victim);
        assert!(matches!(
            dropped_owner.verify(&manifest),
            Err(ModuleProvenanceError::GraphAdmissionFault { .. })
        ));

        let mut wrong_owner = ModuleProvenanceIndexes::derive(&manifest);
        wrong_owner
            .owners
            .insert(victim.clone(), (id("B"), DeclarationClass::Declaration));
        assert!(matches!(
            wrong_owner.verify(&manifest),
            Err(ModuleProvenanceError::GraphAdmissionFault { .. })
        ));

        let mut flattened_class = ModuleProvenanceIndexes::derive(&manifest);
        let extra = manifest.records()[0].extra_declarations()[0].clone();
        flattened_class
            .owners
            .insert(extra, (id("A"), DeclarationClass::Declaration));
        assert!(
            matches!(
                flattened_class.verify(&manifest),
                Err(ModuleProvenanceError::GraphAdmissionFault { .. })
            ),
            "collapsing the ordinary/extra class distinction must fault"
        );

        let mut lost_occurrence = ModuleProvenanceIndexes::derive(&manifest);
        let entry = manifest.records()[0].extension_contributions()[0].entries()[0];
        lost_occurrence.entry_occurrences.remove(&entry);
        assert!(matches!(
            lost_occurrence.verify(&manifest),
            Err(ModuleProvenanceError::GraphAdmissionFault { .. })
        ));

        // And the healthy projection still verifies, so none of the above is a
        // blanket refusal.
        assert_eq!(
            ModuleProvenanceIndexes::derive(&manifest).verify(&manifest),
            Ok(())
        );
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
            CaptureStatus::Complete,
            PayloadTransparency::Understood,
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

        // Non-interference across field families, not just one variant: move a
        // representative field from each independently-rooted family and assert the
        // environment's logical root never observes any of it, and that no provenance
        // root ever aliases it. Building, varying, encoding and decoding provenance is
        // all invisible to the environment by construction — this pins that.
        let mut transparency = sample_records();
        transparency[0].extension_contributions = vec![ExtensionContribution::new(
            extension_descriptor("opaqueExt", PayloadProvenance::Opaque),
            7,
            Digest([0x31; 32]),
            vec![entry_for(
                &extension_descriptor("opaqueExt", PayloadProvenance::Opaque),
                &[0x41],
            )],
        )]
        .into();
        transparency[0].completeness = ProvenanceCompleteness::new(
            CaptureStatus::Complete,
            PayloadTransparency::Opaque,
            vec![id("Ghost")],
        );

        let mut capture = sample_records();
        capture[0].completeness = ProvenanceCompleteness::new(
            CaptureStatus::Partial,
            PayloadTransparency::Understood,
            vec![id("Ghost")],
        );

        let mut artifact = sample_records();
        artifact[0].module.artifact.content_digest = Digest([0xEE; 32]);

        let mut roots = BTreeSet::from([base.root()]);
        for (family, records) in [
            ("transparency", transparency),
            ("capture", capture),
            ("artifact", artifact),
        ] {
            let manifest = ModuleProvenanceManifest::new(epoch(), records, TEST_LIMITS)
                .expect("variant validates");
            // Round-trip too: decoding is equally invisible to the environment.
            let decoded = ModuleProvenanceManifest::from_canonical_bytes(
                &manifest.to_canonical_bytes(),
                TEST_LIMITS,
            )
            .expect("variant round-trips");
            assert_eq!(decoded.root(), manifest.root(), "family={family}");
            assert!(roots.insert(manifest.root()), "family={family} is distinct");
            assert_eq!(
                logical_before,
                environment.logical_root(&KVMap::new()),
                "family={family} disturbed the environment's logical root"
            );
            assert_ne!(
                manifest.root().0,
                logical_before.0,
                "family={family} provenance root aliased the logical root"
            );
        }
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
            CaptureStatus::Complete,
            PayloadTransparency::Understood,
            vec![],
        );
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), wrong_missing, TEST_LIMITS),
            Err(ModuleProvenanceError::MissingDependenciesMismatch { .. })
        ));

        let mut wrong_knowledge = baseline_records.clone();
        wrong_knowledge[0].completeness = ProvenanceCompleteness::new(
            CaptureStatus::Complete,
            PayloadTransparency::Opaque,
            vec![id("Ghost")],
        );
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), wrong_knowledge, TEST_LIMITS),
            Err(ModuleProvenanceError::PayloadTransparencyMismatch { .. })
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

        // There is deliberately no "entry index disagrees with the range" row here any
        // more: an occurrence carries no journal coordinate of its own, so that class of
        // malformed input is unrepresentable rather than merely rejected. The property
        // that replaced it is proved by
        // `entry_identity_is_content_derived_and_survives_journal_rebasing`.

        let mut overflow = baseline_records.clone();
        let original = &overflow[0].extension_contributions[0];
        overflow[0].extension_contributions = vec![ExtensionContribution::new(
            original.descriptor().clone(),
            u64::MAX,
            original.base_history_digest(),
            vec![entry(1)],
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
        let opaque_entry = entry_for(&descriptor, &[9]);
        let contribution =
            ExtensionContribution::new(descriptor.clone(), 0, Digest([0; 32]), vec![opaque_entry]);
        let record = ModuleContributionRecord::new(
            ModuleRecord::new(id("Opaque"), true, vec![], evidence(9)),
            vec![name("Opaque.one")],
            vec![],
            vec![contribution],
            ProvenanceCompleteness::new(
                CaptureStatus::Partial,
                PayloadTransparency::Opaque,
                vec![],
            ),
        );
        let manifest = ModuleProvenanceManifest::new(epoch(), vec![record], TEST_LIMITS)
            .expect("opaque partial manifest is retained honestly");
        let completeness = manifest.records()[0].completeness();
        assert_eq!(completeness.capture(), CaptureStatus::Partial);
        assert_eq!(completeness.transparency(), PayloadTransparency::Opaque);
        // Partial + Opaque is a legal state that keeps inspection and nothing else.
        // There is deliberately no `is_complete()` to ask instead: that accessor ANDed
        // the two axes together, so a byte-complete opaque module reported "incomplete"
        // and the caller could not tell which axis had said so.
        assert_eq!(
            completeness.authority(),
            vec![ProvenanceAuthority::Inspection]
        );
        // An opaque payload still gets a full content identity: opacity is about
        // understanding the bytes, not about being unable to name them.
        assert_eq!(
            manifest.records()[0].extension_contributions()[0].entries()[0],
            ExtensionEntryId::derive(&epoch(), &descriptor, &[9])
        );
        // The schema contains only a fixed-size digest, not the source payload Arc.
        assert_eq!(
            std::mem::size_of::<ExtensionEntryId>(),
            std::mem::size_of::<Digest>()
        );
    }

    /// The authority table, written out independently of the implementation so it can
    /// serve as an oracle rather than a restatement. Consulted by both axis tests.
    fn expected_authority(
        capture: CaptureStatus,
        transparency: PayloadTransparency,
        has_missing: bool,
    ) -> Vec<ProvenanceAuthority> {
        use ProvenanceAuthority::*;
        match capture {
            // Nothing was captured, so there is nothing to inspect, replay, or trust.
            CaptureStatus::Missing => vec![],
            // Something was captured but not all of it: it can be read and nothing more.
            CaptureStatus::Partial => vec![Inspection],
            CaptureStatus::Complete => {
                if has_missing {
                    // The module's own content is whole, but its import closure is not,
                    // so it cannot anchor a cache key or an invalidation cone.
                    vec![Inspection, ExactReplay, CompleteInventory]
                } else if transparency == PayloadTransparency::Understood {
                    vec![
                        Inspection,
                        ExactReplay,
                        CompleteInventory,
                        AuthoritativeCache,
                        FineInvalidation,
                    ]
                } else {
                    // Byte-complete but not semantically attributable: everything except
                    // the one capability that needs to know what the payloads *mean*.
                    vec![
                        Inspection,
                        ExactReplay,
                        CompleteInventory,
                        AuthoritativeCache,
                    ]
                }
            }
        }
    }

    /// The named mutant this kills: *collapse capture with transparency*.
    ///
    /// The rejected design exposed one `is_complete()` boolean that ANDed the capture
    /// axis, the transparency axis, and the missing-dependency set together. That is
    /// not merely imprecise, it is lossy: it maps genuinely different states onto the
    /// same answer, so no caller could recover which axis objected. This test executes
    /// that collapsed predicate and shows exactly what it destroys.
    #[test]
    fn the_axes_are_independent_and_capture_is_not_collapsed_with_transparency() {
        let completeness = |capture, transparency, missing: Vec<ModuleId>| {
            ProvenanceCompleteness::new(capture, transparency, missing)
        };

        // The two states the design names as "both valid with limited authority".
        let complete_opaque =
            completeness(CaptureStatus::Complete, PayloadTransparency::Opaque, vec![]);
        let partial_understood = completeness(
            CaptureStatus::Partial,
            PayloadTransparency::Understood,
            vec![],
        );

        // The collapsed predicate the axes replaced, executed rather than described.
        let collapsed = |c: &ProvenanceCompleteness| {
            c.capture() == CaptureStatus::Complete
                && c.transparency() == PayloadTransparency::Understood
                && c.missing_dependencies().is_empty()
        };
        assert!(!collapsed(&complete_opaque));
        assert!(!collapsed(&partial_understood));
        assert_eq!(
            collapsed(&complete_opaque),
            collapsed(&partial_understood),
            "the collapsed predicate is expected to conflate these two states — that is the defect"
        );

        // The axes keep them apart, and so does the authority derived from them: one is
        // byte-complete and cacheable, the other can only be looked at.
        assert_ne!(complete_opaque.capture(), partial_understood.capture());
        assert_ne!(
            complete_opaque.transparency(),
            partial_understood.transparency()
        );
        assert_ne!(
            complete_opaque.authority(),
            partial_understood.authority(),
            "the collapse mutant survives if authority cannot tell these apart"
        );
        assert!(complete_opaque.grants(ProvenanceAuthority::AuthoritativeCache));
        assert!(!complete_opaque.grants(ProvenanceAuthority::FineInvalidation));
        assert_eq!(
            partial_understood.authority(),
            vec![ProvenanceAuthority::Inspection]
        );

        // Neither axis may be inferred from the other anywhere in the cross-product: for
        // each fixed capture there exist transparencies that differ, and vice versa.
        for capture in [
            CaptureStatus::Complete,
            CaptureStatus::Partial,
            CaptureStatus::Missing,
        ] {
            for transparency in [
                PayloadTransparency::Understood,
                PayloadTransparency::Mixed,
                PayloadTransparency::Opaque,
            ] {
                let value = completeness(capture, transparency, vec![]);
                assert_eq!(value.capture(), capture, "capture was rewritten");
                assert_eq!(
                    value.transparency(),
                    transparency,
                    "transparency was rewritten"
                );
            }
        }

        // The sharp form of "not collapsed", and the reason this test carries the
        // mutant's name: transparency is permitted to move EXACTLY ONE capability, the
        // one that needs semantic attribution. Every collapse — the original
        // `is_complete()` shape, or a later one that lets transparency gate replay or
        // inventory — widens this set, so it is caught here rather than only by the
        // cross-product table. Found by injecting exactly that mutant and observing
        // that the earlier version of this test still passed.
        for capture in [
            CaptureStatus::Complete,
            CaptureStatus::Partial,
            CaptureStatus::Missing,
        ] {
            for missing in [Vec::new(), vec![id("Ghost")]] {
                let understood =
                    completeness(capture, PayloadTransparency::Understood, missing.clone());
                for other in [PayloadTransparency::Mixed, PayloadTransparency::Opaque] {
                    let shifted = completeness(capture, other, missing.clone());
                    let moved: Vec<_> = ProvenanceAuthority::ALL
                        .into_iter()
                        .filter(|candidate| {
                            understood.grants(*candidate) != shifted.grants(*candidate)
                        })
                        .collect();
                    assert!(
                        moved
                            .iter()
                            .all(|candidate| *candidate == ProvenanceAuthority::FineInvalidation),
                        "transparency moved {moved:?} for {capture:?}; only FineInvalidation \
                         may depend on it, so an axis has been collapsed"
                    );
                }
            }
        }
    }

    /// The named mutant this kills: *grant authority*.
    ///
    /// Authority is derived, never stored, so a record cannot assert a capability in
    /// its bytes. What remains possible is a derivation that hands out too much, which
    /// this pins against an independently written table over the whole cross-product.
    #[test]
    fn every_authority_capability_is_earned_from_the_full_axis_tuple() {
        let mut observed = BTreeSet::new();
        for capture in [
            CaptureStatus::Complete,
            CaptureStatus::Partial,
            CaptureStatus::Missing,
        ] {
            for transparency in [
                PayloadTransparency::Understood,
                PayloadTransparency::Mixed,
                PayloadTransparency::Opaque,
            ] {
                for missing in [Vec::new(), vec![id("Ghost")]] {
                    let has_missing = !missing.is_empty();
                    let value = ProvenanceCompleteness::new(capture, transparency, missing);
                    let expected = expected_authority(capture, transparency, has_missing);
                    assert_eq!(
                        value.authority(),
                        expected,
                        "authority for {capture:?}/{transparency:?}/missing={has_missing} \
                         disagrees with the reviewed table"
                    );
                    // `grants` and `authority` must agree capability by capability, or
                    // one of the two surfaces could quietly widen.
                    for candidate in ProvenanceAuthority::ALL {
                        assert_eq!(
                            value.grants(candidate),
                            expected.contains(&candidate),
                            "{candidate:?} disagrees for {capture:?}/{transparency:?}"
                        );
                    }
                    observed.insert(value.authority());
                }
            }
        }
        // The tuple must produce genuinely different capability sets: exactly four
        // distinct ones (none, inspection-only, complete-with-unknown-closure,
        // complete-but-opaque, and fully authoritative is five). A derivation that
        // ignored an axis would collapse this count.
        assert_eq!(observed.len(), 5, "an axis stopped affecting authority");
    }

    /// Capture is knowledge from outside the record, so it cannot be recomputed — but
    /// the one available cross-check is mandatory: claiming nothing was captured while
    /// carrying contributions is a contradiction, not a permitted axis combination.
    #[test]
    fn a_record_cannot_claim_missing_capture_while_carrying_contributions() {
        for (tag, declarations, extra, contributions) in [
            ("declaration", vec![name("A.one")], vec![], vec![]),
            ("extra", vec![], vec![name("A.generated")], vec![]),
            (
                "contribution",
                vec![],
                vec![],
                vec![ExtensionContribution::new(
                    extension_descriptor("simpExt", PayloadProvenance::Understood),
                    0,
                    Digest([0x31; 32]),
                    vec![entry(0x41)],
                )],
            ),
        ] {
            let record = ModuleContributionRecord::new(
                ModuleRecord::new(id("A"), true, vec![], evidence(0xA1)),
                declarations,
                extra,
                contributions,
                ProvenanceCompleteness::new(
                    CaptureStatus::Missing,
                    PayloadTransparency::Understood,
                    vec![],
                ),
            );
            assert!(
                matches!(
                    ModuleProvenanceManifest::new(epoch(), vec![record], TEST_LIMITS),
                    Err(ModuleProvenanceError::CaptureStatusContradicted { .. })
                ),
                "a Missing record carrying a {tag} was accepted"
            );
        }

        // The refusal is not blanket: Missing over genuinely empty content is the whole
        // point of the variant, and it is distinguishable from an empty Complete record.
        let empty = |capture| {
            ModuleContributionRecord::new(
                ModuleRecord::new(id("A"), true, vec![], evidence(0xA1)),
                vec![],
                vec![],
                vec![],
                ProvenanceCompleteness::new(capture, PayloadTransparency::Understood, vec![]),
            )
        };
        let missing = ModuleProvenanceManifest::new(
            epoch(),
            vec![empty(CaptureStatus::Missing)],
            TEST_LIMITS,
        )
        .expect("Missing over empty content is legal");
        let complete = ModuleProvenanceManifest::new(
            epoch(),
            vec![empty(CaptureStatus::Complete)],
            TEST_LIMITS,
        )
        .expect("Complete over empty content is legal");
        assert_ne!(
            missing.root(),
            complete.root(),
            "the two opposite claims about the same empty content must not share a root"
        );
        assert_eq!(missing.records()[0].completeness().authority(), vec![]);
    }

    /// Transparency is recomputed from the descriptors and resolves to three states.
    /// `Mixed` is what keeps an opaque boundary localized; folding it into `Opaque`
    /// would condemn every understood contribution beside it.
    #[test]
    fn mixed_transparency_is_derived_and_localizes_the_opaque_boundary() {
        let understood = extension_descriptor("simpExt", PayloadProvenance::Understood);
        let opaque = extension_descriptor("opaqueExt", PayloadProvenance::Opaque);
        let contribution = |descriptor: &ExtensionDescriptor, seed: u8| {
            ExtensionContribution::new(
                descriptor.clone(),
                0,
                Digest([0x31; 32]),
                vec![entry_for(descriptor, &[seed])],
            )
        };

        for (contributions, expected) in [
            (
                vec![contribution(&understood, 1)],
                PayloadTransparency::Understood,
            ),
            (vec![contribution(&opaque, 2)], PayloadTransparency::Opaque),
            (
                vec![contribution(&understood, 1), contribution(&opaque, 2)],
                PayloadTransparency::Mixed,
            ),
            // A module with no extension contributions is vacuously understood.
            (vec![], PayloadTransparency::Understood),
        ] {
            let record = ModuleContributionRecord::new(
                ModuleRecord::new(id("A"), true, vec![], evidence(0xA1)),
                vec![name("A.one")],
                vec![],
                contributions,
                ProvenanceCompleteness::new(CaptureStatus::Complete, expected, vec![]),
            );
            let manifest = ModuleProvenanceManifest::new(epoch(), vec![record], TEST_LIMITS)
                .expect("the claimed transparency matches the descriptors");
            assert_eq!(
                manifest.records()[0].completeness().transparency(),
                expected
            );

            // Mixed is byte-complete, so it keeps every capability except the semantic
            // one — the localization claim, stated as authority rather than prose.
            if expected == PayloadTransparency::Mixed {
                let completeness = manifest.records()[0].completeness();
                assert!(completeness.grants(ProvenanceAuthority::AuthoritativeCache));
                assert!(!completeness.grants(ProvenanceAuthority::FineInvalidation));
            }
        }

        // A record that rounds Mixed off to Opaque is refused by the recomputation.
        let record = ModuleContributionRecord::new(
            ModuleRecord::new(id("A"), true, vec![], evidence(0xA1)),
            vec![name("A.one")],
            vec![],
            vec![contribution(&understood, 1), contribution(&opaque, 2)],
            ProvenanceCompleteness::new(
                CaptureStatus::Complete,
                PayloadTransparency::Opaque,
                vec![],
            ),
        );
        assert!(matches!(
            ModuleProvenanceManifest::new(epoch(), vec![record], TEST_LIMITS),
            Err(ModuleProvenanceError::PayloadTransparencyMismatch {
                expected: PayloadTransparency::Mixed,
                actual: PayloadTransparency::Opaque,
                ..
            })
        ));
    }

    /// Destructure a verdict that must be a collision, with the offending verdict in the
    /// failure message. One helper rather than a destructure-or-panic at each site.
    fn expect_collision(verdict: IdentityVerdict, context: &str) -> IdentityCollision {
        match verdict {
            IdentityVerdict::Collision(collision) => collision,
            other => panic!("{context}: expected a collision verdict, got {other:?}"),
        }
    }

    /// A manifest that differs from `sample_manifest` in one authoritative field, used
    /// as the second canonical value in the collision model.
    fn other_manifest() -> ModuleProvenanceManifest {
        let mut records = sample_records();
        records[0].declarations = vec![name("A.one"), name("A.different")].into();
        ModuleProvenanceManifest::new(epoch(), records, TEST_LIMITS)
            .expect("the variant manifest validates")
    }

    /// Identity is decided by the exact canonical value. The root is a *locator* and a
    /// fast inequality check, never the equality test itself.
    #[test]
    fn identity_equality_is_exact_canonical_value_and_the_root_is_only_a_locator() {
        let held = sample_manifest();
        let same = sample_manifest();
        let other = other_manifest();

        assert_eq!(held.classify_candidate(&same), IdentityVerdict::Idempotent);
        assert_eq!(held.classify_candidate(&other), IdentityVerdict::Distinct);
        assert_ne!(held.root(), other.root());

        // A decoded candidate recomputes its own root at construction, so it cannot
        // arrive claiming an identity its bytes do not have. That is the precondition
        // `classify_identity` relies on, asserted rather than assumed.
        let decoded = ModuleProvenanceManifest::from_canonical_bytes(
            &other.to_canonical_bytes(),
            TEST_LIMITS,
        )
        .expect("the variant round-trips");
        assert_eq!(decoded.root(), other.root());
        assert_eq!(decoded.verify_self_consistency(), Ok(()));
        assert_eq!(held.verify_self_consistency(), Ok(()));
    }

    /// **Bounded-model collision seam.**
    ///
    /// This test does NOT find a digest collision and must never be cited as evidence
    /// that one exists. It *injects* the equality a collision would produce — by
    /// handing `classify_identity` two genuinely different canonical values under one
    /// root — and asks the only question that matters if collision resistance ever
    /// failed: does the schema still tell the two values apart? Claim type is
    /// `bounded_model`; collision resistance itself remains a HYPOTHESIS of the digest,
    /// never an injectivity proof.
    ///
    /// This is also why `classify_identity` takes roots and bytes separately instead of
    /// re-deriving the digest: re-deriving would make the injection impossible and the
    /// property untestable.
    #[test]
    fn a_bounded_model_collision_stays_distinguishable_and_is_reported_not_resolved() {
        let held = sample_manifest();
        let other = other_manifest();
        let held_bytes = held.to_canonical_bytes();
        let other_bytes = other.to_canonical_bytes();
        assert_ne!(
            held_bytes, other_bytes,
            "the model needs two genuinely different canonical values"
        );

        // The counterfactual: assume these two values digest alike. Only `other`'s root
        // is replaced; its bytes are untouched.
        let injected = classify_identity(
            (held.root(), &held_bytes),
            (held.root(), &other_bytes), // <- `other`'s value under `held`'s root
        );
        let collision = expect_collision(injected, "an injected equal-digest/unequal-value pair");
        assert_eq!(collision.root, held.root());
        assert_eq!(collision.held_len, held_bytes.len());
        assert_eq!(collision.candidate_len, other_bytes.len());
        // First-divergence data must actually locate the disagreement, so the outcome is
        // diagnosable from the artifact alone.
        assert!(collision.first_divergence < held_bytes.len().max(other_bytes.len()));
        assert_eq!(
            held_bytes[..collision.first_divergence],
            other_bytes[..collision.first_divergence],
            "everything before the reported divergence must actually agree"
        );

        // Reported, never resolved: the seam picks no winner. Swapping the two sides
        // yields a collision again with the lengths exchanged and the same offset — if
        // either side were being preferred, the swap would disagree.
        let swapped = classify_identity((held.root(), &other_bytes), (held.root(), &held_bytes));
        let swapped = expect_collision(swapped, "the verdict must not depend on argument order");
        assert_eq!(swapped.first_divergence, collision.first_divergence);
        assert_eq!(swapped.held_len, collision.candidate_len);
        assert_eq!(swapped.candidate_len, collision.held_len);

        // The digest's *inequality* remains conclusive — that direction never depends on
        // collision resistance, because a hash cannot report different for equal inputs.
        assert_eq!(
            classify_identity((held.root(), &held_bytes), (other.root(), &other_bytes)),
            IdentityVerdict::Distinct
        );
        // And equal value under one root is still idempotent, so the collision arm has
        // not swallowed the common case.
        assert_eq!(
            classify_identity((held.root(), &held_bytes), (held.root(), &held_bytes)),
            IdentityVerdict::Idempotent
        );
    }

    /// A strict-prefix pair is the boundary case for first-divergence reporting: there
    /// is no disagreeing byte, so the offset must be the shorter length rather than a
    /// panic or a silent zero.
    #[test]
    fn a_prefix_collision_reports_the_shorter_length_as_its_divergence() {
        let held = sample_manifest();
        let bytes = held.to_canonical_bytes();
        let truncated = &bytes[..bytes.len() - 1];
        let collision = expect_collision(
            classify_identity((held.root(), &bytes), (held.root(), truncated)),
            "a strict prefix is a different canonical value",
        );
        assert_eq!(collision.first_divergence, truncated.len());
        assert_eq!(collision.held_len, bytes.len());
        assert_eq!(collision.candidate_len, truncated.len());
    }

    /// The same shape means two different things depending on where it is found.
    /// Arriving from outside it is untrusted input and a normal thing to refuse; found
    /// inside validated state it is an invariant failure, and FL-INV-07 forbids
    /// rendering that as a verdict about the module.
    #[test]
    fn the_same_inconsistency_inside_validated_state_is_an_internal_fault() {
        let healthy = sample_manifest();
        assert_eq!(healthy.verify_self_consistency(), Ok(()));

        // Only reachable from inside the module: the constructor recomputes the root, so
        // no external caller can build this state. That is exactly why finding it later
        // is a fault rather than a rejection.
        let mut corrupted = sample_manifest();
        corrupted.root = ModuleProvenanceRoot(Digest([0x00; 32]));
        let error = corrupted
            .verify_self_consistency()
            .expect_err("a corrupted validated manifest must fault");
        assert!(matches!(
            error,
            ModuleProvenanceError::InternalFault { held, recomputed, .. }
                if held == ModuleProvenanceRoot(Digest([0x00; 32]))
                    && recomputed == healthy.root()
        ));
        // It is a fault, not any of the refusals a malformed input earns.
        assert!(!matches!(
            error,
            ModuleProvenanceError::MalformedEncoding { .. }
                | ModuleProvenanceError::NonCanonicalEncoding
        ));
        assert!(
            error.to_string().contains("internal fault"),
            "the fault must be self-identifying in diagnostics: {error}"
        );
    }

    /// The named mutant this kills: *alias `ExtensionEntryId` to the mutable journal
    /// ordinal*. If the target position were folded into the identity, replaying the
    /// same module's contribution at a different journal offset would silently rename
    /// every entry, and no downstream consumer could recognise an entry across a
    /// rebase, restore, or merge.
    #[test]
    fn entry_identity_is_content_derived_and_survives_journal_rebasing() {
        let descriptor = extension_descriptor("simpExt", PayloadProvenance::Understood);
        let entries = vec![entry(0x41), entry(0x42)];

        let rebase = |start: u64| {
            let mut records = sample_records();
            records[0].extension_contributions = vec![ExtensionContribution::new(
                descriptor.clone(),
                start,
                Digest([0x31; 32]),
                entries.clone(),
            )]
            .into();
            ModuleProvenanceManifest::new(epoch(), records, TEST_LIMITS)
                .expect("a rebased range is still a valid manifest")
        };

        let at_seven = rebase(7);
        let at_zero = rebase(0);
        let far = rebase(1_000_000);

        // Rebasing invariance: the ids are byte-identical at every applied offset.
        for rebased in [&at_zero, &far] {
            assert_eq!(
                at_seven.records()[0].extension_contributions()[0].entries(),
                rebased.records()[0].extension_contributions()[0].entries(),
                "a journal offset must not rename an entry"
            );
        }

        // The applied range is still authoritative committed state, so moving it does
        // change the aggregate root. Identity-stability must not be bought by dropping
        // the range from the canonical bytes.
        assert_ne!(at_seven.root(), at_zero.root());
        assert_ne!(at_seven.root(), far.root());

        // Source ordinal and target position are two coordinates, not aliases.
        let contribution = &at_seven.records()[0].extension_contributions()[0];
        assert_eq!(contribution.source_ordinal(0), Some(0));
        assert_eq!(contribution.source_ordinal(1), Some(1));
        assert_eq!(contribution.target_position(0), Some(7));
        assert_eq!(contribution.target_position(1), Some(8));
        assert_eq!(contribution.source_ordinal(2), None);
        assert_eq!(contribution.target_position(2), None);
        assert_eq!(contribution.end(), Some(9));

        // The mutant, executed rather than merely described: derive the id the way the
        // rejected design would have, by folding the target position in. If that mutant
        // were also offset-invariant the assertions above would be vacuous, so this
        // proves the property discriminates instead of holding for free.
        let mutant = |start: u64| {
            let mut writer = CanonWriter::new();
            writer.schema(EXTENSION_ENTRY_ID_SCHEMA);
            writer.str(epoch().tag());
            writer.str(epoch().commit());
            descriptor.name.write_body(&mut writer);
            writer.u8(merge_semantics_tag(descriptor.merge));
            writer.u8(checkpoint_semantics_tag(descriptor.checkpoint));
            writer.u8(payload_provenance_tag(descriptor.provenance));
            writer.bytes(&[0x41]);
            writer.u64(start); // the defect: a rebasable journal coordinate
            hash(Domain::ModuleProvenance, &writer.into_bytes())
        };
        assert_ne!(
            mutant(7),
            mutant(0),
            "the position-folding mutant must be offset-sensitive, or this test proves nothing"
        );
        assert_ne!(
            ExtensionEntryId::from_digest(mutant(7)),
            entry(0x41),
            "the shipped derivation must not be the position-folding mutant"
        );
    }

    /// The identity's input set is exactly epoch + descriptor + payload. Every one of
    /// those must move it, and the excluded facts must not — that pair of claims is
    /// what makes the id a *content* id rather than a position or a contributor tag.
    #[test]
    fn entry_identity_binds_epoch_descriptor_and_payload_and_nothing_else() {
        let descriptor = extension_descriptor("simpExt", PayloadProvenance::Understood);
        let baseline = ExtensionEntryId::derive(&epoch(), &descriptor, &[0x41]);

        // Each authoritative input moves the identity.
        let mut moved = BTreeSet::new();
        moved.insert(baseline);
        moved.insert(ExtensionEntryId::derive(
            &ModuleEpoch::new("v4.33.0", PIN_COMMIT),
            &descriptor,
            &[0x41],
        ));
        moved.insert(ExtensionEntryId::derive(&epoch(), &descriptor, &[0x42]));
        moved.insert(ExtensionEntryId::derive(&epoch(), &descriptor, &[]));
        for altered in [
            extension_descriptor("otherExt", PayloadProvenance::Understood),
            extension_descriptor("simpExt", PayloadProvenance::Opaque),
            ExtensionDescriptor {
                merge: MergeSemantics::SetUnion,
                ..descriptor.clone()
            },
            ExtensionDescriptor {
                checkpoint: CheckpointSemantics::FullJournal,
                ..descriptor.clone()
            },
        ] {
            moved.insert(ExtensionEntryId::derive(&epoch(), &altered, &[0x41]));
        }
        assert_eq!(
            moved.len(),
            8,
            "an authoritative input failed to move the id"
        );

        // The excluded facts do not move it: the same payload contributed by a
        // different module, at a different source ordinal, in a different range, is the
        // same entry.
        let elsewhere = ExtensionContribution::new(
            descriptor.clone(),
            4_096,
            Digest([0xAB; 32]),
            vec![entry(0x99), entry(0x41)],
        );
        assert_eq!(elsewhere.entries()[1], baseline);
        assert_eq!(elsewhere.source_ordinal(1), Some(1));
        assert_eq!(elsewhere.target_position(1), Some(4_097));
    }

    /// Equal descriptor and payload share one content id by construction; occurrences
    /// stay distinct through `(ModuleId, source ordinal, entry id)`. This is what lets
    /// duplicate replay data be retained without collapsing it.
    #[test]
    fn equal_payloads_share_one_content_id_while_occurrences_stay_distinct() {
        let descriptor = extension_descriptor("simpExt", PayloadProvenance::Understood);
        let repeated = entry(0x41);
        let mut records = sample_records();
        records[0].extension_contributions = vec![ExtensionContribution::new(
            descriptor,
            7,
            Digest([0x31; 32]),
            vec![repeated, repeated, entry(0x42)],
        )]
        .into();
        let manifest = ModuleProvenanceManifest::new(epoch(), records, TEST_LIMITS)
            .expect("repeated occurrences are ordered replay data, not a duplicate error");

        let contribution = &manifest.records()[0].extension_contributions()[0];
        assert_eq!(
            contribution.entries().len(),
            3,
            "an occurrence was collapsed"
        );
        assert_eq!(contribution.entries()[0], contribution.entries()[1]);
        assert_ne!(contribution.entries()[0], contribution.entries()[2]);

        // The two identical entries are the same *entry* at two different occurrences.
        assert_ne!(
            contribution.source_ordinal(0),
            contribution.source_ordinal(1)
        );
        assert_ne!(
            contribution.target_position(0),
            contribution.target_position(1)
        );

        // Retention is observable in the canonical bytes, not just in memory.
        let bytes = manifest.to_canonical_bytes().to_vec();
        let decoded = ModuleProvenanceManifest::from_canonical_bytes(&bytes, TEST_LIMITS)
            .expect("repeated occurrences round-trip");
        assert_eq!(decoded.root(), manifest.root());
        assert_eq!(
            decoded.records()[0].extension_contributions()[0].entries(),
            contribution.entries()
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
                        CaptureStatus::Complete,
                        PayloadTransparency::Understood,
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
