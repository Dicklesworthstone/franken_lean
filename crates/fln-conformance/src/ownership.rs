//! Bounded, fail-closed ownership evidence for the kernel contract.
//!
//! The tracked manifest is always authoritative and always required. A local Beads
//! export is either required explicitly or may be absent only when the caller pins
//! both the exact manifest-byte digest and its projection digest. If the source is
//! present in either mode, its sorted issue-id projection must equal the manifest
//! projection exactly.

#![forbid(unsafe_code)]

use fln_hash::domain::{Digest, Domain, DomainHasher};
use std::collections::BTreeSet;
use std::fs::{self, File, Metadata};
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::str;

pub const MANIFEST_RELATIVE_PATH: &str = "ci/KERNEL_CONTRACT_OWNERSHIP.jsonl";
pub const SOURCE_RELATIVE_PATH: &str = ".beads/issues.jsonl";
pub const MANIFEST_SCHEMA: &str = "fln.kernel-contract-ownership/1";
pub const PROJECTION_SCHEMA: &str = "sorted-canonical-issue-ids-v1";
pub const HASH_ALGORITHM: &str = "fln-domain-registry-v1";
pub const HASH_DOMAIN: &str = "fln 2026 domain fixture/1";
pub const PROJECTION_HASH_PREIMAGE: &str =
    "fln.kernel-contract-ownership.ids/1+nul+u64le-length-prefixed-utf8";
pub const MANIFEST_HASH_PREIMAGE: &str =
    "fln.kernel-contract-ownership.manifest/1+nul+u64le-length-prefixed-bytes";

const PROJECTION_HASH_TAG: &[u8] = b"fln.kernel-contract-ownership.ids/1";
const MANIFEST_HASH_TAG: &[u8] = b"fln.kernel-contract-ownership.manifest/1";
const CANONICAL_ID_PREFIX: &[u8] = b"{\"id\":\"";

pub const ABSOLUTE_MAX_FILE_BYTES: u64 = 64 * 1024 * 1024;
pub const ABSOLUTE_MAX_LINE_BYTES: u64 = 1024 * 1024;
pub const ABSOLUTE_MAX_RECORDS: u64 = 1_000_000;
pub const ABSOLUTE_MAX_ID_BYTES: u64 = 4096;
pub const ABSOLUTE_MAX_PARSE_DEPTH: u64 = 256;
pub const ABSOLUTE_MAX_DIAGNOSTIC_BYTES: usize = 64 * 1024;

/// Explicit resource contract for both tracked inputs.
///
/// File and line limits apply independently to each input. `max_records` excludes
/// the manifest header. JSON container depth counts the top-level object as one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OwnershipLimits {
    max_file_bytes: u64,
    max_line_bytes: u64,
    max_records: u64,
    max_id_bytes: u64,
    max_parse_depth: u64,
    max_diagnostic_bytes: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnershipLimitField {
    FileBytes,
    LineBytes,
    Records,
    IdBytes,
    ParseDepth,
    DiagnosticBytes,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OwnershipLimitError {
    field: OwnershipLimitField,
    requested: u64,
    absolute_maximum: u64,
}

impl OwnershipLimitError {
    pub fn field(&self) -> OwnershipLimitField {
        self.field
    }

    pub fn requested(&self) -> u64 {
        self.requested
    }

    pub fn absolute_maximum(&self) -> u64 {
        self.absolute_maximum
    }
}

impl std::fmt::Display for OwnershipLimitError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "ownership limit {:?} requested {} but the absolute maximum is {}",
            self.field, self.requested, self.absolute_maximum
        )
    }
}

impl std::error::Error for OwnershipLimitError {}

impl OwnershipLimits {
    pub fn try_new(
        max_file_bytes: u64,
        max_line_bytes: u64,
        max_records: u64,
        max_id_bytes: u64,
        max_parse_depth: u64,
        max_diagnostic_bytes: usize,
    ) -> Result<Self, OwnershipLimitError> {
        check_limit(
            OwnershipLimitField::FileBytes,
            max_file_bytes,
            ABSOLUTE_MAX_FILE_BYTES,
        )?;
        check_limit(
            OwnershipLimitField::LineBytes,
            max_line_bytes,
            ABSOLUTE_MAX_LINE_BYTES,
        )?;
        check_limit(
            OwnershipLimitField::Records,
            max_records,
            ABSOLUTE_MAX_RECORDS,
        )?;
        check_limit(
            OwnershipLimitField::IdBytes,
            max_id_bytes,
            ABSOLUTE_MAX_ID_BYTES,
        )?;
        check_limit(
            OwnershipLimitField::ParseDepth,
            max_parse_depth,
            ABSOLUTE_MAX_PARSE_DEPTH,
        )?;
        let diagnostic_bytes = u64::try_from(max_diagnostic_bytes).unwrap_or(u64::MAX);
        check_limit(
            OwnershipLimitField::DiagnosticBytes,
            diagnostic_bytes,
            ABSOLUTE_MAX_DIAGNOSTIC_BYTES as u64,
        )?;
        Ok(Self {
            max_file_bytes,
            max_line_bytes,
            max_records,
            max_id_bytes,
            max_parse_depth,
            max_diagnostic_bytes,
        })
    }

    pub fn max_file_bytes(&self) -> u64 {
        self.max_file_bytes
    }

    pub fn max_line_bytes(&self) -> u64 {
        self.max_line_bytes
    }

    pub fn max_records(&self) -> u64 {
        self.max_records
    }

    pub fn max_id_bytes(&self) -> u64 {
        self.max_id_bytes
    }

    pub fn max_parse_depth(&self) -> u64 {
        self.max_parse_depth
    }

    pub fn max_diagnostic_bytes(&self) -> usize {
        self.max_diagnostic_bytes
    }
}

fn check_limit(
    field: OwnershipLimitField,
    requested: u64,
    absolute_maximum: u64,
) -> Result<(), OwnershipLimitError> {
    if requested <= absolute_maximum {
        Ok(())
    } else {
        Err(OwnershipLimitError {
            field,
            requested,
            absolute_maximum,
        })
    }
}

impl Default for OwnershipLimits {
    fn default() -> Self {
        Self {
            max_file_bytes: 8 * 1024 * 1024,
            max_line_bytes: 256 * 1024,
            max_records: 100_000,
            max_id_bytes: 256,
            max_parse_depth: 128,
            max_diagnostic_bytes: 4096,
        }
    }
}

/// Digests pinned independently of the manifest being loaded.
///
/// `manifest_digest` binds every byte of the tracked manifest, including its final
/// LF. `projection_digest` binds the sorted issue-id sequence.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExpectedManifestBinding {
    pub manifest_digest: Digest,
    pub projection_digest: Digest,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnershipBindingField {
    ManifestDigest,
    ProjectionDigest,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OwnershipBindingParseError {
    field: OwnershipBindingField,
}

impl OwnershipBindingParseError {
    pub fn field(&self) -> OwnershipBindingField {
        self.field
    }
}

impl std::fmt::Display for OwnershipBindingParseError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "expected ownership {:?} must be exactly 64 lowercase hexadecimal digits",
            self.field
        )
    }
}

impl std::error::Error for OwnershipBindingParseError {}

impl ExpectedManifestBinding {
    pub fn from_lower_hex(
        manifest_digest: &str,
        projection_digest: &str,
    ) -> Result<Self, OwnershipBindingParseError> {
        Ok(Self {
            manifest_digest: parse_digest(manifest_digest).map_err(|_| {
                OwnershipBindingParseError {
                    field: OwnershipBindingField::ManifestDigest,
                }
            })?,
            projection_digest: parse_digest(projection_digest).map_err(|_| {
                OwnershipBindingParseError {
                    field: OwnershipBindingField::ProjectionDigest,
                }
            })?,
        })
    }
}

/// Whether the canonical Beads export must be available in this execution
/// environment.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnershipSourceMode {
    /// Local/CI mode: the source export must exist and equal the manifest.
    RequireSource,
    /// Transfer-constrained mode: source absence is accepted only after both exact
    /// independently supplied digests match. A present source is still verified.
    ManifestOnly(ExpectedManifestBinding),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OwnershipBinding {
    manifest_digest: Digest,
    projection_digest: Digest,
    record_count: u64,
}

impl OwnershipBinding {
    pub fn manifest_digest(&self) -> Digest {
        self.manifest_digest
    }

    pub fn projection_digest(&self) -> Digest {
        self.projection_digest
    }

    pub fn record_count(&self) -> u64 {
        self.record_count
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnershipSourceState {
    NotAttempted,
    Absent,
    Unavailable,
    Present,
    PresentVerified,
}

impl OwnershipSourceState {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::NotAttempted => "not-attempted",
            Self::Absent => "absent",
            Self::Unavailable => "unavailable",
            Self::Present => "present",
            Self::PresentVerified => "present-verified",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InputUsage {
    file_bytes_observed: u64,
    bytes_read: u64,
    physical_lines: u64,
    records_observed: u64,
    max_line_bytes_observed: u64,
    max_id_bytes_observed: u64,
    max_parse_depth_observed: u64,
}

impl InputUsage {
    pub fn file_bytes_observed(&self) -> u64 {
        self.file_bytes_observed
    }

    pub fn bytes_read(&self) -> u64 {
        self.bytes_read
    }

    pub fn physical_lines(&self) -> u64 {
        self.physical_lines
    }

    pub fn records_observed(&self) -> u64 {
        self.records_observed
    }

    pub fn max_line_bytes_observed(&self) -> u64 {
        self.max_line_bytes_observed
    }

    pub fn max_id_bytes_observed(&self) -> u64 {
        self.max_id_bytes_observed
    }

    pub fn max_parse_depth_observed(&self) -> u64 {
        self.max_parse_depth_observed
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnershipUsage {
    manifest: InputUsage,
    source: InputUsage,
    source_state: OwnershipSourceState,
    required_owners: u64,
}

impl Default for OwnershipUsage {
    fn default() -> Self {
        Self {
            manifest: InputUsage::default(),
            source: InputUsage::default(),
            source_state: OwnershipSourceState::NotAttempted,
            required_owners: 0,
        }
    }
}

impl OwnershipUsage {
    pub fn manifest(&self) -> &InputUsage {
        &self.manifest
    }

    pub fn source(&self) -> &InputUsage {
        &self.source
    }

    pub fn source_state(&self) -> OwnershipSourceState {
        self.source_state
    }

    pub fn required_owners(&self) -> u64 {
        self.required_owners
    }
}

/// Returned only after manifest, optional/required source, and all required owners
/// have been verified. There is no partially valid evidence value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnershipEvidence {
    owners: BTreeSet<String>,
    binding: OwnershipBinding,
    usage: OwnershipUsage,
}

impl OwnershipEvidence {
    pub fn owners(&self) -> &BTreeSet<String> {
        &self.owners
    }

    pub fn binding(&self) -> OwnershipBinding {
        self.binding
    }

    pub fn usage(&self) -> &OwnershipUsage {
        &self.usage
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnershipInput {
    Manifest,
    Source,
    Requirements,
}

impl OwnershipInput {
    fn relative_path(self) -> Option<&'static str> {
        match self {
            Self::Manifest => Some(MANIFEST_RELATIVE_PATH),
            Self::Source => Some(SOURCE_RELATIVE_PATH),
            Self::Requirements => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnershipResource {
    FileBytes,
    LineBytes,
    Records,
    IdBytes,
    ParseDepth,
}

impl OwnershipResource {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::FileBytes => "file-bytes",
            Self::LineBytes => "line-bytes",
            Self::Records => "records",
            Self::IdBytes => "id-bytes",
            Self::ParseDepth => "parse-depth",
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MalformedReason {
    InvalidUtf8,
    InvalidJson,
    InvalidUnicodeEscape,
    InvalidNumber,
    InvalidDigest,
    NumericOverflow,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NoncanonicalReason {
    Header,
    ManifestRecord,
    SourceRecord,
    IdMissing,
    IdNotFirst,
    EscapedId,
    InvalidId,
    RecordOrder,
    BlankLine,
    CrLf,
    MissingFinalLf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StaleBindingReason {
    ManifestRecordCount,
    ManifestProjectionDigest,
    ExpectedManifestDigest,
    ExpectedProjectionDigest,
    SourceProjection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OwnershipFailureClass {
    Missing,
    Unreadable,
    Malformed,
    Empty,
    DuplicateId,
    Noncanonical,
    StaleBinding,
    PhantomOwner,
    ResourceExhausted,
}

impl OwnershipFailureClass {
    pub const fn code(self) -> &'static str {
        match self {
            Self::Missing => "bead-evidence/missing",
            Self::Unreadable => "bead-evidence/unreadable",
            Self::Malformed => "bead-evidence/malformed",
            Self::Empty => "bead-evidence/empty",
            Self::DuplicateId => "bead-evidence/duplicate-id",
            Self::Noncanonical => "bead-evidence/noncanonical",
            Self::StaleBinding => "bead-evidence/stale-binding",
            Self::PhantomOwner => "bead-evidence/phantom-owner",
            Self::ResourceExhausted => "bead-evidence/resource-exhausted",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OwnershipFailureKind {
    Missing,
    Unreadable {
        kind: io::ErrorKind,
    },
    Malformed {
        reason: MalformedReason,
    },
    Empty,
    DuplicateId {
        id: String,
    },
    Noncanonical {
        reason: NoncanonicalReason,
    },
    StaleBinding {
        reason: StaleBindingReason,
    },
    PhantomOwner {
        owner: String,
    },
    ResourceExhausted {
        resource: OwnershipResource,
        limit: u64,
        observed: u64,
    },
}

impl OwnershipFailureKind {
    fn class(&self) -> OwnershipFailureClass {
        match self {
            Self::Missing => OwnershipFailureClass::Missing,
            Self::Unreadable { .. } => OwnershipFailureClass::Unreadable,
            Self::Malformed { .. } => OwnershipFailureClass::Malformed,
            Self::Empty => OwnershipFailureClass::Empty,
            Self::DuplicateId { .. } => OwnershipFailureClass::DuplicateId,
            Self::Noncanonical { .. } => OwnershipFailureClass::Noncanonical,
            Self::StaleBinding { .. } => OwnershipFailureClass::StaleBinding,
            Self::PhantomOwner { .. } => OwnershipFailureClass::PhantomOwner,
            Self::ResourceExhausted { .. } => OwnershipFailureClass::ResourceExhausted,
        }
    }

    pub const fn result_classification(&self) -> &'static str {
        match self {
            Self::Missing => "missing",
            Self::Unreadable { .. } => "unreadable",
            Self::Malformed { .. } => "malformed",
            Self::Empty => "empty",
            Self::DuplicateId { .. } => "duplicate-id",
            Self::Noncanonical { .. } => "noncanonical",
            Self::StaleBinding { .. } => "stale-binding",
            Self::PhantomOwner { .. } => "phantom-owner",
            Self::ResourceExhausted {
                resource: OwnershipResource::FileBytes,
                ..
            } => "resource-exhausted/file-bytes",
            Self::ResourceExhausted {
                resource: OwnershipResource::LineBytes,
                ..
            } => "resource-exhausted/line-bytes",
            Self::ResourceExhausted {
                resource: OwnershipResource::Records,
                ..
            } => "resource-exhausted/records",
            Self::ResourceExhausted {
                resource: OwnershipResource::IdBytes,
                ..
            } => "resource-exhausted/id-bytes",
            Self::ResourceExhausted {
                resource: OwnershipResource::ParseDepth,
                ..
            } => "resource-exhausted/parse-depth",
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnershipLocation {
    input: OwnershipInput,
    path: Option<PathBuf>,
    line: Option<u64>,
    column: Option<u64>,
    record: Option<u64>,
}

impl OwnershipLocation {
    fn new(input: OwnershipInput, path: Option<PathBuf>) -> Self {
        Self {
            input,
            path,
            line: None,
            column: None,
            record: None,
        }
    }

    fn at_line(mut self, line: u64) -> Self {
        self.line = Some(line);
        self
    }

    fn at_column(mut self, column: u64) -> Self {
        self.column = Some(column);
        self
    }

    fn at_record(mut self, record: u64) -> Self {
        self.record = Some(record);
        self
    }

    pub fn input(&self) -> OwnershipInput {
        self.input
    }

    pub fn path(&self) -> Option<&Path> {
        self.path.as_deref()
    }

    pub fn line(&self) -> Option<u64> {
        self.line
    }

    pub fn column(&self) -> Option<u64> {
        self.column
    }

    pub fn record(&self) -> Option<u64> {
        self.record
    }
}

/// Typed failure. A verified binding is deliberately retained only for
/// `PhantomOwner`: that class occurs after all evidence inputs have been verified.
/// Every earlier refusal carries numeric usage but no partial IDs or binding.
#[derive(Debug, Clone, PartialEq, Eq)]
struct OwnershipFailureData {
    kind: OwnershipFailureKind,
    location: OwnershipLocation,
    usage: OwnershipUsage,
    diagnostic_limit: usize,
    binding: Option<OwnershipBinding>,
}

/// The detailed refusal payload is boxed so the public `Result` error remains
/// pointer-sized. Refusals are exceptional, and keeping the success-path return
/// compact avoids copying two complete resource-usage records at every `?`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnershipFailure {
    data: Box<OwnershipFailureData>,
}

impl OwnershipFailure {
    fn new(
        kind: OwnershipFailureKind,
        location: OwnershipLocation,
        usage: OwnershipUsage,
        diagnostic_limit: usize,
        binding: Option<OwnershipBinding>,
    ) -> Self {
        Self {
            data: Box::new(OwnershipFailureData {
                kind,
                location,
                usage,
                diagnostic_limit,
                binding,
            }),
        }
    }

    pub fn class(&self) -> OwnershipFailureClass {
        self.data.kind.class()
    }

    pub fn kind(&self) -> &OwnershipFailureKind {
        &self.data.kind
    }

    pub fn result_classification(&self) -> &'static str {
        self.data.kind.result_classification()
    }

    pub fn location(&self) -> &OwnershipLocation {
        &self.data.location
    }

    pub fn usage(&self) -> &OwnershipUsage {
        &self.data.usage
    }

    /// `Some` if and only if `class() == PhantomOwner`.
    pub fn binding(&self) -> Option<OwnershipBinding> {
        self.data.binding
    }

    pub fn diagnostic(&self) -> String {
        let mut out = BoundedDiagnostic::new(self.data.diagnostic_limit);
        out.push("[");
        out.push(self.class().code());
        out.push("] ");
        out.push(match &self.data.kind {
            OwnershipFailureKind::Missing => "required ownership evidence is missing",
            OwnershipFailureKind::Unreadable { .. } => "ownership evidence cannot be read",
            OwnershipFailureKind::Malformed { .. } => "ownership evidence is malformed",
            OwnershipFailureKind::Empty => "ownership evidence contains no issue ids",
            OwnershipFailureKind::DuplicateId { .. } => "ownership evidence repeats an issue id",
            OwnershipFailureKind::Noncanonical { .. } => "ownership evidence is not canonical",
            OwnershipFailureKind::StaleBinding { .. } => "ownership evidence binding is stale",
            OwnershipFailureKind::PhantomOwner { .. } => {
                "kernel-contract stub owner is not tracked"
            }
            OwnershipFailureKind::ResourceExhausted { .. } => {
                "ownership evidence exceeded a resource limit"
            }
        });
        if let Some(path) = &self.data.location.path {
            out.push(" path=");
            out.push_path(path);
        }
        if let Some(line) = self.data.location.line {
            out.push(" line=");
            out.push_u64(line);
        }
        if let Some(column) = self.data.location.column {
            out.push(" column=");
            out.push_u64(column);
        }
        if let Some(record) = self.data.location.record {
            out.push(" record=");
            out.push_u64(record);
        }
        match &self.data.kind {
            OwnershipFailureKind::Unreadable { kind } => {
                out.push(" io_kind=");
                out.push(io_kind_name(*kind));
            }
            OwnershipFailureKind::Malformed { reason } => {
                out.push(" reason=");
                out.push(malformed_reason_name(*reason));
            }
            OwnershipFailureKind::DuplicateId { id } => {
                out.push(" id=");
                out.push(id);
            }
            OwnershipFailureKind::Noncanonical { reason } => {
                out.push(" reason=");
                out.push(noncanonical_reason_name(*reason));
            }
            OwnershipFailureKind::StaleBinding { reason } => {
                out.push(" reason=");
                out.push(stale_reason_name(*reason));
            }
            OwnershipFailureKind::PhantomOwner { owner } => {
                out.push(" owner=");
                out.push(owner);
            }
            OwnershipFailureKind::ResourceExhausted {
                resource,
                limit,
                observed,
            } => {
                out.push(" resource=");
                out.push(resource_name(*resource));
                out.push(" limit=");
                out.push_u64(*limit);
                out.push(" observed=");
                out.push_u64(*observed);
            }
            OwnershipFailureKind::Missing | OwnershipFailureKind::Empty => {}
        }
        out.finish()
    }
}

impl std::fmt::Display for OwnershipFailure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.diagnostic())
    }
}

impl std::error::Error for OwnershipFailure {}

fn io_kind_name(kind: io::ErrorKind) -> &'static str {
    match kind {
        io::ErrorKind::NotFound => "not-found",
        io::ErrorKind::PermissionDenied => "permission-denied",
        io::ErrorKind::BrokenPipe => "broken-pipe",
        io::ErrorKind::AlreadyExists => "already-exists",
        io::ErrorKind::WouldBlock => "would-block",
        io::ErrorKind::InvalidInput => "invalid-input",
        io::ErrorKind::InvalidData => "invalid-data",
        io::ErrorKind::TimedOut => "timed-out",
        io::ErrorKind::WriteZero => "write-zero",
        io::ErrorKind::Interrupted => "interrupted",
        io::ErrorKind::Unsupported => "unsupported",
        io::ErrorKind::UnexpectedEof => "unexpected-eof",
        io::ErrorKind::Other => "other",
        _ => "unknown",
    }
}

fn malformed_reason_name(reason: MalformedReason) -> &'static str {
    match reason {
        MalformedReason::InvalidUtf8 => "invalid-utf8",
        MalformedReason::InvalidJson => "invalid-json",
        MalformedReason::InvalidUnicodeEscape => "invalid-unicode-escape",
        MalformedReason::InvalidNumber => "invalid-number",
        MalformedReason::InvalidDigest => "invalid-digest",
        MalformedReason::NumericOverflow => "numeric-overflow",
    }
}

fn noncanonical_reason_name(reason: NoncanonicalReason) -> &'static str {
    match reason {
        NoncanonicalReason::Header => "header",
        NoncanonicalReason::ManifestRecord => "manifest-record",
        NoncanonicalReason::SourceRecord => "source-record",
        NoncanonicalReason::IdMissing => "id-missing",
        NoncanonicalReason::IdNotFirst => "id-not-first",
        NoncanonicalReason::EscapedId => "escaped-id",
        NoncanonicalReason::InvalidId => "invalid-id",
        NoncanonicalReason::RecordOrder => "record-order",
        NoncanonicalReason::BlankLine => "blank-line",
        NoncanonicalReason::CrLf => "crlf",
        NoncanonicalReason::MissingFinalLf => "missing-final-lf",
    }
}

fn stale_reason_name(reason: StaleBindingReason) -> &'static str {
    match reason {
        StaleBindingReason::ManifestRecordCount => "manifest-record-count",
        StaleBindingReason::ManifestProjectionDigest => "manifest-projection-digest",
        StaleBindingReason::ExpectedManifestDigest => "expected-manifest-digest",
        StaleBindingReason::ExpectedProjectionDigest => "expected-projection-digest",
        StaleBindingReason::SourceProjection => "source-projection",
    }
}

fn resource_name(resource: OwnershipResource) -> &'static str {
    resource.as_str()
}

struct BoundedDiagnostic {
    text: String,
    limit: usize,
}

impl BoundedDiagnostic {
    fn new(limit: usize) -> Self {
        Self {
            text: String::with_capacity(limit.min(512)),
            limit,
        }
    }

    fn push(&mut self, text: &str) {
        for character in text.chars() {
            let character = if character.is_control() {
                '?'
            } else {
                character
            };
            if self.text.len() + character.len_utf8() > self.limit {
                break;
            }
            self.text.push(character);
        }
    }

    fn push_path(&mut self, path: &Path) {
        self.push(path.to_string_lossy().as_ref());
    }

    fn push_u64(&mut self, value: u64) {
        self.push(&value.to_string());
    }

    fn finish(self) -> String {
        self.text
    }
}

fn same_file_identity(before: &Metadata, after: &Metadata) -> bool {
    before.file_type().is_file()
        && after.file_type().is_file()
        && before.len() == after.len()
        && platform_file_identity_matches(before, after)
}

#[cfg(unix)]
fn platform_file_identity_matches(before: &Metadata, after: &Metadata) -> bool {
    use std::os::unix::fs::MetadataExt;

    before.dev() == after.dev() && before.ino() == after.ino()
}

#[cfg(not(unix))]
fn platform_file_identity_matches(before: &Metadata, after: &Metadata) -> bool {
    matches!(
        (before.modified(), after.modified()),
        (Ok(before_modified), Ok(after_modified)) if before_modified == after_modified
    )
}

struct Loader<'a> {
    root: &'a Path,
    limits: OwnershipLimits,
    usage: OwnershipUsage,
}

impl<'a> Loader<'a> {
    fn new(root: &'a Path, limits: OwnershipLimits, required_owners: u64) -> Self {
        Self {
            root,
            limits,
            usage: OwnershipUsage {
                required_owners,
                ..OwnershipUsage::default()
            },
        }
    }

    fn path(&self, input: OwnershipInput) -> PathBuf {
        self.root.join(
            input
                .relative_path()
                .expect("only evidence inputs have filesystem paths"),
        )
    }

    fn input_usage_mut(&mut self, input: OwnershipInput) -> &mut InputUsage {
        match input {
            OwnershipInput::Manifest => &mut self.usage.manifest,
            OwnershipInput::Source => &mut self.usage.source,
            OwnershipInput::Requirements => {
                unreachable!("requirements do not consume an evidence file")
            }
        }
    }

    fn location(&self, input: OwnershipInput) -> OwnershipLocation {
        OwnershipLocation::new(input, input.relative_path().map(|_| self.path(input)))
    }

    fn failure(&self, kind: OwnershipFailureKind, location: OwnershipLocation) -> OwnershipFailure {
        OwnershipFailure::new(
            kind,
            location,
            self.usage.clone(),
            self.limits.max_diagnostic_bytes,
            None,
        )
    }

    fn phantom_failure(&self, owner: String, binding: OwnershipBinding) -> OwnershipFailure {
        OwnershipFailure::new(
            OwnershipFailureKind::PhantomOwner { owner },
            OwnershipLocation::new(OwnershipInput::Requirements, None),
            self.usage.clone(),
            self.limits.max_diagnostic_bytes,
            Some(binding),
        )
    }

    fn read_required(&mut self, input: OwnershipInput) -> Result<Vec<u8>, OwnershipFailure> {
        match self.read_file(input)? {
            Some(bytes) => Ok(bytes),
            None => Err(self.failure(OwnershipFailureKind::Missing, self.location(input))),
        }
    }

    fn read_file(&mut self, input: OwnershipInput) -> Result<Option<Vec<u8>>, OwnershipFailure> {
        let path = self.path(input);
        for directory in [
            self.root,
            path.parent().expect("evidence paths have parents"),
        ] {
            let metadata = match fs::symlink_metadata(directory) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
                Err(error) => {
                    if input == OwnershipInput::Source {
                        self.usage.source_state = OwnershipSourceState::Unavailable;
                    }
                    return Err(self.failure(
                        OwnershipFailureKind::Unreadable { kind: error.kind() },
                        self.location(input),
                    ));
                }
            };
            if !metadata.file_type().is_dir() {
                if input == OwnershipInput::Source {
                    self.usage.source_state = OwnershipSourceState::Unavailable;
                }
                return Err(self.failure(
                    OwnershipFailureKind::Unreadable {
                        kind: io::ErrorKind::InvalidInput,
                    },
                    self.location(input),
                ));
            }
        }
        let path_metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => {
                if input == OwnershipInput::Source {
                    self.usage.source_state = OwnershipSourceState::Present;
                }
                metadata
            }
            Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(None),
            Err(error) => {
                if input == OwnershipInput::Source {
                    self.usage.source_state = OwnershipSourceState::Unavailable;
                }
                return Err(self.failure(
                    OwnershipFailureKind::Unreadable { kind: error.kind() },
                    self.location(input),
                ));
            }
        };
        if !path_metadata.file_type().is_file() {
            return Err(self.failure(
                OwnershipFailureKind::Unreadable {
                    kind: io::ErrorKind::InvalidInput,
                },
                self.location(input),
            ));
        }

        let mut file = match File::open(&path) {
            Ok(file) => file,
            Err(error) => {
                // The path existed at preflight. A NotFound here is a race, not
                // permission to downgrade a required/present source to absence.
                return Err(self.failure(
                    OwnershipFailureKind::Unreadable { kind: error.kind() },
                    self.location(input),
                ));
            }
        };
        let metadata = match file.metadata() {
            Ok(metadata) => metadata,
            Err(error) => {
                return Err(self.failure(
                    OwnershipFailureKind::Unreadable { kind: error.kind() },
                    self.location(input),
                ));
            }
        };
        if !metadata.file_type().is_file() {
            return Err(self.failure(
                OwnershipFailureKind::Unreadable {
                    kind: io::ErrorKind::InvalidInput,
                },
                self.location(input),
            ));
        }
        if !same_file_identity(&path_metadata, &metadata) {
            return Err(self.failure(
                OwnershipFailureKind::Unreadable {
                    kind: io::ErrorKind::InvalidData,
                },
                self.location(input),
            ));
        }

        {
            let usage = self.input_usage_mut(input);
            usage.file_bytes_observed = metadata.len();
        }
        if metadata.len() > self.limits.max_file_bytes {
            return Err(self.failure(
                OwnershipFailureKind::ResourceExhausted {
                    resource: OwnershipResource::FileBytes,
                    limit: self.limits.max_file_bytes,
                    observed: metadata.len(),
                },
                self.location(input),
            ));
        }

        let mut bytes = Vec::new();
        let mut buffer = [0_u8; 8192];
        loop {
            let bytes_read = self.input_usage_mut(input).bytes_read;
            let remaining = self.limits.max_file_bytes.saturating_sub(bytes_read);
            let request = if remaining >= buffer.len() as u64 {
                buffer.len()
            } else {
                usize::try_from(remaining).expect("remaining is less than the fixed read buffer")
                    + 1
            };
            let count = match file.read(&mut buffer[..request]) {
                Ok(0) => break,
                Ok(count) => count,
                Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                Err(error) => {
                    return Err(self.failure(
                        OwnershipFailureKind::Unreadable { kind: error.kind() },
                        self.location(input),
                    ));
                }
            };
            let observed = bytes_read.saturating_add(count as u64);
            {
                let usage = self.input_usage_mut(input);
                usage.bytes_read = observed;
                usage.file_bytes_observed = usage.file_bytes_observed.max(observed);
            }
            if observed > self.limits.max_file_bytes {
                return Err(self.failure(
                    OwnershipFailureKind::ResourceExhausted {
                        resource: OwnershipResource::FileBytes,
                        limit: self.limits.max_file_bytes,
                        observed,
                    },
                    self.location(input),
                ));
            }
            bytes.extend_from_slice(&buffer[..count]);
        }
        let opened_after = match file.metadata() {
            Ok(metadata) => metadata,
            Err(error) => {
                return Err(self.failure(
                    OwnershipFailureKind::Unreadable { kind: error.kind() },
                    self.location(input),
                ));
            }
        };
        let path_after = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error) => {
                return Err(self.failure(
                    OwnershipFailureKind::Unreadable { kind: error.kind() },
                    self.location(input),
                ));
            }
        };
        if !same_file_identity(&metadata, &opened_after)
            || !same_file_identity(&metadata, &path_after)
            || u64::try_from(bytes.len()).ok() != Some(metadata.len())
        {
            return Err(self.failure(
                OwnershipFailureKind::Unreadable {
                    kind: io::ErrorKind::InvalidData,
                },
                self.location(input),
            ));
        }
        Ok(Some(bytes))
    }

    fn observe_line(
        &mut self,
        input: OwnershipInput,
        line_number: u64,
        line: &[u8],
    ) -> Result<(), OwnershipFailure> {
        let observed = line.len() as u64;
        {
            let usage = self.input_usage_mut(input);
            usage.physical_lines = line_number;
            usage.max_line_bytes_observed = usage.max_line_bytes_observed.max(observed);
        }
        if observed > self.limits.max_line_bytes {
            return Err(self.failure(
                OwnershipFailureKind::ResourceExhausted {
                    resource: OwnershipResource::LineBytes,
                    limit: self.limits.max_line_bytes,
                    observed,
                },
                self.location(input).at_line(line_number),
            ));
        }
        Ok(())
    }

    fn observe_record(
        &mut self,
        input: OwnershipInput,
        line_number: u64,
        record_number: u64,
    ) -> Result<(), OwnershipFailure> {
        self.input_usage_mut(input).records_observed = record_number;
        if record_number > self.limits.max_records {
            return Err(self.failure(
                OwnershipFailureKind::ResourceExhausted {
                    resource: OwnershipResource::Records,
                    limit: self.limits.max_records,
                    observed: record_number,
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        }
        Ok(())
    }

    fn observe_id(
        &mut self,
        input: OwnershipInput,
        line_number: u64,
        record_number: u64,
        id_len: u64,
    ) -> Result<(), OwnershipFailure> {
        {
            let usage = self.input_usage_mut(input);
            usage.max_id_bytes_observed = usage.max_id_bytes_observed.max(id_len);
        }
        if id_len > self.limits.max_id_bytes {
            return Err(self.failure(
                OwnershipFailureKind::ResourceExhausted {
                    resource: OwnershipResource::IdBytes,
                    limit: self.limits.max_id_bytes,
                    observed: id_len,
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        }
        Ok(())
    }

    fn parse_json_object(
        &mut self,
        input: OwnershipInput,
        line_number: u64,
        record_number: Option<u64>,
        line: &str,
    ) -> Result<RootObject, OwnershipFailure> {
        let parsed = JsonParser::new(
            line.as_bytes(),
            self.limits.max_parse_depth,
            self.limits.max_id_bytes,
        )
        .parse_root();
        {
            let usage = self.input_usage_mut(input);
            usage.max_parse_depth_observed = usage
                .max_parse_depth_observed
                .max(parsed.observation.max_depth);
            usage.max_id_bytes_observed = usage
                .max_id_bytes_observed
                .max(parsed.observation.max_id_bytes);
        }
        match parsed.result {
            Ok(root) => Ok(root),
            Err(JsonProblem::Depth { column, observed }) => {
                let mut location = self.location(input).at_line(line_number).at_column(column);
                if let Some(record_number) = record_number {
                    location = location.at_record(record_number);
                }
                Err(self.failure(
                    OwnershipFailureKind::ResourceExhausted {
                        resource: OwnershipResource::ParseDepth,
                        limit: self.limits.max_parse_depth,
                        observed,
                    },
                    location,
                ))
            }
            Err(JsonProblem::IdBytes { column, observed }) => {
                let mut location = self.location(input).at_line(line_number).at_column(column);
                if let Some(record_number) = record_number {
                    location = location.at_record(record_number);
                }
                Err(self.failure(
                    OwnershipFailureKind::ResourceExhausted {
                        resource: OwnershipResource::IdBytes,
                        limit: self.limits.max_id_bytes,
                        observed,
                    },
                    location,
                ))
            }
            Err(JsonProblem::Syntax { column, reason }) => {
                let mut location = self.location(input).at_line(line_number).at_column(column);
                if let Some(record_number) = record_number {
                    location = location.at_record(record_number);
                }
                Err(self.failure(OwnershipFailureKind::Malformed { reason }, location))
            }
        }
    }

    fn parse_manifest(&mut self, bytes: &[u8]) -> Result<ParsedManifest, OwnershipFailure> {
        let input = OwnershipInput::Manifest;
        if bytes.is_empty() {
            return Err(self.failure(OwnershipFailureKind::Empty, self.location(input)));
        }
        let mut lines = PhysicalLines::new(bytes);
        let header_line = self.next_line(input, &mut lines, 1)?;
        let header_text = self.line_utf8(input, 1, None, header_line)?;
        let _root = self.parse_json_object(input, 1, None, header_text)?;
        let header = self.parse_header(header_text)?;

        let mut ids = BTreeSet::new();
        let mut previous: Option<String> = None;
        let mut record_number = 0_u64;
        for raw_line in lines {
            let line_number = record_number.saturating_add(2);
            self.observe_line(input, line_number, raw_line.bytes)?;
            record_number = record_number.saturating_add(1);
            self.observe_record(input, line_number, record_number)?;
            let line = self.validate_line(input, line_number, raw_line)?;
            let text = self.line_utf8(input, line_number, Some(record_number), line)?;
            let id = self.parse_id_record(input, line_number, record_number, text, true)?;
            if !ids.insert(id.clone()) {
                return Err(self.failure(
                    OwnershipFailureKind::DuplicateId { id },
                    self.location(input)
                        .at_line(line_number)
                        .at_record(record_number),
                ));
            }
            if previous.as_ref().is_some_and(|previous| previous >= &id) {
                return Err(self.failure(
                    OwnershipFailureKind::Noncanonical {
                        reason: NoncanonicalReason::RecordOrder,
                    },
                    self.location(input)
                        .at_line(line_number)
                        .at_record(record_number),
                ));
            }
            previous = Some(id);
        }
        if ids.is_empty() {
            return Err(self.failure(OwnershipFailureKind::Empty, self.location(input)));
        }

        let actual_count = ids.len() as u64;
        if header.record_count != actual_count {
            return Err(self.failure(
                OwnershipFailureKind::StaleBinding {
                    reason: StaleBindingReason::ManifestRecordCount,
                },
                self.location(input),
            ));
        }
        let projection_digest = projection_digest(&ids);
        // ubs:ignore — public content-integrity digests, not authentication secrets.
        if header.projection_digest != projection_digest {
            return Err(self.failure(
                OwnershipFailureKind::StaleBinding {
                    reason: StaleBindingReason::ManifestProjectionDigest,
                },
                self.location(input),
            ));
        }
        Ok(ParsedManifest {
            ids,
            projection_digest,
            record_count: actual_count,
        })
    }

    fn parse_source(&mut self, bytes: &[u8]) -> Result<BTreeSet<String>, OwnershipFailure> {
        let input = OwnershipInput::Source;
        if bytes.is_empty() {
            return Err(self.failure(OwnershipFailureKind::Empty, self.location(input)));
        }
        let lines = PhysicalLines::new(bytes);
        let mut ids = BTreeSet::new();
        let mut record_number = 0_u64;
        for raw_line in lines {
            let line_number = record_number.saturating_add(1);
            self.observe_line(input, line_number, raw_line.bytes)?;
            record_number = record_number.saturating_add(1);
            self.observe_record(input, line_number, record_number)?;
            let line = self.validate_line(input, line_number, raw_line)?;
            let text = self.line_utf8(input, line_number, Some(record_number), line)?;
            let id = self.parse_id_record(input, line_number, record_number, text, false)?;
            if !ids.insert(id.clone()) {
                return Err(self.failure(
                    OwnershipFailureKind::DuplicateId { id },
                    self.location(input)
                        .at_line(line_number)
                        .at_record(record_number),
                ));
            }
        }
        if ids.is_empty() {
            return Err(self.failure(OwnershipFailureKind::Empty, self.location(input)));
        }
        Ok(ids)
    }

    fn next_line<'b>(
        &mut self,
        input: OwnershipInput,
        lines: &mut PhysicalLines<'b>,
        line_number: u64,
    ) -> Result<&'b [u8], OwnershipFailure> {
        let raw = lines
            .next()
            .expect("the caller established that the input is nonempty");
        self.observe_line(input, line_number, raw.bytes)?;
        self.validate_line(input, line_number, raw)
    }

    fn validate_line<'b>(
        &self,
        input: OwnershipInput,
        line_number: u64,
        raw: PhysicalLine<'b>,
    ) -> Result<&'b [u8], OwnershipFailure> {
        if !raw.terminated {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::MissingFinalLf,
                },
                self.location(input).at_line(line_number),
            ));
        }
        if raw.bytes.is_empty() {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::BlankLine,
                },
                self.location(input).at_line(line_number),
            ));
        }
        // ubs:ignore — public parser delimiter, not secret data.
        if raw.bytes.last() == Some(&b'\r') {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::CrLf,
                },
                self.location(input).at_line(line_number),
            ));
        }
        Ok(raw.bytes)
    }

    fn line_utf8<'b>(
        &self,
        input: OwnershipInput,
        line_number: u64,
        record_number: Option<u64>,
        line: &'b [u8],
    ) -> Result<&'b str, OwnershipFailure> {
        match str::from_utf8(line) {
            Ok(line) => Ok(line),
            Err(error) => {
                let mut location = self
                    .location(input)
                    .at_line(line_number)
                    .at_column(error.valid_up_to() as u64 + 1);
                if let Some(record_number) = record_number {
                    location = location.at_record(record_number);
                }
                Err(self.failure(
                    OwnershipFailureKind::Malformed {
                        reason: MalformedReason::InvalidUtf8,
                    },
                    location,
                ))
            }
        }
    }

    fn parse_header(&self, line: &str) -> Result<ManifestHeader, OwnershipFailure> {
        const PREFIX: &str = concat!(
            "{\"schema\":\"fln.kernel-contract-ownership/1\",",
            "\"source\":\".beads/issues.jsonl\",",
            "\"projection\":\"sorted-canonical-issue-ids-v1\",",
            "\"hash_algorithm\":\"fln-domain-registry-v1\",",
            "\"hash_domain\":\"fln 2026 domain fixture/1\",",
            "\"hash_preimage\":\"",
            "fln.kernel-contract-ownership.ids/1+nul+u64le-length-prefixed-utf8\",",
            "\"record_count\":"
        );
        const HASH_MARKER: &str = ",\"projection_hash\":\"";
        let Some(rest) = line.strip_prefix(PREFIX) else {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::Header,
                },
                self.location(OwnershipInput::Manifest).at_line(1),
            ));
        };
        let Some((count_text, digest_text)) = rest.split_once(HASH_MARKER) else {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::Header,
                },
                self.location(OwnershipInput::Manifest).at_line(1),
            ));
        };
        let Some(digest_text) = digest_text.strip_suffix("\"}") else {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::Header,
                },
                self.location(OwnershipInput::Manifest).at_line(1),
            ));
        };
        if count_text.is_empty()
            || (count_text.len() > 1 && count_text.starts_with('0'))
            || !count_text.bytes().all(|byte| byte.is_ascii_digit())
        {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::Header,
                },
                self.location(OwnershipInput::Manifest).at_line(1),
            ));
        }
        let record_count = match count_text.parse::<u64>() {
            Ok(count) => count,
            Err(_) => {
                return Err(self.failure(
                    OwnershipFailureKind::Malformed {
                        reason: MalformedReason::NumericOverflow,
                    },
                    self.location(OwnershipInput::Manifest).at_line(1),
                ));
            }
        };
        let projection_digest = match parse_digest(digest_text) {
            Ok(digest) => digest,
            Err(DigestProblem::Uppercase) => {
                return Err(self.failure(
                    OwnershipFailureKind::Noncanonical {
                        reason: NoncanonicalReason::Header,
                    },
                    self.location(OwnershipInput::Manifest).at_line(1),
                ));
            }
            Err(DigestProblem::Malformed) => {
                return Err(self.failure(
                    OwnershipFailureKind::Malformed {
                        reason: MalformedReason::InvalidDigest,
                    },
                    self.location(OwnershipInput::Manifest).at_line(1),
                ));
            }
        };
        Ok(ManifestHeader {
            record_count,
            projection_digest,
        })
    }

    fn parse_id_record(
        &mut self,
        input: OwnershipInput,
        line_number: u64,
        record_number: u64,
        line: &str,
        strict_manifest_record: bool,
    ) -> Result<String, OwnershipFailure> {
        let root = self.parse_json_object(input, line_number, Some(record_number), line)?;
        if let Some(first_id) = &root.first_id_value {
            self.observe_id(
                input,
                line_number,
                record_number,
                first_id.value.len() as u64,
            )?;
        }
        if root.id_occurrences > 1 {
            return Err(self.failure(
                OwnershipFailureKind::DuplicateId {
                    id: root
                        .first_id_value
                        .as_ref()
                        .map(|value| value.value.clone())
                        .unwrap_or_else(|| "<id-field>".to_string()),
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        }
        if root.id_occurrences == 0 {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::IdMissing,
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        }
        // ubs:ignore — public JSON field name, not secret data.
        if root.first_key.as_ref().map(|key| key.value.as_str()) != Some("id") {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::IdNotFirst,
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        }
        let first_key = root.first_key.as_ref().expect("the root has an id key");
        let Some(first_id) = root.first_id_value else {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::SourceRecord,
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        };
        if first_key.escaped || first_id.escaped {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::EscapedId,
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        }
        if first_id.value.is_empty() || !first_id.value.bytes().all(is_canonical_id_byte) {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::InvalidId,
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        }

        let expected_prefix_len = CANONICAL_ID_PREFIX.len() + first_id.value.len();
        let bytes = line.as_bytes();
        let canonical_prefix = bytes.starts_with(CANONICAL_ID_PREFIX)
            && bytes.get(CANONICAL_ID_PREFIX.len()..expected_prefix_len)
                == Some(first_id.value.as_bytes())
            && bytes.get(expected_prefix_len) == Some(&b'"'); // ubs:ignore — public parser delimiter, not secret data.
        if !canonical_prefix {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: if strict_manifest_record {
                        NoncanonicalReason::ManifestRecord
                    } else {
                        NoncanonicalReason::SourceRecord
                    },
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        }
        let after_quote = expected_prefix_len + 1;
        if strict_manifest_record {
            // ubs:ignore — public JSON syntax, not secret data.
            if bytes.get(after_quote..) != Some(&b"}"[..]) {
                return Err(self.failure(
                    OwnershipFailureKind::Noncanonical {
                        reason: NoncanonicalReason::ManifestRecord,
                    },
                    self.location(input)
                        .at_line(line_number)
                        .at_record(record_number),
                ));
            }
        } else if !matches!(bytes.get(after_quote), Some(b'}' | b','))
            // ubs:ignore — public parser delimiter, not secret data.
            || bytes.last() != Some(&b'}')
        {
            return Err(self.failure(
                OwnershipFailureKind::Noncanonical {
                    reason: NoncanonicalReason::SourceRecord,
                },
                self.location(input)
                    .at_line(line_number)
                    .at_record(record_number),
            ));
        }
        Ok(first_id.value)
    }
}

/// Load, bind, and atomically validate kernel-contract ownership evidence.
///
/// `root` and its two fixed evidence subdirectories are trust-bearing inputs and
/// must not be mutated concurrently. The loader rejects symlinked roots, parents,
/// and final components, compares opened file identity, and rechecks identity and
/// length after reading. Portable `std` APIs cannot exclude a same-inode,
/// same-length write that races the read, so callers must provide an immutable
/// checkout or otherwise serialize writers for the duration of this call.
pub fn load_kernel_contract_ownership(
    root: &Path,
    required_owners: &BTreeSet<String>,
    source_mode: OwnershipSourceMode,
    limits: OwnershipLimits,
) -> Result<OwnershipEvidence, OwnershipFailure> {
    let required_count = u64::try_from(required_owners.len()).unwrap_or(u64::MAX);
    let mut loader = Loader::new(root, limits, required_count);

    let manifest_bytes = loader.read_required(OwnershipInput::Manifest)?;
    let parsed_manifest = loader.parse_manifest(&manifest_bytes)?;
    let manifest_digest = manifest_digest(&manifest_bytes);
    let binding = OwnershipBinding {
        manifest_digest,
        projection_digest: parsed_manifest.projection_digest,
        record_count: parsed_manifest.record_count,
    };

    if let OwnershipSourceMode::ManifestOnly(expected) = source_mode {
        // ubs:ignore — public content-integrity digests, not authentication secrets.
        if expected.manifest_digest != binding.manifest_digest {
            return Err(loader.failure(
                OwnershipFailureKind::StaleBinding {
                    reason: StaleBindingReason::ExpectedManifestDigest,
                },
                loader.location(OwnershipInput::Manifest),
            ));
        }
        // ubs:ignore — public content-integrity digests, not authentication secrets.
        if expected.projection_digest != binding.projection_digest {
            return Err(loader.failure(
                OwnershipFailureKind::StaleBinding {
                    reason: StaleBindingReason::ExpectedProjectionDigest,
                },
                loader.location(OwnershipInput::Manifest),
            ));
        }
    }

    match loader.read_file(OwnershipInput::Source)? {
        Some(source_bytes) => {
            let source_ids = loader.parse_source(&source_bytes)?;
            if source_ids != parsed_manifest.ids {
                return Err(loader.failure(
                    OwnershipFailureKind::StaleBinding {
                        reason: StaleBindingReason::SourceProjection,
                    },
                    loader.location(OwnershipInput::Source),
                ));
            }
            loader.usage.source_state = OwnershipSourceState::PresentVerified;
        }
        None => match source_mode {
            OwnershipSourceMode::RequireSource => {
                loader.usage.source_state = OwnershipSourceState::Absent;
                return Err(loader.failure(
                    OwnershipFailureKind::Missing,
                    loader.location(OwnershipInput::Source),
                ));
            }
            OwnershipSourceMode::ManifestOnly(_) => {
                loader.usage.source_state = OwnershipSourceState::Absent;
            }
        },
    }

    if let Some(owner) = required_owners
        .iter()
        .find(|owner| !parsed_manifest.ids.contains(*owner))
    {
        return Err(loader.phantom_failure(owner.clone(), binding));
    }

    Ok(OwnershipEvidence {
        owners: parsed_manifest.ids,
        binding,
        usage: loader.usage,
    })
}

fn is_canonical_id_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'-' | b'.')
}

fn projection_digest(ids: &BTreeSet<String>) -> Digest {
    let mut hasher = DomainHasher::new(Domain::Fixture);
    hasher.update(PROJECTION_HASH_TAG);
    hasher.update(&[0]);
    for id in ids {
        hasher.update(&(id.len() as u64).to_le_bytes());
        hasher.update(id.as_bytes());
    }
    hasher.finalize()
}

fn manifest_digest(bytes: &[u8]) -> Digest {
    let mut hasher = DomainHasher::new(Domain::Fixture);
    hasher.update(MANIFEST_HASH_TAG);
    hasher.update(&[0]);
    hasher.update(&(bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
    hasher.finalize()
}

struct ManifestHeader {
    record_count: u64,
    projection_digest: Digest,
}

struct ParsedManifest {
    ids: BTreeSet<String>,
    projection_digest: Digest,
    record_count: u64,
}

enum DigestProblem {
    Uppercase,
    Malformed,
}

fn parse_digest(text: &str) -> Result<Digest, DigestProblem> {
    if text.len() != 64 {
        return Err(DigestProblem::Malformed);
    }
    if text.bytes().any(|byte| !byte.is_ascii_hexdigit()) {
        return Err(DigestProblem::Malformed);
    }
    if text.bytes().any(|byte| matches!(byte, b'A'..=b'F')) {
        return Err(DigestProblem::Uppercase);
    }
    let mut bytes = [0_u8; 32];
    let (pairs, remainder) = text.as_bytes().as_chunks::<2>();
    debug_assert!(remainder.is_empty());
    for (index, pair) in pairs.iter().enumerate() {
        let high = hex_nibble(pair[0]).ok_or(DigestProblem::Malformed)?;
        let low = hex_nibble(pair[1]).ok_or(DigestProblem::Malformed)?;
        bytes[index] = (high << 4) | low;
    }
    Ok(Digest(bytes))
}

fn hex_nibble(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        _ => None,
    }
}

struct PhysicalLine<'a> {
    bytes: &'a [u8],
    terminated: bool,
}

struct PhysicalLines<'a> {
    bytes: &'a [u8],
    cursor: usize,
}

impl<'a> PhysicalLines<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, cursor: 0 }
    }
}

impl<'a> Iterator for PhysicalLines<'a> {
    type Item = PhysicalLine<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.cursor >= self.bytes.len() {
            return None;
        }
        let start = self.cursor;
        // ubs:ignore — public parser delimiter, not secret data.
        if let Some(offset) = self.bytes[start..].iter().position(|byte| *byte == b'\n') {
            let end = start + offset;
            self.cursor = end + 1;
            Some(PhysicalLine {
                bytes: &self.bytes[start..end],
                terminated: true,
            })
        } else {
            self.cursor = self.bytes.len();
            Some(PhysicalLine {
                bytes: &self.bytes[start..],
                terminated: false,
            })
        }
    }
}

#[derive(Debug)]
struct DecodedString {
    value: String,
    escaped: bool,
}

#[derive(Debug)]
struct RootObject {
    first_key: Option<DecodedString>,
    first_id_value: Option<DecodedString>,
    id_occurrences: u64,
}

enum JsonProblem {
    Depth {
        column: u64,
        observed: u64,
    },
    IdBytes {
        column: u64,
        observed: u64,
    },
    Syntax {
        column: u64,
        reason: MalformedReason,
    },
}

struct JsonObservation {
    max_depth: u64,
    max_id_bytes: u64,
}

struct JsonParse {
    result: Result<RootObject, JsonProblem>,
    observation: JsonObservation,
}

struct JsonParser<'a> {
    bytes: &'a [u8],
    cursor: usize,
    depth_limit: u64,
    id_limit: u64,
    max_depth: u64,
    max_id_bytes: u64,
}

impl<'a> JsonParser<'a> {
    fn new(bytes: &'a [u8], depth_limit: u64, id_limit: u64) -> Self {
        Self {
            bytes,
            cursor: 0,
            depth_limit,
            id_limit,
            max_depth: 0,
            max_id_bytes: 0,
        }
    }

    fn parse_root(mut self) -> JsonParse {
        let result = self.parse_root_inner();
        JsonParse {
            result,
            observation: JsonObservation {
                max_depth: self.max_depth,
                max_id_bytes: self.max_id_bytes,
            },
        }
    }

    fn parse_root_inner(&mut self) -> Result<RootObject, JsonProblem> {
        self.skip_space();
        if self.peek() != Some(b'{') {
            return Err(self.syntax(MalformedReason::InvalidJson));
        }
        let root = self.parse_root_object(1)?;
        self.skip_space();
        if self.cursor != self.bytes.len() {
            return Err(self.syntax(MalformedReason::InvalidJson));
        }
        Ok(root)
    }

    fn parse_root_object(&mut self, depth: u64) -> Result<RootObject, JsonProblem> {
        self.enter_depth(depth)?;
        self.expect(b'{')?;
        self.skip_space();
        let mut root = RootObject {
            first_key: None,
            first_id_value: None,
            id_occurrences: 0,
        };
        if self.take(b'}') {
            return Ok(root);
        }
        let mut member_index = 0_u64;
        loop {
            let key = self.parse_string(true)?.expect("captured key");
            let is_id = key.value == "id"; // ubs:ignore — public JSON field name, not secret data.
            if is_id {
                root.id_occurrences = root.id_occurrences.saturating_add(1);
            }
            self.skip_space();
            self.expect(b':')?;
            self.skip_space();
            if member_index == 0 {
                if self.peek() == Some(b'"') {
                    let value = self
                        .parse_string_with_limit(true, is_id.then_some(self.id_limit))?
                        .expect("captured string");
                    if is_id {
                        root.first_id_value = Some(value);
                    }
                } else {
                    self.parse_value(depth)?;
                }
                root.first_key = Some(key);
            } else {
                self.parse_value(depth)?;
            }
            member_index = member_index.saturating_add(1);
            self.skip_space();
            if self.take(b'}') {
                return Ok(root);
            }
            self.expect(b',')?;
            self.skip_space();
        }
    }

    fn parse_value(&mut self, parent_depth: u64) -> Result<(), JsonProblem> {
        self.skip_space();
        match self.peek() {
            Some(b'{') => self.parse_object(parent_depth.saturating_add(1)),
            Some(b'[') => self.parse_array(parent_depth.saturating_add(1)),
            Some(b'"') => {
                self.parse_string(false)?;
                Ok(())
            }
            Some(b't') => self.parse_literal(b"true"),
            Some(b'f') => self.parse_literal(b"false"),
            Some(b'n') => self.parse_literal(b"null"),
            Some(b'-' | b'0'..=b'9') => self.parse_number(),
            _ => Err(self.syntax(MalformedReason::InvalidJson)),
        }
    }

    fn parse_object(&mut self, depth: u64) -> Result<(), JsonProblem> {
        self.enter_depth(depth)?;
        self.expect(b'{')?;
        self.skip_space();
        if self.take(b'}') {
            return Ok(());
        }
        loop {
            self.parse_string(false)?;
            self.skip_space();
            self.expect(b':')?;
            self.parse_value(depth)?;
            self.skip_space();
            if self.take(b'}') {
                return Ok(());
            }
            self.expect(b',')?;
            self.skip_space();
        }
    }

    fn parse_array(&mut self, depth: u64) -> Result<(), JsonProblem> {
        self.enter_depth(depth)?;
        self.expect(b'[')?;
        self.skip_space();
        if self.take(b']') {
            return Ok(());
        }
        loop {
            self.parse_value(depth)?;
            self.skip_space();
            if self.take(b']') {
                return Ok(());
            }
            self.expect(b',')?;
            self.skip_space();
        }
    }

    fn parse_string(&mut self, capture: bool) -> Result<Option<DecodedString>, JsonProblem> {
        self.parse_string_with_limit(capture, None)
    }

    fn parse_string_with_limit(
        &mut self,
        capture: bool,
        decoded_limit: Option<u64>,
    ) -> Result<Option<DecodedString>, JsonProblem> {
        self.expect(b'"')?;
        let mut decoded = capture.then(Vec::new);
        let mut escaped = false;
        loop {
            let Some(byte) = self.peek() else {
                return Err(self.syntax(MalformedReason::InvalidJson));
            };
            match byte {
                b'"' => {
                    self.cursor += 1;
                    let value = match decoded {
                        Some(bytes) => String::from_utf8(bytes)
                            .map_err(|_| self.syntax(MalformedReason::InvalidUtf8))?,
                        None => return Ok(None),
                    };
                    return Ok(Some(DecodedString { value, escaped }));
                }
                0..=31 => return Err(self.syntax(MalformedReason::InvalidJson)),
                b'\\' => {
                    escaped = true;
                    self.cursor += 1;
                    let Some(escape) = self.peek() else {
                        return Err(self.syntax(MalformedReason::InvalidJson));
                    };
                    self.cursor += 1;
                    match escape {
                        b'"' | b'\\' | b'/' => {
                            self.push_decoded(&mut decoded, &[escape], decoded_limit)?
                        }
                        b'b' => self.push_decoded(&mut decoded, &[0x08], decoded_limit)?,
                        b'f' => self.push_decoded(&mut decoded, &[0x0c], decoded_limit)?,
                        b'n' => self.push_decoded(&mut decoded, b"\n", decoded_limit)?,
                        b'r' => self.push_decoded(&mut decoded, b"\r", decoded_limit)?,
                        b't' => self.push_decoded(&mut decoded, b"\t", decoded_limit)?,
                        b'u' => {
                            let scalar = self.parse_unicode_escape()?;
                            let mut utf8 = [0_u8; 4];
                            self.push_decoded(
                                &mut decoded,
                                scalar.encode_utf8(&mut utf8).as_bytes(),
                                decoded_limit,
                            )?;
                        }
                        _ => return Err(self.syntax(MalformedReason::InvalidJson)),
                    }
                }
                _ => {
                    self.cursor += 1;
                    self.push_decoded(&mut decoded, &[byte], decoded_limit)?;
                }
            }
        }
    }

    fn push_decoded(
        &mut self,
        output: &mut Option<Vec<u8>>,
        bytes: &[u8],
        decoded_limit: Option<u64>,
    ) -> Result<(), JsonProblem> {
        let Some(output) = output else {
            return Ok(());
        };
        output.extend_from_slice(bytes);
        let observed = output.len() as u64;
        if let Some(limit) = decoded_limit {
            self.max_id_bytes = self.max_id_bytes.max(observed);
            if observed > limit {
                return Err(JsonProblem::IdBytes {
                    column: self.column(),
                    observed,
                });
            }
        }
        Ok(())
    }

    fn parse_unicode_escape(&mut self) -> Result<char, JsonProblem> {
        let first = self.parse_hex_quad()?;
        let scalar = if (0xd800..=0xdbff).contains(&first) {
            let second_byte = self
                .cursor
                .checked_add(1)
                .and_then(|index| self.bytes.get(index));
            if self.peek() != Some(b'\\') || second_byte != Some(&b'u') {
                return Err(self.syntax(MalformedReason::InvalidUnicodeEscape));
            }
            self.cursor += 2;
            let second = self.parse_hex_quad()?;
            if !(0xdc00..=0xdfff).contains(&second) {
                return Err(self.syntax(MalformedReason::InvalidUnicodeEscape));
            }
            0x10000 + (((u32::from(first) - 0xd800) << 10) | (u32::from(second) - 0xdc00))
        } else if (0xdc00..=0xdfff).contains(&first) {
            return Err(self.syntax(MalformedReason::InvalidUnicodeEscape));
        } else {
            u32::from(first)
        };
        char::from_u32(scalar).ok_or_else(|| self.syntax(MalformedReason::InvalidUnicodeEscape))
    }

    fn parse_hex_quad(&mut self) -> Result<u16, JsonProblem> {
        let mut value = 0_u16;
        for _ in 0..4 {
            let Some(byte) = self.peek() else {
                return Err(self.syntax(MalformedReason::InvalidUnicodeEscape));
            };
            let digit = match byte {
                b'0'..=b'9' => u16::from(byte - b'0'),
                b'a'..=b'f' => u16::from(byte - b'a' + 10),
                b'A'..=b'F' => u16::from(byte - b'A' + 10),
                _ => return Err(self.syntax(MalformedReason::InvalidUnicodeEscape)),
            };
            value = (value << 4) | digit;
            self.cursor += 1;
        }
        Ok(value)
    }

    fn parse_literal(&mut self, literal: &[u8]) -> Result<(), JsonProblem> {
        let Some(end) = self.cursor.checked_add(literal.len()) else {
            return Err(self.syntax(MalformedReason::InvalidJson));
        };
        // ubs:ignore — public JSON syntax, not secret data.
        if self.bytes.get(self.cursor..end) != Some(literal) {
            return Err(self.syntax(MalformedReason::InvalidJson));
        }
        self.cursor = end;
        Ok(())
    }

    fn parse_number(&mut self) -> Result<(), JsonProblem> {
        self.take(b'-');
        match self.peek() {
            Some(b'0') => {
                self.cursor += 1;
                if matches!(self.peek(), Some(b'0'..=b'9')) {
                    return Err(self.syntax(MalformedReason::InvalidNumber));
                }
            }
            Some(b'1'..=b'9') => {
                self.cursor += 1;
                while matches!(self.peek(), Some(b'0'..=b'9')) {
                    self.cursor += 1;
                }
            }
            _ => return Err(self.syntax(MalformedReason::InvalidNumber)),
        }
        if self.take(b'.') {
            let start = self.cursor;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.cursor += 1;
            }
            if self.cursor == start {
                return Err(self.syntax(MalformedReason::InvalidNumber));
            }
        }
        if matches!(self.peek(), Some(b'e' | b'E')) {
            self.cursor += 1;
            if matches!(self.peek(), Some(b'+' | b'-')) {
                self.cursor += 1;
            }
            let start = self.cursor;
            while matches!(self.peek(), Some(b'0'..=b'9')) {
                self.cursor += 1;
            }
            if self.cursor == start {
                return Err(self.syntax(MalformedReason::InvalidNumber));
            }
        }
        Ok(())
    }

    fn enter_depth(&mut self, depth: u64) -> Result<(), JsonProblem> {
        self.max_depth = self.max_depth.max(depth);
        if depth > self.depth_limit {
            return Err(JsonProblem::Depth {
                column: self.column(),
                observed: depth,
            });
        }
        Ok(())
    }

    fn skip_space(&mut self) {
        while matches!(self.peek(), Some(b' ' | b'\n' | b'\r' | b'\t')) {
            self.cursor += 1;
        }
    }

    fn expect(&mut self, expected: u8) -> Result<(), JsonProblem> {
        if self.take(expected) {
            Ok(())
        } else {
            Err(self.syntax(MalformedReason::InvalidJson))
        }
    }

    fn take(&mut self, expected: u8) -> bool {
        if self.peek() == Some(expected) {
            self.cursor += 1;
            true
        } else {
            false
        }
    }

    fn peek(&self) -> Option<u8> {
        self.bytes.get(self.cursor).copied()
    }

    fn column(&self) -> u64 {
        self.cursor as u64 + 1
    }

    fn syntax(&self, reason: MalformedReason) -> JsonProblem {
        JsonProblem::Syntax {
            column: self.column(),
            reason,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::{self, OpenOptions};
    use std::io::Write;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_FIXTURE: AtomicU64 = AtomicU64::new(0);

    fn fixture_root(label: &str) -> PathBuf {
        loop {
            let serial = NEXT_FIXTURE.fetch_add(1, Ordering::Relaxed);
            let root = std::env::temp_dir().join(format!(
                "fln-ownership-{}-{serial}-{label}",
                std::process::id()
            ));
            let creation = fs::create_dir(&root);
            if creation
                .as_ref()
                .is_err_and(|error| error.kind() == io::ErrorKind::AlreadyExists)
            {
                continue;
            }
            creation.expect("create retained fixture root");
            fs::create_dir(root.join("ci")).expect("create retained ci fixture");
            fs::create_dir(root.join(".beads")).expect("create retained beads fixture");
            return root;
        }
    }

    fn set(values: &[&str]) -> BTreeSet<String> {
        values.iter().map(|value| (*value).to_string()).collect()
    }

    fn source_bytes(ids: &BTreeSet<String>) -> Vec<u8> {
        let mut bytes = Vec::new();
        for id in ids {
            bytes.extend_from_slice(b"{\"id\":\"");
            bytes.extend_from_slice(id.as_bytes());
            bytes.extend_from_slice(b"\"}\n");
        }
        bytes
    }

    fn manifest_bytes(ids: &BTreeSet<String>) -> Vec<u8> {
        let digest = projection_digest(ids);
        let mut bytes = format!(
            concat!(
                "{{\"schema\":\"{}\",",
                "\"source\":\"{}\",",
                "\"projection\":\"{}\",",
                "\"hash_algorithm\":\"{}\",",
                "\"hash_domain\":\"{}\",",
                "\"hash_preimage\":\"{}\",",
                "\"record_count\":{},",
                "\"projection_hash\":\"{}\"}}\n"
            ),
            MANIFEST_SCHEMA,
            SOURCE_RELATIVE_PATH,
            PROJECTION_SCHEMA,
            HASH_ALGORITHM,
            HASH_DOMAIN,
            PROJECTION_HASH_PREIMAGE,
            ids.len(),
            digest.to_hex()
        )
        .into_bytes();
        bytes.extend_from_slice(&source_bytes(ids));
        bytes
    }

    fn write_at(root: &Path, relative: &str, bytes: &[u8]) {
        let path = root.join(relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("create retained fixture parent");
        }
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .expect("create retained fixture without overwrite");
        file.write_all(bytes).expect("write retained fixture");
        file.flush().expect("flush retained fixture");
    }

    fn install(root: &Path, ids: &BTreeSet<String>, with_source: bool) -> Vec<u8> {
        let manifest = manifest_bytes(ids);
        write_at(root, MANIFEST_RELATIVE_PATH, &manifest);
        if with_source {
            write_at(root, SOURCE_RELATIVE_PATH, &source_bytes(ids));
        }
        manifest
    }

    fn expected(manifest: &[u8], ids: &BTreeSet<String>) -> ExpectedManifestBinding {
        ExpectedManifestBinding {
            manifest_digest: manifest_digest(manifest),
            projection_digest: projection_digest(ids),
        }
    }

    fn load_required(
        root: &Path,
        required: &BTreeSet<String>,
        limits: OwnershipLimits,
    ) -> Result<OwnershipEvidence, OwnershipFailure> {
        load_kernel_contract_ownership(root, required, OwnershipSourceMode::RequireSource, limits)
    }

    fn assert_class(
        result: Result<OwnershipEvidence, OwnershipFailure>,
        class: OwnershipFailureClass,
    ) -> OwnershipFailure {
        let error = result.expect_err("fixture must be refused");
        assert_eq!(error.class(), class);
        if class != OwnershipFailureClass::PhantomOwner {
            assert_eq!(error.binding(), None, "partial binding leaked on refusal");
        }
        error
    }

    fn flip(digest: Digest) -> Digest {
        let mut bytes = digest.0;
        bytes[0] ^= 1;
        Digest(bytes)
    }

    #[test]
    fn valid_present_source_matches_manifest_projection() {
        let root = fixture_root("valid-present");
        let ids = set(&["fln-a", "franken_lean-z6c"]);
        let manifest = install(&root, &ids, true);
        let evidence = load_required(
            &root,
            &set(&["franken_lean-z6c"]),
            OwnershipLimits::default(),
        )
        .expect("valid evidence");
        assert_eq!(evidence.owners(), &ids);
        assert_eq!(
            evidence.usage().source_state(),
            OwnershipSourceState::PresentVerified
        );
        assert_eq!(
            evidence.binding().manifest_digest(),
            manifest_digest(&manifest)
        );
        assert_eq!(
            evidence.binding().projection_digest(),
            projection_digest(&ids)
        );
        assert_eq!(evidence.binding().record_count(), 2);
    }

    #[test]
    fn verified_manifest_is_authoritative_only_with_explicit_exact_binding() {
        let root = fixture_root("manifest-only");
        let ids = set(&["fln-a"]);
        let manifest = install(&root, &ids, false);
        let evidence = load_kernel_contract_ownership(
            &root,
            &ids,
            OwnershipSourceMode::ManifestOnly(expected(&manifest, &ids)),
            OwnershipLimits::default(),
        )
        .expect("explicit exact binding permits absent source");
        assert_eq!(evidence.owners(), &ids);
        assert_eq!(
            evidence.usage().source_state(),
            OwnershipSourceState::Absent
        );
    }

    #[test]
    fn require_source_refuses_absence_and_manifest_is_always_required() {
        let ids = set(&["fln-a"]);

        let source_absent = fixture_root("source-absent");
        install(&source_absent, &ids, false);
        let error = assert_class(
            load_required(&source_absent, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::Missing,
        );
        assert_eq!(error.location().input(), OwnershipInput::Source);
        assert_eq!(error.usage().source_state(), OwnershipSourceState::Absent);

        let manifest_absent = fixture_root("manifest-absent");
        write_at(&manifest_absent, SOURCE_RELATIVE_PATH, &source_bytes(&ids));
        let error = assert_class(
            load_required(
                &manifest_absent,
                &BTreeSet::new(),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::Missing,
        );
        assert_eq!(error.location().input(), OwnershipInput::Manifest);
    }

    #[test]
    fn manifest_only_refuses_either_wrong_independent_digest() {
        let ids = set(&["fln-a"]);
        let root = fixture_root("wrong-expected");
        let manifest = install(&root, &ids, false);
        let exact = expected(&manifest, &ids);

        let error = assert_class(
            load_kernel_contract_ownership(
                &root,
                &BTreeSet::new(),
                OwnershipSourceMode::ManifestOnly(ExpectedManifestBinding {
                    manifest_digest: flip(exact.manifest_digest),
                    projection_digest: exact.projection_digest,
                }),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::StaleBinding,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::StaleBinding {
                reason: StaleBindingReason::ExpectedManifestDigest
            }
        ));

        let error = assert_class(
            load_kernel_contract_ownership(
                &root,
                &BTreeSet::new(),
                OwnershipSourceMode::ManifestOnly(ExpectedManifestBinding {
                    manifest_digest: exact.manifest_digest,
                    projection_digest: flip(exact.projection_digest),
                }),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::StaleBinding,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::StaleBinding {
                reason: StaleBindingReason::ExpectedProjectionDigest
            }
        ));
    }

    #[test]
    fn non_regular_manifest_and_source_are_unreadable() {
        let manifest_directory = fixture_root("manifest-directory");
        fs::create_dir_all(manifest_directory.join(MANIFEST_RELATIVE_PATH))
            .expect("create non-file manifest path");
        let error = assert_class(
            load_required(
                &manifest_directory,
                &BTreeSet::new(),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::Unreadable,
        );
        assert_eq!(error.location().input(), OwnershipInput::Manifest);

        let source_directory = fixture_root("source-directory");
        let ids = set(&["fln-a"]);
        install(&source_directory, &ids, false);
        fs::create_dir_all(source_directory.join(SOURCE_RELATIVE_PATH))
            .expect("create non-file source path");
        let error = assert_class(
            load_required(
                &source_directory,
                &BTreeSet::new(),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::Unreadable,
        );
        assert_eq!(error.location().input(), OwnershipInput::Source);
        assert_ne!(
            error.usage().source_state(),
            OwnershipSourceState::Absent,
            "an unreadable source must not be treated as absent"
        );
    }

    #[cfg(unix)]
    #[test]
    fn symlinked_manifest_and_source_are_unreadable() {
        use std::os::unix::fs::symlink;

        let ids = set(&["fln-a"]);
        let manifest_target_root = fixture_root("manifest-symlink");
        write_at(
            &manifest_target_root,
            "manifest-target.jsonl",
            &manifest_bytes(&ids),
        );
        symlink(
            manifest_target_root.join("manifest-target.jsonl"),
            manifest_target_root.join(MANIFEST_RELATIVE_PATH),
        )
        .expect("create retained manifest symlink");
        let error = assert_class(
            load_required(
                &manifest_target_root,
                &BTreeSet::new(),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::Unreadable,
        );
        assert_eq!(error.location().input(), OwnershipInput::Manifest);

        let source_target_root = fixture_root("source-symlink");
        install(&source_target_root, &ids, false);
        write_at(
            &source_target_root,
            "source-target.jsonl",
            &source_bytes(&ids),
        );
        symlink(
            source_target_root.join("source-target.jsonl"),
            source_target_root.join(SOURCE_RELATIVE_PATH),
        )
        .expect("create retained source symlink");
        let error = assert_class(
            load_required(
                &source_target_root,
                &BTreeSet::new(),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::Unreadable,
        );
        assert_eq!(error.location().input(), OwnershipInput::Source);
    }

    #[test]
    fn malformed_json_and_utf8_are_typed_without_panics() {
        let ids = set(&["fln-a"]);
        let cases: &[(&str, &[u8], MalformedReason)] = &[
            (
                "invalid-utf8",
                b"{\"id\":\"fln-\xff\"}\n",
                MalformedReason::InvalidUtf8,
            ),
            (
                "truncated",
                b"{\"id\":\"fln-a\"\n",
                MalformedReason::InvalidJson,
            ),
            (
                "bad-escape",
                b"{\"id\":\"fln-a\",\"x\":\"\\q\"}\n",
                MalformedReason::InvalidJson,
            ),
            (
                "lone-surrogate",
                b"{\"id\":\"fln-a\",\"x\":\"\\uD800\"}\n",
                MalformedReason::InvalidUnicodeEscape,
            ),
            (
                "bad-number-leading-zero",
                b"{\"id\":\"fln-a\",\"x\":01}\n",
                MalformedReason::InvalidNumber,
            ),
            (
                "bad-number-fraction",
                b"{\"id\":\"fln-a\",\"x\":1.}\n",
                MalformedReason::InvalidNumber,
            ),
            (
                "bad-number-exponent",
                b"{\"id\":\"fln-a\",\"x\":1e}\n",
                MalformedReason::InvalidNumber,
            ),
            (
                "trailing-garbage",
                b"{\"id\":\"fln-a\"}x\n",
                MalformedReason::InvalidJson,
            ),
        ];
        for (label, source, reason) in cases {
            let root = fixture_root(label);
            install(&root, &ids, false);
            write_at(&root, SOURCE_RELATIVE_PATH, source);
            let error = assert_class(
                load_required(&root, &BTreeSet::new(), OwnershipLimits::default()),
                OwnershipFailureClass::Malformed,
            );
            assert!(
                matches!(
                    error.kind(),
                    OwnershipFailureKind::Malformed { reason: actual } if actual == reason
                ),
                "wrong malformed reason for {label}: {error:?}"
            );
        }
    }

    #[test]
    fn valid_json_string_and_surrogate_edge_cases_parse() {
        let ids = set(&["fln-a"]);
        let root = fixture_root("valid-json-edges");
        install(&root, &ids, false);
        write_at(
            &root,
            SOURCE_RELATIVE_PATH,
            concat!(
                "{\"id\":\"fln-a\",",
                "\"braces\":\"{[,]}\",",
                "\"quote\":\"a\\\\\\\"b\",",
                "\"astral\":\"\\uD83D\\uDE00\"}\n"
            )
            .as_bytes(),
        );
        load_required(&root, &BTreeSet::new(), OwnershipLimits::default())
            .expect("valid escaped strings and surrogate pair");
    }

    #[test]
    fn empty_manifest_header_only_manifest_and_empty_source_are_distinct() {
        let ids = set(&["fln-a"]);

        let zero_manifest = fixture_root("zero-manifest");
        write_at(&zero_manifest, MANIFEST_RELATIVE_PATH, b"");
        assert_class(
            load_required(&zero_manifest, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::Empty,
        );

        let header_only = fixture_root("header-only");
        let empty_ids = BTreeSet::new();
        write_at(
            &header_only,
            MANIFEST_RELATIVE_PATH,
            &manifest_bytes(&empty_ids),
        );
        assert_class(
            load_required(&header_only, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::Empty,
        );

        let zero_source = fixture_root("zero-source");
        install(&zero_source, &ids, false);
        write_at(&zero_source, SOURCE_RELATIVE_PATH, b"");
        let error = assert_class(
            load_required(&zero_source, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::Empty,
        );
        assert_eq!(error.location().input(), OwnershipInput::Source);
    }

    #[test]
    fn duplicate_ids_in_manifest_source_and_one_object_are_typed() {
        let ids = set(&["fln-a", "fln-b"]);

        let duplicate_manifest = fixture_root("duplicate-manifest");
        let mut manifest = manifest_bytes(&ids);
        manifest.extend_from_slice(b"{\"id\":\"fln-a\"}\n");
        write_at(&duplicate_manifest, MANIFEST_RELATIVE_PATH, &manifest);
        assert_class(
            load_required(
                &duplicate_manifest,
                &BTreeSet::new(),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::DuplicateId,
        );

        let duplicate_source = fixture_root("duplicate-source");
        install(&duplicate_source, &ids, false);
        write_at(
            &duplicate_source,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"fln-a\"}\n{\"id\":\"fln-b\"}\n{\"id\":\"fln-a\"}\n",
        );
        assert_class(
            load_required(
                &duplicate_source,
                &BTreeSet::new(),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::DuplicateId,
        );

        let duplicate_field = fixture_root("duplicate-id-field");
        let one = set(&["fln-a"]);
        install(&duplicate_field, &one, false);
        write_at(
            &duplicate_field,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"fln-a\",\"\\u0069d\":\"fln-a\"}\n",
        );
        assert_class(
            load_required(
                &duplicate_field,
                &BTreeSet::new(),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::DuplicateId,
        );
    }

    #[test]
    fn valid_json_but_noncanonical_source_forms_are_rejected() {
        let ids = set(&["fln-a"]);
        let cases: &[(&str, &[u8], NoncanonicalReason)] = &[
            (
                "leading-space",
                b" {\"id\":\"fln-a\"}\n",
                NoncanonicalReason::SourceRecord,
            ),
            (
                "id-second",
                b"{\"x\":0,\"id\":\"fln-a\"}\n",
                NoncanonicalReason::IdNotFirst,
            ),
            (
                "escaped-id",
                b"{\"id\":\"fln-\\u0061\"}\n",
                NoncanonicalReason::EscapedId,
            ),
            (
                "invalid-id",
                b"{\"id\":\"not a bead\"}\n",
                NoncanonicalReason::InvalidId,
            ),
            (
                "outer-space",
                b"{\"id\":\"fln-a\"} \n",
                NoncanonicalReason::SourceRecord,
            ),
            ("crlf", b"{\"id\":\"fln-a\"}\r\n", NoncanonicalReason::CrLf),
            (
                "missing-final-lf",
                b"{\"id\":\"fln-a\"}",
                NoncanonicalReason::MissingFinalLf,
            ),
            ("blank-line", b"\n", NoncanonicalReason::BlankLine),
        ];
        for (label, source, reason) in cases {
            let root = fixture_root(label);
            install(&root, &ids, false);
            write_at(&root, SOURCE_RELATIVE_PATH, source);
            let error = assert_class(
                load_required(&root, &BTreeSet::new(), OwnershipLimits::default()),
                OwnershipFailureClass::Noncanonical,
            );
            assert!(
                matches!(
                    error.kind(),
                    OwnershipFailureKind::Noncanonical { reason: actual } if actual == reason
                ),
                "wrong noncanonical reason for {label}: {error:?}"
            );
        }
    }

    #[test]
    fn manifest_serialization_and_record_order_are_canonical() {
        let ids = set(&["fln-a", "fln-b"]);

        let reordered_header = fixture_root("reordered-header");
        let canonical = String::from_utf8(manifest_bytes(&ids)).expect("fixture utf8");
        let altered = canonical.replacen(
            "{\"schema\":\"fln.kernel-contract-ownership/1\",\"source\":",
            "{\"source\":",
            1,
        );
        write_at(
            &reordered_header,
            MANIFEST_RELATIVE_PATH,
            altered.as_bytes(),
        );
        assert_class(
            load_required(
                &reordered_header,
                &BTreeSet::new(),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::Noncanonical,
        );

        let row_extra = fixture_root("manifest-row-extra");
        let altered = canonical.replace("{\"id\":\"fln-a\"}", "{\"id\":\"fln-a\",\"extra\":true}");
        write_at(&row_extra, MANIFEST_RELATIVE_PATH, altered.as_bytes());
        assert_class(
            load_required(&row_extra, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::Noncanonical,
        );

        let descending = fixture_root("manifest-descending");
        let altered = canonical
            .replace("{\"id\":\"fln-a\"}\n{\"id\":\"fln-b\"}", "__ORDER__")
            .replace("__ORDER__", "{\"id\":\"fln-b\"}\n{\"id\":\"fln-a\"}");
        write_at(&descending, MANIFEST_RELATIVE_PATH, altered.as_bytes());
        let error = assert_class(
            load_required(&descending, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::Noncanonical,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::Noncanonical {
                reason: NoncanonicalReason::RecordOrder
            }
        ));
    }

    #[test]
    fn internal_manifest_count_and_projection_hash_mismatches_are_stale() {
        let ids = set(&["fln-a"]);
        let canonical = String::from_utf8(manifest_bytes(&ids)).expect("fixture utf8");

        let bad_count = fixture_root("stale-count");
        let altered = canonical.replace("\"record_count\":1", "\"record_count\":2");
        write_at(&bad_count, MANIFEST_RELATIVE_PATH, altered.as_bytes());
        let error = assert_class(
            load_required(&bad_count, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::StaleBinding,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::StaleBinding {
                reason: StaleBindingReason::ManifestRecordCount
            }
        ));

        let bad_hash = fixture_root("stale-hash");
        let digest = projection_digest(&ids).to_hex();
        let mut replacement = digest.clone().into_bytes();
        replacement[0] = if replacement[0] == b'0' { b'1' } else { b'0' }; // ubs:ignore — test-only public digest mutation, not secret data.
        let replacement = String::from_utf8(replacement).expect("ascii digest");
        let altered = canonical.replace(&digest, &replacement);
        write_at(&bad_hash, MANIFEST_RELATIVE_PATH, altered.as_bytes());
        let error = assert_class(
            load_required(&bad_hash, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::StaleBinding,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::StaleBinding {
                reason: StaleBindingReason::ManifestProjectionDigest
            }
        ));
    }

    #[test]
    fn present_source_must_equal_manifest_set_exactly_in_both_modes() {
        let ids = set(&["fln-a", "fln-b"]);
        let variants = [
            ("source-missing-id", set(&["fln-a"])),
            ("source-added-id", set(&["fln-a", "fln-b", "fln-c"])),
            ("source-replaced-id", set(&["fln-a", "fln-c"])),
        ];
        for (label, source_ids) in variants {
            let root = fixture_root(label);
            let manifest = install(&root, &ids, false);
            write_at(&root, SOURCE_RELATIVE_PATH, &source_bytes(&source_ids));
            let error = assert_class(
                load_kernel_contract_ownership(
                    &root,
                    &BTreeSet::new(),
                    OwnershipSourceMode::ManifestOnly(expected(&manifest, &ids)),
                    OwnershipLimits::default(),
                ),
                OwnershipFailureClass::StaleBinding,
            );
            assert!(matches!(
                error.kind(),
                OwnershipFailureKind::StaleBinding {
                    reason: StaleBindingReason::SourceProjection
                }
            ));
        }
    }

    #[test]
    fn source_projection_is_order_independent_but_still_rejects_duplicates() {
        let ids = set(&["fln-a", "fln-b"]);
        let root = fixture_root("source-order-independent");
        install(&root, &ids, false);
        write_at(
            &root,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"fln-b\",\"updated\":2}\n{\"id\":\"fln-a\",\"updated\":1}\n",
        );
        let evidence = load_required(&root, &BTreeSet::new(), OwnershipLimits::default())
            .expect("Beads append order does not change its sorted projection");
        assert_eq!(evidence.owners(), &ids);

        let duplicate = fixture_root("source-order-duplicate");
        install(&duplicate, &ids, false);
        write_at(
            &duplicate,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"fln-b\"}\n{\"id\":\"fln-a\"}\n{\"id\":\"fln-b\"}\n",
        );
        let error = assert_class(
            load_required(&duplicate, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::DuplicateId,
        );
        assert_eq!(error.location().input(), OwnershipInput::Source);
    }

    #[test]
    fn phantom_owner_is_atomic_and_retains_only_the_verified_binding() {
        let root = fixture_root("phantom");
        let ids = set(&["fln-a"]);
        install(&root, &ids, true);
        let error = assert_class(
            load_required(
                &root,
                &set(&["fln-a", "fln-phantom"]),
                OwnershipLimits::default(),
            ),
            OwnershipFailureClass::PhantomOwner,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::PhantomOwner { owner } if owner == "fln-phantom"
        ));
        let binding = error
            .binding()
            .expect("fully verified binding is retained for phantom owner");
        assert_eq!(binding.projection_digest(), projection_digest(&ids));
    }

    #[test]
    fn file_byte_limit_has_zero_exact_and_one_over_boundaries() {
        let ids = set(&["fln-a"]);
        let root = fixture_root("file-boundaries");
        let manifest = install(&root, &ids, true);
        let source = source_bytes(&ids);

        let mut limits = OwnershipLimits {
            max_file_bytes: 0,
            ..OwnershipLimits::default()
        };
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(
            &error,
            OwnershipResource::FileBytes,
            0,
            manifest.len() as u64,
        );

        limits.max_file_bytes = manifest.len().max(source.len()) as u64;
        load_required(&root, &BTreeSet::new(), limits).expect("exact file limit");

        limits.max_file_bytes = manifest.len() as u64 - 1;
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(
            &error,
            OwnershipResource::FileBytes,
            manifest.len() as u64 - 1,
            manifest.len() as u64,
        );
    }

    #[test]
    fn line_byte_limit_has_zero_exact_and_one_over_boundaries() {
        let ids = set(&["fln-a"]);
        let root = fixture_root("line-boundaries");
        let manifest = install(&root, &ids, true);
        let max_line = manifest
            .split(|byte| *byte == b'\n')
            .map(|line| line.len())
            .max()
            .expect("manifest line") as u64;

        let mut limits = OwnershipLimits {
            max_line_bytes: 0,
            ..OwnershipLimits::default()
        };
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(&error, OwnershipResource::LineBytes, 0, max_line);

        limits.max_line_bytes = max_line;
        load_required(&root, &BTreeSet::new(), limits).expect("exact line limit");

        limits.max_line_bytes = max_line - 1;
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(&error, OwnershipResource::LineBytes, max_line - 1, max_line);
    }

    #[test]
    fn record_limit_has_zero_exact_and_one_over_boundaries() {
        let ids = set(&["fln-a", "fln-b"]);
        let root = fixture_root("record-boundaries");
        install(&root, &ids, true);
        let mut limits = OwnershipLimits {
            max_records: 0,
            ..OwnershipLimits::default()
        };
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(&error, OwnershipResource::Records, 0, 1);

        limits.max_records = 2;
        load_required(&root, &BTreeSet::new(), limits).expect("exact record limit");

        limits.max_records = 1;
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(&error, OwnershipResource::Records, 1, 2);
    }

    #[test]
    fn id_byte_limit_has_zero_exact_and_one_over_boundaries() {
        let ids = set(&["abcd"]);
        let root = fixture_root("id-boundaries");
        install(&root, &ids, true);
        let mut limits = OwnershipLimits {
            max_id_bytes: 0,
            ..OwnershipLimits::default()
        };
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(&error, OwnershipResource::IdBytes, 0, 1);

        limits.max_id_bytes = 4;
        load_required(&root, &BTreeSet::new(), limits).expect("exact id limit");

        limits.max_id_bytes = 3;
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(&error, OwnershipResource::IdBytes, 3, 4);
    }

    #[test]
    fn parse_depth_limit_has_zero_exact_and_one_over_boundaries() {
        let ids = set(&["fln-a"]);
        let root = fixture_root("depth-boundaries");
        install(&root, &ids, false);
        write_at(
            &root,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"fln-a\",\"meta\":{\"items\":[]}}\n",
        );
        let mut limits = OwnershipLimits {
            max_parse_depth: 0,
            ..OwnershipLimits::default()
        };
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(&error, OwnershipResource::ParseDepth, 0, 1);

        limits.max_parse_depth = 3;
        load_required(&root, &BTreeSet::new(), limits).expect("exact depth limit");

        limits.max_parse_depth = 2;
        let error = assert_class(
            load_required(&root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_resource(&error, OwnershipResource::ParseDepth, 2, 3);
    }

    #[test]
    fn resource_refusal_precedes_later_syntax_or_duplicate_failures() {
        let ids = set(&["abcd"]);

        let line_root = fixture_root("line-before-syntax");
        install(&line_root, &ids, false);
        write_at(&line_root, SOURCE_RELATIVE_PATH, b"{not-json}\n");
        let line_limits = OwnershipLimits {
            max_line_bytes: 2,
            ..OwnershipLimits::default()
        };
        let error = assert_class(
            load_required(&line_root, &BTreeSet::new(), line_limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::ResourceExhausted {
                resource: OwnershipResource::LineBytes,
                ..
            }
        ));

        let duplicate_root = fixture_root("records-before-duplicate");
        let two = set(&["a", "b"]);
        install(&duplicate_root, &two, false);
        write_at(
            &duplicate_root,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"a\"}\n{\"id\":\"a\"}\n",
        );
        let record_limits = OwnershipLimits {
            max_records: 1,
            ..OwnershipLimits::default()
        };
        let error = assert_class(
            load_required(&duplicate_root, &BTreeSet::new(), record_limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::ResourceExhausted {
                resource: OwnershipResource::Records,
                ..
            }
        ));

        let id_root = fixture_root("id-before-noncanonical");
        install(&id_root, &ids, false);
        write_at(&id_root, SOURCE_RELATIVE_PATH, b"{\"id\":\"abcd \"}\n");
        let id_limits = OwnershipLimits {
            max_id_bytes: 4,
            ..OwnershipLimits::default()
        };
        let error = assert_class(
            load_required(&id_root, &BTreeSet::new(), id_limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::ResourceExhausted {
                resource: OwnershipResource::IdBytes,
                ..
            }
        ));

        let depth_root = fixture_root("depth-before-truncation");
        install(&depth_root, &set(&["a"]), false);
        write_at(
            &depth_root,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"a\",\"x\":{\"y\":{\"z\":\n",
        );
        let depth_limits = OwnershipLimits {
            max_parse_depth: 2,
            ..OwnershipLimits::default()
        };
        let error = assert_class(
            load_required(&depth_root, &BTreeSet::new(), depth_limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert!(matches!(
            error.kind(),
            OwnershipFailureKind::ResourceExhausted {
                resource: OwnershipResource::ParseDepth,
                ..
            }
        ));
    }

    #[test]
    fn bytewise_manifest_order_is_canonical_but_source_order_is_not_semantic() {
        let ids = set(&["a.10", "a.2"]);
        let valid_root = fixture_root("bytewise-order-valid");
        install(&valid_root, &ids, true);
        load_required(&valid_root, &BTreeSet::new(), OwnershipLimits::default())
            .expect("BTree byte order is canonical");

        let append_order_root = fixture_root("bytewise-source-append-order");
        install(&append_order_root, &ids, false);
        write_at(
            &append_order_root,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"a.2\"}\n{\"id\":\"a.10\"}\n",
        );
        let evidence = load_required(
            &append_order_root,
            &BTreeSet::new(),
            OwnershipLimits::default(),
        )
        .expect("source append order is canonicalized into a sorted set");
        assert_eq!(evidence.owners(), &ids);
    }

    #[test]
    fn refusal_does_not_mutate_last_good_evidence_and_restoration_recovers() {
        let ids = set(&["fln-a", "fln-b"]);
        let baseline_root = fixture_root("recovery-baseline");
        let baseline_manifest = install(&baseline_root, &ids, true);
        let baseline = load_required(&baseline_root, &set(&["fln-a"]), OwnershipLimits::default())
            .expect("baseline");

        let refused_root = fixture_root("recovery-refused");
        install(&refused_root, &ids, false);
        write_at(
            &refused_root,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"fln-a\"}\n{\"id\":\"fln-c\"}\n",
        );
        assert_class(
            load_required(&refused_root, &set(&["fln-a"]), OwnershipLimits::default()),
            OwnershipFailureClass::StaleBinding,
        );
        assert_eq!(baseline.owners(), &ids, "prior evidence remains immutable");
        assert_eq!(
            baseline.binding().manifest_digest(),
            manifest_digest(&baseline_manifest)
        );

        let recovered_root = fixture_root("recovery-restored");
        install(&recovered_root, &ids, true);
        let recovered = load_required(
            &recovered_root,
            &set(&["fln-a"]),
            OwnershipLimits::default(),
        )
        .expect("restored source recovers");
        assert_eq!(recovered.owners(), baseline.owners());
        assert_eq!(recovered.binding(), baseline.binding());
    }

    #[test]
    fn diagnostics_are_single_line_valid_utf8_and_bounded_at_every_cut() {
        let root = fixture_root("diagnostic-\u{1f642}");
        let ids = set(&["fln-a"]);
        install(&root, &ids, true);
        let required = set(&["owner-with-\n-control-\u{1f642}"]);
        for limit in [0, 1, 2, 7, 31, 64, 127] {
            let limits = OwnershipLimits {
                max_diagnostic_bytes: limit,
                ..OwnershipLimits::default()
            };
            let error = assert_class(
                load_required(&root, &required, limits),
                OwnershipFailureClass::PhantomOwner,
            );
            let diagnostic = error.diagnostic();
            assert!(diagnostic.len() <= limit);
            assert!(!diagnostic.contains('\n'));
            assert!(str::from_utf8(diagnostic.as_bytes()).is_ok());
            assert_eq!(error.class(), OwnershipFailureClass::PhantomOwner);
        }
    }

    #[test]
    fn manifest_and_projection_preimages_are_separate_and_length_delimited() {
        assert_eq!(
            Domain::Fixture.tag(),
            HASH_DOMAIN,
            "the checked-in manifest domain must equal the registered Fixture domain"
        );
        let first = set(&["a", "bc"]);
        let second = set(&["ab", "c"]);
        assert_eq!(
            projection_digest(&first).to_hex(),
            "92ec6f3c2c699843a122a64c98ceb0618aef584cca24e1bb75eb065117f2fbc6",
            "the independently frozen projection vector changed"
        );
        assert_ne!(
            projection_digest(&first),
            projection_digest(&second),
            "u64 length prefixes prevent concatenation ambiguity"
        );
        let first_manifest = manifest_bytes(&first);
        assert_eq!(
            manifest_digest(&first_manifest).to_hex(),
            "5f3b6f6f91dd4a6d2e611f4a833049d9fb33b0fe0d0f5f7cc4c84f4c090b2de4",
            "the independently frozen exact-manifest vector changed"
        );
        assert_ne!(
            manifest_digest(&first_manifest),
            projection_digest(&first),
            "separate tagged preimages prevent domain confusion"
        );
        let mut changed = first_manifest.clone();
        changed.push(b'\n');
        assert_ne!(
            manifest_digest(&first_manifest),
            manifest_digest(&changed),
            "the exact manifest bytes, including line endings, are bound"
        );
    }

    #[test]
    fn public_configuration_constructors_are_checked_and_stable() {
        let defaults = OwnershipLimits::default();
        assert_eq!(
            OwnershipLimits::try_new(
                defaults.max_file_bytes(),
                defaults.max_line_bytes(),
                defaults.max_records(),
                defaults.max_id_bytes(),
                defaults.max_parse_depth(),
                defaults.max_diagnostic_bytes(),
            ),
            Ok(defaults)
        );
        let over_depth = OwnershipLimits::try_new(
            defaults.max_file_bytes(),
            defaults.max_line_bytes(),
            defaults.max_records(),
            defaults.max_id_bytes(),
            ABSOLUTE_MAX_PARSE_DEPTH + 1,
            defaults.max_diagnostic_bytes(),
        )
        .expect_err("unbounded parser recursion must be rejected before I/O");
        assert_eq!(over_depth.field(), OwnershipLimitField::ParseDepth);
        assert_eq!(over_depth.requested(), ABSOLUTE_MAX_PARSE_DEPTH + 1);
        assert_eq!(over_depth.absolute_maximum(), ABSOLUTE_MAX_PARSE_DEPTH);

        let ids = set(&["a", "bc"]);
        let manifest = manifest_bytes(&ids);
        let binding = ExpectedManifestBinding::from_lower_hex(
            &manifest_digest(&manifest).to_hex(),
            &projection_digest(&ids).to_hex(),
        )
        .expect("canonical lowercase binding");
        assert_eq!(binding, expected(&manifest, &ids));
        let uppercase = ExpectedManifestBinding::from_lower_hex(
            &manifest_digest(&manifest).to_hex().to_uppercase(),
            &projection_digest(&ids).to_hex(),
        )
        .expect_err("uppercase digests are not canonical configuration");
        assert_eq!(uppercase.field(), OwnershipBindingField::ManifestDigest);
    }

    #[test]
    fn refusal_classifications_and_parser_observations_are_public_and_exact() {
        let root = fixture_root("observed-malformed-manifest");
        write_at(
            &root,
            MANIFEST_RELATIVE_PATH,
            b"{\"schema\": definitely-not-json}\n",
        );
        let malformed = assert_class(
            load_required(&root, &BTreeSet::new(), OwnershipLimits::default()),
            OwnershipFailureClass::Malformed,
        );
        assert_eq!(malformed.result_classification(), "malformed");
        assert_eq!(malformed.usage().manifest().max_parse_depth_observed(), 1);
        assert_eq!(malformed.usage().manifest().max_id_bytes_observed(), 0);
        assert_eq!(
            malformed.usage().source_state(),
            OwnershipSourceState::NotAttempted
        );

        let ids = set(&["fln-a"]);
        let depth_root = fixture_root("observed-source-depth");
        install(&depth_root, &ids, false);
        write_at(
            &depth_root,
            SOURCE_RELATIVE_PATH,
            b"{\"id\":\"fln-a\",\"nested\":{}}\n",
        );
        let limits = OwnershipLimits {
            max_parse_depth: 1,
            ..OwnershipLimits::default()
        };
        let depth = assert_class(
            load_required(&depth_root, &BTreeSet::new(), limits),
            OwnershipFailureClass::ResourceExhausted,
        );
        assert_eq!(
            depth.result_classification(),
            "resource-exhausted/parse-depth"
        );
        assert_eq!(depth.usage().source_state(), OwnershipSourceState::Present);
        assert_eq!(depth.usage().source().max_parse_depth_observed(), 2);
        assert_eq!(depth.usage().source().max_id_bytes_observed(), 5);
    }

    fn assert_resource(
        error: &OwnershipFailure,
        resource: OwnershipResource,
        limit: u64,
        observed: u64,
    ) {
        assert!(
            matches!(
                error.kind(),
                OwnershipFailureKind::ResourceExhausted {
                    resource: actual_resource,
                    limit: actual_limit,
                    observed: actual_observed,
                } if *actual_resource == resource
                    && *actual_limit == limit
                    && *actual_observed == observed
            ),
            "wrong resource refusal: {error:?}"
        );
    }
}
