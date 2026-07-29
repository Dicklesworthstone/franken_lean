//! The typed error taxonomy and diagnostic-projection values (plan D8 normative
//! taxonomy, risk R9; beads fln-rk6 and franken_lean-wlan).
//!
//! Errors cross crate boundaries as **typed, versioned values** — the fourteen
//! variants of [`ErrorValue`], defined once here, consumed everywhere. Panics are
//! invariant failures, never user diagnostics. This rank-zero crate owns values and
//! pure ordering/classification rules only. CLI, JSON, LSP, and library adapters live
//! in their frontend crates; each consumes the same [`ProjectionSnapshot`] so no
//! rendered string becomes a second error authority.
//!
//! Semantics anchors (vendor/lean4-src at the SUITE.lock pin):
//! * `MessageSeverity` — src/Lean/Message.lean:44-54 (`information`/`warning`/`error`);
//! * the CLI frame — `mkErrorStringWithPos`, Message.lean:31-42:
//!   `{file}:{line}:{col}{-endLine:endCol?}: {kind}({name})?: {msg}`;
//! * severity framing — `SerialMessage.toString`, Message.lean:608-620: `information`
//!   renders the body with NO positional frame; `warning`/`error` frame with their
//!   kind word; a caption prefixes `caption:\n`; a final newline is appended when
//!   missing.
//!
//! FL-INV-07 is structural here: [`ErrorValue::KernelInconclusive`] is a distinct
//! variant with no conversion path to or from [`ErrorValue::KernelRejection`], and
//! [`ErrorValue::is_rejection`]/[`ErrorValue::is_inconclusive`] never overlap.

use crate::name::Name;
use crate::outcome::{
    Authority, BoundedText, InconclusiveCause, InternalFault, Outcome, ResourceUsage,
};
use crate::pos::Position;

/// `MessageSeverity` (Message.lean:44-54).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Severity {
    Information,
    Warning,
    Error,
}

impl Severity {
    /// `MessageSeverity.toString` (Message.lean:48-51).
    pub fn as_str(self) -> &'static str {
        match self {
            Severity::Information => "information",
            Severity::Warning => "warning",
            Severity::Error => "error",
        }
    }

    /// Stable CGSE ordering rank. Severity is a projection coordinate, not an
    /// authority: this rank may order diagnostics but may never change an outcome.
    pub const fn order_rank(self) -> u8 {
        match self {
            Severity::Error => 0,
            Severity::Warning => 1,
            Severity::Information => 2,
        }
    }
}

/// Typed resource exhaustion (FL-INV-07): each reason is a value, never a hang and
/// never a rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ResourceReason {
    /// `maxHeartbeats` exhausted (thousand-unit option; effective ×1000).
    Heartbeats { consumed: u64, limit: u64 },
    /// `maxRecDepth` exhausted.
    RecursionDepth { limit: u64 },
    /// Cooperative cancellation observed.
    Cancelled,
    /// A declared memory budget was exhausted.
    Memory { limit_bytes: u64 },
    /// A **native budget over the size or work of a data structure** was exhausted
    /// (bead franken_lean-vui8).
    ///
    /// The four entries above all name a specific *upstream* condition —
    /// `maxHeartbeats`, `maxRecDepth`, cancellation, a declared memory budget. This one
    /// does not: it is a FrankenLean-owned budget over our own structures, and it is
    /// marked as one axis rather than scattered among the upstream option names so the
    /// taxonomy keeps saying what kind of thing each entry is. Which quantity was bounded
    /// is a *value* ([`StructuralUnit`]), not a comment, because consumers must act on it.
    ///
    /// **Deliberately carries no numbers.** `allowed` and `observed` live in
    /// `ResourceUsage`, and `Heartbeats` duplicating them there is a known wart this
    /// variant does not copy: one fact, one home.
    StructuralBudget { unit: StructuralUnit },
}

/// Which structural quantity a [`ResourceReason::StructuralBudget`] bounded.
///
/// Three units rather than one catch-all, because each answers a different question and
/// a consumer must do something different about it. That is the bar for a new unit: not
/// "it is a different number" but "a caller has to react differently".
///
/// * [`InputBytes`](StructuralUnit::InputBytes) — how much serialized input was consumed.
///   Hitting this while few values were produced means the input is padded, sparse, or
///   garbage; the retry raises a byte allowance.
/// * [`ProducedNodes`](StructuralUnit::ProducedNodes) — how much structure was actually
///   materialized. Hitting this on few bytes means a high expansion ratio — a
///   decompression bomb — and the retry raises a node allowance, or streams instead.
///   Deliberately a count of *work*, not of nesting: a depth cap would refuse
///   legitimately deep terms, which bead franken_lean-fnj forbids.
/// * [`ExpandedWeight`](StructuralUnit::ExpandedWeight) — the size of the tree a shared
///   DAG *denotes*, measured without building it.
///
/// The last is why `ProducedNodes` and `ExpandedWeight` are not one unit, which is the
/// distinction most likely to be collapsed by someone tidying up. Stored size and denoted
/// size differ by orders of magnitude on a shared DAG, and the correct reaction inverts:
/// exceeding `ProducedNodes` means "bigger than I allowed to materialize", where raising
/// the budget is a reasonable response; exceeding `ExpandedWeight` means "this small value
/// denotes something astronomical", where raising the budget is usually the wrong move
/// because the input is a DAG bomb. A single unit could not tell a caller which of those
/// two situations it is in.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StructuralUnit {
    /// Bytes consumed from a serialized input.
    InputBytes,
    /// Values materialized from it — nodes, entries, components.
    ProducedNodes,
    /// The denoted (fully expanded) tree size of a shared graph, computed without
    /// expanding it.
    ExpandedWeight,
}

impl StructuralUnit {
    /// The unit's own name, for renderers and structured logs.
    pub const fn as_str(self) -> &'static str {
        match self {
            StructuralUnit::InputBytes => "input bytes",
            StructuralUnit::ProducedNodes => "produced nodes",
            StructuralUnit::ExpandedWeight => "expanded weight",
        }
    }

    /// Every unit, for taxonomy-wide tests.
    pub const ALL: [StructuralUnit; 3] = [
        StructuralUnit::InputBytes,
        StructuralUnit::ProducedNodes,
        StructuralUnit::ExpandedWeight,
    ];
}

/// The D8 normative taxonomy, version 1. Closed: adding a variant is a reviewed
/// taxonomy revision that breaks every consumer until handled (no catch-all arms in
/// authoritative crates).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorValue {
    /// Vellum rejected the source text.
    SyntaxFailure { message: String },
    /// Macro expansion failed (hygiene, recursion, or user macro error).
    MacroFailure { macro_name: Name, message: String },
    /// Athanor could not elaborate the declaration.
    ElaborationFailure { message: String },
    /// Crucible rejected a declaration: a real verdict, with a stable class for
    /// cross-release comparison.
    KernelRejection {
        decl: Name,
        stable_error_class: String,
        message: String,
    },
    /// Crucible could not finish (FL-INV-07): never rendered as, cached as, or
    /// promoted to acceptance OR rejection.
    KernelInconclusive {
        decl: Name,
        resource: ResourceReason,
    },
    /// An artifact failed structural validation.
    ArtifactCorrupt { path: String, detail: String },
    /// An artifact was produced under a different epoch than expected.
    ArtifactEpochMismatch {
        path: String,
        expected_epoch: String,
        found_epoch: String,
    },
    /// The ABI membrane observed a contract violation.
    AbiViolation { symbol: String, detail: String },
    /// A capability-scoped operation was denied (sound-mode fail-closed).
    CapabilityDenied { capability: String, detail: String },
    /// A native plugin crashed; isolated, never silently repaired.
    PluginCrashed { plugin: String, detail: String },
    /// The build fabric failed a job.
    BuildFailure { job: String, detail: String },
    /// A wire-protocol message violated its schema.
    ProtocolFailure { detail: String },
    /// A deterministic replay diverged from its recording.
    ReplayDivergence { detail: String },
    /// An internal invariant failed: process-fatal in certified profiles; NEVER a
    /// user diagnostic.
    InternalInvariantViolation { invariant: String, detail: String },
}

impl ErrorValue {
    /// Stable class name, exhaustively matched — adding a variant breaks this (and
    /// every other consumer) until handled.
    pub fn class_name(&self) -> &'static str {
        match self {
            ErrorValue::SyntaxFailure { .. } => "SyntaxFailure",
            ErrorValue::MacroFailure { .. } => "MacroFailure",
            ErrorValue::ElaborationFailure { .. } => "ElaborationFailure",
            ErrorValue::KernelRejection { .. } => "KernelRejection",
            ErrorValue::KernelInconclusive { .. } => "KernelInconclusive",
            ErrorValue::ArtifactCorrupt { .. } => "ArtifactCorrupt",
            ErrorValue::ArtifactEpochMismatch { .. } => "ArtifactEpochMismatch",
            ErrorValue::AbiViolation { .. } => "AbiViolation",
            ErrorValue::CapabilityDenied { .. } => "CapabilityDenied",
            ErrorValue::PluginCrashed { .. } => "PluginCrashed",
            ErrorValue::BuildFailure { .. } => "BuildFailure",
            ErrorValue::ProtocolFailure { .. } => "ProtocolFailure",
            ErrorValue::ReplayDivergence { .. } => "ReplayDivergence",
            ErrorValue::InternalInvariantViolation { .. } => "InternalInvariantViolation",
        }
    }

    /// All fourteen class names, for registry-completeness tests.
    pub const CLASS_NAMES: [&'static str; 14] = [
        "SyntaxFailure",
        "MacroFailure",
        "ElaborationFailure",
        "KernelRejection",
        "KernelInconclusive",
        "ArtifactCorrupt",
        "ArtifactEpochMismatch",
        "AbiViolation",
        "CapabilityDenied",
        "PluginCrashed",
        "BuildFailure",
        "ProtocolFailure",
        "ReplayDivergence",
        "InternalInvariantViolation",
    ];

    /// A real negative verdict. Disjoint from [`ErrorValue::is_inconclusive`] by
    /// construction (FL-INV-07).
    pub fn is_rejection(&self) -> bool {
        matches!(self, ErrorValue::KernelRejection { .. })
    }

    /// Resource exhaustion / cancellation: not a rejection, not an acceptance.
    pub fn is_inconclusive(&self) -> bool {
        matches!(self, ErrorValue::KernelInconclusive { .. })
    }

    /// The message body the faithful frame carries. For structured variants this is
    /// the faithful projection; sound mode may render richer bodies (BN-02) but the
    /// positions and severities never change.
    pub fn faithful_body(&self) -> String {
        match self {
            ErrorValue::SyntaxFailure { message } | ErrorValue::ElaborationFailure { message } => {
                message.clone()
            }
            ErrorValue::MacroFailure { message, .. } => message.clone(),
            ErrorValue::KernelRejection { message, .. } => message.clone(),
            ErrorValue::KernelInconclusive { decl, resource } => match resource {
                ResourceReason::Heartbeats { .. } => format!(
                    "(deterministic) timeout at `{}`, maximum number of heartbeats has been reached",
                    decl.to_display_string()
                ),
                ResourceReason::RecursionDepth { .. } => {
                    crate::diag::MAX_REC_DEPTH_ERROR_MESSAGE.to_string()
                }
                ResourceReason::Cancelled => {
                    format!(
                        "elaboration of `{}` was cancelled",
                        decl.to_display_string()
                    )
                }
                ResourceReason::Memory { limit_bytes } => format!(
                    "memory budget of {limit_bytes} bytes exhausted at `{}`",
                    decl.to_display_string()
                ),
                // Names the unit and nothing else. The numbers belong to ResourceUsage,
                // and a renderer that invented one here would be the second home this
                // variant exists to avoid.
                ResourceReason::StructuralBudget { unit } => format!(
                    "{} budget exhausted at `{}`",
                    unit.as_str(),
                    decl.to_display_string()
                ),
            },
            ErrorValue::ArtifactCorrupt { path, detail } => {
                format!("object file '{path}' is corrupt: {detail}")
            }
            ErrorValue::ArtifactEpochMismatch {
                path,
                expected_epoch,
                found_epoch,
            } => format!(
                "object file '{path}' was produced by epoch {found_epoch}, expected {expected_epoch}"
            ),
            ErrorValue::AbiViolation { symbol, detail } => {
                format!("ABI violation at `{symbol}`: {detail}")
            }
            ErrorValue::CapabilityDenied { capability, detail } => {
                format!("capability `{capability}` denied: {detail}")
            }
            ErrorValue::PluginCrashed { plugin, detail } => {
                format!("plugin `{plugin}` crashed: {detail}")
            }
            ErrorValue::BuildFailure { job, detail } => {
                format!("build of `{job}` failed: {detail}")
            }
            ErrorValue::ProtocolFailure { detail } => format!("protocol violation: {detail}"),
            ErrorValue::ReplayDivergence { detail } => format!("replay divergence: {detail}"),
            ErrorValue::InternalInvariantViolation { invariant, detail } => format!(
                "internal invariant `{invariant}` violated: {detail} (this is a bug in FrankenLean, not in your code)"
            ),
        }
    }
}

/// `maxRecDepthErrorMessage` (src/Init/Prelude.lean:4807-4810) — verbatim.
pub const MAX_REC_DEPTH_ERROR_MESSAGE: &str = "maximum recursion depth has been reached\n\
use `set_option maxRecDepth <num>` to increase limit\n\
use `set_option diagnostics true` to get diagnostic information";

/// One diagnostic: a typed value plus its rendering coordinates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Diagnostic {
    pub file_name: String,
    pub pos: Position,
    /// Present only when the frontend requested end positions.
    pub end_pos: Option<Position>,
    pub severity: Severity,
    /// The upstream error-kind name rendered as `kind(name):` when present
    /// (`errorNameOfKind?`, Message.lean:616-618).
    pub error_name: Option<Name>,
    /// `caption:` prefix line, when non-empty (Message.lean:611-612).
    pub caption: String,
    pub value: ErrorValue,
}

/// Closed schema for the values every diagnostic adapter consumes.
pub const DIAGNOSTIC_PROJECTION_SCHEMA: &str = "fln.diagnostic-projection/1";
pub const DIAGNOSTIC_PROJECTION_SCHEMA_VERSION: u16 = 1;
/// Plan §18.8 BN-02: sound/frontier diagnostic bodies may be richer while
/// faithful bytes, authority, severity, and positions remain unchanged.
pub const DIAGNOSTIC_SOUND_BEHAVIOR_NOTE: crate::mode::BehaviorNoteId =
    crate::mode::BehaviorNoteId::new(2);
pub const DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME: &str = "BN-02";

/// Which closed projection axis failed to decode.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ProjectionAxis {
    Epoch,
    Frontend,
    Format,
    Channel,
    Color,
    Path,
    Ordering,
}

/// Missing and unknown values never select a default renderer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProjectionDecodeError {
    Missing { axis: ProjectionAxis },
    Unknown { axis: ProjectionAxis, tag: u16 },
}

/// The epoch a frontend projection reproduces. Released variants are immutable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum DiagnosticEpoch {
    V4_32_0 = 1,
}

impl DiagnosticEpoch {
    pub const ALL: [DiagnosticEpoch; 1] = [DiagnosticEpoch::V4_32_0];

    pub const fn tag(self) -> u16 {
        self as u16
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            DiagnosticEpoch::V4_32_0 => "v4.32.0",
        }
    }

    pub const fn from_tag(tag: Option<u16>) -> Result<Self, ProjectionDecodeError> {
        match tag {
            Some(1) => Ok(DiagnosticEpoch::V4_32_0),
            Some(tag) => Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Epoch,
                tag,
            }),
            None => Err(ProjectionDecodeError::Missing {
                axis: ProjectionAxis::Epoch,
            }),
        }
    }
}

/// Representative user-facing projection owners.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum DiagnosticFrontend {
    Cli = 1,
    Json = 2,
    Lsp = 3,
    Library = 4,
}

impl DiagnosticFrontend {
    pub const ALL: [DiagnosticFrontend; 4] = [
        DiagnosticFrontend::Cli,
        DiagnosticFrontend::Json,
        DiagnosticFrontend::Lsp,
        DiagnosticFrontend::Library,
    ];

    pub const fn tag(self) -> u16 {
        self as u16
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            DiagnosticFrontend::Cli => "cli",
            DiagnosticFrontend::Json => "json",
            DiagnosticFrontend::Lsp => "lsp",
            DiagnosticFrontend::Library => "library",
        }
    }

    pub const fn from_tag(tag: Option<u16>) -> Result<Self, ProjectionDecodeError> {
        match tag {
            Some(1) => Ok(DiagnosticFrontend::Cli),
            Some(2) => Ok(DiagnosticFrontend::Json),
            Some(3) => Ok(DiagnosticFrontend::Lsp),
            Some(4) => Ok(DiagnosticFrontend::Library),
            Some(tag) => Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Frontend,
                tag,
            }),
            None => Err(ProjectionDecodeError::Missing {
                axis: ProjectionAxis::Frontend,
            }),
        }
    }
}

/// Human and robot encodings remain separate closed values.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum DiagnosticFormat {
    Human = 1,
    Json = 2,
    Ndjson = 3,
    Lsp = 4,
    Typed = 5,
}

impl DiagnosticFormat {
    pub const ALL: [DiagnosticFormat; 5] = [
        DiagnosticFormat::Human,
        DiagnosticFormat::Json,
        DiagnosticFormat::Ndjson,
        DiagnosticFormat::Lsp,
        DiagnosticFormat::Typed,
    ];

    pub const fn tag(self) -> u16 {
        self as u16
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            DiagnosticFormat::Human => "human",
            DiagnosticFormat::Json => "json",
            DiagnosticFormat::Ndjson => "ndjson",
            DiagnosticFormat::Lsp => "lsp",
            DiagnosticFormat::Typed => "typed",
        }
    }

    pub const fn from_tag(tag: Option<u16>) -> Result<Self, ProjectionDecodeError> {
        match tag {
            Some(1) => Ok(DiagnosticFormat::Human),
            Some(2) => Ok(DiagnosticFormat::Json),
            Some(3) => Ok(DiagnosticFormat::Ndjson),
            Some(4) => Ok(DiagnosticFormat::Lsp),
            Some(5) => Ok(DiagnosticFormat::Typed),
            Some(tag) => Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Format,
                tag,
            }),
            None => Err(ProjectionDecodeError::Missing {
                axis: ProjectionAxis::Format,
            }),
        }
    }
}

/// Where a rendered projection travels.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum DiagnosticChannel {
    Stdout = 1,
    Stderr = 2,
    Protocol = 3,
    ReturnValue = 4,
}

impl DiagnosticChannel {
    pub const ALL: [DiagnosticChannel; 4] = [
        DiagnosticChannel::Stdout,
        DiagnosticChannel::Stderr,
        DiagnosticChannel::Protocol,
        DiagnosticChannel::ReturnValue,
    ];

    pub const fn tag(self) -> u16 {
        self as u16
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            DiagnosticChannel::Stdout => "stdout",
            DiagnosticChannel::Stderr => "stderr",
            DiagnosticChannel::Protocol => "protocol",
            DiagnosticChannel::ReturnValue => "return_value",
        }
    }

    pub const fn from_tag(tag: Option<u16>) -> Result<Self, ProjectionDecodeError> {
        match tag {
            Some(1) => Ok(DiagnosticChannel::Stdout),
            Some(2) => Ok(DiagnosticChannel::Stderr),
            Some(3) => Ok(DiagnosticChannel::Protocol),
            Some(4) => Ok(DiagnosticChannel::ReturnValue),
            Some(tag) => Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Channel,
                tag,
            }),
            None => Err(ProjectionDecodeError::Missing {
                axis: ProjectionAxis::Channel,
            }),
        }
    }
}

/// Color is explicit input. Environment-derived "auto" would be D4 and is absent.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum DiagnosticColorPolicy {
    Never = 1,
    Ansi = 2,
}

impl DiagnosticColorPolicy {
    pub const ALL: [DiagnosticColorPolicy; 2] =
        [DiagnosticColorPolicy::Never, DiagnosticColorPolicy::Ansi];

    pub const fn tag(self) -> u16 {
        self as u16
    }

    pub const fn from_tag(tag: Option<u16>) -> Result<Self, ProjectionDecodeError> {
        match tag {
            Some(1) => Ok(DiagnosticColorPolicy::Never),
            Some(2) => Ok(DiagnosticColorPolicy::Ansi),
            Some(tag) => Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Color,
                tag,
            }),
            None => Err(ProjectionDecodeError::Missing {
                axis: ProjectionAxis::Color,
            }),
        }
    }
}

/// Path rendering is explicit and deterministic.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum DiagnosticPathPolicy {
    Preserve = 1,
    Basename = 2,
}

impl DiagnosticPathPolicy {
    pub const ALL: [DiagnosticPathPolicy; 2] = [
        DiagnosticPathPolicy::Preserve,
        DiagnosticPathPolicy::Basename,
    ];

    pub const fn tag(self) -> u16 {
        self as u16
    }

    pub const fn from_tag(tag: Option<u16>) -> Result<Self, ProjectionDecodeError> {
        match tag {
            Some(1) => Ok(DiagnosticPathPolicy::Preserve),
            Some(2) => Ok(DiagnosticPathPolicy::Basename),
            Some(tag) => Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Path,
                tag,
            }),
            None => Err(ProjectionDecodeError::Missing {
                axis: ProjectionAxis::Path,
            }),
        }
    }
}

/// Registered CGSE ordering policy. An adapter may not use input arrival order.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(u16)]
pub enum DiagnosticOrderPolicy {
    SourcePositionV1 = 1,
}

impl DiagnosticOrderPolicy {
    pub const ALL: [DiagnosticOrderPolicy; 1] = [DiagnosticOrderPolicy::SourcePositionV1];

    pub const fn tag(self) -> u16 {
        self as u16
    }

    pub const fn as_str(self) -> &'static str {
        match self {
            DiagnosticOrderPolicy::SourcePositionV1 => "source-position-v1",
        }
    }

    pub const fn from_tag(tag: Option<u16>) -> Result<Self, ProjectionDecodeError> {
        match tag {
            Some(1) => Ok(DiagnosticOrderPolicy::SourcePositionV1),
            Some(tag) => Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Ordering,
                tag,
            }),
            None => Err(ProjectionDecodeError::Missing {
                axis: ProjectionAxis::Ordering,
            }),
        }
    }
}

/// Every coordinate a renderer must bind before it can project a value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ProjectionRequest {
    pub epoch: DiagnosticEpoch,
    pub mode: crate::mode::Mode,
    pub frontend: DiagnosticFrontend,
    pub format: DiagnosticFormat,
    pub channel: DiagnosticChannel,
    pub color: DiagnosticColorPolicy,
    pub path: DiagnosticPathPolicy,
    pub ordering: DiagnosticOrderPolicy,
}

impl ProjectionRequest {
    /// Bind the visible projection to the mode lattice before rendering.
    pub const fn validated_product_class(
        self,
    ) -> Result<crate::mode::ValidatedProductClass, crate::mode::ProductRefusal> {
        let observation = match self.mode {
            crate::mode::Mode::Faithful => crate::mode::ProductObservation::ReferenceParity,
            crate::mode::Mode::Sound | crate::mode::Mode::Frontier => {
                crate::mode::ProductObservation::SoundDivergence {
                    behavior_note: Some(DIAGNOSTIC_SOUND_BEHAVIOR_NOTE),
                }
            }
        };
        crate::mode::validate_mode_product(self.mode, observation)
    }
}

/// Typed adapter refusal. Unsupported tuples never fall back to another format,
/// channel, or frontend.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProjectionRefusal {
    Mode(crate::mode::ProductRefusal),
    Frontend {
        expected: DiagnosticFrontend,
        actual: DiagnosticFrontend,
    },
    UnsupportedFormat {
        frontend: DiagnosticFrontend,
        format: DiagnosticFormat,
    },
    UnsupportedChannel {
        frontend: DiagnosticFrontend,
        channel: DiagnosticChannel,
    },
    UnsupportedColor {
        frontend: DiagnosticFrontend,
        color: DiagnosticColorPolicy,
    },
}

/// A secondary source location retained alongside the primary diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelatedSpan {
    pub file_name: BoundedText,
    pub start: Position,
    pub end: Position,
    pub label: BoundedText,
}

impl RelatedSpan {
    pub fn new(
        file_name: impl Into<String>,
        start: Position,
        end: Position,
        label: impl Into<String>,
    ) -> RelatedSpan {
        RelatedSpan {
            file_name: BoundedText::new(file_name),
            start,
            end,
            label: BoundedText::new(label),
        }
    }
}

/// Maximum fan-out carried by one report. Omitted entries are counted explicitly.
pub const MAX_RELATED_SPANS: usize = 32;
pub const MAX_EVIDENCE_REFS: usize = 32;

/// A non-authoritative cause cannot be smuggled into an authoritative diagnostic
/// report. It must travel in the corresponding [`Outcome`] arm instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagnosticReportRefusal {
    NonAuthoritativeCause { cause_class: &'static str },
}

/// A typed diagnostic plus links that must survive every rendered projection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticReport {
    diagnostic: Diagnostic,
    related: Vec<RelatedSpan>,
    evidence: Vec<BoundedText>,
    omitted_related: usize,
    omitted_evidence: usize,
}

impl DiagnosticReport {
    pub fn new(diagnostic: Diagnostic) -> Result<DiagnosticReport, DiagnosticReportRefusal> {
        if matches!(
            &diagnostic.value,
            ErrorValue::KernelInconclusive { .. } | ErrorValue::InternalInvariantViolation { .. }
        ) {
            return Err(DiagnosticReportRefusal::NonAuthoritativeCause {
                cause_class: diagnostic.value.class_name(),
            });
        }
        Ok(DiagnosticReport {
            diagnostic,
            related: Vec::new(),
            evidence: Vec::new(),
            omitted_related: 0,
            omitted_evidence: 0,
        })
    }

    pub fn with_related(mut self, span: RelatedSpan) -> DiagnosticReport {
        if self.related.len() < MAX_RELATED_SPANS {
            self.related.push(span);
        } else {
            self.omitted_related = self.omitted_related.saturating_add(1);
        }
        self
    }

    pub fn with_evidence(mut self, evidence: impl Into<String>) -> DiagnosticReport {
        if self.evidence.len() < MAX_EVIDENCE_REFS {
            self.evidence.push(BoundedText::new(evidence));
        } else {
            self.omitted_evidence = self.omitted_evidence.saturating_add(1);
        }
        self
    }

    pub const fn diagnostic(&self) -> &Diagnostic {
        &self.diagnostic
    }
}

/// Closed structured record shared by all adapters. `body` is the bounded faithful
/// body; sound/frontier adapters may render additional text, but may not change the
/// cause, severity, positions, related spans, or evidence retained here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredDiagnostic {
    pub file_name: BoundedText,
    pub pos: Position,
    pub end_pos: Option<Position>,
    pub severity: Severity,
    pub error_name: Option<String>,
    pub caption: BoundedText,
    pub body: BoundedText,
    pub cause_class: &'static str,
    pub related: Vec<RelatedSpan>,
    pub evidence: Vec<BoundedText>,
    pub omitted_related: usize,
    pub omitted_evidence: usize,
}

impl DiagnosticReport {
    fn structured(&self) -> StructuredDiagnostic {
        let mut related = self.related.clone();
        related.sort_by(|left, right| {
            (
                left.file_name.text(),
                left.start.line,
                left.start.column,
                left.end.line,
                left.end.column,
                left.label.text(),
                left.label.truncated(),
            )
                .cmp(&(
                    right.file_name.text(),
                    right.start.line,
                    right.start.column,
                    right.end.line,
                    right.end.column,
                    right.label.text(),
                    right.label.truncated(),
                ))
        });
        let mut evidence = self.evidence.clone();
        evidence.sort_by(|left, right| {
            (left.text(), left.truncated()).cmp(&(right.text(), right.truncated()))
        });
        StructuredDiagnostic {
            file_name: BoundedText::new(self.diagnostic.file_name.clone()),
            pos: self.diagnostic.pos,
            end_pos: self.diagnostic.end_pos,
            severity: self.diagnostic.severity,
            error_name: self
                .diagnostic
                .error_name
                .as_ref()
                .map(Name::to_display_string),
            caption: BoundedText::new(self.diagnostic.caption.clone()),
            body: BoundedText::new(self.diagnostic.value.faithful_body()),
            cause_class: self.diagnostic.value.class_name(),
            related,
            evidence,
            omitted_related: self.omitted_related,
            omitted_evidence: self.omitted_evidence,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredCause {
    pub class_name: &'static str,
    pub body: BoundedText,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredInconclusive {
    pub cause_class: &'static str,
    pub detail: BoundedText,
    pub diagnostic: Option<StructuredCause>,
    pub progress: Option<BoundedText>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StructuredInternalFault {
    pub invariant: &'static str,
    pub detail: BoundedText,
    pub evidence: Option<BoundedText>,
}

/// One structured snapshot, before a frontend selects bytes or a protocol value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProjectionSnapshot {
    Complete {
        diagnostics: Vec<StructuredDiagnostic>,
    },
    Inconclusive(StructuredInconclusive),
    InternalFault(StructuredInternalFault),
}

/// Semantic exit/disposition class. A C-family CLI maps these to 0/1/2/3;
/// long-lived protocol and library adapters retain the class without exiting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ExitClass {
    Success,
    UserError,
    Inconclusive,
    InternalFault,
}

impl ExitClass {
    pub const fn as_str(self) -> &'static str {
        match self {
            ExitClass::Success => "success",
            ExitClass::UserError => "user_error",
            ExitClass::Inconclusive => "inconclusive",
            ExitClass::InternalFault => "internal_fault",
        }
    }

    pub const fn c_family_code(self) -> u8 {
        match self {
            ExitClass::Success => 0,
            ExitClass::UserError => 1,
            ExitClass::Inconclusive => 2,
            ExitClass::InternalFault => 3,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct DiagnosticOrderKey {
    file_name: String,
    line: usize,
    column: usize,
    end: Option<(usize, usize)>,
    severity: u8,
    error_name: String,
    cause_class: &'static str,
    caption: String,
    body: String,
    links: String,
    ordinal: usize,
}

fn structured_links_key(diagnostic: &StructuredDiagnostic) -> String {
    let mut key = String::new();
    for related in &diagnostic.related {
        key.push_str(related.file_name.text());
        key.push('\0');
        key.push_str(&related.start.line.to_string());
        key.push('\0');
        key.push_str(&related.start.column.to_string());
        key.push('\0');
        key.push_str(&related.end.line.to_string());
        key.push('\0');
        key.push_str(&related.end.column.to_string());
        key.push('\0');
        key.push_str(related.label.text());
        key.push(if related.label.truncated() {
            '\u{1}'
        } else {
            '\0'
        });
    }
    key.push('\u{1f}');
    for evidence in &diagnostic.evidence {
        key.push_str(evidence.text());
        key.push(if evidence.truncated() { '\u{1}' } else { '\0' });
        key.push('\0');
    }
    key.push_str(&diagnostic.omitted_related.to_string());
    key.push('\0');
    key.push_str(&diagnostic.omitted_evidence.to_string());
    key
}

fn ordered_diagnostics(
    reports: &[DiagnosticReport],
    policy: DiagnosticOrderPolicy,
) -> Vec<StructuredDiagnostic> {
    let DiagnosticOrderPolicy::SourcePositionV1 = policy;
    let mut keyed = reports
        .iter()
        .enumerate()
        .map(|(ordinal, report)| {
            let diagnostic = report.structured();
            (
                DiagnosticOrderKey {
                    file_name: diagnostic.file_name.text().to_string(),
                    line: diagnostic.pos.line,
                    column: diagnostic.pos.column,
                    end: diagnostic.end_pos.map(|pos| (pos.line, pos.column)),
                    severity: diagnostic.severity.order_rank(),
                    error_name: diagnostic.error_name.clone().unwrap_or_default(),
                    cause_class: diagnostic.cause_class,
                    caption: diagnostic.caption.text().to_string(),
                    body: diagnostic.body.text().to_string(),
                    links: structured_links_key(&diagnostic),
                    ordinal,
                },
                diagnostic,
            )
        })
        .collect::<Vec<_>>();
    keyed.sort_by(|(left, _), (right, _)| left.cmp(right));
    keyed
        .into_iter()
        .map(|(_, diagnostic)| diagnostic)
        .collect()
}

fn resource_reason_class(usage: &ResourceUsage) -> &'static str {
    match &usage.reason {
        ResourceReason::Heartbeats { .. } => "heartbeats",
        ResourceReason::RecursionDepth { .. } => "recursion_depth",
        ResourceReason::Cancelled => "cancelled_not_exhaustion",
        ResourceReason::Memory { .. } => "memory",
        ResourceReason::StructuralBudget { .. } => "structural_budget",
    }
}

fn structured_inconclusive(inconclusive: &crate::outcome::Inconclusive) -> StructuredInconclusive {
    let (cause_class, detail) = match &inconclusive.cause {
        InconclusiveCause::Cancelled { at } => ("cancelled", at.clone()),
        InconclusiveCause::ResourceExhausted { usage } => (
            resource_reason_class(usage),
            BoundedText::new(format!(
                "{} exhausted: allowed {}, observed {}",
                resource_reason_class(usage),
                usage.allowed,
                usage.observed
            )),
        ),
        InconclusiveCause::DependencyUnavailable { what } => {
            ("dependency_unavailable", what.clone())
        }
        InconclusiveCause::AuthorityIncomplete { what } => ("authority_incomplete", what.clone()),
    };
    StructuredInconclusive {
        cause_class,
        detail,
        diagnostic: inconclusive
            .diagnostic
            .as_ref()
            .map(|diagnostic| StructuredCause {
                class_name: diagnostic.class_name(),
                body: BoundedText::new(diagnostic.faithful_body()),
            }),
        progress: inconclusive.progress.as_deref().cloned(),
    }
}

fn structured_internal_fault(fault: &InternalFault) -> StructuredInternalFault {
    StructuredInternalFault {
        invariant: fault.invariant,
        detail: fault.detail.clone(),
        evidence: fault.evidence.clone(),
    }
}

impl ProjectionSnapshot {
    /// Build the one structured value every frontend consumes. Sorting happens before
    /// rendering and uses only registered typed coordinates.
    pub fn from_outcome(
        outcome: &Outcome<Vec<DiagnosticReport>>,
        ordering: DiagnosticOrderPolicy,
    ) -> ProjectionSnapshot {
        match outcome {
            Outcome::Complete(reports) => ProjectionSnapshot::Complete {
                diagnostics: ordered_diagnostics(reports, ordering),
            },
            Outcome::Inconclusive(inconclusive) => {
                ProjectionSnapshot::Inconclusive(structured_inconclusive(inconclusive))
            }
            Outcome::InternalFault(fault) => {
                ProjectionSnapshot::InternalFault(structured_internal_fault(fault))
            }
        }
    }

    pub const fn authority(&self) -> Authority {
        match self {
            ProjectionSnapshot::Complete { .. } => Authority::Authoritative,
            ProjectionSnapshot::Inconclusive(_) | ProjectionSnapshot::InternalFault(_) => {
                Authority::NonAuthoritative
            }
        }
    }

    pub fn exit_class(&self) -> ExitClass {
        match self {
            ProjectionSnapshot::Complete { diagnostics } => {
                if diagnostics
                    .iter()
                    .any(|diagnostic| diagnostic.severity == Severity::Error)
                {
                    ExitClass::UserError
                } else {
                    ExitClass::Success
                }
            }
            ProjectionSnapshot::Inconclusive(_) => ExitClass::Inconclusive,
            ProjectionSnapshot::InternalFault(_) => ExitClass::InternalFault,
        }
    }

    pub const fn outcome_class(&self) -> &'static str {
        match self {
            ProjectionSnapshot::Complete { .. } => "complete",
            ProjectionSnapshot::Inconclusive(_) => "inconclusive",
            ProjectionSnapshot::InternalFault(_) => "internal_fault",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn err(message: &str) -> ErrorValue {
        ErrorValue::SyntaxFailure {
            message: message.to_string(),
        }
    }

    fn diag(value: ErrorValue) -> Diagnostic {
        Diagnostic {
            file_name: "Foo.lean".to_string(),
            pos: Position { line: 2, column: 0 },
            end_pos: None,
            severity: Severity::Error,
            error_name: None,
            caption: String::new(),
            value,
        }
    }

    #[test]
    fn the_taxonomy_is_complete_and_classes_are_stable() {
        assert_eq!(ErrorValue::CLASS_NAMES.len(), 14);
        let mut seen = std::collections::BTreeSet::new();
        for name in ErrorValue::CLASS_NAMES {
            assert!(seen.insert(name), "duplicate class {name}");
        }
        assert_eq!(err("x").class_name(), "SyntaxFailure");
    }

    #[test]
    fn inconclusive_is_not_rejected_structurally() {
        let rejection = ErrorValue::KernelRejection {
            decl: Name::str(Name::anonymous(), "foo"),
            stable_error_class: "type_mismatch".to_string(),
            message: "type mismatch".to_string(),
        };
        let inconclusive = ErrorValue::KernelInconclusive {
            decl: Name::str(Name::anonymous(), "foo"),
            resource: ResourceReason::Heartbeats {
                consumed: 200_001_000,
                limit: 200_000_000,
            },
        };
        assert!(rejection.is_rejection() && !rejection.is_inconclusive());
        assert!(inconclusive.is_inconclusive() && !inconclusive.is_rejection());
    }

    #[test]
    fn projection_axes_refuse_missing_and_unknown_values() {
        assert_eq!(
            DiagnosticEpoch::from_tag(None),
            Err(ProjectionDecodeError::Missing {
                axis: ProjectionAxis::Epoch
            })
        );
        assert_eq!(
            DiagnosticFrontend::from_tag(Some(99)),
            Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Frontend,
                tag: 99
            })
        );
        assert_eq!(
            DiagnosticFormat::from_tag(Some(DiagnosticFormat::Ndjson.tag())),
            Ok(DiagnosticFormat::Ndjson)
        );
        assert_eq!(
            DiagnosticFormat::from_tag(Some(99)),
            Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Format,
                tag: 99
            })
        );
        assert_eq!(
            DiagnosticChannel::from_tag(Some(99)),
            Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Channel,
                tag: 99
            })
        );
        assert_eq!(
            DiagnosticColorPolicy::from_tag(Some(99)),
            Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Color,
                tag: 99
            })
        );
        assert_eq!(
            DiagnosticPathPolicy::from_tag(Some(99)),
            Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Path,
                tag: 99
            })
        );
        assert_eq!(
            DiagnosticOrderPolicy::from_tag(Some(0)),
            Err(ProjectionDecodeError::Unknown {
                axis: ProjectionAxis::Ordering,
                tag: 0
            })
        );
    }

    #[test]
    fn structured_snapshot_orders_before_rendering_and_classifies_exit() {
        let mut late = diag(err("late"));
        late.file_name = "Z.lean".to_string();
        late.pos = Position { line: 9, column: 0 };
        let mut early = diag(err("early"));
        early.file_name = "A.lean".to_string();
        early.pos = Position { line: 1, column: 2 };
        let outcome = Outcome::complete(vec![
            DiagnosticReport::new(late).expect("ordinary diagnostic"),
            DiagnosticReport::new(early).expect("ordinary diagnostic"),
        ]);
        let snapshot =
            ProjectionSnapshot::from_outcome(&outcome, DiagnosticOrderPolicy::SourcePositionV1);
        let ProjectionSnapshot::Complete { diagnostics } = &snapshot else {
            panic!("complete input remains complete");
        };
        assert_eq!(diagnostics[0].file_name.text(), "A.lean");
        assert_eq!(diagnostics[1].file_name.text(), "Z.lean");
        assert_eq!(snapshot.authority(), Authority::Authoritative);
        assert_eq!(snapshot.exit_class(), ExitClass::UserError);
    }

    #[test]
    fn bounded_records_mark_every_loss_and_keep_cause_and_evidence() {
        let oversized = "x".repeat(BoundedText::LIMIT + 19);
        let mut report = DiagnosticReport::new(diag(err(&oversized)))
            .expect("ordinary diagnostic")
            .with_evidence(oversized.clone())
            .with_related(RelatedSpan::new(
                "Other.lean",
                Position { line: 1, column: 0 },
                Position { line: 1, column: 1 },
                oversized,
            ));
        for index in 0..(MAX_EVIDENCE_REFS - 1) {
            report = report.with_evidence(format!("receipt-{index}"));
        }
        report = report.with_evidence("omitted-receipt");
        let snapshot = ProjectionSnapshot::from_outcome(
            &Outcome::complete(vec![report]),
            DiagnosticOrderPolicy::SourcePositionV1,
        );
        let ProjectionSnapshot::Complete { diagnostics } = snapshot else {
            panic!("complete input remains complete");
        };
        let projected = &diagnostics[0];
        assert_eq!(projected.cause_class, "SyntaxFailure");
        assert!(projected.body.truncated());
        assert!(projected.evidence.iter().any(BoundedText::truncated));
        assert!(projected.related[0].label.truncated());
        assert_eq!(projected.omitted_evidence, 1);
    }

    #[test]
    fn non_authoritative_causes_cannot_enter_a_complete_report() {
        let inconclusive = diag(ErrorValue::KernelInconclusive {
            decl: Name::str(Name::anonymous(), "slow"),
            resource: ResourceReason::Heartbeats {
                consumed: 11,
                limit: 10,
            },
        });
        assert_eq!(
            DiagnosticReport::new(inconclusive),
            Err(DiagnosticReportRefusal::NonAuthoritativeCause {
                cause_class: "KernelInconclusive"
            })
        );

        let internal_fault = diag(ErrorValue::InternalInvariantViolation {
            invariant: "FL-INV-07".to_string(),
            detail: "authority mismatch".to_string(),
        });
        assert_eq!(
            DiagnosticReport::new(internal_fault),
            Err(DiagnosticReportRefusal::NonAuthoritativeCause {
                cause_class: "InternalInvariantViolation"
            })
        );
    }

    #[test]
    fn max_rec_depth_message_is_the_pin_verbatim() {
        let d = ErrorValue::KernelInconclusive {
            decl: Name::str(Name::anonymous(), "deep"),
            resource: ResourceReason::RecursionDepth { limit: 512 },
        };
        assert!(
            d.faithful_body()
                .starts_with("maximum recursion depth has been reached")
        );
        assert!(d.faithful_body().contains("set_option maxRecDepth"));
    }

    #[test]
    fn internal_invariant_violations_name_themselves_as_our_bug() {
        let v = ErrorValue::InternalInvariantViolation {
            invariant: "FL-INV-01".to_string(),
            detail: "schedule-dependent result".to_string(),
        };
        assert!(v.faithful_body().contains("bug in FrankenLean"));
        assert!(!v.is_rejection() && !v.is_inconclusive());
    }
}
