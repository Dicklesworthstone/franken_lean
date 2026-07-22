//! The typed error taxonomy and the faithful diagnostic renderer (plan D8 normative
//! taxonomy, risk R9; bead fln-rk6).
//!
//! Errors cross crate boundaries as **typed, versioned values** — the fourteen
//! variants of [`ErrorValue`], defined once here, consumed everywhere. Panics are
//! invariant failures, never user diagnostics. The renderer is a *projection* of the
//! typed value: faithful-mode frontends reproduce the Reference's CLI framing
//! exactly, per epoch; receipts retain the typed cause even when the rendered text
//! is upstream-identical.
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
}

/// The D8 normative taxonomy, version 1. Closed: adding a variant is a reviewed
/// taxonomy revision that breaks every consumer until handled (no catch-all arms in
/// authoritative crates).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ErrorValue {
    /// Quill rejected the source text.
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

/// Rendering modes (plan §4.2). One typed value, two projections; faithful is pinned
/// per epoch, sound may say more but never changes positions or severities.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RenderMode {
    Faithful,
    Sound,
}

/// The per-epoch renderer registry. Adding an epoch adds a variant; faithful output
/// for a released epoch never changes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Epoch {
    V4_32_0,
}

/// `mkErrorStringWithPos` (Message.lean:31-42), byte-exact.
fn frame_with_pos(
    file_name: &str,
    pos: Position,
    msg: &str,
    end_pos: Option<Position>,
    kind: &str,
    name: Option<&Name>,
) -> String {
    let end = match end_pos {
        Some(e) => format!("-{}:{}", e.line, e.column),
        None => String::new(),
    };
    let label = match name {
        Some(n) => format!(" {kind}({}):", n.to_display_string()),
        None => format!(" {kind}:"),
    };
    format!("{file_name}:{}:{}{end}:{label} {msg}", pos.line, pos.column)
}

/// `SerialMessage.toString` (Message.lean:608-620), byte-exact for the faithful
/// projection at the epoch.
pub fn render_cli(diag: &Diagnostic, mode: RenderMode, epoch: Epoch) -> String {
    let Epoch::V4_32_0 = epoch;
    let mut body = diag.value.faithful_body();
    if mode == RenderMode::Sound {
        // BN-02: sound mode may append a richer, typed-cause trailer. The frame,
        // position, and severity are IDENTICAL to faithful; the trailer is
        // sound-only vocabulary that the leak-regression test pins out of faithful.
        body.push_str(&format!("\n[typed cause: {}]", diag.value.class_name()));
    }
    let mut text = body;
    if !diag.caption.is_empty() {
        text = format!("{}:\n{text}", diag.caption);
    }
    match diag.severity {
        Severity::Information => {}
        Severity::Warning => {
            text = frame_with_pos(
                &diag.file_name,
                diag.pos,
                &text,
                diag.end_pos,
                "warning",
                diag.error_name.as_ref(),
            );
        }
        Severity::Error => {
            text = frame_with_pos(
                &diag.file_name,
                diag.pos,
                &text,
                diag.end_pos,
                "error",
                diag.error_name.as_ref(),
            );
        }
    }
    if text.is_empty() || !text.ends_with('\n') {
        text.push('\n');
    }
    text
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
    fn faithful_frame_matches_the_pin_formula() {
        let rendered = render_cli(
            &diag(err("unterminated comment")),
            RenderMode::Faithful,
            Epoch::V4_32_0,
        );
        assert_eq!(rendered, "Foo.lean:2:0: error: unterminated comment\n");

        // warning kind word; end-position suffix; error-name label.
        let mut d = diag(err("shadowed"));
        d.severity = Severity::Warning;
        d.end_pos = Some(Position { line: 2, column: 7 });
        assert_eq!(
            render_cli(&d, RenderMode::Faithful, Epoch::V4_32_0),
            "Foo.lean:2:0-2:7: warning: shadowed\n"
        );
        let mut named = diag(err("boom"));
        named.error_name = Some(Name::from_components(["lean", "unknownIdentifier"]));
        assert_eq!(
            render_cli(&named, RenderMode::Faithful, Epoch::V4_32_0),
            "Foo.lean:2:0: error(lean.unknownIdentifier): boom\n"
        );
    }

    #[test]
    fn information_severity_has_no_frame_and_captions_prefix() {
        let mut d = diag(err("just a note"));
        d.severity = Severity::Information;
        assert_eq!(
            render_cli(&d, RenderMode::Faithful, Epoch::V4_32_0),
            "just a note\n"
        );
        let mut captioned = diag(err("body"));
        captioned.caption = "context".to_string();
        assert_eq!(
            render_cli(&captioned, RenderMode::Faithful, Epoch::V4_32_0),
            "Foo.lean:2:0: error: context:\nbody\n"
        );
    }

    #[test]
    fn sound_wording_can_never_leak_into_faithful_output() {
        for value in [
            err("x"),
            ErrorValue::ReplayDivergence {
                detail: "seed 7".to_string(),
            },
            ErrorValue::KernelInconclusive {
                decl: Name::str(Name::anonymous(), "slow"),
                resource: ResourceReason::Cancelled,
            },
        ] {
            let d = diag(value);
            let faithful = render_cli(&d, RenderMode::Faithful, Epoch::V4_32_0);
            let sound = render_cli(&d, RenderMode::Sound, Epoch::V4_32_0);
            assert!(
                !faithful.contains("[typed cause:"),
                "sound leaked into faithful"
            );
            assert!(
                sound.contains("[typed cause:"),
                "sound renders the typed cause"
            );
            assert!(
                sound.starts_with(faithful.trim_end_matches('\n')),
                "sound preserves the faithful frame, positions, and severities"
            );
        }
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
