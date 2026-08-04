//! **fln-server** — Lantern's LSP diagnostic adapter (plan §14; bead
//! `franken_lean-wlan`).
//!
//! User diagnostics become `textDocument/publishDiagnostics` notifications.
//! Inconclusive and internal-fault outcomes use the distinct
//! `$/lean/diagnosticOutcome` channel: neither can be mislabeled as a user error or
//! silently converted into an empty diagnostic list.

#![forbid(unsafe_code)]

use std::collections::BTreeMap;

use fln_core::diag::{
    DIAGNOSTIC_PROJECTION_SCHEMA, DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME, DiagnosticChannel,
    DiagnosticColorPolicy, DiagnosticFormat, DiagnosticFrontend, DiagnosticPathPolicy, ExitClass,
    ProjectionRefusal, ProjectionRequest, ProjectionSnapshot, RelatedSpan, Severity,
    StructuredDiagnostic, StructuredInconclusive, StructuredInternalFault,
};
use fln_core::mode::Mode;
use fln_core::outcome::BoundedText;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LspProjection {
    /// One canonical JSON-RPC notification per source file, or one typed non-answer.
    pub messages: Vec<String>,
    /// Semantic disposition only. A long-lived server does not turn this into a
    /// process exit code.
    pub disposition: ExitClass,
    pub semantic: ProjectionSnapshot,
}

fn validate_request(request: ProjectionRequest) -> Result<(), ProjectionRefusal> {
    request
        .validated_product_class()
        .map_err(ProjectionRefusal::Mode)?;
    if request.frontend != DiagnosticFrontend::Lsp {
        return Err(ProjectionRefusal::Frontend {
            expected: DiagnosticFrontend::Lsp,
            actual: request.frontend,
        });
    }
    if request.format != DiagnosticFormat::Lsp {
        return Err(ProjectionRefusal::UnsupportedFormat {
            frontend: request.frontend,
            format: request.format,
        });
    }
    if request.channel != DiagnosticChannel::Protocol {
        return Err(ProjectionRefusal::UnsupportedChannel {
            frontend: request.frontend,
            channel: request.channel,
        });
    }
    if request.color != DiagnosticColorPolicy::Never {
        return Err(ProjectionRefusal::UnsupportedColor {
            frontend: request.frontend,
            color: request.color,
        });
    }
    Ok(())
}

fn mode_name(mode: Mode) -> &'static str {
    match mode {
        Mode::Faithful => "faithful",
        Mode::Sound => "sound",
        Mode::Frontier => "frontier",
    }
}

fn projected_path(path: &str, policy: DiagnosticPathPolicy) -> &str {
    match policy {
        DiagnosticPathPolicy::Preserve => path,
        DiagnosticPathPolicy::Basename => path
            .rsplit(['/', '\\'])
            .find(|component| !component.is_empty())
            .unwrap_or(path),
    }
}

fn json_string(value: &str) -> String {
    let mut encoded = String::with_capacity(value.len() + 2);
    encoded.push('"');
    for character in value.chars() {
        match character {
            '"' => encoded.push_str("\\\""),
            '\\' => encoded.push_str("\\\\"),
            '\n' => encoded.push_str("\\n"),
            '\r' => encoded.push_str("\\r"),
            '\t' => encoded.push_str("\\t"),
            '\u{08}' => encoded.push_str("\\b"),
            '\u{0c}' => encoded.push_str("\\f"),
            character if character <= '\u{1f}' => {
                encoded.push_str(&format!("\\u{:04x}", u32::from(character)));
            }
            character => encoded.push(character),
        }
    }
    encoded.push('"');
    encoded
}

fn bounded_json(value: &BoundedText) -> String {
    format!(
        "{{\"text\":{},\"truncated\":{}}}",
        json_string(value.text()),
        value.truncated()
    )
}

fn lsp_position(position: fln_core::pos::Position) -> String {
    format!(
        "{{\"line\":{},\"character\":{}}}",
        position.line.saturating_sub(1),
        position.column
    )
}

fn uri(path: &str, policy: DiagnosticPathPolicy) -> String {
    format!("file://{}", projected_path(path, policy))
}

fn related_json(span: &RelatedSpan, policy: DiagnosticPathPolicy) -> String {
    format!(
        concat!(
            "{{\"location\":{{\"uri\":{},\"range\":{{\"start\":{},\"end\":{}}}}},",
            "\"message\":{},\"data\":{{\"truncated\":{}}}}}"
        ),
        json_string(&uri(span.file_name.text(), policy)),
        lsp_position(span.start),
        lsp_position(span.end),
        json_string(span.label.text()),
        span.label.truncated()
    )
}

fn severity_code(severity: Severity) -> u8 {
    match severity {
        Severity::Error => 1,
        Severity::Warning => 2,
        Severity::Information => 3,
    }
}

fn diagnostic_message(diagnostic: &StructuredDiagnostic, mode: Mode) -> String {
    let mut message = diagnostic.body.text().to_string();
    if diagnostic.body.truncated() {
        message.push_str(&format!(
            "\n[diagnostic body truncated after {} bytes; typed links retained]",
            BoundedText::LIMIT
        ));
    }
    if !matches!(mode, Mode::Faithful) {
        message.push_str(&format!(
            "\n[behavior note: {DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME}]"
        ));
        message.push_str(&format!("\n[typed cause: {}]", diagnostic.cause_class));
    }
    message
}

fn lsp_diagnostic(diagnostic: &StructuredDiagnostic, request: ProjectionRequest) -> String {
    let end = diagnostic.end_pos.unwrap_or(diagnostic.pos);
    let behavior_note = if matches!(request.mode, Mode::Faithful) {
        "null".to_string()
    } else {
        json_string(DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME)
    };
    let related = diagnostic
        .related
        .iter()
        .map(|span| related_json(span, request.path))
        .collect::<Vec<_>>()
        .join(",");
    let evidence = diagnostic
        .evidence
        .iter()
        .map(bounded_json)
        .collect::<Vec<_>>()
        .join(",");
    format!(
        concat!(
            "{{\"range\":{{\"start\":{},\"end\":{}}},\"severity\":{},",
            "\"code\":{},\"source\":\"FrankenLean\",\"message\":{},",
            "\"relatedInformation\":[{}],\"data\":{{\"schema\":{},",
            "\"causeClass\":{},\"behaviorNote\":{},\"bodyTruncated\":{},\"evidence\":[{}],",
            "\"omittedRelated\":{},\"omittedEvidence\":{}}}}}"
        ),
        lsp_position(diagnostic.pos),
        lsp_position(end),
        severity_code(diagnostic.severity),
        json_string(diagnostic.cause_class),
        json_string(&diagnostic_message(diagnostic, request.mode)),
        related,
        json_string(DIAGNOSTIC_PROJECTION_SCHEMA),
        json_string(diagnostic.cause_class),
        behavior_note,
        diagnostic.body.truncated(),
        evidence,
        diagnostic.omitted_related,
        diagnostic.omitted_evidence
    )
}

fn complete_messages(
    diagnostics: &[StructuredDiagnostic],
    request: ProjectionRequest,
) -> Vec<String> {
    let mut by_file: BTreeMap<String, Vec<&StructuredDiagnostic>> = BTreeMap::new();
    for diagnostic in diagnostics {
        by_file
            .entry(projected_path(diagnostic.file_name.text(), request.path).to_string())
            .or_default()
            .push(diagnostic);
    }
    if by_file.is_empty() {
        return vec![format!(
            concat!(
                "{{\"jsonrpc\":\"2.0\",\"method\":\"$/lean/diagnosticOutcome\",",
                "\"params\":{{\"schema\":{},\"outcome\":\"complete\",",
                "\"authority\":true,\"diagnosticCount\":0}}}}"
            ),
            json_string(DIAGNOSTIC_PROJECTION_SCHEMA)
        )];
    }
    by_file
        .into_iter()
        .map(|(file, diagnostics)| {
            let encoded = diagnostics
                .into_iter()
                .map(|diagnostic| lsp_diagnostic(diagnostic, request))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                concat!(
                    "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",",
                    "\"params\":{{\"uri\":{},\"version\":null,\"diagnostics\":[{}]}}}}"
                ),
                json_string(&format!("file://{file}")),
                encoded
            )
        })
        .collect()
}

fn inconclusive_message(value: &StructuredInconclusive, request: ProjectionRequest) -> String {
    let diagnostic = value
        .diagnostic
        .as_ref()
        .map(|diagnostic| {
            format!(
                "{{\"causeClass\":{},\"body\":{}}}",
                json_string(diagnostic.class_name),
                bounded_json(&diagnostic.body)
            )
        })
        .unwrap_or_else(|| "null".to_string());
    let progress = value
        .progress
        .as_ref()
        .map(bounded_json)
        .unwrap_or_else(|| "null".to_string());
    format!(
        concat!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"$/lean/diagnosticOutcome\",",
            "\"params\":{{\"schema\":{},\"epoch\":{},\"mode\":{},",
            "\"outcome\":\"inconclusive\",\"authority\":false,\"causeClass\":{},",
            "\"detail\":{},\"diagnostic\":{},\"progress\":{}}}}}"
        ),
        json_string(DIAGNOSTIC_PROJECTION_SCHEMA),
        json_string(request.epoch.as_str()),
        json_string(mode_name(request.mode)),
        json_string(value.cause_class),
        bounded_json(&value.detail),
        diagnostic,
        progress
    )
}

fn internal_fault_message(value: &StructuredInternalFault, request: ProjectionRequest) -> String {
    let evidence = value
        .evidence
        .as_ref()
        .map(bounded_json)
        .unwrap_or_else(|| "null".to_string());
    format!(
        concat!(
            "{{\"jsonrpc\":\"2.0\",\"method\":\"$/lean/diagnosticOutcome\",",
            "\"params\":{{\"schema\":{},\"epoch\":{},\"mode\":{},",
            "\"outcome\":\"internal_fault\",\"authority\":false,\"invariant\":{},",
            "\"detail\":{},\"evidence\":{}}}}}"
        ),
        json_string(DIAGNOSTIC_PROJECTION_SCHEMA),
        json_string(request.epoch.as_str()),
        json_string(mode_name(request.mode)),
        json_string(value.invariant),
        bounded_json(&value.detail),
        evidence
    )
}

pub fn project(
    request: ProjectionRequest,
    snapshot: &ProjectionSnapshot,
) -> Result<LspProjection, ProjectionRefusal> {
    validate_request(request)?;
    let messages = match snapshot {
        ProjectionSnapshot::Complete { diagnostics } => complete_messages(diagnostics, request),
        ProjectionSnapshot::Inconclusive(value) => {
            vec![inconclusive_message(value, request)]
        }
        ProjectionSnapshot::InternalFault(value) => {
            vec![internal_fault_message(value, request)]
        }
    };
    Ok(LspProjection {
        messages,
        disposition: snapshot.exit_class(),
        semantic: snapshot.clone(),
    })
}
