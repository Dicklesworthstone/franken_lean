//! **fln-cli** — front-door diagnostic adapters for the `lean`/`leanc`/`lake`
//! personalities and the `fln` multiplexer (plan §17.1; bead
//! `franken_lean-wlan`).
//!
//! `fln-core` supplies a typed [`ProjectionSnapshot`]. This crate owns the CLI
//! framing and JSON/NDJSON bytes. The bytes never become authority: exit class,
//! cause, positions, related spans, evidence links, and truncation markers all
//! remain bound to the snapshot returned beside them.

#![forbid(unsafe_code)]

use fln_core::diag::{
    DIAGNOSTIC_PROJECTION_SCHEMA, DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME, DiagnosticChannel,
    DiagnosticColorPolicy, DiagnosticFormat, DiagnosticFrontend, DiagnosticPathPolicy, ExitClass,
    ProjectionRefusal, ProjectionRequest, ProjectionSnapshot, RelatedSpan, Severity,
    StructuredDiagnostic, StructuredInconclusive, StructuredInternalFault,
};
use fln_core::mode::Mode;
use fln_core::outcome::BoundedText;

/// Rendered C-family streams plus the exact structured value that authorized them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CliProjection {
    pub stdout: String,
    pub stderr: String,
    pub exit: ExitClass,
    pub semantic: ProjectionSnapshot,
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

fn validate_request(request: ProjectionRequest) -> Result<(), ProjectionRefusal> {
    request
        .validated_product_class()
        .map_err(ProjectionRefusal::Mode)?;
    match request.frontend {
        DiagnosticFrontend::Cli => {
            if request.format != DiagnosticFormat::Human {
                return Err(ProjectionRefusal::UnsupportedFormat {
                    frontend: request.frontend,
                    format: request.format,
                });
            }
        }
        DiagnosticFrontend::Json => {
            if !matches!(
                request.format,
                DiagnosticFormat::Json | DiagnosticFormat::Ndjson
            ) {
                return Err(ProjectionRefusal::UnsupportedFormat {
                    frontend: request.frontend,
                    format: request.format,
                });
            }
            if request.color != DiagnosticColorPolicy::Never {
                return Err(ProjectionRefusal::UnsupportedColor {
                    frontend: request.frontend,
                    color: request.color,
                });
            }
        }
        actual => {
            return Err(ProjectionRefusal::Frontend {
                expected: DiagnosticFrontend::Cli,
                actual,
            });
        }
    }
    if !matches!(
        request.channel,
        DiagnosticChannel::Stdout | DiagnosticChannel::Stderr
    ) {
        return Err(ProjectionRefusal::UnsupportedChannel {
            frontend: request.frontend,
            channel: request.channel,
        });
    }
    Ok(())
}

fn append_bounded(target: &mut String, value: &BoundedText, label: &str) {
    target.push_str(value.text());
    if value.truncated() {
        target.push_str(&format!(
            "\n[{label} truncated after {} bytes; typed links retained]",
            BoundedText::LIMIT
        ));
    }
}

fn colored_kind(kind: &str, severity: Severity, color: DiagnosticColorPolicy) -> String {
    if color == DiagnosticColorPolicy::Never {
        return kind.to_string();
    }
    let code = match severity {
        Severity::Error => 31,
        Severity::Warning => 33,
        Severity::Information => 36,
    };
    format!("\u{1b}[{code}m{kind}\u{1b}[0m")
}

fn append_sound_links(text: &mut String, diagnostic: &StructuredDiagnostic) {
    text.push_str(&format!(
        "\n[behavior note: {DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME}]"
    ));
    text.push_str(&format!("\n[typed cause: {}]", diagnostic.cause_class));
    for related in &diagnostic.related {
        text.push_str("\n[related: ");
        text.push_str(related.file_name.text());
        text.push_str(&format!(
            ":{}:{}-{}:{} ",
            related.start.line, related.start.column, related.end.line, related.end.column
        ));
        append_bounded(text, &related.label, "related label");
        text.push(']');
    }
    for evidence in &diagnostic.evidence {
        text.push_str("\n[evidence: ");
        append_bounded(text, evidence, "evidence");
        text.push(']');
    }
    if diagnostic.omitted_related > 0 {
        text.push_str(&format!(
            "\n[related spans omitted: {}]",
            diagnostic.omitted_related
        ));
    }
    if diagnostic.omitted_evidence > 0 {
        text.push_str(&format!(
            "\n[evidence links omitted: {}]",
            diagnostic.omitted_evidence
        ));
    }
}

/// `mkErrorStringWithPos` plus `SerialMessage.toString` for v4.32.0.
///
/// Faithful mode adds no local wording. Sound/frontier wording is an explicit
/// projection trailer and cannot alter the frame, severity, or typed cause.
pub fn render_human_diagnostic(
    diagnostic: &StructuredDiagnostic,
    request: ProjectionRequest,
) -> String {
    let mut body = String::new();
    append_bounded(&mut body, &diagnostic.body, "diagnostic body");
    if !matches!(request.mode, Mode::Faithful) {
        append_sound_links(&mut body, diagnostic);
    }
    let mut text = body;
    if !diagnostic.caption.text().is_empty() {
        let mut captioned = String::new();
        append_bounded(&mut captioned, &diagnostic.caption, "caption");
        captioned.push_str(":\n");
        captioned.push_str(&text);
        text = captioned;
    }
    if diagnostic.severity != Severity::Information {
        let path = projected_path(diagnostic.file_name.text(), request.path);
        let end = diagnostic
            .end_pos
            .map(|position| format!("-{}:{}", position.line, position.column))
            .unwrap_or_default();
        let kind = colored_kind(
            diagnostic.severity.as_str(),
            diagnostic.severity,
            request.color,
        );
        let label = diagnostic
            .error_name
            .as_ref()
            .map(|name| format!(" {kind}({name}):"))
            .unwrap_or_else(|| format!(" {kind}:"));
        text = format!(
            "{path}:{}:{}{end}:{label} {text}",
            diagnostic.pos.line, diagnostic.pos.column
        );
    }
    if text.is_empty() || !text.ends_with('\n') {
        text.push('\n');
    }
    text
}

fn render_inconclusive(value: &StructuredInconclusive) -> String {
    let mut text = format!("inconclusive ({}): ", value.cause_class);
    append_bounded(&mut text, &value.detail, "inconclusive detail");
    if let Some(diagnostic) = &value.diagnostic {
        text.push_str(&format!("\n[typed cause: {}] ", diagnostic.class_name));
        append_bounded(&mut text, &diagnostic.body, "diagnostic cause");
    }
    if let Some(progress) = &value.progress {
        text.push_str("\n[progress: ");
        append_bounded(&mut text, progress, "progress");
        text.push(']');
    }
    text.push('\n');
    text
}

fn render_internal_fault(value: &StructuredInternalFault) -> String {
    let mut text = format!("internal fault ({}): ", value.invariant);
    append_bounded(&mut text, &value.detail, "internal fault detail");
    if let Some(evidence) = &value.evidence {
        text.push_str("\n[evidence: ");
        append_bounded(&mut text, evidence, "internal fault evidence");
        text.push(']');
    }
    text.push('\n');
    text
}

fn render_human(snapshot: &ProjectionSnapshot, request: ProjectionRequest) -> String {
    match snapshot {
        ProjectionSnapshot::Complete { diagnostics } => diagnostics
            .iter()
            .map(|diagnostic| render_human_diagnostic(diagnostic, request))
            .collect(),
        ProjectionSnapshot::Inconclusive(value) => render_inconclusive(value),
        ProjectionSnapshot::InternalFault(value) => render_internal_fault(value),
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

fn related_json(span: &RelatedSpan, path: DiagnosticPathPolicy) -> String {
    format!(
        concat!(
            "{{\"file\":{},\"start\":{{\"line\":{},\"column\":{}}},",
            "\"end\":{{\"line\":{},\"column\":{}}},\"label\":{}}}"
        ),
        json_string(projected_path(span.file_name.text(), path)),
        span.start.line,
        span.start.column,
        span.end.line,
        span.end.column,
        bounded_json(&span.label)
    )
}

fn diagnostic_json(diagnostic: &StructuredDiagnostic, request: ProjectionRequest) -> String {
    let end = diagnostic
        .end_pos
        .map(|position| {
            format!(
                "{{\"line\":{},\"column\":{}}}",
                position.line, position.column
            )
        })
        .unwrap_or_else(|| "null".to_string());
    let error_name = diagnostic
        .error_name
        .as_deref()
        .map(json_string)
        .unwrap_or_else(|| "null".to_string());
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
            "{{\"file\":{},\"position\":{{\"line\":{},\"column\":{}}},",
            "\"endPosition\":{},\"severity\":{},\"errorName\":{},\"caption\":{},",
            "\"body\":{},\"causeClass\":{},\"related\":[{}],\"evidence\":[{}],",
            "\"omittedRelated\":{},\"omittedEvidence\":{}}}"
        ),
        json_string(projected_path(diagnostic.file_name.text(), request.path)),
        diagnostic.pos.line,
        diagnostic.pos.column,
        end,
        json_string(diagnostic.severity.as_str()),
        error_name,
        bounded_json(&diagnostic.caption),
        bounded_json(&diagnostic.body),
        json_string(diagnostic.cause_class),
        related,
        evidence,
        diagnostic.omitted_related,
        diagnostic.omitted_evidence
    )
}

fn inconclusive_json(value: &StructuredInconclusive) -> String {
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
        "{{\"causeClass\":{},\"detail\":{},\"diagnostic\":{},\"progress\":{}}}",
        json_string(value.cause_class),
        bounded_json(&value.detail),
        diagnostic,
        progress
    )
}

fn internal_fault_json(value: &StructuredInternalFault) -> String {
    let evidence = value
        .evidence
        .as_ref()
        .map(bounded_json)
        .unwrap_or_else(|| "null".to_string());
    format!(
        "{{\"invariant\":{},\"detail\":{},\"evidence\":{}}}",
        json_string(value.invariant),
        bounded_json(&value.detail),
        evidence
    )
}

/// Canonical semantic JSON. No host, time, PID, duration, or absolute scratch path
/// is admitted to this representation; telemetry belongs in a separately rooted
/// stream.
pub fn render_semantic_json(snapshot: &ProjectionSnapshot, request: ProjectionRequest) -> String {
    let behavior_note = if matches!(request.mode, Mode::Faithful) {
        "null".to_string()
    } else {
        json_string(DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME)
    };
    let payload = match snapshot {
        ProjectionSnapshot::Complete { diagnostics } => format!(
            "\"diagnostics\":[{}]",
            diagnostics
                .iter()
                .map(|diagnostic| diagnostic_json(diagnostic, request))
                .collect::<Vec<_>>()
                .join(",")
        ),
        ProjectionSnapshot::Inconclusive(value) => {
            format!("\"inconclusive\":{}", inconclusive_json(value))
        }
        ProjectionSnapshot::InternalFault(value) => {
            format!("\"internalFault\":{}", internal_fault_json(value))
        }
    };
    format!(
        concat!(
            "{{\"schema\":{},\"epoch\":{},\"mode\":{},\"frontend\":{},",
            "\"format\":{},\"channel\":{},\"ordering\":{},\"outcome\":{},",
            "\"authority\":{},\"exitClass\":{},\"behaviorNote\":{},{}",
            "}}\n"
        ),
        json_string(DIAGNOSTIC_PROJECTION_SCHEMA),
        json_string(request.epoch.as_str()),
        json_string(mode_name(request.mode)),
        json_string(request.frontend.as_str()),
        json_string(request.format.as_str()),
        json_string(request.channel.as_str()),
        json_string(request.ordering.as_str()),
        json_string(snapshot.outcome_class()),
        snapshot.authority().as_bool(),
        json_string(snapshot.exit_class().as_str()),
        behavior_note,
        payload
    )
}

/// Project one already-ordered typed snapshot to CLI or robot bytes.
pub fn project(
    request: ProjectionRequest,
    snapshot: &ProjectionSnapshot,
) -> Result<CliProjection, ProjectionRefusal> {
    validate_request(request)?;
    let rendered = match request.frontend {
        DiagnosticFrontend::Cli => render_human(snapshot, request),
        DiagnosticFrontend::Json => render_semantic_json(snapshot, request),
        DiagnosticFrontend::Lsp | DiagnosticFrontend::Library => {
            unreachable!("validated frontend")
        }
    };
    let (stdout, stderr) = match request.channel {
        DiagnosticChannel::Stdout => (rendered, String::new()),
        DiagnosticChannel::Stderr => (String::new(), rendered),
        DiagnosticChannel::Protocol | DiagnosticChannel::ReturnValue => {
            unreachable!("validated channel")
        }
    };
    Ok(CliProjection {
        stdout,
        stderr,
        exit: snapshot.exit_class(),
        semantic: snapshot.clone(),
    })
}
