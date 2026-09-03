//! **fln-server** — Lantern's LSP diagnostic adapter (plan §14; beads
//! `franken_lean-wlan` and `franken_lean-v2p`).
//!
//! User diagnostics become `textDocument/publishDiagnostics` notifications.
//! Inconclusive and internal-fault outcomes use the distinct
//! `$/lean/diagnosticOutcome` channel: neither can be mislabeled as a user error or
//! silently converted into an empty diagnostic list.
//!
//! The `transport` module implements the Content-Length-framed base protocol.
//! The `dispatch` module owns the bounded JSON-RPC/LSP lifecycle: it parses root
//! envelope fields structurally, preserves integer and string request IDs,
//! refuses malformed IDs and unsupported Lean RPC calls, and routes
//! `didOpen`/Full-sync `didChange`/`didSave`/`didClose`. Latest source text is
//! retained under explicit document/byte limits and monotone client versions so
//! textless saves can re-check the newest valid snapshot; malformed transitions
//! invalidate stale retained source and close clears push diagnostics. Cursor-aware
//! goals, hover/completion/definition semantics, Lean RPC sessions, and persistent
//! elaboration/import state remain outside this bounded server slice.

#![forbid(unsafe_code)]

pub mod dispatch;
pub mod transport;

use std::collections::BTreeMap;

use fln_core::diag::{
    DIAGNOSTIC_PROJECTION_SCHEMA, DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME, DiagnosticChannel,
    DiagnosticColorPolicy, DiagnosticFormat, DiagnosticFrontend, DiagnosticPathPolicy, ExitClass,
    ProjectionRefusal, ProjectionRequest, ProjectionSnapshot, RelatedSpan, Severity,
    StructuredDiagnostic, StructuredInconclusive, StructuredInternalFault,
};
use fln_core::mode::Mode;
use fln_core::outcome::BoundedText;
use fln_core::pos::Position;

/// LSP 3.17's default and FrankenLean's explicitly advertised wire encoding.
pub const LSP_POSITION_ENCODING: &str = "utf-16";

/// One source snapshot available while projecting diagnostics.
///
/// [`fln_core::pos::Position`] stores Lean's 1-based line and zero-based
/// Unicode-codepoint column. LSP positions use zero-based lines and UTF-16 code
/// units. A projector therefore needs the exact source snapshot that authorized
/// a diagnostic; a path alone is insufficient for unsaved editor contents.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LspSource<'a> {
    pub uri: &'a str,
    pub text: &'a str,
}

impl<'a> LspSource<'a> {
    pub const fn new(uri: &'a str, text: &'a str) -> Self {
        Self { uri, text }
    }
}

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

pub fn json_string(value: &str) -> String {
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

fn is_windows_drive_path(path: &str) -> bool {
    let bytes = path.as_bytes();
    bytes.len() >= 2 && bytes[0].is_ascii_alphabetic() && bytes[1] == b':'
}

fn has_uri_scheme(value: &str) -> bool {
    let bytes = value.as_bytes();
    if !bytes.first().is_some_and(u8::is_ascii_alphabetic) {
        return false;
    }
    for byte in &bytes[1..] {
        match *byte {
            b':' => return true,
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'+' | b'-' | b'.' => {}
            _ => return false,
        }
    }
    false
}

fn append_percent_encoded(output: &mut String, value: &str, preserve_slash: bool) {
    const HEX: &[u8; 16] = b"0123456789ABCDEF";
    for byte in value.bytes() {
        if byte.is_ascii_alphanumeric()
            || matches!(byte, b'-' | b'.' | b'_' | b'~' | b':')
            || (preserve_slash && byte == b'/')
        {
            output.push(char::from(byte));
        } else {
            output.push('%');
            output.push(char::from(HEX[usize::from(byte >> 4)]));
            output.push(char::from(HEX[usize::from(byte & 0x0f)]));
        }
    }
}

fn file_uri(path: &str) -> String {
    let normalized = path.replace('\\', "/");
    if let Some(network_path) = normalized.strip_prefix("//") {
        let (authority, tail) = network_path
            .split_once('/')
            .map_or((network_path, ""), |(authority, tail)| (authority, tail));
        let mut encoded = String::from("file://");
        append_percent_encoded(&mut encoded, authority, false);
        encoded.push('/');
        append_percent_encoded(&mut encoded, tail, true);
        return encoded;
    }

    let mut encoded = String::from("file://");
    if !normalized.starts_with('/') {
        encoded.push('/');
    }
    append_percent_encoded(&mut encoded, &normalized, true);
    encoded
}

fn uri(path: &str, policy: DiagnosticPathPolicy) -> String {
    let projected = projected_path(path, policy);
    if !is_windows_drive_path(projected) && has_uri_scheme(projected) {
        projected.to_owned()
    } else {
        file_uri(projected)
    }
}

fn source_for_file<'a>(file_name: &str, sources: &[LspSource<'a>]) -> Option<&'a str> {
    let canonical_uri = uri(file_name, DiagnosticPathPolicy::Preserve);
    sources
        .iter()
        .find(|source| {
            source.uri == file_name
                || uri(source.uri, DiagnosticPathPolicy::Preserve) == canonical_uri
        })
        .map(|source| source.text)
}

fn line_without_terminator(line: &str) -> &str {
    line.strip_suffix('\r').unwrap_or(line)
}

fn utf16_column(line: &str, codepoint_column: usize) -> usize {
    line_without_terminator(line)
        .chars()
        .take(codepoint_column)
        .map(char::len_utf16)
        .sum()
}

/// Convert one Lean position to a valid LSP UTF-16 coordinate against the exact
/// document snapshot. Out-of-range lines and columns are deterministically
/// clamped to the end of the last available line rather than emitting an invalid
/// protocol coordinate.
fn source_lsp_position(source: &str, position: Position) -> (usize, usize) {
    let requested_line = position.line.saturating_sub(1);
    let mut current_line = 0usize;
    let mut start = 0usize;

    for (index, character) in source.char_indices() {
        if character != '\n' {
            continue;
        }
        let line = &source[start..index];
        if current_line == requested_line {
            return (current_line, utf16_column(line, position.column));
        }
        current_line = current_line.saturating_add(1);
        start = index.saturating_add(character.len_utf8());
    }

    let final_line = &source[start..];
    if current_line == requested_line {
        return (current_line, utf16_column(final_line, position.column));
    }
    (current_line, utf16_column(final_line, usize::MAX))
}

fn resolved_lsp_position(
    file_name: &str,
    position: Position,
    sources: &[LspSource<'_>],
) -> (usize, usize) {
    source_for_file(file_name, sources).map_or_else(
        || (position.line.saturating_sub(1), position.column),
        |source| source_lsp_position(source, position),
    )
}

fn lsp_position_json(position: (usize, usize)) -> String {
    let (line, character) = position;
    format!("{{\"line\":{line},\"character\":{character}}}")
}

fn lsp_range(file_name: &str, start: Position, end: Position, sources: &[LspSource<'_>]) -> String {
    let start = resolved_lsp_position(file_name, start, sources);
    let mut end = resolved_lsp_position(file_name, end, sources);
    if end < start {
        end = start;
    }
    format!(
        "{{\"start\":{},\"end\":{}}}",
        lsp_position_json(start),
        lsp_position_json(end)
    )
}

fn related_json(
    span: &RelatedSpan,
    policy: DiagnosticPathPolicy,
    sources: &[LspSource<'_>],
) -> String {
    format!(
        concat!(
            "{{\"location\":{{\"uri\":{},\"range\":{}}},",
            "\"message\":{},\"data\":{{\"truncated\":{}}}}}"
        ),
        json_string(&uri(span.file_name.text(), policy)),
        lsp_range(span.file_name.text(), span.start, span.end, sources),
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
    let mut message = String::new();
    if !diagnostic.caption.text().is_empty() {
        message.push_str(diagnostic.caption.text());
        message.push_str(":\n");
        if diagnostic.caption.truncated() {
            message.push_str(&format!(
                "[diagnostic caption truncated after {} bytes]\n",
                BoundedText::LIMIT
            ));
        }
    }
    message.push_str(diagnostic.body.text());
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

fn lsp_diagnostic(
    diagnostic: &StructuredDiagnostic,
    request: ProjectionRequest,
    sources: &[LspSource<'_>],
) -> String {
    let end = diagnostic.end_pos.unwrap_or(diagnostic.pos);
    let behavior_note = if matches!(request.mode, Mode::Faithful) {
        "null".to_string()
    } else {
        json_string(DIAGNOSTIC_SOUND_BEHAVIOR_NOTE_NAME)
    };
    let related = diagnostic
        .related
        .iter()
        .map(|span| related_json(span, request.path, sources))
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
            "{{\"range\":{},\"severity\":{},",
            "\"code\":{},\"source\":\"FrankenLean\",\"message\":{},",
            "\"relatedInformation\":[{}],\"data\":{{\"schema\":{},",
            "\"causeClass\":{},\"behaviorNote\":{},\"bodyTruncated\":{},\"evidence\":[{}],",
            "\"omittedRelated\":{},\"omittedEvidence\":{}}}}}"
        ),
        lsp_range(diagnostic.file_name.text(), diagnostic.pos, end, sources),
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
    sources: &[LspSource<'_>],
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
                .map(|diagnostic| lsp_diagnostic(diagnostic, request, sources))
                .collect::<Vec<_>>()
                .join(",");
            format!(
                concat!(
                    "{{\"jsonrpc\":\"2.0\",\"method\":\"textDocument/publishDiagnostics\",",
                    "\"params\":{{\"uri\":{},\"version\":null,\"diagnostics\":[{}]}}}}"
                ),
                json_string(&uri(&file, DiagnosticPathPolicy::Preserve)),
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

/// Project a snapshot whose positions are already in LSP-compatible columns.
///
/// This compatibility entry point preserves the original API. Call
/// [`project_with_sources`] whenever diagnostics can follow non-BMP characters;
/// without source snapshots a Unicode-codepoint column cannot be converted to
/// the UTF-16 units required by LSP.
pub fn project(
    request: ProjectionRequest,
    snapshot: &ProjectionSnapshot,
) -> Result<LspProjection, ProjectionRefusal> {
    project_with_sources(request, snapshot, &[])
}

/// Project diagnostics using the exact source snapshots that authorized them.
/// Primary and related positions are independently resolved by URI/path and
/// converted from Lean codepoint columns to LSP UTF-16 code units.
pub fn project_with_sources(
    request: ProjectionRequest,
    snapshot: &ProjectionSnapshot,
    sources: &[LspSource<'_>],
) -> Result<LspProjection, ProjectionRefusal> {
    validate_request(request)?;
    let messages = match snapshot {
        ProjectionSnapshot::Complete { diagnostics } => {
            complete_messages(diagnostics, request, sources)
        }
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

#[cfg(test)]
mod tests {
    use super::*;
    use fln_core::diag::{DiagnosticEpoch, DiagnosticOrderPolicy};

    fn request() -> ProjectionRequest {
        ProjectionRequest {
            epoch: DiagnosticEpoch::V4_32_0,
            mode: Mode::Sound,
            frontend: DiagnosticFrontend::Lsp,
            format: DiagnosticFormat::Lsp,
            channel: DiagnosticChannel::Protocol,
            color: DiagnosticColorPolicy::Never,
            path: DiagnosticPathPolicy::Preserve,
            ordering: DiagnosticOrderPolicy::SourcePositionV1,
        }
    }

    fn diagnostic() -> StructuredDiagnostic {
        StructuredDiagnostic {
            file_name: BoundedText::new("/tmp/Emoji.lean"),
            pos: Position { line: 1, column: 2 },
            end_pos: Some(Position { line: 1, column: 3 }),
            severity: Severity::Error,
            error_name: None,
            caption: BoundedText::new("parser"),
            body: BoundedText::new("unexpected token"),
            cause_class: "SyntaxFailure",
            related: vec![RelatedSpan::new(
                "/tmp/Other.lean",
                Position { line: 1, column: 1 },
                Position { line: 1, column: 2 },
                "introduced here",
            )],
            evidence: Vec::new(),
            omitted_related: 0,
            omitted_evidence: 0,
        }
    }

    #[test]
    fn source_positions_convert_codepoints_to_utf16_for_primary_and_related_ranges() {
        let snapshot = ProjectionSnapshot::Complete {
            diagnostics: vec![diagnostic()],
        };
        let projection = project_with_sources(
            request(),
            &snapshot,
            &[
                LspSource::new("file:///tmp/Emoji.lean", "a😀b\nlast"),
                LspSource::new("/tmp/Other.lean", "🤖z"),
            ],
        )
        .expect("the LSP projection tuple is supported");
        let message = &projection.messages[0];
        assert!(message.contains(
            "\"start\":{\"line\":0,\"character\":3},\"end\":{\"line\":0,\"character\":4}"
        ));
        assert!(message.contains(
            "\"start\":{\"line\":0,\"character\":2},\"end\":{\"line\":0,\"character\":3}"
        ));
        assert!(message.contains("\"message\":\"parser:\\nunexpected token"));
    }

    #[test]
    fn encoded_editor_uri_matches_raw_diagnostic_path() {
        let mut diagnostic = diagnostic();
        diagnostic.file_name = BoundedText::new("/tmp/Emoji File.lean");
        diagnostic.related.clear();
        let projection = project_with_sources(
            request(),
            &ProjectionSnapshot::Complete {
                diagnostics: vec![diagnostic],
            },
            &[LspSource::new("file:///tmp/Emoji%20File.lean", "a😀b")],
        )
        .expect("the LSP projection tuple is supported");
        let message = &projection.messages[0];
        assert!(message.contains("\"uri\":\"file:///tmp/Emoji%20File.lean\""));
        assert!(message.contains("\"start\":{\"line\":0,\"character\":3}"));
    }

    #[test]
    fn source_positions_clamp_to_the_last_valid_utf16_coordinate() {
        assert_eq!(
            source_lsp_position(
                "first\n🤖z",
                Position {
                    line: usize::MAX,
                    column: usize::MAX,
                }
            ),
            (1, 3)
        );
        assert_eq!(
            source_lsp_position(
                "a\r\n",
                Position {
                    line: 1,
                    column: 99
                }
            ),
            (0, 1),
            "the CRLF terminator is not part of the LSP line character count"
        );
    }

    #[test]
    fn file_paths_are_canonical_document_uris() {
        assert_eq!(
            uri("/tmp/My #1%.lean", DiagnosticPathPolicy::Preserve),
            "file:///tmp/My%20%231%25.lean"
        );
        assert_eq!(
            uri("Foo.lean", DiagnosticPathPolicy::Preserve),
            "file:///Foo.lean"
        );
        assert_eq!(
            uri(r"C:\Lean Files\Foo.lean", DiagnosticPathPolicy::Preserve),
            "file:///C:/Lean%20Files/Foo.lean"
        );
        assert_eq!(
            uri(
                r"\\server\share\Foo Bar.lean",
                DiagnosticPathPolicy::Preserve
            ),
            "file://server/share/Foo%20Bar.lean"
        );
        assert_eq!(
            uri("untitled:Untitled-1", DiagnosticPathPolicy::Preserve),
            "untitled:Untitled-1"
        );
        assert_eq!(
            uri("/tmp/Foo.lean", DiagnosticPathPolicy::Basename),
            "file:///Foo.lean"
        );
    }

    #[test]
    fn reversed_ranges_are_clamped_to_zero_width() {
        let mut diagnostic = diagnostic();
        diagnostic.pos = Position { line: 1, column: 3 };
        diagnostic.end_pos = Some(Position { line: 1, column: 1 });
        diagnostic.related.clear();
        let projection = project_with_sources(
            request(),
            &ProjectionSnapshot::Complete {
                diagnostics: vec![diagnostic],
            },
            &[LspSource::new("file:///tmp/Emoji.lean", "abcd")],
        )
        .expect("the LSP projection tuple is supported");
        assert!(projection.messages[0].contains(
            "\"start\":{\"line\":0,\"character\":3},\"end\":{\"line\":0,\"character\":3}"
        ));
    }

    #[test]
    fn existing_file_uris_are_not_prefixed_twice() {
        let mut diagnostic = diagnostic();
        diagnostic.file_name = BoundedText::new("file:///tmp/Emoji.lean");
        diagnostic.related.clear();
        let projection = project(
            request(),
            &ProjectionSnapshot::Complete {
                diagnostics: vec![diagnostic],
            },
        )
        .expect("the LSP projection tuple is supported");
        assert!(projection.messages[0].contains("\"uri\":\"file:///tmp/Emoji.lean\""));
        assert!(!projection.messages[0].contains("file://file://"));
    }
}
