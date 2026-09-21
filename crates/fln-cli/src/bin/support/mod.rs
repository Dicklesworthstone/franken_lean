#![forbid(unsafe_code)]

use std::io::Write;

#[cfg(test)]
use fln_core::diag::{
    DiagnosticChannel, DiagnosticColorPolicy, DiagnosticEpoch, DiagnosticFormat,
    DiagnosticFrontend, DiagnosticOrderPolicy, DiagnosticPathPolicy, ProjectionRequest,
    ProjectionSnapshot, Severity, StructuredDiagnostic,
};
#[cfg(test)]
use fln_core::outcome::BoundedText;
#[cfg(test)]
use fln_core::pos::Position;

pub(super) fn write_output(output: fln_cli::MultiplexerOutput) -> std::process::ExitCode {
    if std::io::stdout()
        .lock()
        .write_all(output.stdout.as_bytes())
        .is_err()
    {
        return std::process::ExitCode::from(1);
    }
    if std::io::stderr()
        .lock()
        .write_all(output.stderr.as_bytes())
        .is_err()
    {
        return std::process::ExitCode::from(1);
    }
    std::process::ExitCode::from(output.exit_code)
}

#[cfg(test)]
fn lsp_projection_request() -> ProjectionRequest {
    ProjectionRequest {
        epoch: DiagnosticEpoch::V4_32_0,
        mode: fln_core::mode::Mode::Sound,
        frontend: DiagnosticFrontend::Lsp,
        format: DiagnosticFormat::Lsp,
        channel: DiagnosticChannel::Protocol,
        color: DiagnosticColorPolicy::Never,
        path: DiagnosticPathPolicy::Preserve,
        ordering: DiagnosticOrderPolicy::SourcePositionV1,
    }
}

#[cfg(test)]
fn project_snapshot(
    request: ProjectionRequest,
    uri: &str,
    text: &str,
    snapshot: &ProjectionSnapshot,
) -> Vec<String> {
    match fln_server::project_with_sources(
        request,
        snapshot,
        &[fln_server::LspSource::new(uri, text)],
    ) {
        Ok(projection) => projection.messages,
        Err(_) => Vec::new(),
    }
}

pub(super) fn serve_lsp() -> fln_cli::MultiplexerOutput {
    fln_cli::serve_lsp()
}

#[cfg(test)]
fn lsp_error_snapshot(uri: &str, message: &str) -> ProjectionSnapshot {
    lsp_positioned_error_snapshot(uri, message, Position { line: 1, column: 0 })
}

#[cfg(test)]
fn lsp_positioned_error_snapshot(uri: &str, message: &str, pos: Position) -> ProjectionSnapshot {
    ProjectionSnapshot::Complete {
        diagnostics: vec![StructuredDiagnostic {
            file_name: BoundedText::new(uri.to_owned()),
            pos,
            end_pos: None,
            severity: Severity::Error,
            error_name: None,
            caption: BoundedText::new(message.to_owned()),
            body: BoundedText::new(String::new()),
            cause_class: "engine-error",
            related: Vec::new(),
            evidence: Vec::new(),
            omitted_related: 0,
            omitted_evidence: 0,
        }],
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_aware_projection_preserves_uri_and_utf16_coordinates() {
        let uri = "file:///tmp/Unsaved%20Document.lean";
        let snapshot = ProjectionSnapshot::Complete {
            diagnostics: vec![StructuredDiagnostic {
                file_name: BoundedText::new(uri.to_owned()),
                pos: Position { line: 1, column: 1 },
                end_pos: Some(Position { line: 1, column: 2 }),
                severity: Severity::Error,
                error_name: None,
                caption: BoundedText::new("planted".to_owned()),
                body: BoundedText::new(String::new()),
                cause_class: "source-aware-test",
                related: Vec::new(),
                evidence: Vec::new(),
                omitted_related: 0,
                omitted_evidence: 0,
            }],
        };
        let messages = project_snapshot(lsp_projection_request(), uri, "😀x", &snapshot);
        let publication = messages
            .iter()
            .find(|message| message.contains("textDocument/publishDiagnostics"))
            .expect("a diagnostic snapshot publishes diagnostics");
        assert!(publication.contains("\"uri\":\"file:///tmp/Unsaved%20Document.lean\""));
        assert!(!publication.contains("%2520"));
        assert!(publication.contains("\"start\":{\"line\":0,\"character\":2}"));
        assert!(publication.contains("\"end\":{\"line\":0,\"character\":3}"));
    }

    #[test]
    fn engine_error_snapshot_keeps_the_exact_document_identity() {
        let uri = "vscode-notebook-cell:/workspace/notebook.ipynb#cell-1";
        let ProjectionSnapshot::Complete { diagnostics } = lsp_error_snapshot(uri, "failure")
        else {
            panic!("engine errors are authoritative source diagnostics");
        };
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].file_name.text(), uri);
    }
}
