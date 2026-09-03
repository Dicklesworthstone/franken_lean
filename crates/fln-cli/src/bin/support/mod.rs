use std::ffi::OsString;
use std::io::{BufReader, BufWriter, Write};

use fln_core::diag::{
    DiagnosticChannel, DiagnosticColorPolicy, DiagnosticEpoch, DiagnosticFormat,
    DiagnosticFrontend, DiagnosticOrderPolicy, DiagnosticPathPolicy, ProjectionRequest,
    ProjectionSnapshot, Severity, StructuredDiagnostic, StructuredInconclusive,
    StructuredInternalFault,
};
use fln_core::outcome::BoundedText;
use fln_core::pos::Position;

const SOURCE_RUN_KERNEL_STACK_BYTES: usize = 2 * 1024 * 1024;

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

pub(super) fn fln_server_command(arguments: &[OsString]) -> Option<fln_cli::MultiplexerOutput> {
    let Some(first) = arguments.first() else {
        return None;
    };
    if first != "serve-lsp" {
        return None;
    }
    if arguments.len() != 1 {
        return Some(fln_cli::MultiplexerOutput {
            stdout: String::new(),
            stderr: "fln: serve-lsp does not accept arguments\n".to_owned(),
            exit_code: 2,
        });
    }
    Some(serve_lsp())
}

pub(super) fn lean_server_command(arguments: &[OsString]) -> Option<fln_cli::MultiplexerOutput> {
    matches!(arguments, [argument] if argument == "--server").then(serve_lsp)
}

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

fn project_snapshot(
    request: ProjectionRequest,
    uri: &str,
    text: &str,
    snapshot: &ProjectionSnapshot,
) -> Vec<String> {
    fln_server::project_with_sources(
        request,
        snapshot,
        &[fln_server::LspSource::new(uri, text)],
    )
    .map(|projection| projection.messages)
    .unwrap_or_default()
}

pub(super) fn serve_lsp() -> fln_cli::MultiplexerOutput {
    let stdin = std::io::stdin();
    let stdout = std::io::stdout();
    let mut reader = BufReader::new(stdin.lock());
    let mut writer = BufWriter::new(stdout.lock());
    let request = lsp_projection_request();
    let mut on_did_open = move |uri: &str, text: &str| {
        let snapshot = lsp_source_snapshot(uri, text.as_bytes());
        project_snapshot(request, uri, text, &snapshot)
    };

    let outcome = fln_server::dispatch::serve(&mut reader, &mut writer, &mut on_did_open);
    if let Err(error) = writer.flush() {
        return fln_cli::MultiplexerOutput {
            stdout: String::new(),
            stderr: format!("fln serve-lsp: transport flush error: {error}\n"),
            exit_code: 1,
        };
    }
    match outcome {
        Ok(outcome) if outcome.clean => fln_cli::MultiplexerOutput {
            stdout: String::new(),
            stderr: String::new(),
            exit_code: 0,
        },
        Ok(_) => fln_cli::MultiplexerOutput {
            stdout: String::new(),
            stderr: "fln serve-lsp: server exited without clean shutdown\n".to_owned(),
            exit_code: 1,
        },
        Err(error) => fln_cli::MultiplexerOutput {
            stdout: String::new(),
            stderr: format!("fln serve-lsp: transport error: {error}\n"),
            exit_code: 1,
        },
    }
}

fn lsp_source_snapshot(uri: &str, source: &[u8]) -> ProjectionSnapshot {
    let kernel_budget = fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES);
    let engine = match fln::Engine::with_source_seed(fln::EngineAdmissionLimits::new(kernel_budget)) {
        Ok(fln::Outcome::Complete(engine)) => engine,
        Ok(fln::Outcome::Inconclusive(inconclusive)) => {
            return ProjectionSnapshot::Inconclusive(StructuredInconclusive {
                cause_class: "seed",
                detail: BoundedText::new(format!("{inconclusive:?}")),
                diagnostic: None,
                progress: None,
            });
        }
        Ok(fln::Outcome::InternalFault(fault)) => {
            return ProjectionSnapshot::InternalFault(StructuredInternalFault {
                invariant: "seed-admission",
                detail: BoundedText::new(format!("{fault:?}")),
                evidence: None,
            });
        }
        Err(error) => return lsp_error_snapshot(uri, &error.to_string()),
    };
    let options = fln::KVMap::new();
    let limits = fln::EngineExecutionLimits::new(kernel_budget);
    match engine.execute_source_commands_with_checks(source, &options, limits) {
        Ok(fln::Outcome::Complete(_)) => ProjectionSnapshot::Complete {
            diagnostics: Vec::new(),
        },
        Ok(fln::Outcome::Inconclusive(inconclusive)) => {
            ProjectionSnapshot::Inconclusive(StructuredInconclusive {
                cause_class: "source-check",
                detail: BoundedText::new(format!("{inconclusive:?}")),
                diagnostic: None,
                progress: None,
            })
        }
        Ok(fln::Outcome::InternalFault(fault)) => {
            ProjectionSnapshot::InternalFault(StructuredInternalFault {
                invariant: "source-check",
                detail: BoundedText::new(format!("{fault:?}")),
                evidence: None,
            })
        }
        Err(error) => lsp_error_snapshot(uri, &error.to_string()),
    }
}

fn lsp_error_snapshot(uri: &str, message: &str) -> ProjectionSnapshot {
    ProjectionSnapshot::Complete {
        diagnostics: vec![StructuredDiagnostic {
            file_name: BoundedText::new(uri.to_owned()),
            pos: Position { line: 1, column: 0 },
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
        let ProjectionSnapshot::Complete { diagnostics } = lsp_error_snapshot(uri, "failure") else {
            panic!("engine errors are authoritative source diagnostics");
        };
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(diagnostics[0].file_name.text(), uri);
    }

    #[test]
    fn server_argument_selection_is_exact() {
        assert!(fln_server_command(&[OsString::from("other")]).is_none());
        let invalid = fln_server_command(&[
            OsString::from("serve-lsp"),
            OsString::from("unexpected"),
        ])
        .expect("serve-lsp owns its argument prefix");
        assert_eq!(invalid.exit_code, 2);
        assert!(invalid.stdout.is_empty());
        assert!(invalid.stderr.contains("does not accept arguments"));
        assert!(lean_server_command(&[OsString::from("--server"), OsString::from("extra")]).is_none());
    }
}
