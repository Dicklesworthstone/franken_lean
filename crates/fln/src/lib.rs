//! **fln** — the embeddable library facade (plan §17.2).
//!
//! The first live surface is the typed diagnostic return adapter (bead
//! `franken_lean-wlan`). It deliberately returns the shared structured value rather
//! than serializing it: an embedder receives the same cause, authority, positions,
//! related spans, evidence, and truncation facts as every other frontend.

#![forbid(unsafe_code)]

use fln_core::diag::{
    DiagnosticChannel, DiagnosticColorPolicy, DiagnosticFormat, DiagnosticFrontend, ExitClass,
    ProjectionRefusal, ProjectionRequest, ProjectionSnapshot,
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LibraryProjection {
    pub request: ProjectionRequest,
    pub disposition: ExitClass,
    pub semantic: ProjectionSnapshot,
}

pub fn project_diagnostics(
    request: ProjectionRequest,
    snapshot: &ProjectionSnapshot,
) -> Result<LibraryProjection, ProjectionRefusal> {
    request
        .validated_product_class()
        .map_err(ProjectionRefusal::Mode)?;
    if request.frontend != DiagnosticFrontend::Library {
        return Err(ProjectionRefusal::Frontend {
            expected: DiagnosticFrontend::Library,
            actual: request.frontend,
        });
    }
    if request.format != DiagnosticFormat::Typed {
        return Err(ProjectionRefusal::UnsupportedFormat {
            frontend: request.frontend,
            format: request.format,
        });
    }
    if request.channel != DiagnosticChannel::ReturnValue {
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
    Ok(LibraryProjection {
        request,
        disposition: snapshot.exit_class(),
        semantic: snapshot.clone(),
    })
}
