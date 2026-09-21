//! Native proof-library diagnostics on a long-lived, stack-calibrated worker.
use super::imports::editor::{self, Sources};
use super::*;
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckError, SourceModuleCheckLimits, SourceModuleSession,
};
use fln_server::dispatch::OpenDocumentSource;
use std::sync::mpsc::{Receiver, SyncSender, sync_channel};

mod dependencies;
mod render;
use fln::source_check::inspect::{ObservationKind, SourceObservation};
use fln_server::dispatch::semantic::{Answer, Query, QueryKind};

enum Request {
    Check(Sources),
    Inspect(Sources, usize, QueryKind),
}
enum Response {
    Diagnostics(Vec<String>),
    Semantic(Result<Option<Answer>, String>),
}

pub(crate) struct Checker {
    worker: Option<Worker>,
    dependencies: dependencies::Dependencies,
}
struct Worker {
    input: SyncSender<Option<Request>>,
    output: Receiver<Response>,
    thread: Option<std::thread::JoinHandle<()>>,
}
impl Worker {
    fn new() -> std::io::Result<Self> {
        let (input, requests) = sync_channel::<Option<Request>>(1);
        let (responses, output) = sync_channel(1);
        let thread = std::thread::Builder::new()
            .name("fln-lsp-proof-check".to_owned())
            .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
            .spawn(move || {
                let mut session = None;
                while let Ok(Some(request)) = requests.recv() {
                    let response = match request {
                        Request::Check(sources) => {
                            Response::Diagnostics(check_sources(&mut session, &sources))
                        }
                        Request::Inspect(sources, offset, kind) => Response::Semantic(
                            inspect_sources(&mut session, &sources, offset, kind),
                        ),
                    };
                    if responses.send(response).is_err() {
                        break;
                    }
                }
            })?;
        Ok(Self {
            input,
            output,
            thread: Some(thread),
        })
    }
}
impl Drop for Worker {
    fn drop(&mut self) {
        let _ = self.input.send(None);
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}
impl Checker {
    pub(crate) fn new() -> Self {
        Self {
            worker: None,
            dependencies: dependencies::Dependencies::default(),
        }
    }
    pub(crate) fn check(
        &mut self,
        uri: &str,
        text: &str,
        documents: &[OpenDocumentSource<'_>],
    ) -> Vec<String> {
        self.dependencies.begin(uri, documents);
        if text.len() > SOURCE_RUN_DEFAULT_MAX_BYTES {
            return project(
                uri,
                text,
                &nonanswer("resource", "editor source exceeds its byte limit"),
            );
        }
        // Header parsing uses the complete lexical source view. Keep its exact
        // error offset instead of flattening a syntax error into an I/O failure.
        match fln::source_check::modules::parse_source_header(text.as_bytes()) {
            Ok(header) if header.imports.is_empty() => self.dependencies.no_imports(uri),
            Ok(_) => {}
            Err(error) => {
                return project(
                    uri,
                    text,
                    &diagnostic(
                        uri,
                        text.as_bytes(),
                        error.primary_offset().map_or(0, |p| p.0),
                        &error.to_string(),
                    ),
                );
            }
        }
        let sources = match editor::load(uri, text, documents, SOURCE_RUN_DEFAULT_MAX_BYTES) {
            Ok(sources) => sources,
            Err(error) => {
                let snapshot = failure(uri, text.as_bytes(), 0, error.class, &error.detail);
                return project(uri, text, &snapshot);
            }
        };
        self.dependencies.loaded(uri, &sources.uris);
        if self.worker.is_none() {
            match Worker::new() {
                Ok(worker) => self.worker = Some(worker),
                Err(error) => {
                    return project(
                        uri,
                        text,
                        &nonanswer(
                            "resource",
                            &format!("could not start proof worker: {error}"),
                        ),
                    );
                }
            }
        }
        let worker = self.worker.as_ref().expect("started worker");
        if worker.input.send(Some(Request::Check(sources))).is_ok()
            && let Ok(Response::Diagnostics(messages)) = worker.output.recv()
        {
            return messages;
        }
        // A dead worker never leaves a previous success authoritative. A later
        // check starts with a fresh seed/cache rather than a half-mutated world.
        self.worker = None;
        project(
            uri,
            text,
            &fault("lsp-proof-worker", "proof worker stopped without a result"),
        )
    }
}

fn project(uri: &str, text: &str, snapshot: &ProjectionSnapshot) -> Vec<String> {
    let request = ProjectionRequest {
        epoch: fln_core::diag::DiagnosticEpoch::V4_32_0,
        mode: Mode::Sound,
        frontend: DiagnosticFrontend::Lsp,
        format: DiagnosticFormat::Lsp,
        channel: DiagnosticChannel::Protocol,
        color: DiagnosticColorPolicy::Never,
        path: DiagnosticPathPolicy::Preserve,
        ordering: fln_core::diag::DiagnosticOrderPolicy::SourcePositionV1,
    };
    fln_server::project_with_sources(request, snapshot, &[fln_server::LspSource::new(uri, text)])
        .map(|projection| projection.messages)
        .unwrap_or_default()
}
fn nonanswer(class: &'static str, detail: &str) -> ProjectionSnapshot {
    ProjectionSnapshot::Inconclusive(StructuredInconclusive {
        cause_class: class,
        detail: BoundedText::new(detail.to_owned()),
        diagnostic: None,
        progress: None,
    })
}
fn fault(invariant: &'static str, detail: &str) -> ProjectionSnapshot {
    ProjectionSnapshot::InternalFault(StructuredInternalFault {
        invariant,
        detail: BoundedText::new(detail.to_owned()),
        evidence: None,
    })
}
fn diagnostic(uri: &str, source: &[u8], offset: usize, message: &str) -> ProjectionSnapshot {
    ProjectionSnapshot::Complete {
        diagnostics: vec![StructuredDiagnostic {
            // Preserve the entire URI; re-encoding an already escaped path
            // would disconnect this publication from its open document.
            file_name: BoundedText::new(uri.to_owned()),
            pos: source_position_at(source, offset)
                .unwrap_or(fln_core::pos::Position { line: 1, column: 0 }),
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
fn failure(
    uri: &str,
    source: &[u8],
    offset: usize,
    class: &'static str,
    detail: &str,
) -> ProjectionSnapshot {
    match class {
        "internal-fault" => fault("source-check", detail),
        "resource" | "inconclusive" | "cancelled" => nonanswer(class, detail),
        _ => diagnostic(uri, source, offset, detail),
    }
}

fn check_sources(session: &mut Option<SourceModuleSession>, sources: &Sources) -> Vec<String> {
    let uri = &sources.uris[0];
    // Source bytes came from validated UTF-8 editor text or the native lexer.
    let text = std::str::from_utf8(&sources.sources[0]).expect("editor source is UTF-8");
    if let Err(snapshot) = ensure_session(session) {
        return project(uri, text, &snapshot);
    }
    let inputs: Vec<_> = sources
        .names
        .iter()
        .zip(&sources.sources)
        .map(|(name, source)| fln::SourceModuleInput { name, source })
        .collect();
    match session
        .as_mut()
        .expect("initialized checker")
        .check(&inputs, &sources.names[0])
    {
        Ok(fln::Outcome::Complete(result)) => {
            let mut messages = project(
                uri,
                text,
                &ProjectionSnapshot::Complete {
                    diagnostics: Vec::new(),
                },
            );
            messages.insert(0, format!(
                "{{\"jsonrpc\":\"2.0\",\"method\":\"$/frankenLean/sourceCheck\",\"params\":{{\"uri\":{},\"files\":{},\"commands\":{},\"theorems\":{},\"reusedModules\":{},\"elaboratedModules\":{},\"replayedDeclarations\":{},\"executed\":false}}}}",
                json_string(uri), result.checked.checked.files, result.checked.checked.commands,
                result.checked.checked.theorems, result.reused_modules, result.elaborated_modules,
                result.checked.replayed_declarations,
            ));
            messages
        }
        Ok(fln::Outcome::Inconclusive(reason)) => project(
            uri,
            text,
            &nonanswer("source-check", &format!("{reason:?}")),
        ),
        Ok(fln::Outcome::InternalFault(reason)) => {
            project(uri, text, &fault("source-check", &format!("{reason:?}")))
        }
        Err(error) => {
            let offset = match &error {
                SourceModuleCheckError::Header { module, error } if module == &sources.names[0] => {
                    error.primary_offset().map_or(0, |p| p.0)
                }
                SourceModuleCheckError::Source {
                    module,
                    error:
                        fln::SourceCheckError::Command { offset, .. }
                        | fln::SourceCheckError::Scope { offset, .. },
                } if module == &sources.names[0] => *offset,
                _ => 0,
            };
            let (class, _, _) = error.disposition();
            project(
                uri,
                text,
                &failure(uri, &sources.sources[0], offset, class, &error.to_string()),
            )
        }
    }
}

impl fln_server::dispatch::WorkspaceChecker for Checker {
    fn semantic_queries(&self) -> bool {
        true
    }
    fn query(
        &mut self,
        query: Query<'_>,
        documents: &[OpenDocumentSource<'_>],
    ) -> Result<Option<Answer>, String> {
        if query.text.len() > SOURCE_RUN_DEFAULT_MAX_BYTES {
            return Err("editor source exceeds its byte limit".to_owned());
        }
        let sources = editor::load(
            query.uri,
            query.text,
            documents,
            SOURCE_RUN_DEFAULT_MAX_BYTES,
        )
        .map_err(|error| error.detail)?;
        if self.worker.is_none() {
            self.worker =
                Some(Worker::new().map_err(|e| format!("could not start proof worker: {e}"))?);
        }
        let worker = self.worker.as_ref().expect("started query worker");
        if worker
            .input
            .send(Some(Request::Inspect(sources, query.offset, query.kind)))
            .is_ok()
            && let Ok(Response::Semantic(result)) = worker.output.recv()
        {
            return result;
        }
        self.worker = None;
        Err("proof worker stopped without a semantic result".to_owned())
    }

    fn check(
        &mut self,
        uri: &str,
        text: &str,
        documents: &[OpenDocumentSource<'_>],
    ) -> Vec<String> {
        Checker::check(self, uri, text, documents)
    }
    fn affected(
        &mut self,
        changed: &[String],
        documents: &[OpenDocumentSource<'_>],
    ) -> Vec<String> {
        self.dependencies.affected(changed, documents)
    }
}

fn ensure_session(
    session: &mut Option<SourceModuleSession>,
) -> Result<(), Box<ProjectionSnapshot>> {
    if session.is_none() {
        let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(
            SOURCE_RUN_KERNEL_STACK_BYTES,
        ));
        let engine = match fln::Engine::with_coercion_seed(admission) {
            Ok(fln::Outcome::Complete(engine)) => engine,
            Ok(fln::Outcome::Inconclusive(reason)) => {
                return Err(Box::new(nonanswer("seed", &format!("{reason:?}"))));
            }
            Ok(fln::Outcome::InternalFault(reason)) => {
                return Err(Box::new(fault("seed-admission", &format!("{reason:?}"))));
            }
            Err(error) => return Err(Box::new(fault("seed-admission", &error.to_string()))),
        };
        let mut limits = fln::SourceCheckLimits::new(admission);
        limits.max_bytes = SOURCE_RUN_DEFAULT_MAX_BYTES;
        *session = Some(SourceModuleSession::new(
            engine,
            fln::KVMap::new(),
            SourceModuleCheckLimits::new(limits),
            SourceModuleCacheLimits::default(),
        ));
    }
    Ok(())
}

fn inspect_sources(
    session: &mut Option<SourceModuleSession>,
    sources: &Sources,
    offset: usize,
    kind: QueryKind,
) -> Result<Option<Answer>, String> {
    ensure_session(session).map_err(|_| "native seed admission did not complete".to_owned())?;
    let inputs: Vec<_> = sources
        .names
        .iter()
        .zip(&sources.sources)
        .map(|(name, source)| fln::SourceModuleInput { name, source })
        .collect();
    let wanted = match kind {
        QueryKind::Goals => ObservationKind::Goals,
        QueryKind::Hover => ObservationKind::Term,
    };
    let result = session
        .as_mut()
        .expect("initialized semantic session")
        .inspect(&inputs, &sources.names[0], offset, wanted)
        .map_err(|e| e.to_string())?;
    let inspected = match result {
        fln::Outcome::Complete(result) => result,
        fln::Outcome::Inconclusive(reason) => {
            return Err(format!("native inspection was inconclusive: {reason:?}"));
        }
        fln::Outcome::InternalFault(reason) => {
            return Err(format!("native inspection fault: {reason:?}"));
        }
    };
    Ok(match inspected.observation {
        None => None,
        Some(SourceObservation::Goals { goals, .. }) => {
            if goals.len() > 256 {
                return Err("too many goals for one editor response".to_owned());
            }
            let mut displayed = Vec::new();
            let mut total = 0usize;
            for goal in goals {
                let mut renderer = render::Renderer::new();
                let mut names = Vec::new();
                for local in goal.locals.decls() {
                    names.push(renderer.local(&local.id, &local.user_name)?);
                }
                let mut lines = Vec::new();
                for (local, name) in goal.locals.decls().iter().zip(names) {
                    let type_ = renderer.expr(&local.type_)?;
                    let value = match &local.value {
                        Some(v) => format!(" := {}", renderer.expr(v)?),
                        None => String::new(),
                    };
                    lines.push(format!("{name} : {type_}{value}"));
                }
                lines.push(format!("⊢ {}", renderer.expr(&goal.target)?));
                let text = lines.join("\n");
                total = total
                    .checked_add(text.len())
                    .filter(|bytes| *bytes <= 64 * 1024)
                    .ok_or("goal display exceeded its byte limit")?;
                displayed.push(text);
            }
            Some(Answer::Goals { goals: displayed })
        }
        Some(SourceObservation::Term {
            range,
            expression,
            type_,
            locals,
        }) => {
            let mut renderer = render::Renderer::new();
            for local in locals.decls() {
                renderer.local(&local.id, &local.user_name)?;
            }
            Some(Answer::Hover {
                contents: format!(
                    "{} : {}",
                    renderer.expr(&expression)?,
                    renderer.expr(&type_)?
                ),
                range,
            })
        }
    })
}
