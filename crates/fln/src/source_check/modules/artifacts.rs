//! Per-module, checked declaration products for the native Lake `.olean` facet.
use super::*;
use std::sync::Arc;

/// One basic (pre-module-system) `.olean`, containing only its own constants.
#[derive(Debug)]
pub struct SourceModuleArtifact {
    pub name: Name,
    pub bytes: Vec<u8>,
    pub report: OleanModuleWriteReport,
}

/// All products of a successfully checked import closure. No filesystem writes
/// occur here, and no partial products escape a failed check or encoding.
#[derive(Debug)]
pub struct SourceModuleBuild {
    pub checked: SourceModuleCheck,
    pub artifacts: Vec<SourceModuleArtifact>,
    /// Module snapshots reused from this process's checked build session.
    /// Every returned artifact is still encoded under this call's writer budget.
    pub reused_modules: usize,
    pub elaborated_modules: usize,
}

#[derive(Debug)]
pub enum SourceModuleBuildError {
    /// An ambient seed or caller-created environment has no import identity.
    UnboundBase,
    Check(SourceModuleCheckError),
    Encode {
        module: Name,
        error: OleanWriteError,
    },
}

impl std::fmt::Display for SourceModuleBuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnboundBase => f.write_str(
                "module artifacts require an empty base or rechecked .olean imports; an ambient source seed cannot be exported as a library",
            ),
            Self::Check(error) => error.fmt(f),
            Self::Encode { module, error } => write!(
                f,
                "encoding module `{}`: {error}",
                module.to_display_string()
            ),
        }
    }
}
impl std::error::Error for SourceModuleBuildError {}
impl SourceModuleBuildError {
    pub fn disposition(&self) -> (&'static str, bool, u8) {
        match self {
            Self::UnboundBase => ("input", false, 1),
            Self::Check(error) => error.disposition(),
            Self::Encode { error, .. } => match error {
                OleanWriteError::Budget { .. } => ("resource", false, 3),
                OleanWriteError::Unsupported { .. } => ("unsupported", false, 3),
                OleanWriteError::Contract { .. } | OleanWriteError::Region(_) => {
                    ("internal-fault", false, 4)
                }
            },
        }
    }
}

pub(super) struct PendingArtifact {
    name: Name,
    imports: Vec<OleanModuleImport>,
    constants: Vec<ConstantInfo>,
}

/// Every artifact must name its entire external base, directly or through local
/// dependencies. Import receipts project that base per module; legacy explicit
/// Engine callers must supply the exact world themselves. Neither path may
/// let an unrelated external sibling leak names into a module's declarations.
pub(super) fn validate_import_scope(
    base: &Engine,
    index: usize,
    dependencies: &[usize],
    plan: &graph::Plan,
    modules: &[SourceModuleInput<'_>],
    meter: &mut Meter,
) -> Result<(), SourceModuleCheckError> {
    meter.work(modules.len())?;
    let local: BTreeSet<_> = modules.iter().map(|module| module.name).collect();
    let mut work = Vec::new();
    for source in dependencies.iter().copied().chain(std::iter::once(index)) {
        for import in &plan.headers[source].imports {
            meter.work(1)?;
            if !local.contains(import) {
                work.push(import.clone());
            }
        }
    }
    let mut visible = BTreeSet::new();
    while let Some(import) = work.pop() {
        meter.work(1)?;
        if visible.insert(import.clone())
            && let Some(dependencies) = base.imported_module_dependencies.get(&import)
        {
            meter.work(dependencies.len())?;
            work.extend(dependencies.iter().cloned());
        }
    }
    for import in base.imported_modules() {
        meter.work(1)?;
        if !visible.contains(import) {
            return Err(SourceModuleCheckError::AmbientImport {
                module: modules[index].name.clone(),
                import: import.clone(),
            });
        }
    }
    Ok(())
}

impl PendingArtifact {
    pub(super) fn capture(
        name: &Name,
        header: &SourceHeader,
        base: &Environment,
        checked: &Environment,
        meter: &mut Meter,
    ) -> Result<Self, SourceModuleCheckError> {
        let mut constants = Vec::new();
        for (name, constant) in checked.constants() {
            meter.work(1)?;
            if !base.contains(name) {
                constants.push(constant.clone());
            }
        }
        // Lean.Elab.HeaderSyntax.imports adds two Init imports (ordinary and
        // meta) unless `prelude` is present. Graph planning inserts the first
        // name, and retains every explicit import row after it.
        let mut imports = Vec::new();
        for (index, module) in header.imports.iter().enumerate() {
            imports.push(OleanModuleImport {
                module: module.clone(),
                import_all: false,
                is_exported: true,
                is_meta: false,
            });
            if index == 0 && !header.prelude {
                imports.push(OleanModuleImport {
                    module: module.clone(),
                    import_all: false,
                    is_exported: true,
                    is_meta: true,
                });
            }
        }
        Ok(Self {
            name: name.clone(),
            imports,
            constants,
        })
    }

    fn encode(
        &self,
        budget: OleanWriteBudget,
    ) -> Result<SourceModuleArtifact, SourceModuleBuildError> {
        let encoded = encode_olean_module(
            OleanModuleWriteInput {
                is_module: false,
                imports: &self.imports,
                constants: &self.constants,
                extra_const_names: &[],
            },
            OleanWriteHeader {
                version: OLEAN_ACCEPTED_VERSIONS[0],
                flags: 1,
                lean_version: OLEAN_PIN_TAG.strip_prefix('v').unwrap_or(OLEAN_PIN_TAG),
                githash: OLEAN_PIN_COMMIT,
                base_addr: (OLEAN_REGION_ALIGN as u64) * 2,
            },
            budget,
        )
        .map_err(|error| SourceModuleBuildError::Encode {
            module: self.name.clone(),
            error,
        })?;
        Ok(SourceModuleArtifact {
            name: self.name.clone(),
            bytes: encoded.bytes,
            report: encoded.report,
        })
    }
}

impl Engine {
    /// Check and encode an ordinary source module closure as separate `.olean`
    /// products. The caller supplies an empty engine or the exact independently
    /// rechecked external import closure; no source seed is silently installed.
    /// Unlike the explicit-environment check API, this applies Lean's implicit
    /// `Init` dependency to every header without `prelude`.
    ///
    /// Both kernel engines must accept the complete graph before any encoded
    /// products are returned. Native extension effects are refused until their
    /// pinned serialization exists; they are never silently dropped. New
    /// `module` headers, runtime/native code artifacts and filesystem publication
    /// are outside this basic `.olean` facet. Writer limits are aggregate across
    /// the closure, including supporting objects and file headers.
    pub fn compile_source_modules(
        &self,
        modules: &[SourceModuleInput<'_>],
        entry: &Name,
        options: &KVMap,
        limits: SourceModuleCheckLimits,
        write_budget: OleanWriteBudget,
    ) -> Result<Outcome<SourceModuleBuild>, SourceModuleBuildError> {
        validate_base(self, modules)?;
        let run = match cache::run_collecting(
            self,
            modules,
            entry,
            options,
            limits,
            None,
            cache::RunOptions {
                cache: None,
                collect_artifacts: true,
                contexts: None,
            },
        )
        .map_err(SourceModuleBuildError::Check)?
        {
            Outcome::Complete(run) => run,
            Outcome::Inconclusive(reason) => return Ok(Outcome::Inconclusive(reason)),
            Outcome::InternalFault(fault) => return Ok(Outcome::InternalFault(fault)),
        };
        finish(run, write_budget).map(Outcome::Complete)
    }
}

pub(super) fn finish(
    run: cache::Run,
    write_budget: OleanWriteBudget,
) -> Result<SourceModuleBuild, SourceModuleBuildError> {
    let mut remaining = write_budget;
    let mut artifacts = Vec::new();
    for pending in run.artifacts {
        let artifact = pending.encode(remaining)?;
        remaining.max_bytes -= artifact.report.file_bytes;
        remaining.max_objects -= artifact.report.runtime_objects;
        artifacts.push(artifact);
    }
    Ok(SourceModuleBuild {
        checked: run.result.checked,
        artifacts,
        reused_modules: run.result.reused_modules,
        elaborated_modules: run.result.elaborated_modules,
    })
}

/// The same authority boundary applies to cold and cached artifact builds.
pub(super) fn validate_base(
    base: &Engine,
    modules: &[SourceModuleInput<'_>],
) -> Result<(), SourceModuleBuildError> {
    if base.environment() != &Environment::new()
        && base.imported_environment.as_ref() != Some(base.environment())
    {
        return Err(SourceModuleBuildError::UnboundBase);
    }
    for module in modules {
        if base.imported_modules().contains(module.name) {
            return Err(SourceModuleBuildError::Check(
                SourceModuleCheckError::DuplicateModule(module.name.clone()),
            ));
        }
    }
    Ok(())
}

/// Encoding never imports persisted cache bytes. Reused, privately captured
/// declaration products obey fresh aggregate writer limits and cancellation.
/// The caller publishes its new cache only after this complete batch succeeds.
pub(super) fn encode_pending(
    pending: &[Arc<PendingArtifact>],
    mut remaining: OleanWriteBudget,
    cancellation: Option<&dyn CancellationProbe>,
) -> Result<Outcome<Vec<SourceModuleArtifact>>, SourceModuleBuildError> {
    let mut artifacts = Vec::new();
    for product in pending {
        if cancellation.is_some_and(CancellationProbe::is_cancelled) {
            return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
                "source-modules/before-encoding",
            )));
        }
        let artifact = product.encode(remaining)?;
        remaining.max_bytes -= artifact.report.file_bytes;
        remaining.max_objects -= artifact.report.runtime_objects;
        artifacts.push(artifact);
    }
    if cancellation.is_some_and(CancellationProbe::is_cancelled) {
        return Ok(Outcome::Inconclusive(Inconclusive::cancelled(
            "source-modules/before-build-publication",
        )));
    }
    Ok(Outcome::Complete(artifacts))
}
