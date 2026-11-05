//! Source proof checking and explicit import resolution for source front doors.
use super::*;
use fln::source_check::modules::imported::SourceOleanImport;
use fln::source_check::modules::reuse::{ImportPosture, ImportPostureReport};
mod imports;
pub(super) mod lsp;
pub(super) use imports::macros::Config as ImportedMacroConfig;

/// An admitted or reused external import closure, with the posture report that says which.
pub(super) type BuildBase = Option<(SourceOleanImport, ImportPostureReport)>;
/// A refused build base: failure class, detail, and whether the refusal is authoritative.
pub(super) type BuildBaseFailure = (&'static str, String, bool);

pub(super) fn load_build_base(
    roots: &[fln::Name],
    source_root: &Path,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> Result<BuildBase, BuildBaseFailure> {
    imports::load_build_base(roots, source_root, jobs, posture)
        .map_err(|error| (error.class, error.detail, error.authority))
}

pub(crate) use imports::{external_inputs, module_records, posture_json, posture_sentence};

pub(super) fn build_macro_config() -> Result<Option<ImportedMacroConfig>, BuildBaseFailure> {
    ImportedMacroConfig::from_environment()
        .map_err(|error| (error.class, error.detail, error.authority))
}

/// A single external world retained across requested Lake targets. Ordinary
/// builds keep their checked source cache; macro builds retain only the admitted
/// import receipt and captured executable inputs, never source cache authority.
pub(super) struct ModuleBuildContext {
    kind: ModuleBuildKind,
}

enum ModuleBuildKind {
    Ordinary(Box<fln::source_check::modules::SourceModuleSession>),
    ImportedMacros {
        base: Box<imports::MacroBuildBase>,
        limits: fln::source_check::modules::SourceModuleCheckLimits,
    },
}

pub(super) struct ModuleMacroReport {
    pub(super) json: String,
    pub(super) sentence: String,
}

impl ModuleBuildContext {
    pub(super) fn load(
        roots: &[fln::Name],
        source_root: &Path,
        jobs: std::num::NonZeroUsize,
        posture: ImportPosture,
        limits: fln::source_check::modules::SourceModuleCheckLimits,
        macros: Option<&ImportedMacroConfig>,
    ) -> Result<(Self, Option<ImportPostureReport>), BuildBaseFailure> {
        if let Some(config) = macros {
            let (base, report) =
                imports::load_macro_build_base(roots, source_root, jobs, posture, config)
                    .map_err(|error| (error.class, error.detail, error.authority))?;
            return Ok((
                Self {
                    kind: ModuleBuildKind::ImportedMacros {
                        base: Box::new(base),
                        limits,
                    },
                },
                Some(report),
            ));
        }
        use fln::source_check::modules::{SourceModuleCacheLimits, SourceModuleSession};
        let (session, report) = match load_build_base(roots, source_root, jobs, posture)? {
            Some((receipt, report)) => (
                SourceModuleSession::from_imports(
                    receipt,
                    fln::KVMap::new(),
                    limits,
                    SourceModuleCacheLimits::default(),
                ),
                Some(report),
            ),
            None => (
                SourceModuleSession::new(
                    fln::Engine::from_environment(fln::Environment::new()),
                    fln::KVMap::new(),
                    limits,
                    SourceModuleCacheLimits::default(),
                ),
                None,
            ),
        };
        Ok((
            Self {
                kind: ModuleBuildKind::Ordinary(Box::new(session)),
            },
            report,
        ))
    }

    pub(super) fn compile(
        &mut self,
        modules: &[fln::SourceModuleInput<'_>],
        entry: &fln::Name,
        write_budget: fln::OleanWriteBudget,
        records: Option<fln::source_check::modules::persisted::PersistedModules<'_>>,
    ) -> Result<
        fln::Outcome<(fln::source_check::modules::SourceModuleBuild, Option<ModuleMacroReport>)>,
        BuildBaseFailure,
    > {
        let failure = |error: fln::source_check::modules::SourceModuleBuildError| {
            let (class, authority, _) = error.disposition();
            (class, error.to_string(), authority)
        };
        match &mut self.kind {
            ModuleBuildKind::Ordinary(session) => session
                .compile_with_records(modules, entry, write_budget, records, None)
                .map(|outcome| outcome.map_complete(|built| (built, None)))
                .map_err(failure),
            ModuleBuildKind::ImportedMacros { base, limits } => {
                let result = base
                    .receipt
                    .compile_source_modules_with_deferred_imported_macros(
                        modules,
                        entry,
                        &fln::KVMap::new(),
                        *limits,
                        base.input.clone(),
                        write_budget,
                        None,
                    );
                let report = imports::macros::Report::from_attempts(
                    base.ir_bytes,
                    &result.attempts,
                    result.completed_vm_usage.steps,
                    result.tree_usage.visits,
                )
                .map_err(|error| (error.class, error.detail, error.authority))?;
                imports::macros::result(result.outcome)
                    .map(|outcome| {
                        outcome.map_complete(|built| {
                            (
                                built,
                                Some(ModuleMacroReport {
                                    json: report.json(),
                                    sentence: report.sentence(),
                                }),
                            )
                        })
                    })
                    .map_err(failure)
            }
        }
    }
}

/// Explicit import programs use their admitted module worlds. `None` keeps the
/// existing headerless and ordinary local-source `fln run` contract.
pub(super) fn run_imported(
    paths: &[PathBuf],
    max_bytes: usize,
    json: bool,
    publication: SourcePublication,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
    vm_limits: fln::VmExecutionLimits,
) -> Option<MultiplexerOutput> {
    imports::execution::run(
        paths,
        max_bytes,
        imports::execution::Presentation::Fln { json },
        publication,
        jobs,
        posture,
        vm_limits,
        None,
    )
}

/// The drop-in `lean` gives every source module its ordinary implicit Init
/// import unless that module declares `prelude`. Imports resolve from
/// `LEAN_PATH`, else the pinned library, under the interactive reuse posture.
/// A missing import never falls back to a synthetic source environment.
pub(super) fn run_imported_lean(
    path: &Path,
    max_bytes: usize,
    import_jobs: std::num::NonZeroUsize,
    vm_limits: fln::VmExecutionLimits,
) -> MultiplexerOutput {
    imports::execution::run(
        &[path.to_path_buf()],
        max_bytes,
        imports::execution::Presentation::Lean,
        SourcePublication::None,
        import_jobs,
        ImportPosture::ReuseVerified,
        vm_limits,
        None,
    )
    .unwrap_or_else(|| {
        source_failure(
            "internal-fault",
            "the Lean source route did not retain its import context",
            false,
            SourcePresentation::Lean,
            4,
        )
    })
}

/// Execute a script in its ordinary Lean import world, then invoke its main.
/// This route never falls back to the import-free synthetic source seed.
pub(super) fn run_imported_lean_main(
    path: &Path,
    arguments: Vec<String>,
    max_bytes: usize,
    import_jobs: std::num::NonZeroUsize,
    vm_limits: fln::VmExecutionLimits,
) -> MultiplexerOutput {
    imports::execution::run(
        &[path.to_path_buf()],
        max_bytes,
        imports::execution::Presentation::Lean,
        SourcePublication::None,
        import_jobs,
        ImportPosture::ReuseVerified,
        vm_limits,
        Some(arguments),
    )
    .unwrap_or_else(|| {
        source_failure(
            "internal-fault",
            "the executable source route did not retain its import context",
            false,
            SourcePresentation::Lean,
            4,
        )
    })
}

/// Standard input has the same import and admission semantics as a Lean file.
pub(super) fn run_imported_lean_stdin(
    source: Vec<u8>,
    max_bytes: usize,
    import_jobs: std::num::NonZeroUsize,
    vm_limits: fln::VmExecutionLimits,
) -> MultiplexerOutput {
    imports::execution::run_stdin(source, max_bytes, import_jobs, vm_limits).unwrap_or_else(|| {
        source_failure(
            "internal-fault",
            "the standard input source route did not retain its import context",
            false,
            SourcePresentation::Lean,
            4,
        )
    })
}

/// Remove `--import-posture P` / `--import-posture=P` from an interactive front
/// door's arguments, which otherwise keep their order. Options end at `--`. The
/// interactive doors default to `reuse-verified` (bead `fln-uyuz`); `check-olean`
/// accepts no posture at all, so G1 evidence is always `recheck`.
pub(super) fn take_import_posture_option(
    arguments: Vec<OsString>,
) -> Result<(Vec<OsString>, ImportPosture), UsageError> {
    let mut posture = None;
    let mut kept = Vec::with_capacity(arguments.len());
    let mut options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
            kept.push(argument);
            continue;
        }
        let value = if options && argument == "--import-posture" {
            Some(arguments.next().ok_or_else(|| {
                UsageError("--import-posture requires `recheck` or `reuse-verified`".to_owned())
            })?)
        } else if options {
            argument
                .to_str()
                .and_then(|value| value.strip_prefix("--import-posture="))
                .map(OsString::from)
        } else {
            None
        };
        let Some(value) = value else {
            kept.push(argument);
            continue;
        };
        if posture.is_some() {
            return Err(UsageError(
                "--import-posture may be supplied at most once".to_owned(),
            ));
        }
        let text = value
            .to_str()
            .ok_or_else(|| UsageError("--import-posture is not UTF-8".to_owned()))?;
        posture = Some(ImportPosture::parse(text).map_err(UsageError)?);
    }
    Ok((kept, posture.unwrap_or(ImportPosture::ReuseVerified)))
}

pub(super) fn parse(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
    let (arguments, jobs) = take_jobs_option(arguments)?;
    let (arguments, import_posture) = take_import_posture_option(arguments)?;
    let (arguments, imported_macros) = ImportedMacroConfig::take(arguments)?;
    // Unlike the legacy path parser, this new surface refuses conflicting repeats.
    let mut json = false;
    let mut bytes = false;
    let mut options = true;
    let mut skip_value = false;
    for arg in &arguments {
        if skip_value {
            skip_value = false;
            continue;
        }
        if arg == "--" {
            options = false;
            continue;
        }
        if !options {
            continue;
        }
        if arg == "--json" {
            if json {
                return Err(UsageError("duplicate --json".to_owned()));
            }
            json = true;
        }
        if arg == "--max-bytes" || arg.to_str().is_some_and(|s| s.starts_with("--max-bytes=")) {
            if bytes {
                return Err(UsageError("duplicate --max-bytes".to_owned()));
            }
            bytes = true;
            skip_value = arg == "--max-bytes";
        }
    }
    let Some((paths, max_bytes, json)) =
        parse_path_options(arguments, "check-source", SOURCE_RUN_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    if imported_macros.is_some() && paths.len() != 1 {
        return Err(UsageError(
            "--imported-macros requires exactly one source entry".to_owned(),
        ));
    }
    Ok(MultiplexerCommand::SourceCheck {
        paths,
        max_bytes,
        json,
        jobs,
        import_posture,
        imported_macros,
    })
}

fn failed(class: &str, detail: &str, authority: bool, json: bool, exit: u8) -> MultiplexerOutput {
    let detail = BoundedText::new(detail.to_owned());
    let stderr = if json {
        format!(
            "{{\"schema\":\"fln.source-check/1\",\"outcome\":{},\"authority\":{},\"detail\":{},\"detailTruncated\":{}}}\n",
            json_string(class),
            authority,
            json_string(detail.text()),
            detail.truncated()
        )
    } else {
        format!(
            "fln check-source: {class}: {}{}\n",
            detail.text(),
            if detail.truncated() {
                " [detail truncated]"
            } else {
                ""
            }
        )
    };
    MultiplexerOutput::failure(stderr, exit)
}

pub(super) fn run(
    paths: Vec<PathBuf>,
    max_bytes: usize,
    json: bool,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
    imported_macros: Option<ImportedMacroConfig>,
) -> MultiplexerOutput {
    if paths.len() > 4096 {
        return failed("resource", "source file count exceeds 4096", false, json, 3);
    }
    let mut sources = Vec::new();
    let mut total = 0;
    for path in &paths {
        let bytes = match read_bounded(path, max_bytes - total, "Lean source") {
            Ok(bytes) => bytes,
            Err(error) => {
                return failed(
                    error.class(),
                    &error.to_string(),
                    false,
                    json,
                    error.exit_code(),
                );
            }
        };
        total += bytes.len();
        sources.push(bytes);
    }
    // Header parsing, elaboration and both checkers use the calibrated worker.
    // Imports read bounded local snapshots; no global streams or cwd are changed.
    let worker = std::thread::Builder::new()
        .name("fln-source-check".to_owned())
        // Imports are admitted on this thread under the `.olean` depth budget.
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(move || {
            let loaded = match imports::load(&paths, sources, total, max_bytes) {
                Ok(loaded) => loaded,
                Err(error) => return failed(error.class, &error.detail, error.authority, json, error.exit),
            };
            let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES));
            let seed = || match fln::Engine::with_coercion_seed(admission) {
                Ok(fln::Outcome::Complete(engine)) => Ok(engine),
                Ok(fln::Outcome::Inconclusive(_)) => Err(imports::Failure::new("inconclusive", "source prelude could not complete", false, 3)),
                Ok(fln::Outcome::InternalFault(_)) => Err(imports::Failure::new("internal-fault", "source prelude faulted", false, 4)),
                Err(error) => {
                    let (class, authority, exit) = admission_error_disposition(&error);
                    Err(imports::Failure::new(class, &error.to_string(), authority, exit))
                }
            };
            let mut limits = fln::SourceCheckLimits::new(admission);
            limits.max_bytes = max_bytes;
            let macro_inputs = if let Some(config) = imported_macros.as_ref() {
                // Headers and source bytes were checked by the loader. Body
                // parsing belongs to the macro-aware checker after its exact
                // imported grammar world is available, not this early preflight.
                match loaded.prepare_macros(config) {
                    Ok(inputs) => Some(inputs),
                    Err(error) => return failed(error.class, &error.detail, error.authority, json, error.exit),
                }
            } else {
                if let Err(error) = loaded.preflight(limits) {
                    return failed(error.class, &error.detail, error.authority, json, error.exit);
                }
                None
            };
            let (engine, mut olean_base) = match loaded.base_engine(seed, jobs, posture) {
                Ok(base) => base,
                Err(error) => return failed(error.class, &error.detail, error.authority, json, error.exit),
            };
            let checked = if let Some(inputs) = macro_inputs {
                inputs.check(&loaded, olean_base.as_mut(), limits)
                    .map(|outcome| outcome.map_complete(|(checked, report)| (checked, Some(report))))
            } else {
                loaded.check(&engine, olean_base.as_ref(), limits)
                    .map(|outcome| outcome.map_complete(|checked| (checked, None)))
            };
            let (result, macro_report) = match checked {
                Ok(fln::Outcome::Complete(result)) => result,
                Ok(fln::Outcome::Inconclusive(_)) => return failed("inconclusive", "source check exhausted its configured resources", false, json, 3),
                Ok(fln::Outcome::InternalFault(_)) => return failed("internal-fault", "source check encountered an internal fault", false, json, 4),
                Err(error) => return failed(error.class, &error.detail, error.authority, json, error.exit),
            };
            let olean_json = olean_base.as_ref().map_or_else(String::new, |base| base.json());
            let executed = macro_report.as_ref().is_some_and(|report| report.vm_steps != 0);
            let macro_json = macro_report.as_ref().map_or_else(String::new, |report| report.json());
            // The sources' own `axiom`s: admitted without proof, so every theorem that uses
            // one trusts it. The pin admits them silently; the report names how many.
            let axioms = result
                .engine
                .environment()
                .constants()
                .filter(|(name, info)| {
                    matches!(info, fln::ConstantInfo::Axiom(_)) && !engine.environment().contains(name)
                })
                .count();
            // The sources' declarations that use `sorry` (`sorryAx`): the pin admits each with
            // the warning "declaration uses `sorry`"; this report, which prints no warnings,
            // counts them.
            let sorries = result
                .engine
                .environment()
                .constants()
                .filter(|(name, info)| {
                    !engine.environment().contains(name) && fln::constant_uses_sorry(info)
                })
                .count();
            let stdout = if json {
                format!("{{\"schema\":\"fln.source-check/1\",\"outcome\":\"complete\",\"authority\":true,\"files\":{},\"commands\":{},\"theorems\":{},\"axioms\":{axioms},\"sorryDeclarations\":{sorries},\"sourceBytes\":{},\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},\"executed\":{executed}{macro_json}{}}}\n",
                    result.files, result.commands, result.theorems, loaded.total_bytes,
                    json_string(&result.base_logical_root.to_string()), json_string(&result.result_logical_root.to_string()), olean_json)
            } else {
                let base = olean_base.as_ref().map_or(String::new(), |base| {
                    format!(" against {} imported .olean modules ({} declarations, {})", base.modules, base.declarations, posture_sentence(&base.report))
                });
                let axioms = if axioms == 0 {
                    String::new()
                } else {
                    format!(", {axioms} axioms asserted without proof")
                };
                let sorries = if sorries == 0 {
                    String::new()
                } else {
                    format!(", {sorries} declarations use `sorry`")
                };
                let execution = macro_report.as_ref().map_or_else(
                    || "No code executed.".to_owned(),
                    |report| format!(
                        "Imported macros: {} attempts, {} VM steps. Source evaluation commands were not executed.",
                        report.attempts, report.vm_steps,
                    ),
                );
                format!("Checked {} source commands ({} theorems{axioms}{sorries}) in {} files{base}; K1 and independent checker agreed. {execution}\n", result.commands, result.theorems, result.files)
            };
            // The process ends with this answer. Tearing down an imported closure
            // (65,404 declarations for `Init`) node by node took seconds; the
            // operating system reclaims it at exit in one step.
            std::mem::forget((engine, olean_base, result, loaded));
            MultiplexerOutput::success(stdout)
        });
    match worker {
        Err(error) => failed(
            "resource",
            &format!("could not start source-check worker: {error}"),
            false,
            json,
            3,
        ),
        Ok(worker) => match worker.join() {
            Ok(result) => result,
            Err(_) => failed(
                "internal-fault",
                "source-check worker panicked",
                false,
                json,
                4,
            ),
        },
    }
}

fn failed_goals(class: &str, detail: &str, json: bool, exit: u8) -> MultiplexerOutput {
    let detail = BoundedText::new(detail.to_owned());
    let stderr = if json {
        format!(
            "{{\"schema\":\"fln.goals/1\",\"outcome\":{},\"detail\":{},\"detailTruncated\":{}}}\n",
            json_string(class),
            json_string(detail.text()),
            detail.truncated()
        )
    } else {
        format!(
            "fln goals: {class}: {}{}\n",
            detail.text(),
            if detail.truncated() {
                " [detail truncated]"
            } else {
                ""
            }
        )
    };
    MultiplexerOutput::failure(stderr, exit)
}

pub(super) fn run_goals(
    path: PathBuf,
    line: Option<usize>,
    col: Option<usize>,
    offset: Option<usize>,
    max_bytes: usize,
    json: bool,
) -> MultiplexerOutput {
    let bytes = match read_bounded(&path, max_bytes, "Lean source") {
        Ok(bytes) => bytes,
        Err(error) => {
            return failed_goals(error.class(), &error.to_string(), json, error.exit_code());
        }
    };
    let text = match std::str::from_utf8(&bytes) {
        Ok(text) => text.to_owned(),
        Err(_) => {
            return failed_goals("input", "source is not valid UTF-8", json, 2);
        }
    };
    let worker = std::thread::Builder::new()
        .name("fln-goals".to_owned())
        .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
        .spawn(move || {
            let target_offset = if let Some(off) = offset {
                off.min(text.len())
            } else if let Some(target_line) = line {
                let target_col = col.unwrap_or(1);
                let mut cur_line = 1;
                let mut cur_col = 1;
                let mut computed_offset = 0;
                for (idx, ch) in text.char_indices() {
                    if cur_line == target_line && cur_col >= target_col {
                        computed_offset = idx;
                        break;
                    }
                    if ch == '\n' {
                        if cur_line == target_line {
                            computed_offset = idx;
                            break;
                        }
                        cur_line += 1;
                        cur_col = 1;
                    } else {
                        cur_col += 1;
                    }
                    computed_offset = idx + ch.len_utf8();
                }
                computed_offset
            } else {
                text.trim_end().len()
            };

            let canonical = match path.canonicalize() {
                Ok(p) => p,
                Err(e) => {
                    return failed_goals("io", &format!("cannot canonicalize path: {e}"), json, 2);
                }
            };
            let uri = match imports::editor::file_uri(&canonical) {
                Ok(u) => u,
                Err(e) => return failed_goals("input", &e.detail, json, 2),
            };

            use fln_server::dispatch::WorkspaceChecker;
            let mut checker = lsp::Checker::new();
            let _ = checker.check(&uri, &text, &[]);
            let answer = checker.query(
                fln_server::dispatch::semantic::Query {
                    kind: fln_server::dispatch::semantic::QueryKind::Goals,
                    uri: &uri,
                    version: 1,
                    text: &text,
                    offset: target_offset,
                },
                &[],
            );

            match answer {
                Ok(Some(fln_server::dispatch::semantic::Answer::Goals { goals })) => {
                    let rendered = if goals.is_empty() {
                        "no goals".to_owned()
                    } else {
                        goals.join("\n\n")
                    };
                    let stdout = if json {
                        let items = goals
                            .iter()
                            .map(|g| json_string(g))
                            .collect::<Vec<_>>()
                            .join(",");
                        format!(
                            "{{\"schema\":\"fln.goals/1\",\"outcome\":\"complete\",\"authority\":true,\"file\":{},\"offset\":{},\"rendered\":{},\"goals\":[{}]}}\n",
                            json_string(&path.to_string_lossy()),
                            target_offset,
                            json_string(&rendered),
                            items
                        )
                    } else {
                        format!("{rendered}\n")
                    };
                    MultiplexerOutput::success(stdout)
                }
                Ok(Some(_)) | Ok(None) => {
                    let stdout = if json {
                        format!(
                            "{{\"schema\":\"fln.goals/1\",\"outcome\":\"complete\",\"authority\":true,\"file\":{},\"offset\":{},\"rendered\":\"no goals\",\"goals\":[]}}\n",
                            json_string(&path.to_string_lossy()),
                            target_offset
                        )
                    } else {
                        "no goals\n".to_owned()
                    };
                    MultiplexerOutput::success(stdout)
                }
                Err(err) => failed_goals("engine-error", &err, json, 2),
            }
        });
    match worker {
        Err(error) => failed_goals(
            "resource",
            &format!("could not start goals worker: {error}"),
            json,
            3,
        ),
        Ok(worker) => match worker.join() {
            Ok(result) => result,
            Err(_) => failed_goals("internal-fault", "goals worker panicked", json, 4),
        },
    }
}
