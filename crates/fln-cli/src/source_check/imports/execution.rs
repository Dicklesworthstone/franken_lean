//! `fln run` and the drop-in `lean` over explicit source and `.olean` imports.
//! `fln run` presents FlN's raw result surface; `lean` presents the entry file's
//! command output through that door's own printer. FlN can retain the entry's
//! exact final executed bytecode and a sidecar binding the complete import program.
use super::*;
use fln::source_check::modules::execution::{
    SourceProgramExecution, SourceProgramLimits, preflight_lean_source_program,
    preflight_source_program,
};

const SCHEMA: &str = "fln.source-program/1";
const MAX_OUTPUT_BYTES: usize = 16 * 1024 * 1024;

/// How a source program's outcome is presented: FlN's raw result surface, or
/// the drop-in `lean` door, which prints what the entry file's own commands
/// print and reports a failure in that door's own form.
#[derive(Clone, Copy)]
pub(in crate::source_check) enum Presentation {
    Fln { json: bool },
    Lean,
}

/// Classic imported source historically uses the scalar presentation when
/// its admitted base has neither printer class. Completing its implicit Init
/// import remains separate work. Preserve that bounded route before execution;
/// once Lean printing is selected, no printer failure retries the raw route.
/// Prelude and module-system inputs always request their actual world's printer.
fn evaluation_presentation(
    presentation: Presentation,
    prelude: bool,
    module_system: bool,
    has_repr: bool,
    has_to_string: bool,
) -> fln::EvaluationPresentation {
    match (
        presentation,
        prelude,
        module_system,
        has_repr,
        has_to_string,
    ) {
        (Presentation::Fln { .. }, ..) | (Presentation::Lean, false, false, false, false) => {
            fln::EvaluationPresentation::Raw
        }
        _ => fln::EvaluationPresentation::Lean,
    }
}

fn failure(error: Failure, presentation: Presentation) -> MultiplexerOutput {
    let json = match presentation {
        Presentation::Fln { json } => json,
        Presentation::Lean => {
            return source_failure(
                error.class,
                &error.detail,
                error.authority,
                SourcePresentation::Lean,
                error.exit,
            );
        }
    };
    let detail = BoundedText::new(error.detail);
    let stderr = if json {
        format!(
            "{{\"schema\":{},\"outcome\":\"error\",\"authority\":{},\"class\":{},\"detail\":{},\"detailTruncated\":{}}}\n",
            json_string(SCHEMA),
            error.authority,
            json_string(error.class),
            json_string(detail.text()),
            detail.truncated(),
        )
    } else {
        format!(
            "fln run: {}: {}{}\n",
            error.class,
            detail.text(),
            if detail.truncated() {
                " [detail truncated]"
            } else {
                ""
            },
        )
    };
    MultiplexerOutput::failure(stderr, error.exit)
}

fn internal(detail: &str) -> Failure {
    Failure::new("internal-fault", detail, false, 4)
}

fn module_error(error: fln::source_check::modules::SourceModuleCheckError) -> Failure {
    let (class, authority, exit) = error.disposition();
    Failure::new(class, &error.to_string(), authority, exit)
}

fn evaluation_error(error: source_evaluation::Error) -> Failure {
    let (class, authority, exit) = error.disposition();
    Failure::new(class, &error.to_string(), authority, exit)
}

fn append(output: &mut String, text: &str) -> Result<(), Failure> {
    if output
        .len()
        .checked_add(text.len())
        .is_none_or(|len| len > MAX_OUTPUT_BYTES)
    {
        return Err(Failure::resource("source program output exceeds 16 MiB"));
    }
    output
        .try_reserve(text.len())
        .map_err(|_| Failure::resource("could not reserve source program output"))?;
    output.push_str(text);
    Ok(())
}

/// A legacy input is left to the existing runner, including its old diagnostics.
/// Header parsing and admission stay on a worker sized for imported declarations.
#[allow(clippy::too_many_arguments)]
pub(in crate::source_check) fn run(
    paths: &[PathBuf],
    max_bytes: usize,
    presentation: Presentation,
    publication: SourcePublication,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
    vm_limits: fln::VmExecutionLimits,
    main_arguments: Option<Vec<String>>,
) -> Option<MultiplexerOutput> {
    let sources = match read_source_batch(paths, max_bytes) {
        Ok(sources) => sources,
        Err(error) if main_arguments.is_some() => {
            return Some(source_failure(
                error.class(),
                &error.to_string(),
                false,
                SourcePresentation::Lean,
                error.exit_code(),
            ));
        }
        Err(_) => return None,
    };
    let paths = paths.to_vec();
    let worker = std::thread::Builder::new()
        .name("fln-imported-source-run".to_owned())
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(move || {
            crate::stdout_capture::optional_json(
                matches!(presentation, Presentation::Fln { json: true }), SCHEMA, || {
            let headers = match sources
                .iter()
                .map(|source| parse_source_header(source))
                .collect::<Result<Vec<_>, _>>()
            {
                Ok(headers) => headers,
                Err(error) if main_arguments.is_some() => {
                    return Some(failure(Failure::input(error.to_string()), presentation));
                }
                Err(_) => return None,
            };
            if main_arguments.is_none() && !headers.iter().any(|header| header.prelude || header.module_system || !header.imports.is_empty()) {
                return None;
            }
            // Explicit source batches keep their existing caller-ordered route.
            // A prelude must never fall through to that route's synthetic seed.
            if paths.len() != 1 {
                return headers.iter().any(|header| header.prelude || header.module_system).then(|| {
                    failure(Failure::input("a prelude or module-system source program requires one entry path"), presentation)
                });
            }
            // The established source-only runner resolves an unambiguous root
            // among bounded ancestors. Preserve that route before the import
            // loader (whose explicit module root is the entry's directory).
            // A transitive `prelude` still requires an empty, isolated world.
            let local = (main_arguments.is_none() && !headers[0].prelude && !headers[0].module_system)
                .then(|| discover_source_closure(paths[0].clone(), max_bytes));
            match &local {
                Some(Ok(discovered))
                    if discovered.sources.iter().all(|source| {
                        parse_source_header(source).is_ok_and(|header| {
                            !header.prelude && !header.module_system
                                && fln::partition_source_module(source)
                                    .is_ok_and(|module| module.imports == header.imports)
                        })
                    }) =>
                {
                    return None;
                }
                // For the `lean` door, an import that names no local source is
                // the one reason to look for a compiled module. Every other
                // answer the local route gives (a budget stop, an ambiguous
                // root, a refused symlink) stays the local route's to give.
                Some(Err(error))
                    if matches!(presentation, Presentation::Lean)
                        && !is_unresolved_local_import(error) =>
                {
                    return None;
                }
                _ => {}
            }
            let total = sources.iter().map(Vec::len).sum();
            let loaded = match if main_arguments.is_some() {
                load_lean(&paths, sources, total, max_bytes)
            } else {
                load(&paths, sources, total, max_bytes)
            } {
                Ok(loaded) => loaded,
                Err(error) => return Some(failure(error, presentation)),
            };
            let Inputs::Modules { names, sources } = &loaded.inputs else {
                return None;
            };
            let explicit_world = main_arguments.is_some() || !loaded.oleans.is_empty()
                || sources.iter().any(|source| {
                    parse_source_header(source).is_ok_and(|header| header.prelude || header.module_system)
                });
            if !explicit_world {
                return None;
            }
            if let Err(error) = preflight_publication(&publication) {
                return Some(failure(error, presentation));
            }
            let inputs: Vec<_> = names.iter().zip(sources).map(|(name, source)| {
                SourceModuleInput { name, source }
            }).collect();
            let mut limits = SourceProgramLimits::new(fln::EngineExecutionLimits::for_user_program(
                fln::Budget::for_stack_bytes(OLEAN_CHECK_KERNEL_STACK_BYTES),
            ));
            limits.execution.vm = vm_limits;
            limits.modules.source.max_bytes = max_bytes;
            let preflight = if main_arguments.is_some() {
                preflight_lean_source_program(&inputs, limits.modules)
            } else {
                preflight_source_program(&inputs, limits.modules)
            };
            if let Err(error) = preflight {
                return Some(failure(module_error(error), presentation));
            }
            let (imported_engine, base) = match loaded.base_engine(
                || Ok(fln::Engine::from_environment(fln::Environment::new())),
                jobs,
                posture,
            ) {
                Ok(base) => base,
                Err(error) => return Some(failure(error, presentation)),
            };
            let empty;
            let receipt = match &base {
                Some(base) => &base.receipt,
                None => {
                    empty = SourceOleanImport::empty(&fln::KVMap::new());
                    &empty
                }
            };
            let evaluation_presentation = evaluation_presentation(
                presentation,
                headers[0].prelude,
                headers[0].module_system,
                imported_engine.environment().contains(&Name::from_components(["Repr"])),
                imported_engine.environment().contains(&Name::from_components(["ToString"])),
            );
            let execution = if main_arguments.is_some() {
                receipt.execute_lean_source_modules_with_presentation(
                    &inputs, &names[0], &fln::KVMap::new(), limits, None, evaluation_presentation,
                )
            } else {
                receipt.execute_source_modules_with_presentation(
                    &inputs, &names[0], &fln::KVMap::new(), limits, None, evaluation_presentation,
                )
            };
            let completed = match execution {
                Ok(Outcome::Complete(completed)) => completed,
                Ok(Outcome::Inconclusive(reason)) => return Some(failure(Failure::new(
                    "inconclusive", &format!("source program did not finish: {reason:?}"), false, 3,
                ), presentation)),
                Ok(Outcome::InternalFault(fault)) => return Some(failure(Failure::new(
                    "internal-fault", &format!("source program faulted: {fault:?}"), false, 4,
                ), presentation)),
                Err(error) => return Some(failure(module_error(error), presentation)),
            };
            Some(match presentation {
                Presentation::Lean => match lean_output(
                    &completed,
                    &names[0],
                    headers[0].prelude && !loaded.reaches(&Name::from_components(["Init"])),
                ) {
                    Ok(output) => match main_arguments.as_ref() {
                        Some(arguments) => main_output(
                            &completed,
                            arguments,
                            limits.execution,
                            output,
                        ),
                        None => output,
                    },
                    Err(error) => failure(error, presentation),
                },
                Presentation::Fln { json } => {
                    let prepared = match prepare_publication(&publication, &completed, &inputs, &loaded) {
                        Ok(prepared) => prepared,
                        Err(error) => return Some(failure(error, presentation)),
                    };
                    // Validate and bound the complete report before linking
                    // either artifact. No recompile or second execution occurs.
                    match render(&completed, &names[0], loaded.total_bytes, base.as_ref(), json, prepared.as_ref()) {
                        Ok(stdout) => match prepared.as_ref().map(|prepared| prepared.publish(fln::publish_file_atomic_new)).transpose() {
                            Ok(_) => MultiplexerOutput::success(stdout),
                            Err(error) => failure(error, presentation),
                        },
                        Err(error) => failure(error, presentation),
                    }
                }
            })
            })
        });
    match worker {
        Err(error) => Some(failure(
            Failure::resource(format!("could not start imported source worker: {error}")),
            presentation,
        )),
        Ok(worker) => match worker.join() {
            Ok(result) => result,
            Err(_) => Some(failure(
                internal("imported source worker panicked"),
                presentation,
            )),
        },
    }
}

fn preflight_publication(publication: &SourcePublication) -> Result<(), Failure> {
    let (product, sidecar) = match publication {
        SourcePublication::None => return Ok(()),
        SourcePublication::OleanSnapshot { .. } => {
            return Err(Failure::new(
                "capability",
                "standalone .olean snapshot publication is not implemented for explicit import source programs; imported module metadata and private artifact parts require their own export contract",
                false,
                CAPABILITY_NOT_IMPLEMENTED_EXIT,
            ));
        }
        SourcePublication::Flbc { path, sidecar } => (path.as_path(), sidecar.as_ref()),
    };
    if sidecar.is_some_and(|sidecar| output_paths_alias(product, &sidecar.path)) {
        return Err(Failure::new(
            "output",
            "the FLBC product and its sidecar must name different paths",
            true,
            1,
        ));
    }
    for path in std::iter::once(product).chain(sidecar.map(|sidecar| sidecar.path.as_path())) {
        match std::fs::symlink_metadata(path) {
            Ok(_) => {
                return Err(Failure::new(
                    "output",
                    &format!(
                        "output path {} already exists; no artifact was published",
                        path.display()
                    ),
                    true,
                    1,
                ));
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                let (class, authority, exit) = publication_failure_disposition(&error);
                return Err(Failure::new(
                    class,
                    &format!("could not inspect output {}: {error}", path.display()),
                    authority,
                    exit,
                ));
            }
        }
        let parent = path
            .parent()
            .filter(|parent| !parent.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        match std::fs::metadata(parent) {
            Ok(metadata) if metadata.is_dir() => {}
            Ok(_) => {
                return Err(Failure::new(
                    "output",
                    &format!("output parent {} is not a directory", parent.display()),
                    true,
                    1,
                ));
            }
            Err(error) => {
                let (class, authority, exit) = publication_failure_disposition(&error);
                return Err(Failure::new(
                    class,
                    &format!(
                        "could not inspect output parent {}: {error}",
                        parent.display()
                    ),
                    authority,
                    exit,
                ));
            }
        }
    }
    Ok(())
}

struct PreparedSidecar<'a> {
    path: &'a Path,
    bytes: Vec<u8>,
    mode: fln::Mode,
    closure_root: fln::ContentRoot,
    product_root: fln::ContentRoot,
}

struct PreparedPublication<'a> {
    module: &'a Name,
    command: usize,
    product_path: &'a Path,
    product: &'a [u8],
    sidecar: Option<PreparedSidecar<'a>>,
}

fn prepare_publication<'a>(
    publication: &'a SourcePublication,
    program: &'a SourceProgramExecution,
    sources: &[SourceModuleInput<'_>],
    loaded: &Loaded,
) -> Result<Option<PreparedPublication<'a>>, Failure> {
    let SourcePublication::Flbc { path, sidecar } = publication else {
        return Ok(None);
    };
    validate_exits(program)?;
    for module in &program.modules {
        if !module.commands.guards.is_empty() {
            let judged = render_lean_source_commands(&module.commands);
            if judged.exit_code != 0 {
                let (class, authority) = match judged.exit_code {
                    3 => ("resource", false),
                    4 => ("internal-fault", false),
                    5 => ("capability", false),
                    _ => ("guard-msgs", true),
                };
                return Err(Failure::new(
                    class,
                    &format!(
                        "module `{}`: {}",
                        module.module.to_display_string(),
                        judged.stderr.trim_end()
                    ),
                    authority,
                    judged.exit_code,
                ));
            }
        }
    }
    let entry = program
        .modules
        .last()
        .ok_or_else(|| internal("source program has no entry for FLBC publication"))?;
    let final_execution = entry.commands.batch.executions.last().ok_or_else(|| {
        Failure::new(
            "execution",
            "entry module has no executed definition or #eval command to publish as FLBC",
            true,
            1,
        )
    })?;
    let command = entry
        .commands
        .execution_command_indices
        .last()
        .copied()
        .ok_or_else(|| internal("entry's final execution has no source command index"))?;
    let sidecar = if let Some(request) = sidecar {
        let current_image;
        let image = match request.toolchain_image.as_deref() {
            Some(image) => image,
            None => {
                current_image =
                    read_current_toolchain_image().map_err(|error| internal(&error.to_string()))?;
                &current_image
            }
        };
        let imports: Vec<_> = loaded
            .oleans
            .iter()
            .map(|import| {
                let [exported, server, private] = &import.parts;
                fln::OleanModuleInput {
                    name: &import.name,
                    artifact: exported,
                    server_artifact: (!server.is_empty()).then_some(server.as_slice()),
                    private_artifact: (!private.is_empty()).then_some(private.as_slice()),
                }
            })
            .collect();
        let sidecar = fln::build_source_program_flbc_sidecar(
            sources,
            &imports,
            &fln::KVMap::new(),
            image,
            program,
        )
        .map_err(|error| Failure::new("sidecar", &error.to_string(), false, 1))?;
        Some(PreparedSidecar {
            path: &request.path,
            bytes: fln::encode_flbc_product_sidecar(&sidecar),
            mode: sidecar.mode(),
            closure_root: sidecar.closure_root(),
            product_root: sidecar.product_root(),
        })
    } else {
        None
    };
    Ok(Some(PreparedPublication {
        module: &entry.module,
        command,
        product_path: path,
        // These bytes were already canonically decoded and validated before
        // Golem executed them. They contain the complete reachable functions
        // and intrinsics, including compiled imported definitions.
        product: &final_execution.flbc_artifact,
        sidecar,
    }))
}

impl PreparedPublication<'_> {
    fn publish<P, E>(&self, mut publish: P) -> Result<(), Failure>
    where
        P: FnMut(&[u8], &Path) -> Result<(), E>,
        E: SourcePublicationFailure,
    {
        // As on the import-free path, each artifact is atomically created,
        // never overwritten. A failed product link may leave its complete
        // sidecar; it never exposes a partial bytecode file.
        if let Some(sidecar) = &self.sidecar {
            publish(&sidecar.bytes, sidecar.path).map_err(|error| {
                let (class, authority, exit) = publication_failure_disposition(&error);
                Failure::new(class, &format!("could not complete durable FLBC sidecar publication to {}: {error}; {}; the FLBC product was not published", sidecar.path.display(), publication_state(&error)), authority, exit)
            })?;
        }
        publish(self.product, self.product_path).map_err(|error| {
            let (class, authority, exit) = publication_failure_disposition(&error);
            let retained = self.sidecar.as_ref().map_or_else(String::new, |sidecar| format!("; the complete sidecar is retained at {}", sidecar.path.display()));
            Failure::new(class, &format!("could not complete durable FLBC artifact publication to {}: {error}; {}{retained}", self.product_path.display(), publication_state(&error)), authority, exit)
        })
    }

    fn report(&self, output: &mut String, json: bool) -> Result<(), Failure> {
        if json {
            append(
                output,
                &format!(
                    ",\"emittedFlbc\":{{\"path\":{},\"bytes\":{},\"module\":{},\"command\":{}}},\"emittedSidecar\":",
                    json_string(&self.product_path.to_string_lossy()),
                    self.product.len(),
                    json_string(&self.module.to_display_string()),
                    self.command
                ),
            )?;
            if let Some(sidecar) = &self.sidecar {
                append(
                    output,
                    &format!(
                        "{{\"path\":{},\"bytes\":{},\"mode\":{},\"profile\":\"standard\",\"closureRoot\":{},\"productRoot\":{}}}",
                        json_string(&sidecar.path.to_string_lossy()),
                        sidecar.bytes.len(),
                        json_string(mode_name(sidecar.mode)),
                        json_string(&root_hex(sidecar.closure_root)),
                        json_string(&root_hex(sidecar.product_root))
                    ),
                )?;
            } else {
                append(output, "null")?;
            }
        } else {
            append(
                output,
                &format!(
                    "Emitted FLBC: {} bytes to {} (module `{}`, command {}).\n",
                    self.product.len(),
                    self.product_path.display(),
                    self.module.to_display_string(),
                    self.command
                ),
            )?;
            if let Some(sidecar) = &self.sidecar {
                append(
                    output,
                    &format!(
                        "Emitted sidecar: {} bytes to {}.\nClosure root: {}\nProduct root: {}\n",
                        sidecar.bytes.len(),
                        sidecar.path.display(),
                        root_hex(sidecar.closure_root),
                        root_hex(sidecar.product_root)
                    ),
                )?;
            }
        }
        Ok(())
    }
}

/// Definitions that produce no output still execute. A later successful `#eval`
/// cannot hide a dependency panic or refusal; inspect the complete table first.
fn validate_exits(program: &SourceProgramExecution) -> Result<(), Failure> {
    for module in &program.modules {
        let commands = &module.commands;
        if commands.execution_command_indices.len() != commands.batch.executions.len()
            || commands.execution_command_indices != commands.batch.source_execution_command_indices
        {
            return Err(internal(
                "source program execution indices do not cover every execution",
            ));
        }
        let mut previous = None;
        for (&command, execution) in commands
            .execution_command_indices
            .iter()
            .zip(&commands.batch.executions)
        {
            if command >= commands.command_count || previous.is_some_and(|last| last >= command) {
                return Err(internal(
                    "source program execution indices are not increasing in range",
                ));
            }
            previous = Some(command);
            let (class, detail, usage) = match &execution.exit {
                fln::VmExit::Returned(_) => {
                    source_evaluation::check(execution).map_err(|error| {
                        let (class, authority, exit) = error.disposition();
                        Failure::new(
                            class,
                            &format!(
                                "module `{}`, command {command}: {error}",
                                module.module.to_display_string()
                            ),
                            authority,
                            exit,
                        )
                    })?;
                    continue;
                }
                fln::VmExit::Panicked { message, usage } => {
                    ("program-panic", message.to_string(), usage)
                }
                fln::VmExit::Refused { refusal, usage } => {
                    ("vm-refusal", refusal.to_string(), usage)
                }
            };
            return Err(Failure::new(
                class,
                &format!(
                    "module `{}`, command {command}: {detail}; execution used {} steps, {} system polls, peak stack {}",
                    module.module.to_display_string(),
                    usage.steps,
                    usage.system_polls,
                    usage.peak_stack_depth,
                ),
                true,
                1,
            ));
        }
    }
    Ok(())
}

/// What the drop-in `lean` prints for a program that ran: the output of the
/// entry file's own commands. The modules it imports ran too, and what they
/// print is not the entry's.
/// `without_init`: the entry is a `prelude` file whose imports never reach `Init`. The pin
/// prints an `#eval` through a `Repr` or `ToString` instance and refuses it without one, which
/// such a world may lack (`Init.Prelude` declares neither). Only an execution retaining
/// checked pure/IO printer intent or validated silent IO Unit intent bypasses this guard. A non-`prelude`
/// file imports `Init` implicitly at the pin, so its instances exist whatever this closure holds.
fn lean_output(
    program: &SourceProgramExecution,
    entry: &Name,
    without_init: bool,
) -> Result<MultiplexerOutput, Failure> {
    validate_exits(program)?;
    let module = program
        .modules
        .last()
        .filter(|module| &module.module == entry)
        .ok_or_else(|| internal("source program did not retain its entry as the final module"))?;
    if without_init
        && module.commands.outputs.iter().any(|output| match output {
            fln::SourceCommandOutput::Evaluation {
                execution_index, ..
            } => module
                .commands
                .batch
                .executions
                .get(*execution_index)
                .is_none_or(|execution| !source_evaluation::has_checked_presentation(execution)),
            _ => false,
        })
    {
        return Err(Failure::new(
            "capability",
            "this prelude file's imports do not reach `Init`; the pin prints an #eval through \
             the Repr or ToString instance its world declares and refuses it without one, and \
             no checked printer or silent IO Unit presentation was selected for this evaluation",
            false,
            CAPABILITY_NOT_IMPLEMENTED_EXIT,
        ));
    }
    Ok(render_lean_source_commands(&module.commands))
}

/// A dependency's saved guard messages must succeed before main is selected.
/// Only batches with guards need this additional presentation pass. The
/// existing renderer validates its complete command/index tables, so keep the
/// whole retained batch instead of constructing a partial guard-only view.
/// Successful dependency output is discarded; no declaration or action reruns.
fn main_output(
    program: &SourceProgramExecution,
    arguments: &[String],
    limits: fln::EngineExecutionLimits,
    frontend: MultiplexerOutput,
) -> MultiplexerOutput {
    if frontend.exit_code != 0 {
        return frontend;
    }
    let Some((entry, dependencies)) = program.modules.split_last() else {
        let mut failed = failure(
            internal("source program did not retain its entry before main"),
            Presentation::Lean,
        );
        failed.stdout = frontend.stdout;
        return failed;
    };
    for dependency in dependencies {
        if dependency.commands.guards.is_empty() {
            continue;
        }
        let mut presented = render_lean_source_commands(&dependency.commands);
        if presented.exit_code != 0 {
            presented.stdout = frontend.stdout;
            return presented;
        }
    }
    crate::source_main::execute(&entry.commands, arguments, limits, frontend)
}

fn render(
    program: &SourceProgramExecution,
    entry: &Name,
    source_bytes: usize,
    base: Option<&OleanBase>,
    json: bool,
    publication: Option<&PreparedPublication<'_>>,
) -> Result<String, Failure> {
    validate_exits(program)?;
    if program
        .modules
        .last()
        .is_none_or(|module| &module.module != entry)
    {
        return Err(internal(
            "source program did not retain its entry as the final module",
        ));
    }
    let mut output = String::new();
    if json {
        append(
            &mut output,
            &format!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"authority\":true,\"entry\":{},\"files\":{},\"sourceBytes\":{}{},\"modules\":[",
                json_string(SCHEMA),
                json_string(&entry.to_display_string()),
                program.modules.len(),
                source_bytes,
                base.map_or_else(|| ",\"oleanImports\":null".to_owned(), OleanBase::json),
            ),
        )?;
    } else {
        append(
            &mut output,
            &format!(
                "Executed {} source modules ({} source bytes).\n",
                program.modules.len(),
                source_bytes
            ),
        )?;
        if let Some(base) = base {
            append(
                &mut output,
                &format!(
                    "Imports: {} .olean modules, {} declarations; {}.\n",
                    base.modules,
                    base.declarations,
                    posture_sentence(&base.report)
                ),
            )?;
        }
    }
    for (index, module) in program.modules.iter().enumerate() {
        let commands = &module.commands;
        let name = module.module.to_display_string();
        if json {
            if index != 0 {
                append(&mut output, ",")?;
            }
            append(
                &mut output,
                &format!(
                    "{{\"module\":{},\"commands\":{},\"executions\":{},\"evaluations\":{},\"checks\":{},\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},\"outputs\":[",
                    json_string(&name),
                    commands.command_count,
                    commands.batch.executions.len(),
                    commands.batch.source_evaluation_indices.len(),
                    commands.checks.len(),
                    json_string(&commands.batch.base_logical_root.to_string()),
                    json_string(&commands.batch.result_logical_root.to_string()),
                ),
            )?;
        } else {
            append(
                &mut output,
                &format!(
                    "Module {name}: {} commands, {} executions.\n",
                    commands.command_count,
                    commands.batch.executions.len()
                ),
            )?;
        }
        render_commands(commands, &name, json, &mut output)?;
        if json {
            append(&mut output, "]}")?;
        }
    }
    if json {
        append(&mut output, "]")?;
    }
    if let Some(publication) = publication {
        publication.report(&mut output, json)?;
    }
    if json {
        append(&mut output, "}\n")?;
    }
    Ok(output)
}

fn render_commands(
    commands: &fln::SourceCommandBatchExecution,
    module: &str,
    json: bool,
    output: &mut String,
) -> Result<(), Failure> {
    let mut previous = None;
    let mut evaluations = 0;
    let mut checks = 0;
    for (position, event) in commands.outputs.iter().enumerate() {
        let command = match event {
            fln::SourceCommandOutput::Evaluation { command_index, .. }
            | fln::SourceCommandOutput::Check { command_index, .. }
            | fln::SourceCommandOutput::Example { command_index, .. } => *command_index,
        };
        if command >= commands.command_count || previous.is_some_and(|last| last >= command) {
            return Err(internal(
                "source program output indices are not increasing in range",
            ));
        }
        previous = Some(command);
        if json && position != 0 {
            append(output, ",")?;
        }
        match event {
            fln::SourceCommandOutput::Evaluation {
                execution_index, ..
            } => {
                if commands.execution_command_indices.get(*execution_index) != Some(&command)
                    || commands.batch.source_evaluation_indices.get(evaluations)
                        != Some(execution_index)
                {
                    return Err(internal(
                        "source program evaluation disagrees with its execution index",
                    ));
                }
                let execution =
                    commands
                        .batch
                        .executions
                        .get(*execution_index)
                        .ok_or_else(|| {
                            internal("source program evaluation escaped the execution table")
                        })?;
                let value = source_evaluation::value(execution)
                    .map_err(evaluation_error)?
                    .ok_or_else(|| Failure::new("capability", &format!(
                        "module `{module}`, command {command}: raw result is not a supported closed Nat, String, Bool, Float, Float32, or nested List value",
                    ), false, CAPABILITY_NOT_IMPLEMENTED_EXIT))?;
                let fln::VmExit::Returned(returned) = &execution.exit else {
                    return Err(internal(
                        "non-returning source execution escaped terminal validation",
                    ));
                };
                if json {
                    append(
                        output,
                        &format!(
                            "{{\"command\":{command},\"event\":\"evaluation\",\"kind\":{},\"value\":{},\"steps\":{},\"systemPolls\":{},\"peakStackDepth\":{}}}",
                            json_string(value.kind()),
                            value.json(),
                            returned.usage.steps,
                            returned.usage.system_polls,
                            returned.usage.peak_stack_depth,
                        ),
                    )?;
                } else {
                    append(output, &format!("  command {command}, #eval: {value}\n"))?;
                }
                evaluations += 1;
            }
            fln::SourceCommandOutput::Check { check_index, .. }
            | fln::SourceCommandOutput::Example { check_index, .. } => {
                if *check_index != checks {
                    return Err(internal(
                        "source program check outputs do not cover their table in order",
                    ));
                }
                let check = commands
                    .checks
                    .get(*check_index)
                    .ok_or_else(|| internal("source program check escaped its table"))?;
                let example = matches!(event, fln::SourceCommandOutput::Example { .. });
                if example != (check.parsed.kind() == fln::SourceCommandKind::Example) {
                    return Err(internal(
                        "source program check event disagrees with its command kind",
                    ));
                }
                checks += 1;
                let fields = if example {
                    String::new()
                } else {
                    let term = check
                        .parsed
                        .query_term_normalized()
                        .ok_or_else(|| internal("source program check has no query term"))?;
                    let type_ = fln::pretty::Printer::in_scope(commands.batch.engine.environment(), &commands.scope)
                        .expr(&check.checked_type, 0)
                        .map_err(|fln::pretty::Unsupported(what)| Failure::new(
                            "capability", &format!("module `{module}`, command {command}: cannot print checked type {what}"),
                            false, CAPABILITY_NOT_IMPLEMENTED_EXIT,
                        ))?;
                    if json {
                        format!(
                            ",\"term\":{},\"type\":{}",
                            json_string(term.trim_ascii()),
                            json_string(&type_)
                        )
                    } else {
                        append(
                            output,
                            &format!(
                                "  command {command}, #check: {} : {type_}\n",
                                term.trim_ascii()
                            ),
                        )?;
                        String::new()
                    }
                };
                if json {
                    append(
                        output,
                        &format!(
                            "{{\"command\":{command},\"event\":{},\"environmentLogicalRoot\":{},\"checker\":{{\"schema\":{},\"ground\":{}}}{fields}}}",
                            json_string(if example { "example" } else { "check" }),
                            json_string(&check.environment_root.to_string()),
                            json_string(check.checker.schema),
                            json_string(checker_ground_name(check.checker.ground)),
                        ),
                    )?;
                }
            }
        }
    }
    if evaluations != commands.batch.source_evaluation_indices.len()
        || checks != commands.checks.len()
    {
        return Err(internal(
            "source program output omitted an evaluation or check",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln::source_check::modules::execution::SourceModuleExecution;

    #[test]
    fn imported_publication_reports_resource_failure_and_retained_sidecar_truthfully() {
        let module = Name::from_components(["Main"]);
        let prepared = PreparedPublication {
            module: &module,
            command: 0,
            product_path: Path::new("program.flbc"),
            product: b"complete product",
            sidecar: Some(PreparedSidecar {
                path: Path::new("program.sidecar"),
                bytes: b"complete sidecar".to_vec(),
                mode: fln::Mode::Sound,
                closure_root: fln::ContentRoot::new([0; 32]),
                product_root: fln::ContentRoot::new([0; 32]),
            }),
        };
        for failed_call in 0..2 {
            for target_created in [false, true] {
                let mut calls = Vec::new();
                let failed = prepared
                    .publish(|bytes, path| {
                        let call = calls.len();
                        calls.push((path.to_path_buf(), bytes.to_vec()));
                        if call != failed_call {
                            return Ok(());
                        }
                        Err(fln::AtomicCreateError::<std::convert::Infallible>::Io {
                            step: if target_created {
                                fln::AtomicCreateStep::SyncDirectoryAfterLink
                            } else {
                                fln::AtomicCreateStep::WriteChunk {
                                    offset: 0,
                                    chunk_len: 1,
                                    total_len: bytes.len() as u64,
                                }
                            },
                            target_created,
                            source: std::io::Error::from(std::io::ErrorKind::StorageFull),
                        })
                    })
                    .unwrap_err();
                assert_eq!(
                    (failed.class, failed.authority, failed.exit),
                    ("resource", false, 3)
                );
                assert_eq!(calls.len(), failed_call + 1);
                assert_eq!(
                    calls[0],
                    (
                        PathBuf::from("program.sidecar"),
                        b"complete sidecar".to_vec()
                    )
                );
                if failed_call == 0 {
                    assert!(failed.detail.contains("the FLBC product was not published"));
                } else {
                    assert_eq!(
                        calls[1],
                        (PathBuf::from("program.flbc"), b"complete product".to_vec())
                    );
                    assert!(
                        failed
                            .detail
                            .contains("the complete sidecar is retained at program.sidecar")
                    );
                }
                assert!(failed.detail.contains(if target_created {
                    "the complete target already exists"
                } else {
                    "the target was not created"
                }));
                let report = failure(failed, Presentation::Fln { json: true });
                assert!(report.stdout.is_empty());
                assert!(report.stderr.contains("\"authority\":false"));
            }
        }
    }

    #[test]
    fn presentation_selection_preserves_the_classic_scalar_boundary() {
        use fln::EvaluationPresentation::{Lean, Raw};
        let cases = [
            (false, false, false, false, Raw),
            (false, false, true, false, Lean),
            (false, false, false, true, Lean),
            (false, false, true, true, Lean),
            (true, false, false, false, Lean),
            (false, true, false, false, Lean),
            (true, true, false, false, Lean),
            (true, true, true, true, Lean),
        ];
        for (prelude, module_system, repr, to_string, expected) in cases {
            assert_eq!(
                evaluation_presentation(
                    Presentation::Lean,
                    prelude,
                    module_system,
                    repr,
                    to_string,
                ),
                expected,
            );
            for json in [false, true] {
                assert_eq!(
                    evaluation_presentation(
                        Presentation::Fln { json },
                        prelude,
                        module_system,
                        repr,
                        to_string,
                    ),
                    Raw,
                );
            }
        }
    }

    #[test]
    fn a_result_projection_limit_is_not_a_program_rejection_or_internal_fault() {
        let error = evaluation_error(source_evaluation::Error::Value(
            SourceValueProjectionError::Shaped(fln::ClosedShapedValueError::TooLarge { limit: 17 }),
        ));
        assert_eq!(
            (error.class, error.authority, error.exit),
            ("resource", false, 3)
        );
        let mismatch = evaluation_error(source_evaluation::Error::Value(
            SourceValueProjectionError::Shaped(fln::ClosedShapedValueError::Representation {
                expected: "List",
            }),
        ));
        assert_eq!(
            (mismatch.class, mismatch.authority, mismatch.exit),
            ("internal-fault", false, 4)
        );
        for (error, expected) in [
            (
                fln::source_format::Error::Limit {
                    resource: "text bytes",
                    limit: 8,
                    observed: 9,
                },
                ("resource", false, 3),
            ),
            (
                fln::source_format::Error::UnsupportedContract {
                    family: "Std.Format",
                },
                ("capability", false, 5),
            ),
            (
                fln::source_format::Error::Representation {
                    expected: "Std.Format",
                },
                ("internal-fault", false, 4),
            ),
        ] {
            let failed = evaluation_error(source_evaluation::Error::Format(error));
            assert_eq!((failed.class, failed.authority, failed.exit), expected);
            let output = failure(failed, Presentation::Lean);
            assert!(output.stdout.is_empty());
            assert_eq!(output.exit_code, expected.2);
            assert!(
                output
                    .stderr
                    .starts_with(&format!("lean: {}: ", expected.0))
            );
        }
    }

    #[test]
    fn dependency_guards_are_judged_before_main_without_publishing_dependency_output() {
        std::thread::Builder::new()
            .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
            .spawn(|| {
                let limits = fln::EngineExecutionLimits::new(fln::Budget::for_stack_bytes(
                    SOURCE_RUN_KERNEL_STACK_BYTES,
                ));
                let engine = fln::Engine::with_source_seed(limits.admission())
                    .unwrap()
                    .into_complete()
                    .unwrap();
                for expected in [2, 999] {
                    let dependency = engine
                        .execute_source_commands_with_checks(
                            format!("#eval 11\n/-- info: {expected} -/\n#guard_msgs in\n#eval 2\n")
                                .as_bytes(),
                            &fln::KVMap::new(),
                            limits,
                        )
                        .unwrap()
                        .into_complete()
                        .unwrap();
                    assert_eq!(dependency.guards.len(), 1);
                    let judged = render_lean_source_commands(&dependency);
                    if expected == 2 {
                        assert_eq!(judged.exit_code, 0, "{}", judged.stderr);
                        assert_eq!(judged.stdout, "11\n");
                    } else {
                        assert_eq!(judged.exit_code, 1);
                        assert!(judged.stderr.starts_with("lean: guard-msgs:"));
                    }
                    // This genuinely checked declaration deliberately has an
                    // invalid executable signature. Its distinct selection
                    // error proves whether the saved dependency guard allowed
                    // the main path to proceed; no synthetic VM result is used.
                    let commands = engine
                        .execute_source_commands_with_checks(
                            b"def main : Nat := 7\n#eval 42\n",
                            &fln::KVMap::new(),
                            limits,
                        )
                        .unwrap()
                        .into_complete()
                        .unwrap();
                    let program = SourceProgramExecution {
                        modules: vec![
                            SourceModuleExecution {
                                module: Name::from_components(["Dependency"]),
                                commands: dependency,
                            },
                            SourceModuleExecution {
                                module: Name::from_components(["Main"]),
                                commands,
                            },
                        ],
                    };
                    let frontend =
                        match lean_output(&program, &Name::from_components(["Main"]), false) {
                            Ok(frontend) => frontend,
                            Err(error) => {
                                panic!("retained source commands must finish: {}", error.detail)
                            }
                        };
                    assert_eq!(frontend.exit_code, 0);
                    assert_eq!(frontend.stdout, "42\n");
                    let result = main_output(&program, &[], limits, frontend);
                    assert_eq!(result.exit_code, 1);
                    assert_eq!(result.stdout, "42\n");
                    if expected == 2 {
                        assert!(result.stderr.contains("`main` function must have type"));
                        assert!(!result.stderr.contains("guard-msgs"));
                    } else {
                        assert!(result.stderr.starts_with("lean: guard-msgs:"));
                        assert!(!result.stderr.contains("`main` function must have type"));
                    }
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn a_non_output_dependency_panic_cannot_be_hidden_by_a_successful_entry() {
        std::thread::Builder::new()
            .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
            .spawn(|| {
                let limits = fln::EngineExecutionLimits::new(fln::Budget::for_stack_bytes(
                    SOURCE_RUN_KERNEL_STACK_BYTES,
                ));
                let engine = fln::Engine::with_source_seed(limits.admission())
                    .unwrap()
                    .into_complete()
                    .unwrap();
                let mut modules = Vec::new();
                for name in ["Dependency", "Main"] {
                    let commands = engine
                        .execute_source_commands_with_checks(
                            b"def answer : Nat := 42\n#eval answer\n",
                            &fln::KVMap::new(),
                            limits,
                        )
                        .unwrap()
                        .into_complete()
                        .unwrap();
                    modules.push(SourceModuleExecution {
                        module: Name::from_components([name]),
                        commands,
                    });
                }
                let mut program = SourceProgramExecution { modules };
                let entry = Name::from_components(["Main"]);
                assert!(render(&program, &entry, 0, None, true, None).is_ok());
                // The `lean` presentation prints the entry's own output only: one
                // `42`, though the dependency evaluated the same term.
                match lean_output(&program, &entry, false) {
                    Ok(presented) => assert_eq!(
                        (presented.exit_code, presented.stdout.as_str()),
                        (0, "42\n")
                    ),
                    Err(error) => panic!("a complete program must present: {}", error.detail),
                }
                // A `prelude` entry whose world lacks `Init` never prints an `#eval`.
                match lean_output(&program, &entry, true) {
                    Err(error) => assert_eq!((error.class, error.exit), ("capability", 5)),
                    Ok(_) => panic!("an #eval without Init's instances must not print"),
                }
                // The VM terminal seam is public typed data. Plant a completed
                // panic in a dependency definition that has no output event,
                // keeping every later evaluation successful and unchanged.
                let execution = &mut program.modules[0].commands.batch.executions[0];
                let fln::VmExit::Returned(returned) = &execution.exit else {
                    panic!("the native definition must return");
                };
                execution.exit = fln::VmExit::Panicked {
                    message: "dependency initialization failed".to_owned(),
                    usage: returned.usage,
                };
                match lean_output(&program, &entry, false) {
                    Err(error) => assert_eq!((error.class, error.exit), ("program-panic", 1)),
                    Ok(_) => panic!("the lean presentation must not hide a dependency panic"),
                }
                for json in [false, true] {
                    let error = match render(&program, &entry, 0, None, json, None) {
                        Err(error) => error,
                        Ok(_) => panic!("a successful entry must not hide a dependency panic"),
                    };
                    assert_eq!(
                        (error.class, error.authority, error.exit),
                        ("program-panic", true, 1)
                    );
                    assert!(
                        error.detail.contains("Dependency") && error.detail.contains("command 0")
                    );
                    let failed = failure(error, Presentation::Fln { json });
                    assert!(failed.stdout.is_empty());
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
