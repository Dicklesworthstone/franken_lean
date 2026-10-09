//! `fln run` and the drop-in `lean` over explicit source and `.olean` imports.
//! `fln run` presents FlN's raw result surface; `lean` presents the entry file's
//! command output through that door's own printer. Neither publishes an artifact.
use super::*;
use fln::source_check::modules::execution::{
    SourceProgramExecution, SourceProgramLimits, preflight_source_program,
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
pub(in crate::source_check) fn run(
    paths: &[PathBuf],
    max_bytes: usize,
    presentation: Presentation,
    emit_artifact: bool,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> Option<MultiplexerOutput> {
    let sources = read_source_batch(paths, max_bytes).ok()?;
    let paths = paths.to_vec();
    let worker = std::thread::Builder::new()
        .name("fln-imported-source-run".to_owned())
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(move || {
            let headers = sources
                .iter()
                .map(|source| parse_source_header(source))
                .collect::<Result<Vec<_>, _>>()
                .ok()?;
            if !headers.iter().any(|header| header.prelude || !header.imports.is_empty()) {
                return None;
            }
            // Explicit source batches keep their existing caller-ordered route.
            // A prelude must never fall through to that route's synthetic seed.
            if paths.len() != 1 {
                return headers.iter().any(|header| header.prelude).then(|| {
                    failure(Failure::input("a prelude source program requires one entry path"), presentation)
                });
            }
            // The established source-only runner resolves an unambiguous root
            // among bounded ancestors. Preserve that route before the import
            // loader (whose explicit module root is the entry's directory).
            // A transitive `prelude` still requires an empty, isolated world.
            let local = (!headers[0].prelude)
                .then(|| discover_source_closure(paths[0].clone(), max_bytes));
            match &local {
                Some(Ok(discovered))
                    if discovered.sources.iter().all(|source| {
                        parse_source_header(source).is_ok_and(|header| {
                            !header.prelude
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
            let loaded = match load(&paths, sources, total, max_bytes) {
                Ok(loaded) => loaded,
                Err(error) => return Some(failure(error, presentation)),
            };
            let Inputs::Modules { names, sources } = &loaded.inputs else {
                return None;
            };
            let explicit_world = !loaded.oleans.is_empty()
                || sources.iter().any(|source| {
                    parse_source_header(source).is_ok_and(|header| header.prelude)
                });
            if !explicit_world {
                return None;
            }
            if emit_artifact {
                return Some(failure(Failure::new(
                    "capability",
                    "artifact publication (--emit-flbc, --emit-sidecar, --emit-olean-snapshot) is not implemented for explicit import source programs",
                    false,
                    CAPABILITY_NOT_IMPLEMENTED_EXIT,
                ), presentation));
            }
            let inputs: Vec<_> = names.iter().zip(sources).map(|(name, source)| {
                SourceModuleInput { name, source }
            }).collect();
            let mut limits = SourceProgramLimits::new(fln::EngineExecutionLimits::for_user_program(
                fln::Budget::for_stack_bytes(OLEAN_CHECK_KERNEL_STACK_BYTES),
            ));
            limits.modules.source.max_bytes = max_bytes;
            if let Err(error) = preflight_source_program(&inputs, limits.modules) {
                return Some(failure(module_error(error), presentation));
            }
            let base = match loaded.base_engine(
                || Ok(fln::Engine::from_environment(fln::Environment::new())),
                jobs,
                posture,
            ) {
                Ok((_, base)) => base,
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
            let completed = match receipt.execute_source_modules(
                &inputs, &names[0], &fln::KVMap::new(), limits, None,
            ) {
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
                    Ok(output) => output,
                    Err(error) => failure(error, presentation),
                },
                Presentation::Fln { json } => {
                    match render(&completed, &names[0], loaded.total_bytes, base.as_ref(), json) {
                        Ok(stdout) => MultiplexerOutput::success(stdout),
                        Err(error) => failure(error, presentation),
                    }
                }
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
/// such a world may lack (`Init.Prelude` declares neither), while this door's printer needs
/// none. Printing there would accept what the pin refuses. A non-`prelude` file imports `Init`
/// implicitly at the pin, so its instances exist whatever this closure holds.
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
        && module
            .commands
            .outputs
            .iter()
            .any(|output| matches!(output, fln::SourceCommandOutput::Evaluation { .. }))
    {
        return Err(Failure::new(
            "capability",
            "this prelude file's imports do not reach `Init`; the pin prints an #eval through \
             the Repr or ToString instance its world declares and refuses it without one, and \
             that instance-directed printing is not implemented",
            false,
            CAPABILITY_NOT_IMPLEMENTED_EXIT,
        ));
    }
    Ok(render_lean_source_commands(&module.commands))
}

fn render(
    program: &SourceProgramExecution,
    entry: &Name,
    source_bytes: usize,
    base: Option<&OleanBase>,
    json: bool,
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
        append(&mut output, "]}\n")?;
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
                    let type_ = fln::pretty::Printer::new(commands.batch.engine.environment())
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
                assert!(render(&program, &entry, 0, None, true).is_ok());
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
                    let error = match render(&program, &entry, 0, None, json) {
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
