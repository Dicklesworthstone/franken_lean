//! User-facing source proof checking. No compiler or VM is entered.
use super::*;
mod imports;
pub(super) mod lsp;

pub(super) fn parse(arguments: Vec<OsString>) -> Result<MultiplexerCommand, UsageError> {
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
    Ok(MultiplexerCommand::SourceCheck {
        paths,
        max_bytes,
        json,
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

pub(super) fn run(paths: Vec<PathBuf>, max_bytes: usize, json: bool) -> MultiplexerOutput {
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
        .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES)
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
            let (engine, olean_base) = match loaded.base_engine(seed) {
                Ok(base) => base,
                Err(error) => return failed(error.class, &error.detail, error.authority, json, error.exit),
            };
            let mut limits = fln::SourceCheckLimits::new(admission);
            limits.max_bytes = max_bytes;
            let result = match loaded.check(&engine, limits) {
                Ok(fln::Outcome::Complete(result)) => result,
                Ok(fln::Outcome::Inconclusive(_)) => return failed("inconclusive", "source check exhausted its configured resources", false, json, 3),
                Ok(fln::Outcome::InternalFault(_)) => return failed("internal-fault", "source check encountered an internal fault", false, json, 4),
                Err(error) => return failed(error.class, &error.detail, error.authority, json, error.exit),
            };
            let olean_json = olean_base.as_ref().map_or(String::new(), |base| {
                format!(",\"oleanImports\":{{\"trust\":\"recheck\",\"modules\":{},\"declarations\":{}}}", base.modules, base.declarations)
            });
            let stdout = if json {
                format!("{{\"schema\":\"fln.source-check/1\",\"outcome\":\"complete\",\"authority\":true,\"files\":{},\"commands\":{},\"theorems\":{},\"sourceBytes\":{},\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},\"executed\":false{}}}\n",
                    result.files, result.commands, result.theorems, loaded.total_bytes,
                    json_string(&result.base_logical_root.to_string()), json_string(&result.result_logical_root.to_string()), olean_json)
            } else {
                let base = olean_base.as_ref().map_or(String::new(), |base| {
                    format!(" against {} imported .olean modules ({} declarations, each admitted by K1 and the independent checker)", base.modules, base.declarations)
                });
                format!("Checked {} source commands ({} theorems) in {} files{base}; K1 and independent checker agreed. No code executed.\n", result.commands, result.theorems, result.files)
            };
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
            return failed_goals(
                error.class(),
                &error.to_string(),
                json,
                error.exit_code(),
            );
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
