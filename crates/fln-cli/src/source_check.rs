//! User-facing source proof checking. No compiler or VM is entered.
use super::*;

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
    // Native stack calibration is tied to the actual worker, not the caller's
    // unknown stack. No process-wide stream or environment is changed.
    let worker = std::thread::Builder::new().name("fln-source-check".to_owned())
        .stack_size(SOURCE_RUN_KERNEL_STACK_BYTES).spawn(move || {
            let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES));
            let engine = match fln::Engine::with_source_seed(admission) {
                Ok(fln::Outcome::Complete(engine)) => engine,
                Ok(fln::Outcome::Inconclusive(_)) => return failed("inconclusive", "source prelude could not complete", false, json, 3),
                Ok(fln::Outcome::InternalFault(_)) => return failed("internal-fault", "source prelude faulted", false, json, 4),
                Err(error) => {
                    let (class, authority, exit) = admission_error_disposition(&error);
                    return failed(class, &error.to_string(), authority, json, exit);
                }
            };
            let mut limits = fln::SourceCheckLimits::new(admission);
            limits.max_bytes = max_bytes;
            let inputs: Vec<_> = sources.iter().map(Vec::as_slice).collect();
            let result = match engine.check_source_files(&inputs, &fln::KVMap::new(), limits) {
                Ok(fln::Outcome::Complete(result)) => result,
                Ok(fln::Outcome::Inconclusive(_)) => return failed("inconclusive", "source check exhausted its configured resources", false, json, 3),
                Ok(fln::Outcome::InternalFault(_)) => return failed("internal-fault", "source check encountered an internal fault", false, json, 4),
                Err(error) => {
                    let (class, authority, exit) = error.disposition();
                    return failed(class, &error.to_string(), authority, json, exit);
                }
            };
            let stdout = if json {
                format!("{{\"schema\":\"fln.source-check/1\",\"outcome\":\"complete\",\"authority\":true,\"files\":{},\"commands\":{},\"theorems\":{},\"sourceBytes\":{},\"baseLogicalRoot\":{},\"resultLogicalRoot\":{},\"executed\":false}}\n",
                    result.files, result.commands, result.theorems, total, json_string(&result.base_logical_root.to_string()), json_string(&result.result_logical_root.to_string()))
            } else {
                format!("Checked {} declarations ({} theorems) in {} files; K1 and independent checker agreed. No code executed.\n",result.commands,result.theorems,result.files)
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
