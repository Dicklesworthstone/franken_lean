//! Air-gapped declaration verification over complete, checked `.olean` inputs.
//! The capsule library owns the semantic profile and both checking seats. This
//! adapter only resolves files, supplies budgets and publishes completed bytes.
use super::{
    BoundedReadFailure, BoundedText, CAPSULE_DEFAULT_MAX_BYTES, MultiplexerCommand,
    MultiplexerOutput, OLEAN_CHECK_KERNEL_STACK_BYTES, OsString, Path, PathBuf, UsageError,
    VERIFY_CAPSULE_SCHEMA, VerifyCapsuleFailure, collect_olean_directory, json_string,
    parse_path_options, read_bounded, verify_capsule_bytes, verify_capsule_failure,
};
use fln::capsule::{
    CapsuleLimits, CapsuleVerification, PINNED_EPOCH, SemanticCapsuleReport, seal_olean_capsule,
    verify_olean_capsule,
};

const SEAL_SCHEMA: &str = "fln.seal-capsule/1";

pub(super) fn parse(
    arguments: Vec<OsString>,
    seal: bool,
) -> Result<MultiplexerCommand, UsageError> {
    let command = if seal {
        "seal-capsule"
    } else {
        "verify-capsule"
    };
    let mut output = None;
    let mut require_semantic = false;
    let mut filtered = Vec::new();
    let mut arguments = arguments.into_iter();
    let mut options = true;
    while let Some(argument) = arguments.next() {
        if options && argument == "--" {
            options = false;
        } else if options && seal && argument == "--output" {
            if output.is_some() {
                return Err(UsageError("--output may be specified only once".into()));
            }
            output = Some(PathBuf::from(arguments.next().ok_or_else(|| {
                UsageError("--output requires a following path".into())
            })?));
            continue;
        } else if options && !seal && argument == "--require-semantic" {
            require_semantic = true;
            continue;
        }
        filtered.push(argument);
    }
    let Some((paths, max_bytes, json)) =
        parse_path_options(filtered, command, CAPSULE_DEFAULT_MAX_BYTES)?
    else {
        return Ok(MultiplexerCommand::Help);
    };
    let [path] = paths.as_slice() else {
        return Err(UsageError(format!(
            "{command} accepts exactly one input path"
        )));
    };
    if seal {
        Ok(MultiplexerCommand::SealCapsule {
            directory: path.clone(),
            output: output
                .ok_or_else(|| UsageError("seal-capsule requires --output PATH".into()))?,
            max_bytes,
            json,
        })
    } else {
        Ok(MultiplexerCommand::VerifyCapsule {
            path: path.clone(),
            max_bytes,
            json,
            require_semantic,
        })
    }
}

#[derive(Clone, Copy)]
enum Command {
    Seal,
    Verify,
}

impl Command {
    fn name(self) -> &'static str {
        match self {
            Self::Seal => "seal-capsule",
            Self::Verify => "verify-capsule",
        }
    }

    fn schema(self) -> &'static str {
        match self {
            Self::Seal => SEAL_SCHEMA,
            Self::Verify => VERIFY_CAPSULE_SCHEMA,
        }
    }
}

fn failure(
    command: Command,
    disposition: (&str, bool, u8),
    detail: &str,
    json: bool,
) -> MultiplexerOutput {
    let (class, authority, exit_code) = disposition;
    let detail = BoundedText::new(detail);
    let stderr = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"error\",\"authority\":{},",
                "\"class\":{},\"detail\":{},\"detailTruncated\":{}}}\n"
            ),
            json_string(command.schema()),
            authority,
            json_string(class),
            json_string(detail.text()),
            detail.truncated(),
        )
    } else {
        format!("fln {}: {class}: {}\n", command.name(), detail.text())
    };
    MultiplexerOutput::failure(stderr, exit_code)
}

fn read_failure(command: Command, error: BoundedReadFailure, json: bool) -> MultiplexerOutput {
    let class = error.class();
    failure(
        command,
        (class, false, if class == "resource" { 3 } else { 1 }),
        &error.to_string(),
        json,
    )
}

fn worker(
    command: Command,
    json: bool,
    work: impl FnOnce() -> MultiplexerOutput + Send + 'static,
) -> MultiplexerOutput {
    let worker = match std::thread::Builder::new()
        .name(format!("fln-{}", command.name()))
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(work)
    {
        Ok(worker) => worker,
        Err(error) => {
            return failure(
                command,
                ("internal_fault", false, 4),
                &format!("could not start bounded kernel worker: {error}"),
                json,
            );
        }
    };
    match worker.join() {
        Ok(output) => output,
        Err(_) => failure(
            command,
            ("internal_fault", false, 4),
            "bounded kernel worker panicked",
            json,
        ),
    }
}

fn limits(max_bytes: usize) -> CapsuleLimits {
    CapsuleLimits::new(
        max_bytes,
        fln::Budget::for_stack_bytes(OLEAN_CHECK_KERNEL_STACK_BYTES),
    )
}

fn success(
    command: Command,
    path: &Path,
    bytes: usize,
    report: &SemanticCapsuleReport,
    json: bool,
) -> MultiplexerOutput {
    let status = match command {
        Command::Seal => "sealed",
        Command::Verify => "declarations_verified",
    };
    let stdout = if json {
        format!(
            concat!(
                "{{\"schema\":{},\"outcome\":\"complete\",\"path\":{},",
                "\"status\":{},\"verification_method\":\"full_recomputation\",",
                "\"modules_verified\":{},\"declarations_verified\":{},\"bytes\":{},",
                "\"manifest_root\":{},\"archive_digest\":{},",
                "\"base_logical_root\":{},\"result_logical_root\":{}}}\n"
            ),
            json_string(command.schema()),
            json_string(&path.display().to_string()),
            json_string(status),
            report.modules,
            report.declarations,
            bytes,
            json_string(&report.manifest_root.to_hex()),
            json_string(&report.archive_digest.to_hex()),
            json_string(&report.base_logical_root.0.to_hex()),
            json_string(&report.result_logical_root.0.to_hex()),
        )
    } else {
        format!(
            concat!(
                "fln {}: {} at {}\n",
                "  verification method: full recomputation through kernel and independent checker\n",
                "  modules verified: {}\n",
                "  declarations verified: {}\n",
                "  bytes: {}\n",
                "  manifest root: {}\n",
                "  archive digest: {}\n",
                "  base logical root: {}\n",
                "  result logical root: {}\n"
            ),
            command.name(),
            status,
            path.display(),
            report.modules,
            report.declarations,
            bytes,
            report.manifest_root.to_hex(),
            report.archive_digest.to_hex(),
            report.base_logical_root.0.to_hex(),
            report.result_logical_root.0.to_hex(),
        )
    };
    MultiplexerOutput::success(stdout)
}

pub(super) fn seal(
    directory: PathBuf,
    output: PathBuf,
    max_bytes: usize,
    json: bool,
) -> MultiplexerOutput {
    match std::fs::symlink_metadata(&directory) {
        Ok(metadata) if metadata.is_dir() && !metadata.file_type().is_symlink() => {}
        Ok(_) => {
            return failure(
                Command::Seal,
                ("input", false, 1),
                "seal-capsule requires a regular directory of named .olean modules",
                json,
            );
        }
        Err(error) => {
            return failure(
                Command::Seal,
                ("input", false, 1),
                &format!("cannot open {}: {error}", directory.display()),
                json,
            );
        }
    }
    let modules = match collect_olean_directory(&directory, max_bytes) {
        Ok(modules) => modules,
        Err(error) => return read_failure(Command::Seal, error, json),
    };
    worker(Command::Seal, json, move || {
        let inputs: Vec<_> = modules
            .iter()
            .map(|module| fln::OleanModuleInput {
                name: &module.name,
                artifact: &module.bytes,
                server_artifact: module.server_bytes.as_deref(),
                private_artifact: module.private_bytes.as_deref(),
            })
            .collect();
        match seal_olean_capsule(&inputs, &fln::KVMap::new(), PINNED_EPOCH, limits(max_bytes)) {
            Ok(fln::Outcome::Complete(sealed)) => {
                // All graph members and companion parts have completed both
                // checks. A rejected prefix never reaches the publication API.
                if let Err(error) = fln::publish_file_atomic(&sealed.bytes, &output) {
                    let disposition = super::publication_failure_disposition(&error);
                    return failure(
                        Command::Seal,
                        disposition,
                        &format!(
                            "could not complete durable capsule publication to {}: {error}",
                            output.display(),
                        ),
                        json,
                    );
                }
                success(
                    Command::Seal,
                    &output,
                    sealed.bytes.len(),
                    &sealed.report,
                    json,
                )
            }
            Ok(fln::Outcome::Inconclusive(reason)) => failure(
                Command::Seal,
                ("inconclusive", false, 3),
                &format!("{reason:?}"),
                json,
            ),
            Ok(fln::Outcome::InternalFault(fault)) => failure(
                Command::Seal,
                ("internal_fault", false, 4),
                &format!("{fault:?}"),
                json,
            ),
            Err(error) => failure(Command::Seal, error.disposition(), &error.to_string(), json),
        }
    })
}

pub(super) fn verify(
    path: PathBuf,
    max_bytes: usize,
    json: bool,
    require_semantic: bool,
) -> MultiplexerOutput {
    let bytes = match read_bounded(&path, max_bytes, ".flnpack capsule") {
        Ok(bytes) => bytes,
        Err(error) => return verify_capsule_failure(VerifyCapsuleFailure::Read(error), json),
    };
    worker(Command::Verify, json, move || {
        match verify_olean_capsule(&bytes, limits(max_bytes)) {
            Ok(fln::Outcome::Complete(CapsuleVerification::Semantic(report))) => {
                success(Command::Verify, &path, bytes.len(), &report, json)
            }
            Ok(fln::Outcome::Complete(CapsuleVerification::Legacy)) if !require_semantic => {
                verify_capsule_bytes(&path, &bytes, max_bytes, json)
            }
            Ok(fln::Outcome::Complete(CapsuleVerification::Legacy)) => failure(
                Command::Verify,
                ("refusal", false, 1),
                "semantic verification was required, but this capsule has no supported declaration profile",
                json,
            ),
            Ok(fln::Outcome::Inconclusive(reason)) => failure(
                Command::Verify,
                ("inconclusive", false, 3),
                &format!("{reason:?}"),
                json,
            ),
            Ok(fln::Outcome::InternalFault(fault)) => failure(
                Command::Verify,
                ("internal_fault", false, 4),
                &format!("{fault:?}"),
                json,
            ),
            Err(error) => failure(
                Command::Verify,
                error.disposition(),
                &error.to_string(),
                json,
            ),
        }
    })
}
