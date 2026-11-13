//! Execute declared Lake programs on the checked native Golem pipeline.
//! Package discovery supplies exact module identities and source directories;
//! the ordinary Lean runner supplies import admission, compilation, main's ABI,
//! bounded stdout and the program's exit status. This does not emit or claim a
//! native executable artifact.

use super::*;

fn program(
    root: &Path,
    config: &LakeConfig,
    target: &str,
) -> Result<source_check::PackageProgram, Failure> {
    let sources = local_dependencies::load(root, config)?;
    let executable = config
        .targets
        .iter()
        .find(|candidate| candidate.name == target && candidate.kind == TargetKind::Executable)
        .ok_or_else(|| Failure::input(format!("unknown executable `{target}`")))?;
    let [root_name] = executable.roots.as_slice() else {
        return Err(Failure::input(
            "an executable must have exactly one root module",
        ));
    };
    let entry = name(root_name)?;
    let directory = executable.src_dir.as_deref().unwrap_or(Path::new("."));
    relative_directory(directory)?;
    let entry_path = root
        .join(&config.src_dir)
        .join(directory)
        .join(source_import_relative_path(&entry)?);
    // Only the selected executable's root is an executable source module.
    // Other local imports belong to declared libraries, as in Lake's
    // findModule? / findTargetModule? distinction. A loose file or another
    // executable cannot silently become an ambient library.
    let mut paths = BTreeMap::<PathBuf, Name>::new();
    let mut modules = load_sources_with(std::slice::from_ref(&entry), |module| {
        let location = if module == &entry {
            Some(SourceLocation {
                package: root.to_path_buf(),
                path: entry_path.clone(),
            })
        } else {
            sources.resolve(module)?
        };
        let Some(location) = location else {
            return Ok(None);
        };
        let path = &location.path;
        check_path(&location.package, path, false)?;
        let canonical = path
            .canonicalize()
            .map_err(|error| Failure::io(path, error))?;
        if !canonical.starts_with(&location.package) {
            return Err(Failure::input("executable source escaped its package"));
        }
        if let Some(previous) = paths.insert(canonical, module.clone())
            && previous != *module
        {
            return Err(Failure::input(format!(
                "source modules `{}` and `{}` resolve to the same file",
                previous.to_display_string(),
                module.to_display_string(),
            )));
        }
        Ok(Some(location))
    })?;
    sources.verify_configurations()?;
    let first = modules
        .remove(&entry)
        .ok_or_else(|| Failure::new("internal-fault", "executable root was not captured"))?;
    let mut sources = Vec::with_capacity(modules.len() + 1);
    sources.push((entry, first.source));
    sources.extend(
        modules
            .into_iter()
            .map(|(name, module)| (name, module.source)),
    );
    Ok(source_check::PackageProgram {
        entry_path,
        root: root.to_path_buf(),
        modules: sources,
    })
}

pub(crate) fn run(
    directory: PathBuf,
    target: String,
    arguments: Vec<OsString>,
    json: bool,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
    vm_limits: fln::VmExecutionLimits,
) -> MultiplexerOutput {
    // Validate raw argv before reading or executing a Lean configuration.
    let arguments = match source_main::arguments(arguments, SOURCE_RUN_DEFAULT_MAX_BYTES) {
        Ok(arguments) => arguments,
        Err(error) => return error.output(),
    };
    let worker = std::thread::Builder::new()
        .name("fln-lake-executable".to_owned())
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(move || {
            let root = directory
                .canonicalize()
                .map_err(|error| Failure::io(&directory, error))?;
            let loaded = if root.join("lakefile.toml").is_file() {
                executable_config(&root).map(|config| (config, None))
            } else {
                load_configuration(&root, jobs, posture)
            };
            let (config, _) = match loaded {
                Err(error) if error.class == "missing-configuration" && !json => {
                    return Ok(MultiplexerOutput::failure(
                        format!(
                            "error: no such file or directory (error code: 2)\n  file: {}\n",
                            root.join("lakefile.lean").display()
                        ),
                        1,
                    ));
                }
                result => result?,
            };
            let program = program(&root, &config, &target)?;
            Ok(source_check::run_package_main(
                program, arguments, jobs, posture, vm_limits,
            ))
        });
    let result = match worker {
        Ok(worker) => worker
            .join()
            .unwrap_or_else(|_| Err(Failure::new("internal-fault", "executable worker panicked"))),
        Err(error) => Err(Failure::new(
            "resource",
            format!("could not start executable worker: {error}"),
        )),
    };
    result.unwrap_or_else(|error| error.render_as(json, "fln.lake-exe/1", "lake exe"))
}
