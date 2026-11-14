//! Check Lake source files and execute declared programs on the native pipeline.
//! Package discovery supplies exact module identities and source directories;
//! the ordinary Lean runner supplies import admission, compilation, main's ABI,
//! bounded stdout and the program's exit status. This does not emit or claim a
//! native executable artifact.

use super::*;

#[derive(Clone, Copy)]
pub(crate) enum DriverKind {
    Test,
    Lint,
}

impl DriverKind {
    pub(super) fn label(self) -> &'static str {
        match self {
            Self::Test => "test",
            Self::Lint => "lint",
        }
    }

    fn configured(self, config: &LakeConfig) -> (&str, &[String]) {
        match self {
            Self::Test => (&config.test_driver, &config.test_driver_args),
            Self::Lint => (&config.lint_driver, &config.lint_driver_args),
        }
    }
}

pub(crate) enum ExecutableSelection {
    Named(String),
    Driver(DriverKind),
}

impl ExecutableSelection {
    fn schema(&self) -> &'static str {
        match self {
            Self::Named(_) => "fln.lake-exe/1",
            Self::Driver(DriverKind::Test) => "fln.lake-test/1",
            Self::Driver(DriverKind::Lint) => "fln.lake-lint/1",
        }
    }

    fn command(&self) -> &'static str {
        match self {
            Self::Named(_) => "lake exe",
            Self::Driver(DriverKind::Test) => "lake test",
            Self::Driver(DriverKind::Lint) => "lake lint",
        }
    }
}

fn program(
    entry: Name,
    location: SourceLocation,
    import_root: PathBuf,
    sources: &local_dependencies::Sources,
    max_bytes: usize,
) -> Result<source_check::PackageProgram, Failure> {
    let entry_path = location.path.clone();
    // Only the selected entry can be an executable or external source module.
    // Other local imports belong to declared libraries, as in Lake's
    // findModule? / findTargetModule? distinction. A loose file or another
    // executable cannot silently become an ambient library.
    let mut paths = BTreeMap::<PathBuf, Name>::new();
    let mut modules = load_sources_with(std::slice::from_ref(&entry), max_bytes, |module| {
        let selected = if module == &entry {
            Some(SourceLocation {
                package: location.package.clone(),
                path: entry_path.clone(),
            })
        } else {
            sources.resolve(module)?
        };
        let Some(location) = selected else {
            return Ok(None);
        };
        let path = &location.path;
        check_path(&location.package, path, false)?;
        let canonical = path
            .canonicalize()
            .map_err(|error| Failure::io(path, error))?;
        if !canonical.starts_with(&location.package) {
            return Err(Failure::input("source file escaped its package"));
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
    // Selecting a file does not make an executable root or external module
    // importable, nor override a different package's same-named library file.
    if modules
        .values()
        .any(|module| module.imports.contains(&entry))
    {
        let imported = sources.resolve(&entry)?;
        if imported.as_ref().is_none_or(|imported| {
            imported.package != location.package || imported.path != entry_path
        }) {
            return Err(Failure::unsupported(format!(
                "selected source module `{}` has a different library-import source or is not importable",
                entry.to_display_string(),
            )));
        }
    }
    sources.verify_configurations()?;
    let first = modules
        .remove(&entry)
        .ok_or_else(|| Failure::new("internal-fault", "source entry was not captured"))?;
    let mut sources = Vec::with_capacity(modules.len() + 1);
    sources.push((entry, first.source));
    sources.extend(
        modules
            .into_iter()
            .map(|(name, module)| (name, module.source)),
    );
    Ok(source_check::PackageProgram {
        entry_path,
        root: import_root,
        modules: sources,
    })
}

pub(crate) fn run(
    directory: PathBuf,
    selection: ExecutableSelection,
    arguments: Vec<OsString>,
    json: bool,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
    vm_limits: fln::VmExecutionLimits,
) -> MultiplexerOutput {
    let schema = selection.schema();
    let command = selection.command();
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
            let evaluation = Some((jobs, posture));
            let loaded =
                match load_configuration(&root, ConfigurationSelection::Default, evaluation) {
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
            let sources = local_dependencies::load(&root, loaded, evaluation)?;
            let (package, executable, arguments) = match selection {
                ExecutableSelection::Named(target) => {
                    let (package, executable) = sources.executable(&target)?;
                    (package, executable, arguments)
                }
                ExecutableSelection::Driver(kind) => {
                    // Driver options belong to the invocation's root package,
                    // including when another package owns the selected target.
                    let root = sources.package("")?;
                    let (driver, configured) = kind.configured(&root.config);
                    let arguments = match source_main::arguments(
                        configured
                            .iter()
                            .cloned()
                            .chain(arguments)
                            .map(OsString::from),
                        SOURCE_RUN_DEFAULT_MAX_BYTES,
                    ) {
                        Ok(arguments) => arguments,
                        Err(error) => return Ok(error.output()),
                    };
                    let (package, executable) =
                        sources.driver(kind, driver, !arguments.is_empty())?;
                    (package, executable, arguments)
                }
            };
            let [root_name] = executable.roots.as_slice() else {
                return Err(Failure::input(
                    "an executable must have exactly one root module",
                ));
            };
            let entry = name(root_name)?;
            let directory = executable.src_dir.as_deref().unwrap_or(Path::new("."));
            relative_directory(directory)?;
            let location = SourceLocation {
                package: package.root.clone(),
                path: package
                    .root
                    .join(&package.config.src_dir)
                    .join(directory)
                    .join(source_import_relative_path(&entry)?),
            };
            let program = program(
                entry,
                location,
                package.root.clone(),
                &sources,
                SOURCE_RUN_DEFAULT_MAX_BYTES,
            )?;
            Ok(source_check::run_package(
                program,
                Some(arguments),
                SOURCE_RUN_DEFAULT_MAX_BYTES,
                jobs,
                posture,
                vm_limits,
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
    result.unwrap_or_else(|error| error.render_as(json, schema, command))
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn run_source(
    directory: PathBuf,
    path: PathBuf,
    json: bool,
    max_bytes: usize,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
    vm_limits: fln::VmExecutionLimits,
) -> MultiplexerOutput {
    let worker = std::thread::Builder::new()
        .name("fln-lake-source".to_owned())
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(move || {
            let root = directory
                .canonicalize()
                .map_err(|error| Failure::io(&directory, error))?;
            // Like prepareLeanCommand in the pin, FILE is relative to the
            // caller's directory, even when --dir selects another workspace.
            let path = std::path::absolute(&path).map_err(|error| Failure::io(&path, error))?;
            let filesystem_root = path
                .ancestors()
                .last()
                .ok_or_else(|| Failure::input("source file has no filesystem root"))?;
            check_path(filesystem_root, &path, false)?;
            let path = path
                .canonicalize()
                .map_err(|error| Failure::io(&path, error))?;
            if !source_import_candidate_is_file(&path)? {
                return Err(Failure::input("source file is missing"));
            }
            let evaluation = Some((jobs, posture));
            let loaded = load_configuration(&root, ConfigurationSelection::Default, evaluation)?;
            let sources = local_dependencies::load(&root, loaded, evaluation)?;
            let (entry, location) = match sources.source_file(&path)? {
                Some(selected) => selected,
                None => (
                    // setupExternalModule supplies exactly this synthetic
                    // module identity to Lean's --setup input in the pin.
                    Name::from_components(["_unknown"]),
                    SourceLocation {
                        package: path
                            .parent()
                            .ok_or_else(|| Failure::input("source file has no parent"))?
                            .to_path_buf(),
                        path,
                    },
                ),
            };
            let program = program(entry, location, root, &sources, max_bytes)?;
            Ok(source_check::run_package(
                program, None, max_bytes, jobs, posture, vm_limits,
            ))
        });
    let result = match worker {
        Ok(worker) => worker
            .join()
            .unwrap_or_else(|_| Err(Failure::new("internal-fault", "source worker panicked"))),
        Err(error) => Err(Failure::new(
            "resource",
            format!("could not start source worker: {error}"),
        )),
    };
    result.unwrap_or_else(|error| error.render_as(json, "fln.lake-lean/1", "lake lean"))
}
