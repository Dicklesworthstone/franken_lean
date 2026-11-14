//! Lake's workspace environment over the same checked package discovery used
//! for builds. Only an explicitly requested `lake env COMMAND` starts a child;
//! configuration loading and source checking stay on the native pipeline.

use super::*;
use std::ffi::OsStr;

struct Environment {
    variables: Vec<(&'static str, Option<OsString>)>,
}

fn inherited_paths(key: &str) -> Vec<PathBuf> {
    std::env::var_os(key)
        .map(|value| std::env::split_paths(&value).collect())
        .unwrap_or_default()
}

fn joined(paths: impl IntoIterator<Item = PathBuf>, key: &str) -> Result<OsString, Failure> {
    std::env::join_paths(paths).map_err(|error| {
        Failure::input(format!(
            "cannot represent workspace paths in {key}: {error}"
        ))
    })
}

fn normalized(path: PathBuf) -> PathBuf {
    // Configured directories have already passed relative_directory. Remove
    // their harmless `.` components without requiring build outputs to exist.
    path.components().collect()
}

fn prepare(
    directory: &Path,
    prefix: &Path,
    executable: &Path,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> Result<Environment, Failure> {
    let root = directory
        .canonicalize()
        .map_err(|error| Failure::io(directory, error))?;
    let evaluation = Some((jobs, posture));
    let sources = match load_configuration(&root, ConfigurationSelection::Default, evaluation) {
        Ok(configuration) => Some(local_dependencies::load(&root, configuration, evaluation)?),
        Err(error) if error.class == "missing-configuration" => None,
        Err(error) => return Err(error),
    };
    let mut binaries = Vec::new();
    let mut libraries = Vec::new();
    let mut source_directories = Vec::new();
    let mut shared_libraries = Vec::new();
    if let Some(sources) = &sources {
        // Workspace.binPath/leanPath/leanSrcPath prepend successive packages.
        // sharedLibPath deliberately retains the opposite, root-first order.
        for package in sources.packages.iter().rev() {
            let build = package.root.join(&package.config.build_dir);
            binaries.push(normalized(build.join("bin")));
            libraries.push(normalized(build.join("lib/lean")));
            for target in &package.config.targets {
                if target.kind == TargetKind::Library {
                    source_directories.push(normalized(
                        package
                            .root
                            .join(&package.config.src_dir)
                            .join(target.src_dir.as_deref().unwrap_or(Path::new("."))),
                    ));
                }
            }
        }
        for package in &sources.packages {
            shared_libraries.push(normalized(
                package.root.join(&package.config.build_dir).join("lib"),
            ));
        }
        sources.verify_configurations()?;
    }

    let toolchain_bin = prefix.join("bin");
    // As in Lake.Env.path, a separately located Lake comes before Lean's
    // toolchain bin. This also keeps a development build's native siblings
    // reachable when LEAN_SYSROOT points at a separately installed library.
    let lake_bin = executable
        .parent()
        .ok_or_else(|| Failure::input("Lake executable has no parent"))?;
    if cfg!(windows) {
        binaries.extend(shared_libraries.iter().cloned());
    }
    if lake_bin != toolchain_bin {
        binaries.push(lake_bin.to_path_buf());
    }
    binaries.push(toolchain_bin);
    binaries.extend(inherited_paths("PATH"));
    libraries.push(prefix.join("lib/lean"));
    libraries.extend(inherited_paths("LEAN_PATH"));
    source_directories.push(prefix.join("src/lean/lake"));
    source_directories.extend(inherited_paths("LEAN_SRC_PATH"));

    let mut variables = vec![
        (
            "ELAN_TOOLCHAIN",
            std::env::var_os("ELAN_TOOLCHAIN").filter(|value| !value.is_empty()),
        ),
        ("LAKE", Some(executable.as_os_str().to_owned())),
        (
            "LEAN",
            Some(
                lake_bin
                    .join(format!("lean{}", std::env::consts::EXE_SUFFIX))
                    .into_os_string(),
            ),
        ),
        ("LEAN_SYSROOT", Some(prefix.as_os_str().to_owned())),
        ("LEAN_PATH", Some(joined(libraries, "LEAN_PATH")?)),
        (
            "LEAN_SRC_PATH",
            Some(joined(source_directories, "LEAN_SRC_PATH")?),
        ),
        (
            "LEAN_GITHASH",
            Some(
                std::env::var_os("LEAN_GITHASH")
                    .filter(|value| !value.is_empty())
                    .unwrap_or_else(|| OsString::from(fln::OLEAN_PIN_COMMIT)),
            ),
        ),
        ("PATH", Some(joined(binaries, "PATH")?)),
    ];
    if !cfg!(windows) {
        let key = if cfg!(target_os = "macos") {
            "DYLD_LIBRARY_PATH"
        } else {
            "LD_LIBRARY_PATH"
        };
        let mut paths = vec![prefix.join("lib/lean"), prefix.join("lib")];
        paths.extend(shared_libraries);
        paths.extend(inherited_paths(key));
        variables.push((key, Some(joined(paths, key)?)));
    }
    Ok(Environment { variables })
}

fn exit_code(status: std::process::ExitStatus) -> u8 {
    if let Some(code) = status.code() {
        return code as u8;
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        if let Some(signal) = status.signal() {
            return (128 + signal) as u8;
        }
    }
    1
}

pub(crate) fn run(
    directory: PathBuf,
    arguments: Vec<OsString>,
    json: bool,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> MultiplexerOutput {
    let executable = match std::env::current_exe() {
        Ok(executable) => executable,
        Err(error) => {
            return Failure::new("io", format!("cannot locate Lake executable: {error}"))
                .render_as(json, "fln.lake-env/1", "lake env");
        }
    };
    let prefix = match derive_lean_installation_paths(&executable) {
        Ok(installation) => installation.prefix,
        Err(_) => {
            return lake_not_implemented(
                "env",
                "this binary is not in a toolchain layout and LEAN_SYSROOT is not set, so there is no sysroot to report",
                json,
            );
        }
    };
    let worker = std::thread::Builder::new()
        .name("fln-lake-environment".to_owned())
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(move || prepare(&directory, &prefix, &executable, jobs, posture));
    let environment = match worker {
        Ok(worker) => worker.join().unwrap_or_else(|_| {
            Err(Failure::new(
                "internal-fault",
                "environment worker panicked",
            ))
        }),
        Err(error) => Err(Failure::new(
            "resource",
            format!("could not start environment worker: {error}"),
        )),
    };
    let environment = match environment {
        Ok(environment) => environment,
        Err(error) => return error.render_as(json, "fln.lake-env/1", "lake env"),
    };
    let Some((program, arguments)) = arguments.split_first() else {
        let mut output = String::new();
        for (key, value) in environment.variables {
            let Some(value) = value.as_deref().unwrap_or(OsStr::new("")).to_str() else {
                return Failure::unsupported("environment listing requires UTF-8 values; lake env COMMAND preserves native environment bytes")
                    .render_as(json, "fln.lake-env/1", "lake env");
            };
            output.push_str(key);
            output.push('=');
            output.push_str(value);
            output.push('\n');
        }
        return MultiplexerOutput::success(output);
    };
    let mut child = std::process::Command::new(program);
    child.args(arguments);
    for (key, value) in environment.variables {
        match value {
            Some(value) => {
                child.env(key, value);
            }
            None => {
                child.env_remove(key);
            }
        }
    }
    // An explicit env command owns its streams, including arbitrary bytes and
    // interactive input. Capturing into MultiplexerOutput would corrupt binary
    // output and close stdin. No cwd/global-environment mutation is needed.
    child
        .stdin(std::process::Stdio::inherit())
        .stdout(std::process::Stdio::inherit())
        .stderr(std::process::Stdio::inherit());
    match child.status() {
        Ok(status) => MultiplexerOutput {
            stdout: String::new(),
            stderr: String::new(),
            exit_code: exit_code(status),
        },
        Err(error) => MultiplexerOutput::failure(
            format!(
                "could not execute external process '{}': {error}\n",
                program.to_string_lossy()
            ),
            255,
        ),
    }
}
