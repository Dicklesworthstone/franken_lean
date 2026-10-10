//! Checked TOML and native Lean package module builds. Only the Reference's `+Module:olean`
//! facet is complete here; library defaults also require other Lean artifacts.
use super::*;
use fln::source_check::modules::persisted::{ModuleProvenance, PersistedModules};
use fln::source_check::modules::reuse::{ImportPosture, ImportPostureReport};
use fln::source_check::modules::{
    SourceModuleCacheLimits, SourceModuleCheckLimits, SourceModuleSession, parse_source_header,
};
use fln::{Name, Outcome};
use fln_lake::{LakeConfig, TargetKind};
use std::path::Component;

mod explain;
#[path = "lake_config.rs"]
mod lean_config;
mod snapshot;
pub(crate) use explain::explain;

const MAX_MODULES: usize = 256;
const MAX_IMPORTS: usize = 4096;
const MAX_ARTIFACT_BYTES: usize = 64 * 1024 * 1024;

struct Failure {
    class: &'static str,
    detail: String,
    authority: bool,
}
impl Failure {
    fn new(class: &'static str, detail: impl Into<String>) -> Self {
        Self {
            class,
            detail: detail.into(),
            authority: false,
        }
    }
    fn input(detail: impl Into<String>) -> Self {
        Self::new("input", detail)
    }
    fn unsupported(detail: impl Into<String>) -> Self {
        Self::new("unsupported", detail)
    }
    fn io(path: &Path, error: std::io::Error) -> Self {
        Self::new("io", format!("{}: {error}", path.display()))
    }
    fn render(self, json: bool) -> MultiplexerOutput {
        self.render_as(json, "fln.lake-build/2", "lake build")
    }
    fn render_as(self, json: bool, schema: &str, command: &str) -> MultiplexerOutput {
        let detail = BoundedText::new(self.detail);
        let output = if json {
            format!(
                "{{\"schema\":{},\"status\":{},\"class\":{},\"authority\":{},\"error\":{},\"detailTruncated\":{}}}\n",
                json_string(schema),
                json_string(if self.class == "unsupported" {
                    "unsupported"
                } else {
                    "error"
                }),
                json_string(self.class),
                self.authority,
                json_string(detail.text()),
                detail.truncated()
            )
        } else {
            format!("{command}: {}: {}\n", self.class, detail.text())
        };
        MultiplexerOutput::failure(output, 1)
    }
}
impl From<BoundedReadFailure> for Failure {
    fn from(error: BoundedReadFailure) -> Self {
        Self::new(error.class(), error.to_string())
    }
}

struct Library {
    roots: Vec<Name>,
    directory: PathBuf,
}
struct Module {
    source: Vec<u8>,
    imports: Vec<Name>,
}

fn name(text: &str) -> Result<Name, Failure> {
    if text.is_empty() || text.split('.').count() > 128 {
        return Err(Failure::input(
            "module name is empty or exceeds 128 components",
        ));
    }
    for component in text.split('.') {
        if component.is_empty()
            || !component
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
        {
            return Err(Failure::unsupported(format!(
                "module name `{text}` requires unsupported quoted or special components"
            )));
        }
    }
    Ok(Name::from_components(text.split('.')))
}

fn relative_directory(path: &Path) -> Result<(), Failure> {
    if path
        .components()
        .any(|component| !matches!(component, Component::Normal(_) | Component::CurDir))
    {
        return Err(Failure::unsupported(format!(
            "build and source directories must stay within the package: {}",
            path.display()
        )));
    }
    Ok(())
}

fn check_path(root: &Path, path: &Path, allow_missing: bool) -> Result<(), Failure> {
    let relative = path
        .strip_prefix(root)
        .map_err(|_| Failure::input("path escaped package"))?;
    let mut cursor = root.to_owned();
    for component in relative.components() {
        cursor.push(component);
        match std::fs::symlink_metadata(&cursor) {
            Ok(metadata) if metadata.file_type().is_symlink() => {
                return Err(Failure::input(format!(
                    "refusing symlink {}",
                    cursor.display()
                )));
            }
            Ok(_) => {}
            Err(error) if allow_missing && error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(Failure::io(&cursor, error)),
        }
    }
    Ok(())
}

fn belongs(module: &Name, root: &Name) -> bool {
    let mut cursor = module.clone();
    while !cursor.is_anonymous() {
        if &cursor == root {
            return true;
        }
        cursor = cursor.parent();
    }
    false
}

fn source_path(module: &Name, libraries: &[Library]) -> Result<Option<PathBuf>, Failure> {
    let components = source_module_components(module)
        .ok_or_else(|| Failure::input("module names require textual components"))?;
    if components.iter().any(|part| {
        part.is_empty()
            || !part
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || c == '\'')
    }) {
        return Err(Failure::unsupported(format!(
            "module `{}` requires unsupported quoted or special path components",
            module.to_display_string()
        )));
    }
    let mut found = None;
    for library in libraries {
        if library.roots.iter().any(|root| belongs(module, root)) {
            let candidate = library.directory.join(source_import_relative_path(module)?);
            if found
                .as_ref()
                .is_some_and(|previous| previous != &candidate)
            {
                return Err(Failure::input(format!(
                    "module `{}` belongs to libraries with different source directories",
                    module.to_display_string()
                )));
            }
            found = Some(candidate);
        }
    }
    Ok(found)
}

fn config(root: &Path) -> Result<LakeConfig, Failure> {
    let path = root.join("lakefile.toml");
    if !path.is_file() {
        if !root.join("lakefile.lean").exists() {
            return Err(Failure::input(format!(
                "error: no such file or directory (error code: 2)\n  file: {}",
                root.join("lakefile.lean").display()
            )));
        }
        return Err(Failure::unsupported(
            "build explain requires lakefile.toml because it does not elaborate or execute lakefile.lean configuration",
        ));
    }
    check_path(root, &path, false)?;
    let bytes = read_bounded(&path, 64 * 1024, "Lake configuration")?;
    let text =
        std::str::from_utf8(&bytes).map_err(|_| Failure::input("lakefile.toml is not UTF-8"))?;
    LakeConfig::parse_toml_for_build(text).map_err(|error| {
        let class = if matches!(error, fln_lake::LakeParseError::UnsupportedBuildSetting(_)) {
            "unsupported"
        } else {
            "input"
        };
        Failure::new(class, error.to_string())
    })
}

fn plan(
    root: &Path,
    config: &LakeConfig,
    targets: &[String],
) -> Result<(Vec<Library>, Vec<Name>), Failure> {
    relative_directory(&config.src_dir)?;
    relative_directory(&config.build_dir)?;
    let mut libraries = Vec::new();
    for target in &config.targets {
        if target.kind != TargetKind::Library {
            continue;
        }
        let directory = target.src_dir.as_deref().unwrap_or(Path::new("."));
        relative_directory(directory)?;
        libraries.push(Library {
            roots: target
                .roots
                .iter()
                .map(|root| name(root))
                .collect::<Result<_, _>>()?,
            directory: root.join(&config.src_dir).join(directory),
        });
    }
    if targets.is_empty() {
        return Err(Failure::unsupported(
            "default library and executable facets are unavailable; request +Module:olean for a declared lean_lib module",
        ));
    }
    if targets.len() > MAX_MODULES {
        return Err(Failure::new("resource", "build target count exceeds 256"));
    }
    let mut modules = Vec::new();
    for target in targets {
        let Some((module, facet)) = target.split_once(':') else {
            return Err(Failure::unsupported(format!(
                "default target `{target}` requires Lean artifacts or executable linking that are unavailable; request +Module:olean for a declared library module"
            )));
        };
        if facet != "olean" {
            return Err(Failure::unsupported(format!(
                "facet `{facet}` is unavailable; supported module facet: +Module:olean"
            )));
        }
        if !module.starts_with('+') && config.targets.iter().any(|target| target.name == module) {
            return Err(Failure::unsupported(format!(
                "target `{module}` has no library or executable olean facet; select the module explicitly as +{module}:olean"
            )));
        }
        let module = name(module.strip_prefix('+').unwrap_or(module))?;
        if source_path(&module, &libraries)?.is_none() {
            return Err(Failure::input(format!(
                "module `{}` does not belong to a declared lean_lib root",
                module.to_display_string()
            )));
        }
        if !modules.contains(&module) {
            modules.push(module);
        }
    }
    Ok((libraries, modules))
}

fn load_sources(
    root: &Path,
    libraries: &[Library],
    entries: &[Name],
) -> Result<BTreeMap<Name, Module>, Failure> {
    let mut pending: BTreeSet<_> = entries.iter().cloned().collect();
    let mut modules = BTreeMap::new();
    let mut source_bytes = 0usize;
    let mut import_count = 0usize;
    while let Some(module) = pending.pop_first() {
        if modules.contains_key(&module) {
            continue;
        }
        if modules.len() >= MAX_MODULES {
            return Err(Failure::new("resource", "source module count exceeds 256"));
        }
        let path = source_path(&module, libraries)?
            .ok_or_else(|| Failure::input("source module lost its library owner"))?;
        check_path(root, &path, false)?;
        if !source_import_candidate_is_file(&path)? {
            return Err(Failure::input(format!(
                "missing source module {}",
                path.display()
            )));
        }
        let source = read_bounded(
            &path,
            SOURCE_RUN_DEFAULT_MAX_BYTES - source_bytes,
            "Lake module source",
        )?;
        source_bytes += source.len();
        let header = parse_source_header(&source)
            .map_err(|error| Failure::input(format!("{}: {error}", path.display())))?;
        fln::source_check::modules::validate_source_header(&module, &header).map_err(|error| {
            let (class, _, _) = error.disposition();
            Failure::new(class, error.to_string())
        })?;
        let mut imports = header.imports;
        if !header.prelude && !imports.contains(&Name::from_components(["Init"])) {
            imports.insert(0, Name::from_components(["Init"]));
        }
        import_count = import_count
            .checked_add(imports.len())
            .filter(|n| *n <= MAX_IMPORTS)
            .ok_or_else(|| Failure::new("resource", "source import count exceeds 4096"))?;
        for imported in &imports {
            if source_path(imported, libraries)?.is_some() {
                pending.insert(imported.clone());
            }
        }
        modules.insert(module, Module { source, imports });
    }
    Ok(modules)
}

struct Compilation {
    artifacts: BTreeMap<Name, Vec<u8>>,
    elaborated_modules: usize,
    reused_modules: usize,
    /// Modules re-admitted from persisted records (bead `franken_lean-z8j.1.1`).
    cached_modules: usize,
    /// Each module's first provenance in this build, in build order.
    modules: Vec<ModuleProvenance>,
    /// One per external `.olean` closure obtained, in the order obtained.
    imports: Vec<ImportPostureReport>,
}

fn compile(
    root: &Path,
    entries: &[Name],
    modules: &BTreeMap<Name, Module>,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
    records: Option<PersistedModules<'_>>,
) -> Result<Compilation, Failure> {
    let mut artifacts = BTreeMap::new();
    let mut imports = Vec::new();
    let mut elaborated_modules = 0usize;
    let mut reused_modules = 0usize;
    let mut cached_modules = 0usize;
    let mut provenance: Vec<ModuleProvenance> = Vec::new();
    // Retain only one external world, never one large engine per target. Target
    // order is observable on failure and is not rearranged to manufacture hits.
    let mut active: Option<(Vec<Name>, SourceModuleSession)> = None;
    let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(
        SOURCE_RUN_KERNEL_STACK_BYTES,
    ));
    let limits = SourceModuleCheckLimits::new(fln::SourceCheckLimits::new(admission));
    // Refuse unparseable source before any import closure is admitted; that
    // admission is the expensive step, and a parse refusal needs no environment.
    for (name, module) in modules {
        fln::source_check::preflight_source_module(name, &module.source).map_err(|error| {
            let (class, authority, _) = error.disposition();
            Failure {
                class,
                detail: error.to_string(),
                authority,
            }
        })?;
    }
    let mut artifact_bytes = 0usize;
    for entry in entries {
        let mut closure = BTreeSet::new();
        let mut seen = BTreeSet::new();
        let mut external = Vec::new();
        let mut pending = vec![entry.clone()];
        while let Some(name) = pending.pop() {
            if !seen.insert(name.clone()) {
                continue;
            }
            if let Some(module) = modules.get(&name) {
                closure.insert(name);
                // Preserve declared order across local dependencies. Sorting
                // external roots changes equal-priority instance selection.
                pending.extend(module.imports.iter().rev().cloned());
            } else {
                external.push(name);
            }
        }
        // The import receipt retains exact per-module declaration and metadata
        // provenance. The facade projects each local module's own external
        // closure and declared order; sibling imports are never ambient.
        // The exact ordered external roots bind this invocation's immutable
        // import snapshot. Disk outputs never become checked cache entries.
        if active.as_ref().is_none_or(|(roots, _)| roots != &external) {
            let base = source_check::load_build_base(&external, root, jobs, posture).map_err(
                |(class, detail, authority)| Failure {
                    class,
                    detail,
                    authority,
                },
            )?;
            let session = match base {
                Some((base, report)) => {
                    imports.push(report);
                    SourceModuleSession::from_imports(
                        base,
                        fln::KVMap::new(),
                        limits,
                        SourceModuleCacheLimits::default(),
                    )
                }
                None => SourceModuleSession::new(
                    fln::Engine::from_environment(fln::Environment::new()),
                    fln::KVMap::new(),
                    limits,
                    SourceModuleCacheLimits::default(),
                ),
            };
            active = Some((external, session));
        }
        let inputs: Vec<_> = closure
            .iter()
            .map(|name| fln::SourceModuleInput {
                name,
                source: &modules.get(name).expect("loaded dependency").source,
            })
            .collect();
        let budget = fln::OleanWriteBudget {
            max_bytes: MAX_ARTIFACT_BYTES as u64,
            ..Default::default()
        };
        let built = active
            .as_mut()
            .expect("the current external context is installed")
            .1
            .compile_with_records(&inputs, entry, budget, records, None)
            .map_err(|error| {
                let (class, authority, _) = error.disposition();
                Failure {
                    class,
                    detail: error.to_string(),
                    authority,
                }
            })?;
        let built = match built {
            Outcome::Complete(built) => built,
            Outcome::Inconclusive(reason) => {
                return Err(Failure::new(
                    "inconclusive",
                    format!("module build exhausted its resources: {reason:?}"),
                ));
            }
            Outcome::InternalFault(fault) => {
                return Err(Failure::new(
                    "internal-fault",
                    format!("module build faulted: {fault:?}"),
                ));
            }
        };
        elaborated_modules += built.elaborated_modules;
        reused_modules += built.reused_modules;
        cached_modules += built.persisted_modules;
        for row in built.modules {
            if !provenance.iter().any(|seen| seen.name == row.name) {
                provenance.push(row);
            }
        }
        for artifact in built.artifacts {
            if let Some(previous) = artifacts.get(&artifact.name) {
                if previous != &artifact.bytes {
                    return Err(Failure::new(
                        "internal-fault",
                        "shared module produced inconsistent artifacts",
                    ));
                }
                continue;
            }
            artifact_bytes = artifact_bytes
                .checked_add(artifact.bytes.len())
                .filter(|n| *n <= MAX_ARTIFACT_BYTES)
                .ok_or_else(|| {
                    Failure::new("resource", "aggregate artifact bytes exceed 64 MiB")
                })?;
            artifacts.insert(artifact.name, artifact.bytes);
        }
    }
    Ok(Compilation {
        artifacts,
        elaborated_modules,
        reused_modules,
        cached_modules,
        modules: provenance,
        imports,
    })
}

fn publish(
    root: &Path,
    directory: &Path,
    artifacts: &BTreeMap<Name, Vec<u8>>,
) -> Result<Vec<PathBuf>, Failure> {
    check_path(root, directory, true)?;
    std::fs::create_dir_all(directory).map_err(|error| Failure::io(directory, error))?;
    // Serialize this publisher's replacements and rollback snapshots. A crash
    // leaves a lock rather than allowing another build to assume completion.
    let lock_path = directory.join(".fln-olean-build.lock");
    let lock_file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&lock_path)
        .map_err(|error| Failure::io(&lock_path, error))?;
    drop(lock_file);
    struct BuildLock(PathBuf);
    impl Drop for BuildLock {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let _lock = BuildLock(lock_path);
    let mut outputs = Vec::new();
    let mut previous_bytes = 0usize;
    // All source checks, encodings and output preflights precede publication.
    for (name, bytes) in artifacts {
        let mut relative = source_import_relative_path(name)?;
        relative.set_extension("olean");
        let path = directory.join(relative);
        check_path(root, &path, true)?;
        for suffix in ["olean.server", "olean.private", "ir"] {
            if path.with_extension(suffix).exists() {
                return Err(Failure::unsupported(format!(
                    "existing artifact family at {} requires coordinated replacement",
                    path.display()
                )));
            }
        }
        let previous = match std::fs::symlink_metadata(&path) {
            Ok(metadata) if metadata.is_file() => {
                let old = read_bounded(
                    &path,
                    MAX_ARTIFACT_BYTES - previous_bytes,
                    "previous Lake artifact",
                )?;
                previous_bytes += old.len();
                Some(old)
            }
            Ok(_) => {
                return Err(Failure::input(format!(
                    "output is not a regular file: {}",
                    path.display()
                )));
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(error) => return Err(Failure::io(&path, error)),
        };
        outputs.push((path, bytes, previous));
    }
    for (index, (path, bytes, _)) in outputs.iter().enumerate() {
        let result = std::fs::create_dir_all(path.parent().expect("artifact parent"))
            .and_then(|()| fln::publish_file_atomic(bytes, path));
        if let Err(error) = result {
            let mut rollback = Vec::new();
            // The atomic writer may report a directory-sync failure after its
            // rename, so the failing output also belongs in the rollback set.
            for (prior, _, previous) in outputs[..=index].iter().rev() {
                let restored = match previous {
                    Some(bytes) => fln::publish_file_atomic(bytes, prior),
                    None => match std::fs::remove_file(prior) {
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
                        result => result,
                    },
                };
                if let Err(error) = restored {
                    rollback.push(format!("{}: {error}", prior.display()));
                }
            }
            return Err(Failure::new(
                "io",
                format!(
                    "{}: {error}{}",
                    path.display(),
                    if rollback.is_empty() {
                        String::new()
                    } else {
                        format!("; rollback failed: {}", rollback.join("; "))
                    }
                ),
            ));
        }
    }
    Ok(outputs.into_iter().map(|(path, _, _)| path).collect())
}

fn build(
    directory: PathBuf,
    targets: Vec<String>,
    json: bool,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> Result<MultiplexerOutput, Failure> {
    let root = directory
        .canonicalize()
        .map_err(|error| Failure::io(&directory, error))?;
    let (config, configuration_imports) = if root.join("lakefile.toml").is_file() {
        (config(&root)?, None)
    } else {
        let loaded = lean_config::load(&root, jobs, posture)?;
        (loaded.config, Some(loaded.imports))
    };
    let (libraries, entries) = plan(&root, &config, &targets)?;
    let modules = load_sources(&root, &libraries, &entries)?;
    let records = source_check::module_records(posture);
    let Compilation {
        artifacts,
        elaborated_modules,
        reused_modules,
        cached_modules,
        modules: provenance,
        imports,
    } = compile(
        &root,
        &entries,
        &modules,
        jobs,
        posture,
        records.persisted(),
    )?;
    let output_dir = root.join(&config.build_dir).join("lib/lean");
    let paths = publish(&root, &output_dir, &artifacts)?;
    let snapshot = record_snapshot(
        &root,
        &config,
        &libraries,
        &entries,
        &modules,
        &artifacts,
        &output_dir,
        &provenance,
        posture,
        records.state(),
    );
    let output = if json {
        let paths = paths
            .iter()
            .map(|path| json_string(&path.display().to_string()))
            .collect::<Vec<_>>()
            .join(",");
        let imports = imports
            .iter()
            .map(|report| format!("{{{}}}", source_check::posture_json(report)))
            .collect::<Vec<_>>()
            .join(",");
        let configuration_imports = configuration_imports
            .as_ref()
            .map(|report| {
                format!(
                    ",\"configuration_imports\":[{{{}}}]",
                    source_check::posture_json(report)
                )
            })
            .unwrap_or_default();
        let rows = provenance
            .iter()
            .map(|row| {
                let mut fields = format!(
                    "\"name\":{},\"decision\":{}",
                    json_string(&row.name.to_display_string()),
                    json_string(row.decision.as_str())
                );
                if let Some(key) = row.key {
                    fields.push_str(&format!(",\"key\":{}", json_string(&key.to_hex())));
                }
                if let Some(record) = row.record.code() {
                    fields.push_str(&format!(",\"record\":{}", json_string(&record)));
                }
                if let Some(write) = row.record_write.code() {
                    fields.push_str(&format!(",\"recordWrite\":{}", json_string(write)));
                }
                format!("{{{fields}}}")
            })
            .collect::<Vec<_>>()
            .join(",");
        let unavailable = records
            .unavailable()
            .map(|reason| format!(",\"module_records_reason\":{}", json_string(reason)))
            .unwrap_or_default();
        let snapshot = match &snapshot {
            Ok(()) => "\"snapshot\":\"written\"".to_owned(),
            Err(reason) => format!(
                "\"snapshot\":\"failed\",\"snapshot_reason\":{}",
                json_string(reason)
            ),
        };
        format!(
            "{{\"schema\":\"fln.lake-build/2\",\"status\":\"success\",\"package\":{},\"facet\":\"olean\",\"modules_built\":{},\"modules_cached\":{cached_modules},\"module_elaborations\":{elaborated_modules},\"module_checks_reused\":{reused_modules},\"artifacts\":[{paths}],\"admission\":\"K1+independent-checker\",\"import_posture\":{},\"imports\":[{imports}]{configuration_imports},\"module_records\":{}{unavailable},\"modules\":[{rows}],{snapshot}}}\n",
            json_string(&config.name),
            artifacts.len(),
            json_string(posture.as_str()),
            json_string(records.state()),
        )
    } else {
        let imports = imports
            .iter()
            .map(|report| format!(" Imports: {}.", source_check::posture_sentence(report)))
            .collect::<String>();
        let configuration_imports = configuration_imports
            .as_ref()
            .map(|report| {
                format!(
                    " Configuration imports: {}.",
                    source_check::posture_sentence(report)
                )
            })
            .unwrap_or_default();
        let snapshot = match &snapshot {
            Ok(()) => String::new(),
            Err(reason) => format!(" The build snapshot was not written: {reason}."),
        };
        format!(
            "Built {} checked .olean modules for {} ({elaborated_modules} elaborated, {cached_modules} re-admitted from verified records; {reused_modules} module checks reused).{imports}{configuration_imports}{snapshot}\n",
            artifacts.len(),
            config.name
        )
    };
    Ok(MultiplexerOutput::success(output))
}

/// Write the build snapshot `fln build explain` compares against (bead
/// `franken_lean-z8j.1.2`). It records inputs and outputs only; nothing reads it back
/// as an authority. A failure is reported, never a reason to fail a published build.
#[allow(clippy::too_many_arguments)]
fn record_snapshot(
    root: &Path,
    config: &LakeConfig,
    libraries: &[Library],
    entries: &[Name],
    modules: &BTreeMap<Name, Module>,
    artifacts: &BTreeMap<Name, Vec<u8>>,
    output_dir: &Path,
    provenance: &[ModuleProvenance],
    posture: ImportPosture,
    records: &str,
) -> Result<(), String> {
    let relative = |path: &Path| {
        path.strip_prefix(root)
            .unwrap_or(path)
            .display()
            .to_string()
    };
    let mut rows = Vec::new();
    let mut external = BTreeSet::new();
    for (name, bytes) in artifacts {
        let module = modules
            .get(name)
            .ok_or("an artifact has no source module")?;
        let source = source_path(name, libraries)
            .map_err(|failure| failure.detail)?
            .ok_or("a built module has no library owner")?;
        let mut artifact =
            source_import_relative_path(name).map_err(|failure| failure.to_string())?;
        artifact.set_extension("olean");
        for import in &module.imports {
            if !modules.contains_key(import) {
                external.insert(import.clone());
            }
        }
        let row = provenance.iter().find(|row| &row.name == name);
        rows.push(snapshot::ModuleRow {
            name: name.to_display_string(),
            source: relative(&source),
            source_digest: snapshot::digest(&module.source),
            imports: module.imports.iter().map(Name::to_display_string).collect(),
            artifact: relative(&output_dir.join(artifact)),
            artifact_digest: snapshot::digest(bytes),
            key: row.and_then(|row| row.key).map(|key| key.to_hex()),
            decision: row
                .map_or("elaborated", |row| row.decision.as_str())
                .to_owned(),
        });
    }
    let roots: Vec<Name> = external.into_iter().collect();
    let externals = if roots.is_empty() {
        Vec::new()
    } else {
        source_check::external_inputs(&roots, root)?
            .into_iter()
            .map(|input| snapshot::ExternalRow {
                name: input.name.to_display_string(),
                digest: input.digest.to_hex(),
                imports: input.imports.iter().map(Name::to_display_string).collect(),
            })
            .collect()
    };
    let text = snapshot::Snapshot {
        posture: posture.as_str().to_owned(),
        records: records.to_owned(),
        targets: entries
            .iter()
            .map(|entry| format!("+{}:olean", entry.to_display_string()))
            .collect(),
        modules: rows,
        externals,
    }
    .to_text();
    let path = root.join(&config.build_dir).join(snapshot::FILE);
    fln::publish_file_atomic(text.as_bytes(), &path)
        .map_err(|error| format!("{}: {error}", path.display()))
}

/// `jobs` external `.olean` closure modules are checked at once; the build does
/// not depend on it.
pub(super) fn run(
    directory: PathBuf,
    targets: Vec<String>,
    json: bool,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> MultiplexerOutput {
    let worker = std::thread::Builder::new()
        .name("fln-lake-build".to_owned())
        // Imports are admitted on this thread under the `.olean` depth budget.
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(move || build(directory, targets, json, jobs, posture));
    match worker {
        Ok(worker) => match worker.join() {
            Ok(Ok(output)) => output,
            Ok(Err(error)) => error.render(json),
            Err(_) => Failure::new("internal-fault", "module build worker panicked").render(json),
        },
        Err(error) => Failure::new(
            "resource",
            format!("could not start module build worker: {error}"),
        )
        .render(json),
    }
}

/// `check-build` loads a Lean configuration before asking whether it has defaults. The
/// subsequent presence check still does not elaborate package sources or build artifacts.
pub(super) fn lean_configuration_for_presence(
    directory: PathBuf,
    json: bool,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> Result<(LakeConfig, ImportPostureReport), MultiplexerOutput> {
    let worker = std::thread::Builder::new()
        .name("fln-lake-configuration".to_owned())
        .stack_size(OLEAN_CHECK_KERNEL_STACK_BYTES)
        .spawn(move || {
            let root = directory
                .canonicalize()
                .map_err(|error| Failure::io(&directory, error))?;
            lean_config::load(&root, jobs, posture).map(|loaded| (loaded.config, loaded.imports))
        });
    let result = match worker {
        Ok(worker) => worker.join().unwrap_or_else(|_| {
            Err(Failure::new(
                "internal-fault",
                "configuration worker panicked",
            ))
        }),
        Err(error) => Err(Failure::new(
            "resource",
            format!("could not start configuration worker: {error}"),
        )),
    };
    result.map_err(|error| error.render_as(json, "fln.lake-check-build/1", "lake check-build"))
}
