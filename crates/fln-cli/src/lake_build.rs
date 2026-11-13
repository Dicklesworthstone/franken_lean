//! Checked TOML and native Lean package module builds. The `+Module:ir` facet
//! also compiles the supported source ABI; library defaults require further artifacts.
use super::*;
use fln::source_check::modules::persisted::{ModuleProvenance, PersistedModules};
use fln::source_check::modules::reuse::{ImportPosture, ImportPostureReport};
use fln::source_check::modules::{SourceModuleCheckLimits, parse_source_header};
use fln::{Name, Outcome};
use fln_lake::{LakeConfig, TargetKind};
use std::path::Component;

mod executable;
mod explain;
mod local_dependencies;
pub(super) use executable::run as run_executable;
#[path = "lake_config.rs"]
mod lean_config;
mod snapshot;
pub(crate) use explain::explain;

const MAX_MODULES: usize = 256;
const MAX_IMPORTS: usize = 4096;
const MAX_ARTIFACT_BYTES: usize = 64 * 1024 * 1024;
/// Ordinary source records and rebuild explanations do not bind macro code,
/// its census policy or selected syntax. Preserve that distinction durably.
const MACRO_RECORDS_UNAVAILABLE: &str = "disabled-imported-macros";
const MACRO_EXPLANATION_UNAVAILABLE: &str = "imported-macro build explanations do not yet bind executable IR, census policy and syntax selection";

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
        // Resource stops and internal faults are nonanswers on both command
        // surfaces, never ordinary source/build rejection (FL-INV-07).
        let (status, exit) = match self.class {
            "resource" | "inconclusive" => ("inconclusive", 3),
            "internal-fault" => ("internal-fault", 4),
            "unsupported" => ("unsupported", 1),
            _ => ("error", 1),
        };
        let detail = BoundedText::new(self.detail);
        let output = if json {
            format!(
                "{{\"schema\":{},\"status\":{},\"class\":{},\"authority\":{},\"error\":{},\"detailTruncated\":{}}}\n",
                json_string(schema),
                json_string(status),
                json_string(self.class),
                self.authority,
                json_string(detail.text()),
                detail.truncated()
            )
        } else if self.class == "missing-configuration" {
            format!(
                "error: [root]: no configuration file with a supported extension:\n{}\n",
                detail.text()
            )
        } else {
            format!("{command}: {}: {}\n", self.class, detail.text())
        };
        MultiplexerOutput::failure(output, exit)
    }
}
impl From<BoundedReadFailure> for Failure {
    fn from(error: BoundedReadFailure) -> Self {
        Self::new(error.class(), error.to_string())
    }
}

#[derive(Clone)]
struct Library {
    roots: Vec<Name>,
    directory: PathBuf,
}
struct Module {
    source: Vec<u8>,
    imports: Vec<Name>,
}

struct SourceLocation {
    package: PathBuf,
    path: PathBuf,
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
    toml_config(root, false)
}

fn executable_config(root: &Path) -> Result<LakeConfig, Failure> {
    toml_config(root, true)
}

fn toml_config(root: &Path, local_requirements: bool) -> Result<LakeConfig, Failure> {
    let path = root.join("lakefile.toml");
    if !path.is_file() {
        if !root.join("lakefile.lean").exists() {
            return Err(Failure::input(format!(
                "error: no such file or directory (error code: 2)\n  file: {}",
                root.join("lakefile.lean").display()
            )));
        }
        if local_requirements {
            return Err(Failure::unsupported(
                "local-path executable dependencies require lakefile.toml configurations",
            ));
        }
        return Err(Failure::unsupported(
            "build explain requires lakefile.toml because it does not elaborate or execute lakefile.lean configuration",
        ));
    }
    check_path(root, &path, false)?;
    let bytes = read_bounded(&path, 64 * 1024, "Lake configuration")?;
    let text =
        std::str::from_utf8(&bytes).map_err(|_| Failure::input("lakefile.toml is not UTF-8"))?;
    let parsed = if local_requirements {
        LakeConfig::parse_toml_for_execution(text)
    } else {
        LakeConfig::parse_toml_for_build(text)
    };
    let config = parsed.map_err(|error| {
        let class = if matches!(error, fln_lake::LakeParseError::UnsupportedBuildSetting(_)) {
            "unsupported"
        } else {
            "input"
        };
        Failure::new(class, error.to_string())
    })?;
    validate_executable_roots(&config)?;
    Ok(config)
}

/// Lake rejects executable targets that claim the same root module, even when
/// their target names or source directories differ.
fn validate_executable_roots(config: &LakeConfig) -> Result<(), Failure> {
    let mut roots = BTreeMap::new();
    for target in &config.targets {
        if target.kind != TargetKind::Executable {
            continue;
        }
        let [root] = target.roots.as_slice() else {
            return Err(Failure::input(
                "an executable must have exactly one root module",
            ));
        };
        let module = name(root)?;
        if let Some(previous) = roots.insert(module, &target.name) {
            return Err(Failure::input(format!(
                "executable targets `{previous}` and `{}` share root module `{root}`",
                target.name
            )));
        }
    }
    Ok(())
}

fn library_sources(root: &Path, config: &LakeConfig) -> Result<Vec<Library>, Failure> {
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
    Ok(libraries)
}

fn plan_modules<'a>(
    target_names: impl IntoIterator<Item = &'a str>,
    libraries: &[Library],
    targets: &[String],
) -> Result<Vec<Name>, Failure> {
    let target_names: BTreeSet<_> = target_names.into_iter().collect();
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
        if !matches!(facet, "olean" | "ir") {
            return Err(Failure::unsupported(format!(
                "facet `{facet}` is unavailable; supported module facets: +Module:olean, +Module:ir"
            )));
        }
        if !module.starts_with('+') && target_names.contains(module) {
            return Err(Failure::unsupported(format!(
                "target `{module}` has no library or executable olean facet; select the module explicitly as +{module}:olean"
            )));
        }
        let module = name(module.strip_prefix('+').unwrap_or(module))?;
        if source_path(&module, libraries)?.is_none() {
            return Err(Failure::input(format!(
                "module `{}` does not belong to a declared lean_lib root",
                module.to_display_string()
            )));
        }
        if !modules.contains(&module) {
            modules.push(module);
        }
    }
    Ok(modules)
}

fn load_sources_with(
    entries: &[Name],
    mut resolve: impl FnMut(&Name) -> Result<Option<SourceLocation>, Failure>,
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
        let location = resolve(&module)?
            .ok_or_else(|| Failure::input("source module lost its package owner"))?;
        let path = location.path;
        check_path(&location.package, &path, false)?;
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
            if resolve(imported)?.is_some() {
                pending.insert(imported.clone());
            }
        }
        modules.insert(module, Module { source, imports });
    }
    Ok(modules)
}

#[derive(Debug, PartialEq, Eq)]
struct CompanionArtifacts {
    server: Vec<u8>,
    private: Vec<u8>,
}

#[derive(Debug, PartialEq, Eq)]
struct ModuleArtifacts {
    exported: Vec<u8>,
    companions: Option<CompanionArtifacts>,
    ir: Option<Vec<u8>>,
}

impl ModuleArtifacts {
    /// Install both companions before publishing the family's public root.
    fn parts(&self) -> impl Iterator<Item = (&'static str, &[u8])> {
        self.companions
            .iter()
            .flat_map(|parts| {
                [
                    ("olean.server", parts.server.as_slice()),
                    ("olean.private", parts.private.as_slice()),
                ]
            })
            .chain(self.ir.iter().map(|bytes| ("ir", bytes.as_slice())))
            .chain(std::iter::once(("olean", self.exported.as_slice())))
    }
}

struct Compilation {
    artifacts: BTreeMap<Name, ModuleArtifacts>,
    elaborated_modules: usize,
    reused_modules: usize,
    /// Modules re-admitted from persisted records (bead `franken_lean-z8j.1.1`).
    cached_modules: usize,
    /// Each module's first provenance in this build, in build order.
    modules: Vec<ModuleProvenance>,
    /// One per external `.olean` closure obtained, in the order obtained.
    imports: Vec<ImportPostureReport>,
    macro_reports: Vec<(Name, source_check::ModuleMacroReport)>,
}

struct CompileFacets<'a> {
    entries: &'a [Name],
    executable: &'a BTreeSet<Name>,
}

/// Every local dependency of an executable target also needs its own companion.
/// Other requested admission-only targets keep their independent facet contract.
fn executable_modules(
    targets: &[String],
    modules: &BTreeMap<Name, Module>,
) -> Result<BTreeSet<Name>, Failure> {
    let mut pending = Vec::new();
    for target in targets {
        if let Some((module, "ir")) = target.split_once(':') {
            pending.push(name(module.strip_prefix('+').unwrap_or(module))?);
        }
    }
    let mut executable = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if let Some(module) = modules.get(&name)
            && executable.insert(name)
        {
            pending.extend(module.imports.iter().cloned());
        }
    }
    Ok(executable)
}

fn compile(
    root: &Path,
    facets: CompileFacets<'_>,
    modules: &BTreeMap<Name, Module>,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
    records: Option<PersistedModules<'_>>,
    macro_config: Option<&source_check::ImportedMacroConfig>,
) -> Result<Compilation, Failure> {
    let mut artifacts = BTreeMap::new();
    let mut imports = Vec::new();
    let mut macro_reports = Vec::new();
    let mut elaborated_modules = 0usize;
    let mut reused_modules = 0usize;
    let mut cached_modules = 0usize;
    let mut provenance: Vec<ModuleProvenance> = Vec::new();
    // Retain only one external world, never one large engine per target. Target
    // order is observable on failure and is not rearranged to manufacture hits.
    let mut active: Option<(Vec<Name>, source_check::ModuleBuildContext)> = None;
    let admission = fln::EngineAdmissionLimits::new(fln::Budget::for_stack_bytes(
        SOURCE_RUN_KERNEL_STACK_BYTES,
    ));
    let limits = SourceModuleCheckLimits::new(fln::SourceCheckLimits::new(admission));
    // Ordinary sources can be parsed before expensive import admission.
    // Imported syntax needs its receipt-bound grammar before parsing bodies;
    // the loader has already validated their headers and bounded their bytes.
    if macro_config.is_none() {
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
    }
    let mut artifact_bytes = 0usize;
    for entry in facets.entries {
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
            let (context, report) = source_check::ModuleBuildContext::load(
                &external,
                root,
                jobs,
                posture,
                limits,
                macro_config,
            )
            .map_err(|(class, detail, authority)| Failure {
                class,
                detail,
                authority,
            })?;
            if let Some(report) = report {
                imports.push(report);
            }
            active = Some((external, context));
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
            .compile(&inputs, entry, budget, records)
            .map_err(|(class, detail, authority)| Failure {
                class,
                detail,
                authority,
            })?;
        let (built, macro_report) = match built {
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
        if let Some(report) = macro_report {
            macro_reports.push((entry.clone(), report));
        }
        elaborated_modules += built.elaborated_modules;
        reused_modules += built.reused_modules;
        cached_modules += built.persisted_modules;
        for row in built.modules {
            if !provenance.iter().any(|seen| seen.name == row.name) {
                provenance.push(row);
            }
        }
        for mut artifact in built.artifacts {
            let ir = if facets.executable.contains(&artifact.name) {
                let mut limits = fln::source_check::modules::SourceModuleIrLimits::new(
                    fln::EngineExecutionLimits::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES),
                );
                limits.writer.container.max_bytes = MAX_ARTIFACT_BYTES as u64;
                let result = artifact.compile_ir(limits).map_err(|error| {
                    let (class, authority, _) = error.disposition();
                    Failure {
                        class,
                        authority,
                        detail: error.to_string(),
                    }
                })?;
                match result {
                    Outcome::Complete(encoded) => Some(encoded.bytes),
                    Outcome::Inconclusive(reason) => {
                        return Err(Failure::new(
                            "inconclusive",
                            format!("module IR compilation exhausted its resources: {reason:?}"),
                        ));
                    }
                    Outcome::InternalFault(fault) => {
                        return Err(Failure::new(
                            "internal-fault",
                            format!("module IR compilation faulted: {fault:?}"),
                        ));
                    }
                }
            } else {
                None
            };
            let family = ModuleArtifacts {
                exported: artifact.bytes,
                companions: artifact.companions.map(|parts| CompanionArtifacts {
                    server: parts.server,
                    private: parts.private,
                }),
                ir,
            };
            if let Some(previous) = artifacts.get(&artifact.name) {
                if previous != &family {
                    return Err(Failure::new(
                        "internal-fault",
                        "shared module produced inconsistent artifacts",
                    ));
                }
                continue;
            }
            for (_, bytes) in family.parts() {
                artifact_bytes = artifact_bytes
                    .checked_add(bytes.len())
                    .filter(|n| *n <= MAX_ARTIFACT_BYTES)
                    .ok_or_else(|| {
                        Failure::new("resource", "aggregate artifact bytes exceed 64 MiB")
                    })?;
            }
            artifacts.insert(artifact.name, family);
        }
    }
    Ok(Compilation {
        artifacts,
        elaborated_modules,
        reused_modules,
        cached_modules,
        modules: provenance,
        imports,
        macro_reports,
    })
}

/// Single-package adapter for the workspace publisher used by fault controls.
#[cfg(test)]
fn publish(
    root: &Path,
    directory: &Path,
    artifacts: &BTreeMap<Name, ModuleArtifacts>,
) -> Result<Vec<PathBuf>, Failure> {
    publish_with(root, directory, artifacts, fln::publish_file_atomic)
}

#[cfg(test)]
fn publish_with(
    root: &Path,
    directory: &Path,
    artifacts: &BTreeMap<Name, ModuleArtifacts>,
    write: impl FnMut(&[u8], &Path) -> std::io::Result<()>,
) -> Result<Vec<PathBuf>, Failure> {
    let destinations = artifacts
        .keys()
        .map(|name| (name.clone(), (root.to_path_buf(), directory.to_path_buf())))
        .collect();
    publish_locations_with(artifacts, &destinations, write)
}

/// Replace every affected package's conventional Lake paths as one rollback
/// unit. All publisher locks and old-byte snapshots precede the first write.
/// Readers opening flat paths independently do not receive the immutable-
/// generation guarantee of `fln::ArtifactStore`.
fn publish_locations_with(
    artifacts: &BTreeMap<Name, ModuleArtifacts>,
    destinations: &BTreeMap<Name, (PathBuf, PathBuf)>,
    mut write: impl FnMut(&[u8], &Path) -> std::io::Result<()>,
) -> Result<Vec<PathBuf>, Failure> {
    struct BuildLock {
        path: PathBuf,
        release: bool,
    }
    impl Drop for BuildLock {
        fn drop(&mut self) {
            if self.release {
                let _ = std::fs::remove_file(&self.path);
            }
        }
    }
    let mut directories = BTreeMap::new();
    for name in artifacts.keys() {
        let (root, directory) = destinations.get(name).ok_or_else(|| {
            Failure::new("internal-fault", "built module has no output destination")
        })?;
        check_path(root, directory, true)?;
        if let Some(previous) = directories.insert(directory, root)
            && previous != root
        {
            return Err(Failure::input(format!(
                "multiple packages share build directory {}",
                directory.display(),
            )));
        }
    }
    // Deterministic lock order also covers separate invocations whose root and
    // dependency roles are reversed. A failed acquisition releases prior locks
    // before any artifact replacement; a crash during writes retains them all.
    let mut locks = Vec::new();
    for &directory in directories.keys() {
        std::fs::create_dir_all(directory).map_err(|error| Failure::io(directory, error))?;
        let path = directory.join(".fln-olean-build.lock");
        let file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(|error| Failure::io(&path, error))?;
        drop(file);
        locks.push(BuildLock {
            path,
            release: true,
        });
    }
    let mut outputs = Vec::new();
    let mut output_paths = BTreeSet::new();
    let mut previous_bytes = 0usize;
    // All source checks, encodings and output preflights precede publication.
    for (name, family) in artifacts {
        let (root, directory) = destinations
            .get(name)
            .expect("every output destination was checked before locking");
        let mut relative = source_import_relative_path(name)?;
        relative.set_extension("olean");
        let path = directory.join(relative);
        // Never leave an old executable or implementation companion next to a
        // new public root. Every existing family member must be regenerated.
        for suffix in ["ir", "olean.server", "olean.private"] {
            if (suffix == "ir" && family.ir.is_some())
                || (suffix != "ir" && family.companions.is_some())
            {
                continue;
            }
            let existing = path.with_extension(suffix);
            check_path(root, &existing, true)?;
            match std::fs::symlink_metadata(&existing) {
                Ok(_) => {
                    return Err(Failure::unsupported(format!(
                        "existing artifact {} requires coordinated replacement",
                        existing.display()
                    )));
                }
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
                Err(error) => return Err(Failure::io(&existing, error)),
            }
        }
        for (suffix, bytes) in family.parts() {
            let path = path.with_extension(suffix);
            if !output_paths.insert(path.clone()) {
                return Err(Failure::input(format!(
                    "multiple modules publish the same artifact {}",
                    path.display(),
                )));
            }
            check_path(root, &path, true)?;
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
    }
    // Once replacements begin, an unwind must leave the same incomplete-build
    // marker as a crash. Only completion or a complete rollback releases it.
    for lock in &mut locks {
        lock.release = false;
    }
    for (index, (path, bytes, _)) in outputs.iter().enumerate() {
        let result = std::fs::create_dir_all(path.parent().expect("artifact parent"))
            .and_then(|()| write(bytes, path));
        if let Err(error) = result {
            let mut rollback = Vec::new();
            // The atomic writer may report a directory-sync failure after its
            // rename, so the failing output also belongs in the rollback set.
            for (prior, _, previous) in outputs[..=index].iter().rev() {
                let restored = match previous {
                    Some(bytes) => write(bytes, prior),
                    None => match std::fs::remove_file(prior) {
                        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
                        result => result,
                    },
                };
                if let Err(error) = restored {
                    rollback.push(format!("{}: {error}", prior.display()));
                }
            }
            for lock in &mut locks {
                lock.release = rollback.is_empty();
            }
            return Err(Failure::new(
                "io",
                format!(
                    "{}: {error}{}",
                    path.display(),
                    if rollback.is_empty() {
                        String::new()
                    } else {
                        format!(
                            "; rollback failed: {}; build lock retained at {}",
                            rollback.join("; "),
                            locks
                                .iter()
                                .map(|lock| lock.path.display().to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        )
                    }
                ),
            ));
        }
    }
    for lock in &mut locks {
        lock.release = true;
    }
    Ok(outputs.into_iter().map(|(path, _, _)| path).collect())
}

fn load_configuration(
    root: &Path,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> Result<(LakeConfig, Option<ImportPostureReport>), Failure> {
    if root.join("lakefile.toml").is_file() {
        return Ok((config(root)?, None));
    }
    let lean = root.join("lakefile.lean");
    let toml = root.join("lakefile.toml");
    if !lean
        .try_exists()
        .map_err(|error| Failure::io(&lean, error))?
        && !toml
            .try_exists()
            .map_err(|error| Failure::io(&toml, error))?
    {
        return Err(Failure::new(
            "missing-configuration",
            format!("{}\n{}", lean.display(), toml.display()),
        ));
    }
    let loaded = lean_config::load(root, jobs, posture)?;
    Ok((loaded.config, Some(loaded.imports)))
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
    let macro_config =
        source_check::build_macro_config().map_err(|(class, detail, authority)| Failure {
            class,
            detail,
            authority,
        })?;
    let (config, configuration_imports) = load_configuration(&root, jobs, posture)?;
    let sources = local_dependencies::load(&root, &config)?;
    let libraries = sources.libraries();
    let entries = plan_modules(
        sources.packages.iter().flat_map(|package| {
            package
                .config
                .targets
                .iter()
                .map(|target| target.name.as_str())
        }),
        &libraries,
        &targets,
    )?;
    let modules = load_sources_with(&entries, |module| sources.resolve(module))?;
    let executable = executable_modules(&targets, &modules)?;
    let records = macro_config
        .is_none()
        .then(|| source_check::module_records(posture));
    let records_state = records
        .as_ref()
        .map_or(MACRO_RECORDS_UNAVAILABLE, |records| records.state());
    let Compilation {
        artifacts,
        elaborated_modules,
        reused_modules,
        cached_modules,
        modules: provenance,
        imports,
        macro_reports,
    } = compile(
        &root,
        CompileFacets {
            entries: &entries,
            executable: &executable,
        },
        &modules,
        jobs,
        posture,
        records.as_ref().and_then(|records| records.persisted()),
        macro_config.as_ref(),
    )?;
    let destinations = sources.destinations(&artifacts)?;
    sources.verify_configurations()?;
    let paths = publish_locations_with(&artifacts, &destinations, fln::publish_file_atomic)?;
    let snapshot = record_snapshot(
        &root,
        &config,
        &sources,
        &targets,
        &modules,
        &artifacts,
        &destinations,
        &provenance,
        posture,
        records_state,
    );
    let executable_count = artifacts
        .values()
        .filter(|family| family.ir.is_some())
        .count();
    let facet = if executable_count == 0 { "olean" } else { "ir" };
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
            .as_ref()
            .and_then(|records| records.unavailable())
            .map(|reason| format!(",\"module_records_reason\":{}", json_string(reason)))
            .unwrap_or_default();
        let macro_json = if macro_reports.is_empty() {
            String::new()
        } else {
            let reports = macro_reports
                .iter()
                .map(|(entry, report)| {
                    format!(
                        "{{\"entry\":{}{}}}",
                        json_string(&entry.to_display_string()),
                        report.json
                    )
                })
                .collect::<Vec<_>>()
                .join(",");
            format!(",\"importedMacroBuilds\":[{reports}]")
        };
        let snapshot = match &snapshot {
            Ok(()) => "\"snapshot\":\"written\"".to_owned(),
            Err(reason) => format!(
                "\"snapshot\":\"failed\",\"snapshot_reason\":{}",
                json_string(reason)
            ),
        };
        format!(
            "{{\"schema\":\"fln.lake-build/2\",\"status\":\"success\",\"package\":{},\"facet\":{},\"modules_built\":{},\"modules_cached\":{cached_modules},\"module_elaborations\":{elaborated_modules},\"module_checks_reused\":{reused_modules},\"executable_modules\":{executable_count},\"artifacts\":[{paths}],\"admission\":\"K1+independent-checker\",\"import_posture\":{},\"imports\":[{imports}]{configuration_imports},\"module_records\":{}{unavailable},\"modules\":[{rows}]{macro_json},{snapshot}}}\n",
            json_string(&config.name),
            json_string(facet),
            artifacts.len(),
            json_string(posture.as_str()),
            json_string(records_state),
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
        let macros = macro_reports
            .iter()
            .map(|(entry, report)| format!(" {}: {}", entry.to_display_string(), report.sentence))
            .collect::<String>();
        let snapshot = match &snapshot {
            Ok(()) => String::new(),
            Err(reason) => format!(" The build snapshot was not written: {reason}."),
        };
        let executable = if executable_count == 0 {
            String::new()
        } else {
            format!(" and {executable_count} native .ir companions")
        };
        format!(
            "Built {} checked .olean modules{executable} for {} ({elaborated_modules} elaborated, {cached_modules} re-admitted from verified records; {reused_modules} module checks reused).{imports}{configuration_imports}{macros}{snapshot}\n",
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
    sources: &local_dependencies::Sources,
    targets: &[String],
    modules: &BTreeMap<Name, Module>,
    artifacts: &BTreeMap<Name, ModuleArtifacts>,
    destinations: &BTreeMap<Name, (PathBuf, PathBuf)>,
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
    for (name, family) in artifacts {
        let module = modules
            .get(name)
            .ok_or("an artifact has no source module")?;
        let source = sources
            .resolve(name)
            .map_err(|failure| failure.detail)?
            .ok_or("a built module has no library owner")?;
        let (owner, output_dir) = destinations
            .get(name)
            .ok_or("a built module has no output destination")?;
        if &source.package != owner {
            return Err("a built module changed its output owner".to_owned());
        }
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
            source: relative(&source.path),
            source_digest: snapshot::digest(&module.source),
            imports: module.imports.iter().map(Name::to_display_string).collect(),
            artifact: relative(&output_dir.join(artifact)),
            artifact_digest: snapshot::digest(&family.exported),
            ir_digest: family.ir.as_ref().map(|bytes| snapshot::digest(bytes)),
            companions: family
                .companions
                .as_ref()
                .map(|parts| snapshot::CompanionDigests {
                    server: snapshot::digest(&parts.server),
                    private: snapshot::digest(&parts.private),
                }),
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
        targets: targets.to_vec(),
        configurations: sources.configuration_rows(root),
        modules: rows,
        externals,
    }
    .to_text();
    sources
        .verify_configurations()
        .map_err(|failure| failure.detail)?;
    let directory = root.join(&config.build_dir);
    let path = directory.join(snapshot::FILE);
    check_path(root, &path, true).map_err(|failure| failure.detail)?;
    std::fs::create_dir_all(&directory)
        .map_err(|error| format!("{}: {error}", directory.display()))?;
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

#[cfg(test)]
mod publication_tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static NEXT: AtomicUsize = AtomicUsize::new(0);
    struct Directory(PathBuf);
    impl Directory {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!(
                "fln-family-publication-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            std::fs::create_dir_all(&path).unwrap();
            Self(path.canonicalize().unwrap())
        }
    }
    impl Drop for Directory {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    fn family(prefix: &str) -> ModuleArtifacts {
        ModuleArtifacts {
            exported: format!("{prefix} public").into_bytes(),
            companions: Some(CompanionArtifacts {
                server: format!("{prefix} server").into_bytes(),
                private: format!("{prefix} private").into_bytes(),
            }),
            ir: None,
        }
    }

    #[test]
    fn family_rollback_restores_existing_files_and_removes_only_new_outputs() {
        let directory = Directory::new();
        let a = Name::from_components(["A"]);
        let b = Name::from_components(["B"]);
        let old = family("old");
        for (part, bytes) in old.parts() {
            std::fs::write(directory.0.join("A.olean").with_extension(part), bytes).unwrap();
        }
        let artifacts = BTreeMap::from([(a, family("new A")), (b, family("new B"))]);
        let failed_path = directory.0.join("B.olean");
        let mut injected = false;
        let mut written = Vec::new();
        let error = publish_with(&directory.0, &directory.0, &artifacts, |bytes, path| {
            fln::publish_file_atomic(bytes, path)?;
            written.push(path.file_name().unwrap().to_string_lossy().into_owned());
            if path == failed_path && !injected {
                injected = true;
                // Model the real writer's directory-sync failure after rename.
                return Err(std::io::Error::other("injected after rename"));
            }
            Ok(())
        })
        .unwrap_err();
        assert!(
            error.detail.contains("injected after rename"),
            "{}",
            error.detail
        );
        assert!(
            !error.detail.contains("rollback failed"),
            "{}",
            error.detail
        );
        assert_eq!(
            &written[..6],
            [
                "A.olean.server",
                "A.olean.private",
                "A.olean",
                "B.olean.server",
                "B.olean.private",
                "B.olean"
            ]
        );
        for (part, bytes) in old.parts() {
            assert_eq!(
                std::fs::read(directory.0.join("A.olean").with_extension(part)).unwrap(),
                bytes
            );
            assert!(!directory.0.join("B.olean").with_extension(part).exists());
        }
        assert!(!directory.0.join(".fln-olean-build.lock").exists());
        assert_eq!(
            publish(&directory.0, &directory.0, &artifacts)
                .unwrap_or_else(|error| panic!("{}", error.detail))
                .len(),
            6
        );
        for (name, family) in &artifacts {
            for (part, bytes) in family.parts() {
                assert_eq!(
                    std::fs::read(
                        directory
                            .0
                            .join(name.to_display_string())
                            .with_extension(part)
                    )
                    .unwrap(),
                    bytes
                );
            }
        }
    }

    #[test]
    fn workspace_publication_rolls_back_every_package_and_holds_all_locks() {
        let directory = Directory::new();
        let first = directory.0.join("first");
        let second = directory.0.join("second");
        for root in [&first, &second] {
            std::fs::create_dir(root).unwrap();
        }
        let old_a = family("old A");
        let old_b = family("old B");
        for (root, name, old) in [(&first, "A", &old_a), (&second, "B", &old_b)] {
            for (part, bytes) in old.parts() {
                std::fs::write(root.join(name).with_extension(part), bytes).unwrap();
            }
        }
        let a = Name::from_components(["A"]);
        let b = Name::from_components(["B"]);
        let destinations = BTreeMap::from([
            (a.clone(), (first.clone(), first.clone())),
            (b.clone(), (second.clone(), second.clone())),
        ]);
        let artifacts = BTreeMap::from([(a, family("new A")), (b, family("new B"))]);
        let mut failed = false;
        let error = publish_locations_with(&artifacts, &destinations, |bytes, path| {
            for root in [&first, &second] {
                assert!(root.join(".fln-olean-build.lock").is_file());
            }
            fln::publish_file_atomic(bytes, path)?;
            if path == second.join("B.olean") && !failed {
                failed = true;
                return Err(std::io::Error::other("failure after dependent publication"));
            }
            Ok(())
        })
        .unwrap_err();
        assert!(failed);
        assert!(
            error.detail.contains("failure after dependent publication"),
            "{}",
            error.detail
        );
        assert!(
            !error.detail.contains("rollback failed"),
            "{}",
            error.detail
        );
        for (root, name, old) in [(&first, "A", &old_a), (&second, "B", &old_b)] {
            for (part, bytes) in old.parts() {
                assert_eq!(
                    std::fs::read(root.join(name).with_extension(part)).unwrap(),
                    bytes,
                );
            }
            assert!(!root.join(".fln-olean-build.lock").exists());
        }
    }

    #[test]
    fn workspace_output_preflight_runs_before_any_package_is_replaced() {
        let directory = Directory::new();
        let first = directory.0.join("first");
        let second = directory.0.join("second");
        for root in [&first, &second] {
            std::fs::create_dir(root).unwrap();
        }
        std::fs::write(first.join("A.olean"), b"old A").unwrap();
        std::fs::write(second.join("B.ir"), b"unmatched executable").unwrap();
        let a = Name::from_components(["A"]);
        let b = Name::from_components(["B"]);
        let destinations = BTreeMap::from([
            (a.clone(), (first.clone(), first.clone())),
            (b.clone(), (second.clone(), second.clone())),
        ]);
        let artifacts = BTreeMap::from([(a, family("new A")), (b, family("new B"))]);
        let mut writes = 0;
        let error = publish_locations_with(&artifacts, &destinations, |bytes, path| {
            writes += 1;
            fln::publish_file_atomic(bytes, path)
        })
        .unwrap_err();
        assert_eq!(error.class, "unsupported");
        assert_eq!(writes, 0);
        assert_eq!(std::fs::read(first.join("A.olean")).unwrap(), b"old A");
        assert_eq!(
            std::fs::read(second.join("B.ir")).unwrap(),
            b"unmatched executable",
        );
        for root in [&first, &second] {
            assert!(!root.join(".fln-olean-build.lock").exists());
        }
    }

    #[test]
    fn nested_output_directories_cannot_publish_colliding_module_paths() {
        let directory = Directory::new();
        let first = directory.0.join("output");
        let second = first.join("Dep/lib/lean");
        std::fs::create_dir_all(&second).unwrap();
        let output = second.join("Foo.olean");
        std::fs::write(&output, b"original").unwrap();
        let a = Name::from_components(["Dep", "lib", "lean", "Foo"]);
        let b = Name::from_components(["Foo"]);
        let destinations = BTreeMap::from([
            (a.clone(), (directory.0.clone(), first.clone())),
            (b.clone(), (second.clone(), second.clone())),
        ]);
        let artifacts = BTreeMap::from([(a, family("new A")), (b, family("new B"))]);
        let mut writes = 0;
        let error = publish_locations_with(&artifacts, &destinations, |bytes, path| {
            writes += 1;
            fln::publish_file_atomic(bytes, path)
        })
        .unwrap_err();
        assert_eq!(error.class, "input");
        assert!(error.detail.contains("same artifact"), "{}", error.detail);
        assert_eq!(writes, 0);
        assert_eq!(std::fs::read(output).unwrap(), b"original");
        for root in [&first, &second] {
            assert!(!root.join(".fln-olean-build.lock").exists());
        }
    }

    #[test]
    fn incomplete_workspace_rollback_retains_every_package_lock() {
        let directory = Directory::new();
        let first = directory.0.join("first");
        let second = directory.0.join("second");
        for root in [&first, &second] {
            std::fs::create_dir(root).unwrap();
        }
        std::fs::write(first.join("A.olean"), b"old A").unwrap();
        std::fs::write(second.join("B.olean"), b"old B").unwrap();
        let a = Name::from_components(["A"]);
        let b = Name::from_components(["B"]);
        let destinations = BTreeMap::from([
            (a.clone(), (first.clone(), first.clone())),
            (b.clone(), (second.clone(), second.clone())),
        ]);
        let artifacts = BTreeMap::from([(a, family("new A")), (b, family("new B"))]);
        let mut failed = false;
        let error = publish_locations_with(&artifacts, &destinations, |bytes, path| {
            if failed && path == first.join("A.olean") {
                return Err(std::io::Error::other("cannot restore first package"));
            }
            fln::publish_file_atomic(bytes, path)?;
            if !failed && path == second.join("B.olean") {
                failed = true;
                return Err(std::io::Error::other("failure after second package"));
            }
            Ok(())
        })
        .unwrap_err();
        assert!(error.detail.contains("rollback failed"), "{}", error.detail);
        for root in [&first, &second] {
            assert!(root.join(".fln-olean-build.lock").is_file());
            assert!(error.detail.contains(&root.display().to_string()));
        }
        let next = publish_locations_with(&artifacts, &destinations, fln::publish_file_atomic)
            .unwrap_err();
        assert!(next.detail.contains(".fln-olean-build.lock"));
    }

    #[test]
    fn executable_companion_rolls_back_with_its_publication_family() {
        let directory = Directory::new();
        let mut old = family("old");
        old.ir = Some(b"old executable".to_vec());
        let mut next = family("new");
        next.ir = Some(b"new executable".to_vec());
        for (part, bytes) in old.parts() {
            std::fs::write(directory.0.join("A.olean").with_extension(part), bytes).unwrap();
        }
        let artifacts = BTreeMap::from([(Name::from_components(["A"]), next)]);
        let mut failed = false;
        let result = publish_with(&directory.0, &directory.0, &artifacts, |bytes, path| {
            fln::publish_file_atomic(bytes, path)?;
            if path == directory.0.join("A.olean") && !failed {
                failed = true;
                assert_eq!(std::fs::read(directory.0.join("A.ir"))?, b"new executable");
                return Err(std::io::Error::other("failure after new public root"));
            }
            Ok(())
        });
        assert!(result.is_err());
        for (part, bytes) in old.parts() {
            assert_eq!(
                std::fs::read(directory.0.join("A.olean").with_extension(part)).unwrap(),
                bytes
            );
        }
        assert!(!directory.0.join(".fln-olean-build.lock").exists());
    }

    #[test]
    fn incomplete_family_rollback_retains_the_lock_and_refuses_the_next_build() {
        let directory = Directory::new();
        let old = family("old");
        for (part, bytes) in old.parts() {
            std::fs::write(directory.0.join("A.olean").with_extension(part), bytes).unwrap();
        }
        let artifacts = BTreeMap::from([(Name::from_components(["A"]), family("new"))]);
        let failed_path = directory.0.join("A.olean.private");
        let mut injected = false;
        let error = publish_with(&directory.0, &directory.0, &artifacts, |bytes, path| {
            if path == failed_path {
                if injected {
                    return Err(std::io::Error::other("injected rollback failure"));
                }
                injected = true;
                fln::publish_file_atomic(bytes, path)?;
                return Err(std::io::Error::other("injected after rename"));
            }
            fln::publish_file_atomic(bytes, path)
        })
        .unwrap_err();
        assert!(error.detail.contains("rollback failed"), "{}", error.detail);
        assert!(
            error.detail.contains("build lock retained"),
            "{}",
            error.detail
        );
        assert!(directory.0.join(".fln-olean-build.lock").is_file());
        assert_eq!(
            std::fs::read(directory.0.join("A.olean.server")).unwrap(),
            old.companions.unwrap().server
        );
        assert_eq!(
            std::fs::read(directory.0.join("A.olean")).unwrap(),
            old.exported
        );
        let error = publish(&directory.0, &directory.0, &artifacts).unwrap_err();
        assert!(
            error.detail.contains(".fln-olean-build.lock"),
            "{}",
            error.detail
        );
    }
}
