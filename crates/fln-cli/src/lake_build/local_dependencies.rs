//! Read-only local and locked Git package discovery for checked source builds and executables.
//!
//! Package identity follows Lake's reverse, breadth-first requirement order.
//! A root manifest locks the path for every reachable package by name; its paths
//! are relative to that root, including transitive dependencies. Without a root
//! manifest, explicitly declared local paths retain the existing discovery mode.
//! Source containment is checked against each owning package.

use super::*;

const MAX_PACKAGES: usize = 64;
const MAX_REQUIREMENTS: usize = 4096;
const MAX_MANIFEST_BYTES: usize = 1024 * 1024;
const MAX_GIT_REFERENCE_BYTES: usize = 4096;
const MAX_GIT_PACKED_REFS_BYTES: usize = 1024 * 1024;
const MAX_GIT_REFERENCE_DEPTH: usize = 16;

/// An already materialized checkout. The root lock remains authoritative; this
/// guard never fetches, checks out, cleans or writes Git metadata.
struct GitCheckout {
    directory: PathBuf,
    package_directory: PathBuf,
    revision: String,
}

impl GitCheckout {
    fn verify(&self) -> Result<(), Failure> {
        // Rewalk canonical paths as well: check_path treats its root as trusted,
        // but a checkout or subdirectory may have been replaced since discovery.
        dependency_root(Path::new(""), &self.directory)?;
        dependency_root(Path::new(""), &self.package_directory)?;
        let actual = checkout_revision(&self.directory)?;
        if actual != self.revision {
            return Err(Failure::unsupported(format!(
                "locked Git checkout {} is at {actual}, expected {}; materialize the locked revision before building",
                self.directory.display(),
                self.revision,
            )));
        }
        Ok(())
    }
}

fn git_hash(text: &str) -> bool {
    matches!(text.len(), 40 | 64) && text.bytes().all(|byte| byte.is_ascii_hexdigit())
}

/// Only ordinary relative Git references are supported. In particular, an
/// untrusted symbolic reference cannot turn a metadata read into a path escape.
fn git_reference(text: &str) -> bool {
    text.starts_with("refs/")
        && !text.contains("..")
        && !text.contains("@{")
        && !text.chars().any(|character| {
            character.is_control()
                || character.is_whitespace()
                || matches!(character, '~' | '^' | ':' | '?' | '*' | '[' | '\\')
        })
        && text.split('/').all(|component| {
            !component.is_empty()
                && !component.starts_with('.')
                && !component.ends_with('.')
                && !component.ends_with(".lock")
        })
}

fn git_metadata(
    directory: &Path,
    relative: &Path,
    max_bytes: usize,
) -> Result<Option<Vec<u8>>, Failure> {
    let path = directory.join(relative);
    check_path(directory, &path, true)?;
    match std::fs::symlink_metadata(&path) {
        Ok(metadata) if !metadata.is_file() => Err(Failure::input(format!(
            "Git metadata is not a regular file: {}",
            path.display(),
        ))),
        Ok(_) => read_bounded(&path, max_bytes, "locked Git metadata")
            .map(Some)
            .map_err(Failure::from),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(Failure::io(&path, error)),
    }
}

fn packed_revision(directory: &Path, reference: &str) -> Result<String, Failure> {
    let bytes = git_metadata(
        directory,
        Path::new("packed-refs"),
        MAX_GIT_PACKED_REFS_BYTES,
    )?
    .ok_or_else(|| {
        Failure::unsupported(format!(
            "locked Git reference {reference} is absent from {}",
            directory.display(),
        ))
    })?;
    let text =
        std::str::from_utf8(&bytes).map_err(|_| Failure::input("Git packed-refs is not UTF-8"))?;
    let mut selected = None;
    for line in text.lines() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if let Some(peeled) = line.strip_prefix('^') {
            if !git_hash(peeled) {
                return Err(Failure::input("malformed peeled Git reference"));
            }
            continue;
        }
        let mut fields = line.split_whitespace();
        let (Some(revision), Some(name), None) = (fields.next(), fields.next(), fields.next())
        else {
            return Err(Failure::input("malformed Git packed reference"));
        };
        if !git_hash(revision) || !git_reference(name) {
            return Err(Failure::input("malformed Git packed reference"));
        }
        if name == reference && selected.replace(revision.to_owned()).is_some() {
            return Err(Failure::input("duplicate selected Git packed reference"));
        }
    }
    selected.ok_or_else(|| {
        Failure::unsupported(format!(
            "locked Git reference {reference} is absent from {}",
            directory.display(),
        ))
    })
}

/// Resolve HEAD from the ordinary .git directory layout without running Git.
/// Gitfiles, common directories and unfamiliar reference stores remain explicit
/// refusals. Like the pin's getHeadRevision?, this observes a revision identity;
/// source bytes are separately captured and checked by the ordinary build path.
fn checkout_revision(directory: &Path) -> Result<String, Failure> {
    let git = directory.join(".git");
    check_path(directory, &git, true)?;
    match std::fs::symlink_metadata(&git) {
        Ok(metadata) if metadata.is_dir() => {}
        Ok(_) => {
            return Err(Failure::unsupported(format!(
                "locked Git checkout {} requires an ordinary .git directory",
                directory.display(),
            )));
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Err(Failure::unsupported(format!(
                "locked Git checkout is not materialized: {}",
                directory.display(),
            )));
        }
        Err(error) => return Err(Failure::io(&git, error)),
    }
    // A HEAD file by itself is not a repository. These directories are the
    // ordinary Git repository-discovery shape; individual objects are not read.
    for relative in ["objects", "refs"] {
        let path = git.join(relative);
        check_path(&git, &path, true)?;
        match std::fs::symlink_metadata(&path) {
            Ok(metadata) if metadata.is_dir() => {}
            Ok(_) => {
                return Err(Failure::unsupported(format!(
                    "locked Git checkout requires an ordinary {relative} directory",
                )));
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                return Err(Failure::unsupported(format!(
                    "locked Git checkout requires an ordinary {relative} directory",
                )));
            }
            Err(error) => return Err(Failure::io(&path, error)),
        }
    }
    if git_metadata(&git, Path::new("commondir"), MAX_GIT_REFERENCE_BYTES)?.is_some() {
        return Err(Failure::unsupported(
            "locked Git common-directory layouts are not implemented",
        ));
    }
    let mut reference = "HEAD".to_owned();
    let mut visited = BTreeSet::new();
    for _ in 0..MAX_GIT_REFERENCE_DEPTH {
        if !visited.insert(reference.clone()) {
            return Err(Failure::input("cyclic Git symbolic reference"));
        }
        let Some(bytes) = git_metadata(&git, Path::new(&reference), MAX_GIT_REFERENCE_BYTES)?
        else {
            if reference == "HEAD" {
                return Err(Failure::unsupported("locked Git checkout has no HEAD"));
            }
            return packed_revision(&git, &reference);
        };
        let text = std::str::from_utf8(&bytes)
            .map_err(|_| Failure::input("Git reference is not UTF-8"))?
            .trim_end_matches(['\r', '\n']);
        if git_hash(text) {
            return Ok(text.to_owned());
        }
        let Some(next) = text.strip_prefix("ref: ") else {
            return Err(Failure::input("malformed Git reference"));
        };
        if !git_reference(next) {
            return Err(Failure::unsupported(
                "locked Git symbolic reference is outside the supported refs namespace",
            ));
        }
        reference = next.to_owned();
    }
    Err(Failure::new(
        "resource",
        "locked Git symbolic reference depth exceeds 16",
    ))
}

/// Lake uses Name.toString(escape := false) for the checkout directory. Keep
/// quoted components intact while removing only their quotation delimiters.
fn git_package_directory(name: &str) -> Result<String, Failure> {
    if name.len() > MAX_GIT_REFERENCE_BYTES {
        return Err(Failure::new(
            "resource",
            "Git package name exceeds 4096 bytes",
        ));
    }
    let mut rendered = String::new();
    let mut quoted = false;
    for character in name.chars() {
        match character {
            '«' if !quoted => quoted = true,
            '»' if quoted => quoted = false,
            '»' => return Err(Failure::input("malformed quoted Git package name")),
            _ => rendered.push(character),
        }
    }
    if quoted
        || rendered.is_empty()
        || matches!(rendered.as_str(), "." | ".." | "[anonymous]")
        || rendered
            .chars()
            .any(|character| character.is_control() || matches!(character, '/' | '\\' | ':'))
        || !matches!(
            Path::new(&rendered)
                .components()
                .collect::<Vec<_>>()
                .as_slice(),
            [Component::Normal(_)]
        )
    {
        return Err(Failure::unsupported(
            "Git package identity is not a safe single directory name",
        ));
    }
    Ok(rendered)
}

pub(super) struct Sources {
    pub(super) packages: Vec<Package>,
    pub(super) configuration_imports: Vec<ImportPostureReport>,
    manifest: ManifestSelection,
    git_checkouts: Vec<GitCheckout>,
    /// Files whose absence selected the supported configuration/resolution path.
    metadata_guards: Vec<(PathBuf, &'static str)>,
}

struct ManifestSelection {
    root: PathBuf,
    path: PathBuf,
    digest: Option<String>,
    entries: Option<BTreeMap<String, fln_lake::ManifestPackageEntry>>,
    packages_dir: PathBuf,
}

fn manifest_bytes(root: &Path, path: &Path) -> Result<Option<Vec<u8>>, Failure> {
    check_path(root, path, true)?;
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if !metadata.is_file() => Err(Failure::input(format!(
            "Lake manifest is not a regular file: {}",
            path.display(),
        ))),
        Ok(_) => read_bounded(path, MAX_MANIFEST_BYTES, "Lake manifest")
            .map(Some)
            .map_err(Failure::from),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(None),
        Err(error) => Err(Failure::io(path, error)),
    }
}

impl ManifestSelection {
    fn load(root: &Path) -> Result<Self, Failure> {
        let path = root.join("lake-manifest.json");
        let bytes = manifest_bytes(root, &path)?;
        let (digest, entries, packages_dir) = if let Some(bytes) = bytes {
            let text = std::str::from_utf8(&bytes)
                .map_err(|_| Failure::input("lake-manifest.json is not UTF-8"))?;
            let manifest = fln_lake::Manifest::parse_json(text).map_err(|error| {
                let class = match &error {
                    fln_lake::ManifestParseError::Invalid(_) => "input",
                    fln_lake::ManifestParseError::Resource(_) => "resource",
                };
                Failure::new(class, format!("{}: {error}", path.display()))
            })?;
            if manifest.packages.len() > MAX_REQUIREMENTS {
                return Err(Failure::new(
                    "resource",
                    "manifest package count exceeds 4096",
                ));
            }
            // The pin inserts entries in order: the last entry for a name wins.
            // Do not inspect unselected paths or fetch unused remote entries.
            let entries = manifest
                .packages
                .into_iter()
                .map(|entry| (entry.name.clone(), entry))
                .collect();
            (
                Some(snapshot::digest(&bytes)),
                Some(entries),
                manifest
                    .packages_dir
                    .unwrap_or_else(|| PathBuf::from(".lake/packages")),
            )
        } else {
            (None, None, PathBuf::from(".lake/packages"))
        };
        Ok(Self {
            root: root.to_path_buf(),
            path,
            digest,
            entries,
            packages_dir,
        })
    }

    fn verify(&self) -> Result<(), Failure> {
        let current = manifest_bytes(&self.root, &self.path)?
            .as_deref()
            .map(snapshot::digest);
        if current != self.digest {
            return Err(Failure::input(format!(
                "Lake manifest changed during the build: {}",
                self.path.display(),
            )));
        }
        Ok(())
    }

    fn dependency(
        &self,
        owner: &Path,
        requirement: &fln_lake::LakeRequire,
        metadata_guards: &mut Vec<(PathBuf, &'static str)>,
        git_checkouts: &mut Vec<GitCheckout>,
    ) -> Result<(PathBuf, ConfigurationSelection), Failure> {
        let Some(entries) = &self.entries else {
            let path = requirement.path.as_deref().ok_or_else(|| {
                Failure::unsupported(
                    "Git dependencies require a root lake-manifest.json and an existing checkout at its locked revision",
                )
            })?;
            let directory = dependency_root(owner, path)?;
            guard_metadata(
                &directory,
                &["lake-manifest.json", ".lake/package-overrides.json"],
                metadata_guards,
            )?;
            return Ok((directory, ConfigurationSelection::Default));
        };
        let identity = fln_lake::canonical_package_name(&requirement.name);
        let entry = entries.get(&identity).ok_or_else(|| {
            Failure::input(format!(
                "dependency '{}' of '{}' is not in lake-manifest.json; use lake update to generate a complete manifest",
                requirement.name,
                owner.display(),
            ))
        })?;
        let directory = match entry.entry_type.as_str() {
            "path" => {
                let path = entry.dir.as_deref().ok_or_else(|| {
                    Failure::input(format!(
                        "manifest path dependency '{}' has no directory",
                        requirement.name,
                    ))
                })?;
                dependency_root(&self.root, path)?
            }
            "git" => {
                let revision = entry
                    .rev
                    .as_deref()
                    .filter(|revision| git_hash(revision))
                    .ok_or_else(|| {
                        Failure::unsupported(
                            "locked Git dependencies require a full hexadecimal commit revision",
                        )
                    })?;
                let package = git_package_directory(&entry.name)?;
                let checkout = dependency_root(&self.root, &self.packages_dir.join(package))?;
                let directory = if let Some(subdir) = &entry.subdir {
                    let subdir = Path::new(subdir);
                    relative_directory(subdir)?;
                    dependency_root(&checkout, subdir)?
                } else {
                    checkout.clone()
                };
                let guard = GitCheckout {
                    directory: checkout,
                    package_directory: directory.clone(),
                    revision: revision.to_owned(),
                };
                guard.verify()?;
                git_checkouts.push(guard);
                directory
            }
            other => {
                return Err(Failure::unsupported(format!(
                    "manifest dependency '{}' has unsupported source '{other}'",
                    requirement.name,
                )));
            }
        };
        let selection = match entry.config_file.as_str() {
            "lakefile.toml" => ConfigurationSelection::Toml,
            "lakefile.lean" => ConfigurationSelection::Lean,
            "lakefile" => ConfigurationSelection::Default,
            file => {
                return Err(Failure::unsupported(format!(
                    "manifest dependency '{}' selects unsupported configuration '{file}'; local locked packages require lakefile.lean or lakefile.toml",
                    requirement.name,
                )));
            }
        };
        // In locked mode only the root manifest selects packages. Dependency
        // manifests and overrides do not replace entries in that root table.
        Ok((directory, selection))
    }
}

pub(super) struct Package {
    pub(super) root: PathBuf,
    pub(super) config: LakeConfig,
    /// Exact input captured before parsing or checked evaluation.
    configuration: (PathBuf, String),
    default_toml: bool,
    libraries: Vec<Library>,
}

impl Sources {
    /// These paths describe discovered inputs; a snapshot reader must resolve
    /// the current package graph again before opening any configuration file.
    pub(super) fn configuration_rows(&self, invocation_root: &Path) -> Vec<snapshot::ConfigRow> {
        self.packages
            .iter()
            .map(|package| (&package.configuration.0, &package.configuration.1))
            .chain(
                self.manifest
                    .digest
                    .as_ref()
                    .map(|digest| (&self.manifest.path, digest)),
            )
            .map(|(path, digest)| {
                (
                    path.strip_prefix(invocation_root)
                        .unwrap_or(path)
                        .display()
                        .to_string(),
                    digest.clone(),
                )
            })
            .collect::<BTreeMap<_, _>>()
            .into_iter()
            .map(|(path, digest)| snapshot::ConfigRow { path, digest })
            .collect()
    }

    /// A successful build must not describe a package graph whose inputs
    /// changed while source modules were being checked and published.
    pub(super) fn verify_configurations(&self) -> Result<(), Failure> {
        self.manifest.verify()?;
        for checkout in &self.git_checkouts {
            checkout.verify()?;
        }
        for (root, relative) in &self.metadata_guards {
            absent_metadata(root, relative)?;
        }
        for package in &self.packages {
            let (path, expected) = &package.configuration;
            if package.default_toml {
                let lean = package.root.join("lakefile.lean");
                check_path(&package.root, &lean, true)?;
                if lean
                    .try_exists()
                    .map_err(|error| Failure::io(&lean, error))?
                {
                    return Err(Failure::input(format!(
                        "Lake configuration selection changed during the build: {}",
                        lean.display(),
                    )));
                }
            }
            check_path(&package.root, path, false)?;
            let bytes = read_bounded(path, 64 * 1024, "Lake configuration")?;
            if snapshot::digest(&bytes) != *expected {
                return Err(Failure::input(format!(
                    "Lake configuration changed during the build: {}",
                    path.display(),
                )));
            }
        }
        Ok(())
    }

    pub(super) fn libraries(&self) -> Vec<Library> {
        self.packages
            .iter()
            .flat_map(|package| package.libraries.iter().cloned())
            .collect()
    }

    /// Keep the exact selected configuration as the module's owner. Different
    /// package identities may share a directory while selecting different
    /// configuration files, source libraries and build directories.
    pub(super) fn resolve_package(
        &self,
        module: &Name,
    ) -> Result<Option<(&Package, PathBuf)>, Failure> {
        let mut found: Option<(&Package, PathBuf)> = None;
        for package in &self.packages {
            let Some(path) = source_path(module, &package.libraries)? else {
                continue;
            };
            if found.as_ref().is_some_and(|(previous, previous_path)| {
                previous_path != &path || previous.root != package.root
            }) {
                return Err(Failure::unsupported(format!(
                    "module `{}` belongs to multiple local packages",
                    module.to_display_string(),
                )));
            }
            // Lake's Workspace.findModule? selects the first package. Identical
            // source aliases must retain that owner's configuration as well.
            if found.is_none() {
                found = Some((package, path));
            }
        }
        Ok(found)
    }

    pub(super) fn resolve(&self, module: &Name) -> Result<Option<SourceLocation>, Failure> {
        Ok(self
            .resolve_package(module)?
            .map(|(package, path)| SourceLocation {
                package: package.root.clone(),
                path,
            }))
    }

    pub(super) fn destinations(
        &self,
        artifacts: &BTreeMap<Name, ModuleArtifacts>,
    ) -> Result<BTreeMap<Name, (PathBuf, PathBuf)>, Failure> {
        artifacts
            .keys()
            .map(|name| {
                let (package, _) = self.resolve_package(name)?.ok_or_else(|| {
                    Failure::new("internal-fault", "built module has no source owner")
                })?;
                Ok((
                    name.clone(),
                    (
                        package.root.clone(),
                        package
                            .root
                            .join(&package.config.build_dir)
                            .join("lib/lean"),
                    ),
                ))
            })
            .collect()
    }
}

fn absent_metadata(root: &Path, relative: &str) -> Result<(), Failure> {
    let path = root.join(relative);
    check_path(root, &path, true)?;
    match std::fs::symlink_metadata(&path) {
        Ok(_) => Err(Failure::unsupported(format!(
            "local-path dependency resolution does not yet support {}",
            path.display(),
        ))),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(error) => Err(Failure::io(&path, error)),
    }
}

fn guard_metadata(
    root: &Path,
    relatives: &[&'static str],
    guards: &mut Vec<(PathBuf, &'static str)>,
) -> Result<(), Failure> {
    for relative in relatives {
        absent_metadata(root, relative)?;
        guards.push((root.to_path_buf(), *relative));
    }
    Ok(())
}

/// Walk the explicitly selected dependency path before canonicalization, so a
/// symlink followed by `..` cannot evade the ordinary package path checks.
fn dependency_root(owner: &Path, path: &Path) -> Result<PathBuf, Failure> {
    if path.components().count() > 128 {
        return Err(Failure::new(
            "resource",
            "local dependency path exceeds 128 components",
        ));
    }
    let mut cursor = owner.to_path_buf();
    for component in path.components() {
        match component {
            Component::Prefix(_) => {
                return Err(Failure::unsupported(
                    "local dependency path has an unsupported platform prefix",
                ));
            }
            Component::RootDir => cursor = PathBuf::from(component.as_os_str()),
            Component::CurDir => continue,
            Component::ParentDir => {
                cursor.pop();
            }
            Component::Normal(part) => cursor.push(part),
        }
        let metadata =
            std::fs::symlink_metadata(&cursor).map_err(|error| Failure::io(&cursor, error))?;
        if metadata.file_type().is_symlink() {
            return Err(Failure::input(format!(
                "refusing symlink {}",
                cursor.display(),
            )));
        }
        if !metadata.is_dir() {
            return Err(Failure::input(format!(
                "local dependency is not a directory: {}",
                cursor.display(),
            )));
        }
    }
    cursor
        .canonicalize()
        .map_err(|error| Failure::io(&cursor, error))
}

pub(super) fn load(
    root: &Path,
    configuration: Configuration,
    evaluation: ConfigurationEvaluation,
) -> Result<Sources, Failure> {
    let manifest = ManifestSelection::load(root)?;
    let mut metadata_guards = Vec::new();
    let mut git_checkouts = Vec::new();
    let config = &configuration.config;
    let mut selected = BTreeMap::from([(fln_lake::canonical_package_name(&config.name), 0)]);
    let mut edges = vec![Vec::new()];
    let mut requirements = 0usize;
    if !config.requires.is_empty() {
        guard_metadata(
            root,
            &[".lake/package-overrides.json"],
            &mut metadata_guards,
        )?;
    }
    let mut packages = vec![(root.to_path_buf(), configuration)];
    let mut next = 0;
    while next < packages.len() {
        let (owner, configuration) = &packages[next];
        let owner = owner.clone();
        let declared = configuration.config.requires.clone();
        requirements = requirements
            .checked_add(declared.len())
            .filter(|count| *count <= MAX_REQUIREMENTS)
            .ok_or_else(|| Failure::new("resource", "local requirement count exceeds 4096"))?;
        // Pinned Lake resolves all direct requirements in reverse order before
        // visiting children. An already selected name wins across diamonds and
        // duplicate declarations, regardless of a later path. Package cycles
        // are checked once these selected identities have been resolved.
        for requirement in declared.iter().rev() {
            let identity = fln_lake::canonical_package_name(&requirement.name);
            if let Some(index) = selected.get(&identity) {
                edges[next].push(*index);
                continue;
            }
            if packages.len() >= MAX_PACKAGES {
                return Err(Failure::new("resource", "local package count exceeds 64"));
            }
            let (directory, selection) = manifest.dependency(
                &owner,
                requirement,
                &mut metadata_guards,
                &mut git_checkouts,
            )?;
            let configuration = load_configuration(&directory, selection, evaluation)?;
            // Lake's loader uses the requirement name as package identity;
            // the dependency's own name field does not override that selection.
            let index = packages.len();
            selected.insert(identity, index);
            packages.push((directory, configuration));
            edges.push(Vec::new());
            edges[next].push(index);
        }
        next += 1;
    }
    // Lake's configuration resolver can represent a package cycle, but an
    // executable's transDeps build refuses it. Do not run a program that the
    // corresponding native executable target cannot build.
    fn cyclic(index: usize, edges: &[Vec<usize>], state: &mut [u8]) -> bool {
        if state[index] != 0 {
            return state[index] == 1;
        }
        state[index] = 1;
        if edges[index].iter().any(|next| cyclic(*next, edges, state)) {
            return true;
        }
        state[index] = 2;
        false
    }
    if cyclic(0, &edges, &mut vec![0; packages.len()]) {
        return Err(Failure::input("local package dependency cycle"));
    }
    let mut configuration_imports = Vec::new();
    let packages = packages
        .into_iter()
        .map(|(root, loaded)| {
            let Configuration {
                config,
                input: configuration,
                default_toml,
                imports,
            } = loaded;
            configuration_imports.extend(imports);
            let libraries = library_sources(&root, &config)?;
            Ok(Package {
                root,
                config,
                configuration,
                default_toml,
                libraries,
            })
        })
        .collect::<Result<_, Failure>>()?;
    let sources = Sources {
        packages,
        configuration_imports,
        manifest,
        git_checkouts,
        metadata_guards,
    };
    sources.verify_configurations()?;
    Ok(sources)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_lake::{LakeConfigFormat, LakeTarget};

    fn package(format: LakeConfigFormat, root_module: &str) -> Package {
        // These are already loaded configuration values. The regression is in
        // source ownership and destination selection, not import admission.
        let (name, filename, build_dir) = match format {
            LakeConfigFormat::Lean => ("leanPart", "lakefile.lean", "lean-out"),
            LakeConfigFormat::Toml => ("tomlPart", "lakefile.toml", "toml-out"),
        };
        let root = PathBuf::from("/workspace/shared");
        let config = LakeConfig {
            name: name.to_owned(),
            default_targets: Vec::new(),
            lean_toolchain: None,
            src_dir: PathBuf::from("src"),
            build_dir: PathBuf::from(build_dir),
            requires: Vec::new(),
            targets: vec![LakeTarget {
                name: root_module.to_owned(),
                kind: TargetKind::Library,
                roots: vec![root_module.to_owned()],
                src_dir: None,
            }],
            format,
        };
        let libraries = library_sources(&root, &config)
            .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
        Package {
            configuration: (root.join(filename), filename.to_owned()),
            root,
            config,
            default_toml: false,
            libraries,
        }
    }

    fn sources(packages: Vec<Package>) -> Sources {
        Sources {
            packages,
            configuration_imports: Vec::new(),
            manifest: ManifestSelection {
                root: PathBuf::from("/workspace/root"),
                path: PathBuf::from("/workspace/root/lake-manifest.json"),
                digest: None,
                entries: None,
                packages_dir: PathBuf::from(".lake/packages"),
            },
            git_checkouts: Vec::new(),
            metadata_guards: Vec::new(),
        }
    }

    fn artifacts(names: &[&str]) -> BTreeMap<Name, ModuleArtifacts> {
        names
            .iter()
            .map(|name| {
                (
                    Name::from_components(name.split('.')),
                    ModuleArtifacts {
                        exported: Vec::new(),
                        companions: None,
                        ir: None,
                    },
                )
            })
            .collect()
    }

    #[test]
    fn configurations_in_one_directory_keep_their_own_artifact_destinations() {
        for reverse in [false, true] {
            let mut packages = vec![
                package(LakeConfigFormat::Lean, "LeanPart"),
                package(LakeConfigFormat::Toml, "TomlPart"),
            ];
            if reverse {
                packages.reverse();
            }
            let sources = sources(packages);
            let destinations = sources
                .destinations(&artifacts(&["LeanPart.Child", "TomlPart.Child"]))
                .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
            for (module, build_dir) in [("LeanPart", "lean-out"), ("TomlPart", "toml-out")] {
                let name = Name::from_components([module, "Child"]);
                let location = sources
                    .resolve(&name)
                    .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail))
                    .expect("declared library module");
                let root = PathBuf::from("/workspace/shared");
                assert_eq!(location.package, root);
                assert_eq!(
                    location.path,
                    root.join("src").join(module).join("Child.lean")
                );
                assert_eq!(
                    destinations[&name],
                    (root.clone(), root.join(build_dir).join("lib/lean")),
                );
            }
        }
    }

    #[test]
    fn shared_source_aliases_keep_the_first_selected_configuration() {
        for (reverse, build_dir) in [(false, "lean-out"), (true, "toml-out")] {
            let mut packages = vec![
                package(LakeConfigFormat::Lean, "Shared"),
                package(LakeConfigFormat::Toml, "Shared"),
            ];
            if reverse {
                packages.reverse();
            }
            let destinations = sources(packages)
                .destinations(&artifacts(&["Shared"]))
                .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
            let root = PathBuf::from("/workspace/shared");
            assert_eq!(
                destinations[&Name::from_components(["Shared"])],
                (root.clone(), root.join(build_dir).join("lib/lean")),
            );
        }
    }

    #[test]
    fn shared_directories_do_not_hide_conflicting_source_ownership() {
        let lean = package(LakeConfigFormat::Lean, "Shared");
        let mut toml = package(LakeConfigFormat::Toml, "Shared");
        toml.config.src_dir = PathBuf::from("different-source");
        toml.libraries = library_sources(&toml.root, &toml.config)
            .unwrap_or_else(|error| panic!("{}: {}", error.class, error.detail));
        let sources = sources(vec![lean, toml]);
        let error = sources
            .destinations(&artifacts(&["Shared"]))
            .expect_err("different physical sources remain ambiguous");
        assert_eq!(error.class, "unsupported");
        assert!(error.detail.contains("belongs to multiple local packages"));
    }

    fn locked_checkout_fixture() -> GitCheckout {
        let stamp = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory =
            std::env::temp_dir().join(format!("fln-locked-git-{}-{stamp}", std::process::id(),));
        for relative in [".git/objects", ".git/refs/heads", "lib"] {
            std::fs::create_dir_all(directory.join(relative)).unwrap();
        }
        let revision = "1".repeat(40);
        std::fs::write(directory.join(".git/HEAD"), format!("{revision}\n")).unwrap();
        let directory = directory.canonicalize().unwrap();
        GitCheckout {
            package_directory: directory.join("lib"),
            directory,
            revision,
        }
    }

    #[test]
    fn locked_git_guards_recheck_revision_identity_before_publication() {
        let guard = locked_checkout_fixture();
        guard
            .verify()
            .unwrap_or_else(|error| panic!("{}", error.detail));
        std::fs::write(guard.directory.join(".git/HEAD"), "2".repeat(40)).unwrap();
        let error = guard
            .verify()
            .expect_err("changed HEAD must invalidate the guard");
        assert_eq!(error.class, "unsupported");
        assert!(error.detail.contains("materialize the locked revision"));
    }

    #[test]
    fn ordinary_git_layout_and_reference_metadata_are_required() {
        let guard = locked_checkout_fixture();
        let git = guard.directory.join(".git");
        std::fs::rename(git.join("objects"), git.join("saved-objects")).unwrap();
        let error = guard
            .verify()
            .expect_err("a HEAD file alone is not a repository");
        assert_eq!(error.class, "unsupported");
        assert!(error.detail.contains("ordinary objects directory"));
        std::fs::rename(git.join("saved-objects"), git.join("objects")).unwrap();

        std::fs::write(git.join("HEAD"), "ref: refs/heads/main\n").unwrap();
        let error = guard.verify().expect_err("missing refs are not accepted");
        assert_eq!(error.class, "unsupported");
        assert!(error.detail.contains("is absent"));
        std::fs::write(
            git.join("packed-refs"),
            format!(
                "# pack-refs with: peeled fully-peeled sorted\n{} refs/heads/main\n",
                guard.revision,
            ),
        )
        .unwrap();
        guard
            .verify()
            .unwrap_or_else(|error| panic!("{}", error.detail));
        std::fs::write(
            git.join("packed-refs"),
            format!("{0} refs/heads/main\n{0} refs/heads/main\n", guard.revision),
        )
        .unwrap();
        let error = guard
            .verify()
            .expect_err("duplicate packed refs are ambiguous");
        assert_eq!(error.class, "input");
        assert!(error.detail.contains("duplicate selected"));
        std::fs::write(git.join("refs/heads/main"), "ref: refs/heads/main\n").unwrap();
        let error = guard.verify().expect_err("cyclic loose refs must not loop");
        assert_eq!(error.class, "input");
        assert!(error.detail.contains("cyclic Git symbolic reference"));

        std::fs::rename(&git, guard.directory.join("saved-git")).unwrap();
        std::fs::write(&git, "gitdir: saved-git\n").unwrap();
        let error = guard.verify().expect_err("gitfiles remain unsupported");
        assert_eq!(error.class, "unsupported");
        assert!(error.detail.contains("ordinary .git directory"));
    }

    #[cfg(unix)]
    #[test]
    fn git_guard_revalidation_refuses_swapped_checkout_and_subdirectory_roots() {
        for subdir in [false, true] {
            let guard = locked_checkout_fixture();
            guard
                .verify()
                .unwrap_or_else(|error| panic!("{}", error.detail));
            let path = if subdir {
                &guard.package_directory
            } else {
                &guard.directory
            };
            let moved = path.with_extension("original");
            std::fs::rename(path, &moved).unwrap();
            std::os::unix::fs::symlink(&moved, path).unwrap();
            let error = guard
                .verify()
                .expect_err("a swapped root must not become trusted");
            assert_eq!(error.class, "input");
            assert!(error.detail.contains("refusing symlink"));
        }
        let guard = locked_checkout_fixture();
        let head = guard.directory.join(".git/HEAD");
        let moved = guard.directory.join(".git/saved-HEAD");
        std::fs::rename(&head, &moved).unwrap();
        std::os::unix::fs::symlink(&moved, &head).unwrap();
        let error = guard.verify().expect_err("HEAD must be a regular file");
        assert_eq!(error.class, "input");
        assert!(error.detail.contains("refusing symlink"));
    }

    #[test]
    fn git_checkout_names_render_quoted_components_without_path_escapes() {
        for (name, directory) in [
            ("«dep-name»", "dep-name"),
            ("scope.«dep-name»", "scope.dep-name"),
            ("«part«name»", "part«name"),
        ] {
            assert_eq!(
                git_package_directory(name).unwrap_or_else(|error| panic!("{}", error.detail)),
                directory,
            );
        }
        for name in [
            "«../dep»",
            "..",
            "«dep/sub»",
            "«dep\\sub»",
            "«dep:sub»",
            "«unclosed",
        ] {
            assert!(git_package_directory(name).is_err(), "{name}");
        }
    }
}
