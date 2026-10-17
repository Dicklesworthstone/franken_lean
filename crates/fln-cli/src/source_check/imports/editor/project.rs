//! Bounded declarative package discovery for editor source closures.
//! Never execute a lakefile while answering a read-only editor query.
use super::*;
use fln_lake::{LakeConfig, TargetKind};
use std::path::Component;

struct Library {
    directory: PathBuf,
    roots: Vec<Name>,
}
pub(super) struct Project {
    pub(super) root: PathBuf,
    pub(super) config: PathBuf,
    libraries: Vec<Library>,
}
fn exists(path: &Path) -> Result<bool, Failure> {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_file() => {
            Err(Failure::input(format!(
                "project configuration is a symlink or not a regular file: {}",
                path.display()
            )))
        }
        Ok(_) => Ok(true),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok(false),
        Err(error) => Err(Failure::io(path, error)),
    }
}
fn directory(root: &Path, package: &Path, library: &Path) -> Result<PathBuf, Failure> {
    let mut path = root.to_owned();
    for component in package.components().chain(library.components()) {
        match component {
            Component::CurDir => continue,
            Component::Normal(part) => path.push(part),
            _ => {
                return Err(Failure::input(
                    "editor source directories must stay within the package",
                ));
            }
        }
        match std::fs::symlink_metadata(&path) {
            Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
                return Err(Failure::input(format!(
                    "refusing symlink or non-directory in editor source directory {}",
                    path.display()
                )));
            }
            Ok(_) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(Failure::io(&path, error)),
        }
    }
    Ok(path)
}
fn module_name(parts: impl IntoIterator<Item = String>) -> Result<Name, Failure> {
    let parts: Vec<String> = parts.into_iter().collect();
    if parts.is_empty() || parts.len() > MAX_NAME_DEPTH {
        return Err(Failure::resource(
            "editor module name exceeds its depth budget",
        ));
    }
    for part in &parts {
        validate_component(part)?;
    }
    Ok(Name::from_components(parts.iter().map(String::as_str)))
}
fn belongs(module: &Name, root: &Name) -> bool {
    let mut module = module.clone();
    while !module.is_anonymous() {
        if &module == root {
            return true;
        }
        module = module.parent();
    }
    false
}
impl Project {
    pub(super) fn discover(entry: &Path) -> Result<Option<(Self, Name)>, Failure> {
        for (depth, root) in entry
            .parent()
            .into_iter()
            .flat_map(Path::ancestors)
            .enumerate()
        {
            if depth >= 128 {
                return Err(Failure::resource(
                    "editor package search exceeds 128 ancestors",
                ));
            }
            let config = root.join("lakefile.toml");
            if !exists(&config)? {
                // A nested executable package is a boundary, not permission to
                // steal its enclosing package's module identity or configuration.
                if exists(&root.join("lakefile.lean"))? {
                    return Ok(None);
                }
                continue;
            }
            let bytes =
                read_bounded(&config, 64 * 1024, "editor Lake configuration").map_err(|error| {
                    Failure {
                        class: error.class(),
                        detail: error.to_string(),
                        authority: false,
                        exit: error.exit_code(),
                    }
                })?;
            let text = std::str::from_utf8(&bytes)
                .map_err(|_| Failure::input("editor Lake configuration is not UTF-8"))?;
            let parsed = LakeConfig::parse_toml_for_build(text)
                .map_err(|error| Failure::input(error.to_string()))?;
            if parsed.targets.len() > MAX_MODULES {
                return Err(Failure::resource("editor library count exceeds 256"));
            }
            let mut libraries = Vec::new();
            let mut roots = 0usize;
            for target in parsed
                .targets
                .iter()
                .filter(|t| t.kind == TargetKind::Library)
            {
                roots = roots
                    .checked_add(target.roots.len())
                    .filter(|n| *n <= MAX_IMPORTS)
                    .ok_or_else(|| Failure::resource("editor library root count exceeds 4096"))?;
                libraries.push(Library {
                    directory: directory(
                        root,
                        &parsed.src_dir,
                        target.src_dir.as_deref().unwrap_or(Path::new(".")),
                    )?,
                    roots: target
                        .roots
                        .iter()
                        .map(|s| module_name(s.split('.').map(str::to_owned)))
                        .collect::<Result<_, _>>()?,
                });
            }
            let project = Self {
                root: root.to_owned(),
                config,
                libraries,
            };
            let mut selected = None;
            for library in &project.libraries {
                let Ok(relative) = entry.strip_prefix(&library.directory) else {
                    continue;
                };
                let parts = relative
                    .with_extension("")
                    .components()
                    .map(|part| {
                        part.as_os_str()
                            .to_str()
                            .map(str::to_owned)
                            .ok_or_else(|| Failure::input("editor module path is not UTF-8"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let candidate = Name::from_components(parts.iter().map(String::as_str));
                if !library.roots.iter().any(|root| belongs(&candidate, root)) {
                    continue;
                }
                let name = module_name(parts)?;
                if selected.as_ref().is_some_and(|previous| previous != &name) {
                    return Err(Failure::input(
                        "editor file has ambiguous module identities",
                    ));
                }
                // Ownership is independent of which candidate happens to exist.
                project.source_root(&name)?;
                selected = Some(name);
            }
            return Ok(selected.map(|name| (project, name)));
        }
        Ok(None)
    }
    pub(super) fn source_root(&self, name: &Name) -> Result<Option<&Path>, Failure> {
        let mut found: Option<&Path> = None;
        for library in &self.libraries {
            if library.roots.iter().any(|root| belongs(name, root)) {
                if found.is_some_and(|old| old != library.directory) {
                    return Err(Failure::input(format!(
                        "module {} has ambiguous source directories",
                        name.to_display_string()
                    )));
                }
                found = Some(&library.directory);
            }
        }
        Ok(found)
    }
}
