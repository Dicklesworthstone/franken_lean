//! Read-only local package discovery for checked source builds and executables.
//!
//! Package identity follows Lake's reverse, breadth-first requirement order.
//! Source containment is checked against each owning package; an explicit
//! dependency path may name a sibling without making source paths unbounded.

use super::*;

const MAX_PACKAGES: usize = 64;
const MAX_REQUIREMENTS: usize = 4096;

pub(super) struct Sources {
    pub(super) packages: Vec<Package>,
}

pub(super) struct Package {
    pub(super) root: PathBuf,
    pub(super) config: LakeConfig,
    libraries: Vec<Library>,
}

impl Sources {
    pub(super) fn libraries(&self) -> Vec<Library> {
        self.packages
            .iter()
            .flat_map(|package| package.libraries.iter().cloned())
            .collect()
    }

    pub(super) fn resolve(&self, module: &Name) -> Result<Option<SourceLocation>, Failure> {
        let mut found: Option<SourceLocation> = None;
        for package in &self.packages {
            let Some(path) = source_path(module, &package.libraries)? else {
                continue;
            };
            if found.as_ref().is_some_and(|previous| {
                previous.path != path || previous.package != package.root
            }) {
                return Err(Failure::unsupported(format!(
                    "module `{}` belongs to multiple local packages",
                    module.to_display_string(),
                )));
            }
            found = Some(SourceLocation {
                package: package.root.clone(),
                path,
            });
        }
        Ok(found)
    }

    pub(super) fn destinations(
        &self,
        artifacts: &BTreeMap<Name, ModuleArtifacts>,
    ) -> Result<BTreeMap<Name, (PathBuf, PathBuf)>, Failure> {
        artifacts
            .keys()
            .map(|name| {
                let source = self.resolve(name)?.ok_or_else(|| {
                    Failure::new("internal-fault", "built module has no source owner")
                })?;
                let package = self
                    .packages
                    .iter()
                    .find(|package| package.root == source.package)
                    .ok_or_else(|| {
                        Failure::new("internal-fault", "built module lost its package")
                    })?;
                Ok((
                    name.clone(),
                    (
                        package.root.clone(),
                        package.root.join(&package.config.build_dir).join("lib/lean"),
                    ),
                ))
            })
            .collect()
    }
}

fn unsupported_metadata(root: &Path) -> Result<(), Failure> {
    for relative in [
        "lake-manifest.json",
        ".lake/package-overrides.json",
        "lakefile.lean",
    ] {
        let path = root.join(relative);
        check_path(root, &path, true)?;
        match std::fs::symlink_metadata(&path) {
            Ok(_) => {
                return Err(Failure::unsupported(format!(
                    "local-path dependency resolution does not yet support {}",
                    path.display(),
                )));
            }
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => return Err(Failure::io(&path, error)),
        }
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

pub(super) fn load(root: &Path, config: &LakeConfig) -> Result<Sources, Failure> {
    let mut packages = vec![(root.to_path_buf(), config.clone())];
    let mut selected = BTreeMap::from([(config.name.clone(), 0)]);
    let mut edges = vec![Vec::new()];
    let mut requirements = 0usize;
    if !config.requires.is_empty() {
        unsupported_metadata(root)?;
    }
    let mut next = 0;
    while next < packages.len() {
        let (owner, config) = &packages[next];
        let owner = owner.clone();
        let declared = config.requires.clone();
        requirements = requirements
            .checked_add(declared.len())
            .filter(|count| *count <= MAX_REQUIREMENTS)
            .ok_or_else(|| Failure::new("resource", "local requirement count exceeds 4096"))?;
        // Pinned Lake resolves all direct requirements in reverse order before
        // visiting children. An already selected name wins across diamonds and
        // duplicate declarations, regardless of a later path. Package cycles
        // are checked once these selected identities have been resolved.
        for requirement in declared.iter().rev() {
            if let Some(index) = selected.get(&requirement.name) {
                edges[next].push(*index);
                continue;
            }
            if packages.len() >= MAX_PACKAGES {
                return Err(Failure::new("resource", "local package count exceeds 64"));
            }
            let path = requirement.path.as_deref().ok_or_else(|| {
                Failure::unsupported("only local path dependencies are supported")
            })?;
            let directory = dependency_root(&owner, path)?;
            unsupported_metadata(&directory)?;
            let config = executable_config(&directory)?;
            // Lake's TOML loader uses the requirement name as package identity;
            // the dependency's own name field does not override that selection.
            let index = packages.len();
            selected.insert(requirement.name.clone(), index);
            packages.push((directory, config));
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
    let packages = packages
        .into_iter()
        .map(|(root, config)| {
            let libraries = library_sources(&root, &config)?;
            Ok(Package {
                root,
                config,
                libraries,
            })
        })
        .collect::<Result<_, Failure>>()?;
    Ok(Sources { packages })
}
