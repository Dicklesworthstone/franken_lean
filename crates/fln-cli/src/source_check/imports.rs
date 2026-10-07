//! Resolve a closed native source library under the entry file's directory.
//! Files are read once, bounded as a closure, and handed to the admission-only
//! module checker. Import text never becomes an arbitrary filesystem path.
//!
//! An import with no source file under the root is looked up as an `.olean`
//! on the search path (`LEAN_PATH`, else the pinned toolchain's `lib/lean`).
//! Its closure is read as data and admitted through K1 and the independent
//! checker before any source is checked: the `recheck` trust level. Under the
//! `reuse-verified` posture (bead `fln-uyuz`) an earlier admission of the
//! identical bytes by this binary is rebuilt and re-proved by logical root
//! instead ([`fln::source_check::modules::reuse`]); every output names which.
use super::*;
pub(super) mod editor;
pub(super) mod execution;
mod metadata;
mod reuse;
use fln::source_check::modules::imported::SourceOleanImport;
use fln::source_check::modules::reuse::{ImportPosture, ImportPostureReport};
use fln::source_check::modules::{SourceModuleCheckLimits, parse_source_header};
use fln::{LeafView, Name, Outcome, SourceFileCheck, SourceModuleInput};
use std::collections::BTreeMap;

const MAX_MODULES: usize = 256;
const MAX_IMPORTS: usize = 4096;
const MAX_NAME_DEPTH: usize = 128;
const MAX_OLEAN_MODULES: usize = 4096;
const MAX_OLEAN_BYTES: usize = 1 << 30;

/// One `.olean` module of the import closure: exported, server and private parts.
pub(super) struct OleanImport {
    name: Name,
    parts: [Vec<u8>; 3],
}

/// What the council admitted from `.olean` imports, for the report.
pub(super) struct OleanBase {
    pub(super) modules: usize,
    pub(super) declarations: usize,
    declaration_root: fln::LogicalRoot,
    metadata: Vec<fln::source_check::modules::imported::SourceMetadataReport>,
    receipt: SourceOleanImport,
    /// The posture this closure was obtained under, and what it did.
    pub(super) report: ImportPostureReport,
}

pub(super) struct Failure {
    pub(super) class: &'static str,
    pub(super) detail: String,
    pub(super) authority: bool,
    pub(super) exit: u8,
}
impl Failure {
    pub(super) fn new(class: &'static str, detail: &str, authority: bool, exit: u8) -> Self {
        Self {
            class,
            detail: detail.to_owned(),
            authority,
            exit,
        }
    }
    fn input(detail: impl Into<String>) -> Self {
        Self {
            class: "input",
            detail: detail.into(),
            authority: false,
            exit: 1,
        }
    }
    fn resource(detail: impl Into<String>) -> Self {
        Self {
            class: "resource",
            detail: detail.into(),
            authority: false,
            exit: 3,
        }
    }
    fn io(path: &Path, error: std::io::Error) -> Self {
        Self {
            class: "io",
            detail: format!("{}: {error}", path.display()),
            authority: false,
            exit: 2,
        }
    }
}

enum Inputs {
    Files(Vec<Vec<u8>>),
    Modules {
        names: Vec<Name>,
        sources: Vec<Vec<u8>>,
    },
}
pub(super) struct Loaded {
    inputs: Inputs,
    pub(super) total_bytes: usize,
    oleans: Vec<OleanImport>,
    olean_roots: Vec<Name>,
}
impl Loaded {
    /// The base engine source is checked against: the council-admitted
    /// `.olean` closure when the source imports one, else `seed()`. `jobs`
    /// closure modules are checked at once, each worker on a stack of the
    /// `.olean` kernel depth budget; the result does not depend on it.
    pub(super) fn base_engine(
        &self,
        seed: impl FnOnce() -> Result<fln::Engine, Failure>,
        jobs: std::num::NonZeroUsize,
        posture: ImportPosture,
    ) -> Result<(fln::Engine, Option<OleanBase>), Failure> {
        if self.oleans.is_empty() {
            return seed().map(|engine| (engine, None));
        }
        let inputs: Vec<fln::OleanModuleInput<'_>> = self
            .oleans
            .iter()
            .map(|import| {
                let [exported, server, private] = &import.parts;
                fln::OleanModuleInput {
                    name: &import.name,
                    artifact: exported,
                    server_artifact: (!server.is_empty()).then_some(server.as_slice()),
                    private_artifact: (!private.is_empty()).then_some(private.as_slice()),
                }
            })
            .collect();
        let limits = fln::OleanCheckLimits::new(
            MAX_OLEAN_BYTES,
            fln::Budget::for_stack_bytes(OLEAN_CHECK_KERNEL_STACK_BYTES),
        );
        let resolved = reuse::Resolved::new(posture);
        let checked = fln::Engine::from_environment(fln::Environment::new())
            .import_olean_modules_with_posture(
                &inputs,
                &self.olean_roots,
                &fln::KVMap::new(),
                fln::source_check::modules::imported::SourceOleanImportLimits {
                    max_roots: MAX_IMPORTS,
                    jobs: fln::OleanFrontierJobs {
                        threads: jobs,
                        worker_stack_bytes: OLEAN_CHECK_KERNEL_STACK_BYTES,
                    },
                    ..fln::source_check::modules::imported::SourceOleanImportLimits::new(limits)
                },
                resolved.request(),
                None,
            )
            .map_err(metadata::failure)?;
        match checked {
            Outcome::Complete((checked, report)) => {
                let declarations = checked
                    .checked
                    .modules
                    .iter()
                    .map(|module| module.declarations.len())
                    .sum();
                Ok((
                    checked.engine.clone(),
                    Some(OleanBase {
                        modules: checked.checked.modules.len(),
                        declarations,
                        declaration_root: checked.checked.result_logical_root,
                        metadata: checked.modules.clone(),
                        receipt: checked,
                        report,
                    }),
                ))
            }
            Outcome::Inconclusive(reason) => Err(Failure {
                class: "inconclusive",
                detail: format!("importing .olean modules did not finish: {reason:?}"),
                authority: false,
                exit: 3,
            }),
            Outcome::InternalFault(fault) => Err(Failure {
                class: "internal-fault",
                detail: format!("importing .olean modules faulted: {fault:?}"),
                authority: false,
                exit: 4,
            }),
        }
    }

    /// Refuse unparseable source before any import is admitted, with the error
    /// [`Self::check`] would report (`fln::source_check::preflight_source_files`).
    pub(super) fn preflight(&self) -> Result<(), Failure> {
        match &self.inputs {
            Inputs::Files(sources) => {
                let inputs: Vec<_> = sources.iter().map(Vec::as_slice).collect();
                fln::source_check::preflight_source_files(&inputs).map_err(|error| {
                    let (class, authority, exit) = error.disposition();
                    Failure {
                        class,
                        authority,
                        exit,
                        detail: error.to_string(),
                    }
                })
            }
            Inputs::Modules { names, sources } => {
                for (name, source) in names.iter().zip(sources) {
                    fln::source_check::preflight_source_module(name, source).map_err(|error| {
                        let (class, authority, exit) = error.disposition();
                        Failure {
                            class,
                            authority,
                            exit,
                            detail: error.to_string(),
                        }
                    })?;
                }
                Ok(())
            }
        }
    }

    pub(super) fn check(
        &self,
        engine: &fln::Engine,
        olean_base: Option<&OleanBase>,
        limits: fln::SourceCheckLimits,
    ) -> Result<Outcome<SourceFileCheck>, Failure> {
        match &self.inputs {
            Inputs::Files(sources) => {
                let inputs: Vec<_> = sources.iter().map(Vec::as_slice).collect();
                engine
                    .check_source_files(&inputs, &fln::KVMap::new(), limits)
                    .map_err(|error| {
                        let (class, authority, exit) = error.disposition();
                        Failure {
                            class,
                            authority,
                            exit,
                            detail: error.to_string(),
                        }
                    })
            }
            Inputs::Modules { names, sources } => {
                let inputs: Vec<_> = names
                    .iter()
                    .zip(sources)
                    .map(|(name, source)| SourceModuleInput { name, source })
                    .collect();
                // The receipt projects each module's exact external world and
                // interleaves external journals with local source exports.
                // A shared ambient engine cannot preserve these semantics.
                let checked = if let Some(base) = olean_base {
                    base.receipt.check_source_modules(
                        &inputs,
                        &names[0],
                        &fln::KVMap::new(),
                        SourceModuleCheckLimits::new(limits),
                        None,
                    )
                } else {
                    engine.check_source_modules(
                        &inputs,
                        &names[0],
                        &fln::KVMap::new(),
                        SourceModuleCheckLimits::new(limits),
                    )
                };
                checked
                    .map(|outcome| outcome.map_complete(|result| result.checked))
                    .map_err(|error| {
                        let (class, authority, exit) = error.disposition();
                        Failure {
                            class,
                            authority,
                            exit,
                            detail: error.to_string(),
                        }
                    })
            }
        }
    }
}

pub(super) fn load(
    paths: &[PathBuf],
    mut sources: Vec<Vec<u8>>,
    mut total_bytes: usize,
    max_bytes: usize,
) -> Result<Loaded, Failure> {
    let mut has_headers = false;
    for (path, source) in paths.iter().zip(&sources) {
        let header = parse_source_header(source)
            .map_err(|error| Failure::input(format!("{}: {error}", path.display())))?;
        has_headers |= !header.imports.is_empty() || header.prelude;
    }
    if !has_headers {
        return Ok(Loaded {
            inputs: Inputs::Files(sources),
            total_bytes,
            oleans: Vec::new(),
            olean_roots: Vec::new(),
        });
    }
    if paths.len() != 1 {
        return Err(Failure::input(
            "source imports require one entry file; pass that file alone to resolve its dependency closure",
        ));
    }
    let entry = &paths[0];
    if entry.extension().and_then(|s| s.to_str()) != Some("lean") {
        return Err(Failure::input(
            "a source module entry must have a .lean extension",
        ));
    }
    let stem = entry
        .file_stem()
        .and_then(|s| s.to_str())
        .ok_or_else(|| Failure::input("the source module entry needs a UTF-8 file name"))?;
    validate_component(stem)?;
    // An empty parent denotes the current directory for a relative entry name.
    let parent = entry
        .parent()
        .filter(|p| !p.as_os_str().is_empty())
        .unwrap_or(Path::new("."));
    let root = std::fs::canonicalize(parent).map_err(|e| Failure::io(parent, e))?;
    let entry_path = std::fs::canonicalize(entry).map_err(|e| Failure::io(entry, e))?;
    if !entry_path.starts_with(&root) {
        return Err(Failure::input("source entry escaped its module root"));
    }
    let entry_name = Name::from_components([stem]);
    let mut names = vec![entry_name.clone()];
    let mut by_name = BTreeMap::from([(entry_name.clone(), 0usize)]);
    let mut by_path = BTreeMap::from([(entry_path, entry_name)]);
    let mut cursor = 0usize;
    let mut import_rows = 0usize;
    let mut olean_roots: Vec<Name> = Vec::new();
    let mut source_imports = BTreeMap::new();
    while cursor < sources.len() {
        let header = parse_source_header(&sources[cursor]).map_err(|error| {
            Failure::input(format!(
                "module `{}`: {error}",
                names[cursor].to_display_string()
            ))
        })?;
        import_rows = import_rows
            .checked_add(header.imports.len())
            .filter(|n| *n <= MAX_IMPORTS)
            .ok_or_else(|| Failure::resource("source import count exceeds 4096"))?;
        source_imports.insert(names[cursor].clone(), header.imports.clone());
        for name in header.imports {
            if by_name.contains_key(&name) || olean_roots.contains(&name) {
                continue;
            }
            if !local_source_exists(&root, &name)? {
                olean_roots.push(name);
                continue;
            }
            if sources.len() >= MAX_MODULES {
                return Err(Failure::resource("source module count exceeds 256"));
            }
            let path = module_path(&root, &name)?;
            let canonical = std::fs::canonicalize(&path).map_err(|e| Failure::io(&path, e))?;
            if !canonical.starts_with(&root) {
                return Err(Failure::input(
                    "resolved source import escaped the module root",
                ));
            }
            if let Some(previous) = by_path.get(&canonical) {
                return Err(Failure::input(format!(
                    "source modules `{}` and `{}` resolve to the same file",
                    previous.to_display_string(),
                    name.to_display_string(),
                )));
            }
            let remaining = max_bytes
                .checked_sub(total_bytes)
                .ok_or_else(|| Failure::resource("source import closure exceeds its byte limit"))?;
            let bytes =
                read_bounded(&path, remaining, "imported Lean source").map_err(|error| {
                    Failure {
                        class: error.class(),
                        detail: error.to_string(),
                        authority: false,
                        exit: error.exit_code(),
                    }
                })?;
            total_bytes = total_bytes
                .checked_add(bytes.len())
                .filter(|n| *n <= max_bytes)
                .ok_or_else(|| Failure::resource("source import closure exceeds its byte limit"))?;
            by_name.insert(name.clone(), sources.len());
            by_path.insert(canonical, name.clone());
            names.push(name);
            sources.push(bytes);
        }
        cursor += 1;
    }
    // Discovery order is breadth-first filesystem work, not Lean import order.
    // Resolve external roots by walking the source headers left-to-right first.
    let olean_roots = metadata::ordered_roots(&source_imports, &names[..1]);
    let oleans = if olean_roots.is_empty() {
        Vec::new()
    } else {
        load_olean_closure(&olean_roots, &root)?
    };
    Ok(Loaded {
        inputs: Inputs::Modules { names, sources },
        total_bytes,
        oleans,
        olean_roots,
    })
}

/// Whether `name` resolves to a source file under `root`. A missing component
/// anywhere means "not a local module"; a present one must pass the same
/// symlink and file-kind checks as any source import.
fn local_source_exists(root: &Path, name: &Name) -> Result<bool, Failure> {
    let (path, present) = module_file(root, name, "lean")?;
    if !present {
        return Ok(false);
    }
    module_path(root, name)?;
    Ok(path.is_file())
}

/// `root/A/B.<extension>` for module `A.B`, and whether it exists. Components
/// are validated exactly as source import names are.
fn module_file(root: &Path, name: &Name, extension: &str) -> Result<(PathBuf, bool), Failure> {
    let mut cursor = name.clone();
    let mut components = Vec::new();
    while !cursor.is_anonymous() {
        if components.len() >= MAX_NAME_DEPTH {
            return Err(Failure::resource("source module name depth exceeds 128"));
        }
        let LeafView::Str(component) = cursor.leaf_view() else {
            return Err(Failure::input(
                "source module names require textual components",
            ));
        };
        validate_component(component)?;
        components.push(component.to_owned());
        cursor = cursor.parent();
    }
    let Some(last) = components.first().cloned() else {
        return Err(Failure::input("source module name must not be anonymous"));
    };
    components.reverse();
    let mut path = root.to_path_buf();
    for component in &components[..components.len() - 1] {
        path.push(component);
    }
    path.push(format!("{last}.{extension}"));
    match std::fs::symlink_metadata(&path) {
        Ok(_) => Ok((path, true)),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => Ok((path, false)),
        Err(error) => Err(Failure::io(&path, error)),
    }
}

/// `LEAN_PATH` entries, else the pinned toolchain's `lib/lean`.
fn olean_search_path() -> Vec<PathBuf> {
    if let Some(value) = std::env::var_os("LEAN_PATH") {
        let entries: Vec<PathBuf> = std::env::split_paths(&value)
            .filter(|entry| !entry.as_os_str().is_empty())
            .collect();
        if !entries.is_empty() {
            return entries;
        }
    }
    std::env::var_os("ELAN_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|home| PathBuf::from(home).join(".elan")))
        .map(|elan| {
            elan.join("toolchains")
                .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                .join("lib")
                .join("lean")
        })
        .into_iter()
        .collect()
}

fn find_olean(search: &[PathBuf], name: &Name) -> Result<Option<PathBuf>, Failure> {
    for root in search {
        let (path, present) = module_file(root, name, "olean")?;
        if present && path.is_file() {
            return Ok(Some(path));
        }
    }
    Ok(None)
}

fn load_olean_closure(roots: &[Name], source_root: &Path) -> Result<Vec<OleanImport>, Failure> {
    let search = olean_search_path();
    let decode = fln::OleanCheckLimits::new(
        MAX_OLEAN_BYTES,
        fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES),
    )
    .decode;
    let mut pending: Vec<Name> = roots.to_vec();
    let mut seen = std::collections::BTreeSet::new();
    let mut loaded = Vec::new();
    let mut total = 0usize;
    while let Some(name) = pending.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        if loaded.len() >= MAX_OLEAN_MODULES {
            return Err(Failure::resource(format!(
                ".olean import closure exceeds {MAX_OLEAN_MODULES} modules"
            )));
        }
        let Some(base) = find_olean(&search, &name)? else {
            let searched: Vec<String> = search.iter().map(|p| p.display().to_string()).collect();
            let (expected, _) = module_file(source_root, &name, "lean")?;
            return Err(Failure::input(format!(
                "import `{}` is neither a source file ({}) nor an .olean on the search path [{}]",
                name.to_display_string(),
                expected.display(),
                searched.join(", ")
            )));
        };
        let mut parts: [Vec<u8>; 3] = Default::default();
        for (slot, path) in parts.iter_mut().zip([
            base.clone(),
            base.with_extension("olean.server"),
            base.with_extension("olean.private"),
        ]) {
            if !path.is_file() && path != base {
                continue;
            }
            let remaining = MAX_OLEAN_BYTES
                .checked_sub(total)
                .ok_or_else(|| Failure::resource(".olean import closure exceeds 1 GiB"))?;
            *slot = read_bounded(&path, remaining, ".olean import").map_err(|error| Failure {
                class: error.class(),
                detail: error.to_string(),
                authority: false,
                exit: error.exit_code(),
            })?;
            total += slot.len();
        }
        let imports = fln::olean_module_imports(&parts[0], decode).map_err(|error| {
            Failure::input(format!(
                "{}: cannot read its imports: {error}",
                base.display()
            ))
        })?;
        pending.extend(imports);
        loaded.push(OleanImport { name, parts });
    }
    Ok(loaded)
}

/// Builds use the same bounded import loader, posture and dual-checker admission
/// as source checking, but never substitute a synthetic seed for missing imports.
pub(super) fn load_build_base(
    roots: &[Name],
    source_root: &Path,
    jobs: std::num::NonZeroUsize,
    posture: ImportPosture,
) -> Result<Option<(SourceOleanImport, ImportPostureReport)>, Failure> {
    let loaded = Loaded {
        inputs: Inputs::Files(Vec::new()),
        total_bytes: 0,
        oleans: load_olean_closure(roots, source_root)?,
        olean_roots: roots.to_vec(),
    };
    loaded
        .base_engine(
            || Ok(fln::Engine::from_environment(fln::Environment::new())),
            jobs,
            posture,
        )
        .map(|(_, base)| base.map(|base| (base.receipt, base.report)))
}

/// An editor session's `.olean` import world (bead `fln-uyuz`): the closure as
/// `check-source` resolves it, read afresh, with an identity over every byte.
pub(in crate::source_check) struct EditorWorld {
    /// Process-local: the closure's bytes and roots, under a fixed label in place of
    /// a checker identity. It decides only whether the session's world is the same
    /// world; the record store keys and checks admissions separately.
    pub(in crate::source_check) identity: fln_hash::domain::Digest,
    loaded: Loaded,
}

impl EditorWorld {
    pub(in crate::source_check) fn read(roots: &[Name], root: &Path) -> Result<Self, Failure> {
        let oleans = load_olean_closure(roots, root)?;
        let inputs: Vec<fln::OleanModuleInput<'_>> = oleans
            .iter()
            .map(|import| {
                let [exported, server, private] = &import.parts;
                fln::OleanModuleInput {
                    name: &import.name,
                    artifact: exported,
                    server_artifact: (!server.is_empty()).then_some(server.as_slice()),
                    private_artifact: (!private.is_empty()).then_some(private.as_slice()),
                }
            })
            .collect();
        let identity = fln::source_check::modules::reuse::ImportClosureKey::compute(
            &inputs,
            roots,
            &fln::KVMap::new(),
            fln::source_check::modules::reuse::CheckerIdentity::of_executable(
                b"fln.editor-import-world/1",
            ),
        )
        .digest();
        drop(inputs);
        Ok(Self {
            identity,
            loaded: Loaded {
                inputs: Inputs::Files(Vec::new()),
                total_bytes: 0,
                oleans,
                olean_roots: roots.to_vec(),
            },
        })
    }

    /// Admit the world, or re-prove an earlier admission's record, under `posture`.
    pub(in crate::source_check) fn admit(
        &self,
        jobs: std::num::NonZeroUsize,
        posture: ImportPosture,
    ) -> Result<(SourceOleanImport, ImportPostureReport), Failure> {
        let (_, base) = self.loaded.base_engine(
            || Err(Failure::input("an .olean world has no seed")),
            jobs,
            posture,
        )?;
        let base = base.ok_or_else(|| Failure::input("an .olean world has no modules"))?;
        Ok((base.receipt, base.report))
    }
}

/// One external `.olean` module as a build input (bead `franken_lean-z8j.1.2`).
pub(crate) struct ExternalInput {
    pub(crate) name: Name,
    /// `Domain::ArtifactClosureComponent` over every part, each length-prefixed and
    /// marked present or absent.
    pub(crate) digest: fln_hash::domain::Digest,
    pub(crate) imports: Vec<Name>,
}

/// The external `.olean` closure of `roots`, as `lake build` resolves it: read and
/// digested, never admitted. Build provenance and `fln build explain` compare these.
pub(crate) fn external_inputs(
    roots: &[Name],
    source_root: &Path,
) -> Result<Vec<ExternalInput>, String> {
    let decode = fln::OleanCheckLimits::new(
        MAX_OLEAN_BYTES,
        fln::Budget::for_stack_bytes(SOURCE_RUN_KERNEL_STACK_BYTES),
    )
    .decode;
    let loaded = load_olean_closure(roots, source_root).map_err(|failure| failure.detail)?;
    loaded
        .into_iter()
        .map(|module| {
            let imports = fln::olean_module_imports(&module.parts[0], decode)
                .map_err(|error| format!("{}: {error}", module.name.to_display_string()))?;
            let mut hasher = fln_hash::domain::DomainHasher::new(
                fln_hash::domain::Domain::ArtifactClosureComponent,
            );
            hasher.update(b"fln.lake-external-olean/1\0");
            for (index, part) in module.parts.iter().enumerate() {
                // The base part is always read; companions are absent when empty.
                let present = index == 0 || !part.is_empty();
                hasher.update(&[u8::from(present)]);
                hasher.update(&u64::try_from(part.len()).unwrap_or(u64::MAX).to_le_bytes());
                hasher.update(part);
            }
            Ok(ExternalInput {
                name: module.name,
                digest: hasher.finalize(),
                imports,
            })
        })
        .collect()
}

/// The source module records a build under `posture` consults (bead `franken_lean-z8j.1.1`).
pub(crate) fn module_records(posture: ImportPosture) -> reuse::ModuleRecords {
    reuse::ModuleRecords::new(posture)
}

/// The posture fields of an import report, for the Lake build report.
pub(crate) fn posture_json(report: &ImportPostureReport) -> String {
    reuse::json_fields(report)
}

/// One human sentence naming the posture an import was obtained under.
pub(crate) fn posture_sentence(report: &ImportPostureReport) -> String {
    reuse::sentence(report)
}

fn validate_component(component: &str) -> Result<(), Failure> {
    if component.is_empty()
        || matches!(component, "." | "..")
        || component.ends_with(['.', ' '])
        || component.chars().any(|c| {
            c.is_control() || matches!(c, '/' | '\\' | ':' | '<' | '>' | '"' | '|' | '?' | '*')
        })
    {
        return Err(Failure::input(
            "source module name contains an unsafe filesystem component",
        ));
    }
    let mut parts = Path::new(component).components();
    if !matches!(parts.next(), Some(std::path::Component::Normal(_))) || parts.next().is_some() {
        return Err(Failure::input(
            "source module name is not a single filesystem component",
        ));
    }
    Ok(())
}

fn module_path(root: &Path, name: &Name) -> Result<PathBuf, Failure> {
    checked_module_path(root, name, false)
}

fn checked_module_path(
    root: &Path,
    name: &Name,
    allow_missing_final: bool,
) -> Result<PathBuf, Failure> {
    let mut cursor = name.clone();
    let mut components = Vec::new();
    while !cursor.is_anonymous() {
        if components.len() >= MAX_NAME_DEPTH {
            return Err(Failure::resource("source module name depth exceeds 128"));
        }
        let LeafView::Str(component) = cursor.leaf_view() else {
            return Err(Failure::input(
                "source module names require textual components",
            ));
        };
        validate_component(component)?;
        components.push(component.to_owned());
        cursor = cursor.parent();
    }
    if components.is_empty() {
        return Err(Failure::input("source module name must not be anonymous"));
    }
    components.reverse();
    let last = components.len() - 1;
    let mut path = root.to_path_buf();
    for (index, component) in components.into_iter().enumerate() {
        // Append, do not replace an extension: «A.B» names the literal A.B.lean.
        path.push(if index == last {
            format!("{component}.lean")
        } else {
            component
        });
        let metadata = match std::fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(error)
                if allow_missing_final
                    && index == last
                    && error.kind() == std::io::ErrorKind::NotFound =>
            {
                return Ok(path);
            }
            Err(error) => return Err(Failure::io(&path, error)),
        };
        if metadata.file_type().is_symlink() {
            return Err(Failure::input(format!(
                "refusing symlink in source import {}",
                path.display()
            )));
        }
        if (index == last && !metadata.is_file()) || (index != last && !metadata.is_dir()) {
            return Err(Failure::input(format!(
                "source import has the wrong file kind: {}",
                path.display()
            )));
        }
    }
    Ok(path)
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_olean::region::OleanView;

    /// The capture ceiling check-source gives the importer must hold the
    /// pinned `Init` closure's extension payloads, or `import Init` is a
    /// resource refusal that no flag can lift.
    #[test]
    fn the_source_import_capture_ceiling_holds_the_pinned_init_closure() {
        let Some(lib) = std::env::var_os("HOME")
            .map(std::path::PathBuf::from)
            .map(|home| {
                home.join(".elan/toolchains")
                    .join(format!("leanprover--lean4---{}", fln::OLEAN_PIN_TAG))
                    .join("lib/lean")
            })
            .filter(|lib| lib.join("Init/Prelude.olean").is_file())
        else {
            assert!(
                std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
                "FLN_REQUIRE_REFERENCE is set but the pinned Reference Init is absent"
            );
            eprintln!("SKIP: pinned Reference lib/lean absent");
            return;
        };
        let limits = fln::source_check::modules::imported::SourceOleanImportLimits::new(
            fln::OleanCheckLimits::new(
                MAX_OLEAN_BYTES,
                fln::Budget::for_stack_bytes(OLEAN_CHECK_KERNEL_STACK_BYTES),
            ),
        );
        let mut modules = vec![lib.join("Init.olean")];
        let mut directories = vec![lib.join("Init")];
        while let Some(directory) = directories.pop() {
            for entry in std::fs::read_dir(&directory).expect("pinned Init directory") {
                let path = entry.expect("pinned Init entry").path();
                if path.is_dir() {
                    directories.push(path);
                } else if path
                    .extension()
                    .is_some_and(|extension| extension == "olean")
                {
                    modules.push(path);
                }
            }
        }
        let mut captured = 0usize;
        for module in &modules {
            let exported = std::fs::read(module).expect("pinned .olean");
            let parts = (
                std::fs::read(module.with_extension("olean.server")),
                std::fs::read(module.with_extension("olean.private")),
            );
            let blocks = match parts {
                (Ok(server), Ok(private)) => {
                    OleanView::parse_with_dependencies(&private, &[&exported, &server])
                        .and_then(|view| view.extension_payloads(limits.capture, usize::MAX))
                }
                _ => OleanView::parse(&exported)
                    .and_then(|view| view.extension_payloads(limits.capture, usize::MAX)),
            }
            .unwrap_or_else(|error| panic!("{}: {error}", module.display()));
            captured += blocks
                .iter()
                .flat_map(|block| &block.entries)
                .map(Vec::len)
                .sum::<usize>();
        }
        assert!(modules.len() > 500, "found {} Init modules", modules.len());
        assert!(
            captured > 64 * 1024 * 1024,
            "Init captures {captured} bytes; the former fixed 64 MiB ceiling held more"
        );
        assert!(
            captured <= limits.max_capture_bytes,
            "Init captures {captured} bytes but the ceiling is {}",
            limits.max_capture_bytes
        );
    }
}
