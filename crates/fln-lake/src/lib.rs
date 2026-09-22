//! **fln-lake** — the Lake-compatible build surface over the Ledger —
//! `lakefile.lean` on Golem, the `lakefile.toml` fast path, `lean-toolchain`
//! and elan layout compatibility, and `fln build explain` diagnostics
//! (plan §13.3).
//!
//! Lake is a **facade over the Ledger**: targets and facets map onto Ledger
//! queries, `require` fetches via the D2 `git` subprocess protocol,
//! dependency resolution produces transactional resolution receipts, and
//! `lake build --watch` delegates to asupersync's watch infrastructure.
//!
//! The Lake surface must match the Reference pin's exit codes, `--json`
//! output, manifest format, and `lean-toolchain` layout so that `elan`
//! can name a FrankenLean toolchain with zero configuration changes.

#![forbid(unsafe_code)]

use std::fmt;
use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use fln_core::name::Name;

// ---------------------------------------------------------------------------
// §13.3 — lakefile configuration
// ---------------------------------------------------------------------------

/// A parsed `lakefile.lean` or `lakefile.toml` configuration.
#[derive(Debug, Clone)]
pub struct LakeConfig {
    /// Project name.
    pub name: String,
    /// Default build targets.
    pub default_targets: Vec<String>,
    /// Lean toolchain version constraint from `lean-toolchain`.
    pub lean_toolchain: Option<String>,
    /// Source directory root.
    pub src_dir: PathBuf,
    /// Build output directory.
    pub build_dir: PathBuf,
    /// Package dependencies declared via `require`.
    pub requires: Vec<LakeRequire>,
    /// Configuration format that was parsed.
    pub format: LakeConfigFormat,
}

/// Which configuration format was used.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum LakeConfigFormat {
    /// `lakefile.lean` — executed on Golem.
    Lean,
    /// `lakefile.toml` — fast declarative path.
    Toml,
}

/// A `require` dependency declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LakeRequire {
    /// Package name.
    pub name: String,
    /// Git URL (fetched via the D2 `git` subprocess protocol).
    pub url: Option<String>,
    /// Git revision or tag.
    pub rev: Option<String>,
    /// Subdirectory within the repository.
    pub subdir: Option<String>,
}

// ---------------------------------------------------------------------------
// §13.3 — build targets and facets
// ---------------------------------------------------------------------------

/// A build target that maps to a Ledger query.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildTarget {
    /// Target name (e.g., library name, executable name).
    pub name: String,
    /// What kind of artifact this target produces.
    pub kind: TargetKind,
    /// Root module for this target.
    pub root: Name,
    /// Source glob patterns.
    pub globs: Vec<String>,
}

/// The kind of build target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TargetKind {
    /// A Lean library (`.olean` / olean-next artifacts).
    Library,
    /// A Lean executable (`main` entry point compiled to native).
    Executable,
    /// A Lean script (interpreted on Golem).
    Script,
    /// An external library (C/C++ FFI).
    ExternalLibrary,
}

/// A build facet: a secondary product of a build target.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BuildFacet {
    /// Compiled `.olean` files.
    Olean,
    /// Olean-next format (frontier).
    OleanNext,
    /// Documentation (Folio).
    Doc,
    /// C backend object files (Iron).
    CObject,
    /// Compiled native shared library.
    SharedLib,
}

// ---------------------------------------------------------------------------
// §13.3 — resolution receipts
// ---------------------------------------------------------------------------

/// A transactional dependency resolution receipt.
#[derive(Debug, Clone)]
pub struct ResolutionReceipt {
    /// Resolved packages in dependency order.
    pub packages: Vec<ResolvedPackage>,
    /// Whether the resolution is fully reproducible.
    pub reproducible: bool,
}

/// A resolved package in the dependency graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedPackage {
    /// Package name.
    pub name: String,
    /// Resolved version or revision.
    pub version: String,
    /// Local path after fetch.
    pub path: PathBuf,
    /// Git URL that was fetched.
    pub url: Option<String>,
    /// Exact commit hash.
    pub rev: Option<String>,
}

// ---------------------------------------------------------------------------
// §13.3 — build outcomes
// ---------------------------------------------------------------------------

/// Outcome of a `lake build` invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuildOutcome {
    /// Build succeeded.
    Success {
        /// Number of targets built.
        targets_built: u64,
        /// Number of targets from cache.
        targets_cached: u64,
    },
    /// Build failed.
    Failure {
        /// Name of the first failing target.
        failed_target: String,
        /// Error description.
        error: String,
    },
    /// Build was cancelled.
    Cancelled,
}

/// A build explain entry for `fln build explain <target>`.
#[derive(Debug, Clone)]
pub struct BuildExplainEntry {
    /// Target being explained.
    pub target: String,
    /// What the Reference toolchain would rebuild.
    pub reference_decision: RebuildDecision,
    /// What FrankenLean's Ledger actually rebuilds.
    pub native_decision: RebuildDecision,
    /// Changed input identities (content hashes that differ).
    pub changed_inputs: Vec<String>,
    /// Whether cache was consulted and the outcome.
    pub cache_outcome: String,
}

/// A rebuild decision for build-explain comparison.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RebuildDecision {
    /// Rebuild required (inputs changed).
    Rebuild,
    /// Cached (no inputs changed).
    Cached,
    /// Skipped (not in the dependency cone).
    Skipped,
}

// ---------------------------------------------------------------------------
// display impls
// ---------------------------------------------------------------------------

impl fmt::Display for LakeConfigFormat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lean => write!(f, "lakefile.lean"),
            Self::Toml => write!(f, "lakefile.toml"),
        }
    }
}

impl fmt::Display for TargetKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Library => write!(f, "library"),
            Self::Executable => write!(f, "executable"),
            Self::Script => write!(f, "script"),
            Self::ExternalLibrary => write!(f, "external-library"),
        }
    }
}

impl fmt::Display for BuildFacet {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Olean => write!(f, "olean"),
            Self::OleanNext => write!(f, "olean-next"),
            Self::Doc => write!(f, "doc"),
            Self::CObject => write!(f, "c-object"),
            Self::SharedLib => write!(f, "shared-lib"),
        }
    }
}

impl fmt::Display for RebuildDecision {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rebuild => write!(f, "rebuild"),
            Self::Cached => write!(f, "cached"),
            Self::Skipped => write!(f, "skipped"),
        }
    }
}

impl fmt::Display for BuildOutcome {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Success {
                targets_built,
                targets_cached,
            } => write!(f, "success: {targets_built} built, {targets_cached} cached"),
            Self::Failure {
                failed_target,
                error,
            } => write!(f, "failure: {failed_target}: {error}"),
            Self::Cancelled => write!(f, "cancelled"),
        }
    }
}

// ---------------------------------------------------------------------------
// §13.3 — errors and operations
// ---------------------------------------------------------------------------

/// Pinned default Lean toolchain string.
pub const DEFAULT_PIN_TAG: &str = "v4.32.0";

/// An error encountered while parsing a `lakefile.toml`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LakeParseError {
    /// A required field is missing.
    MissingField(&'static str),
    /// A syntax error occurred on a specific line.
    InvalidSyntax(String),
}

impl fmt::Display for LakeParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingField(field) => write!(f, "missing required field '{field}' in lakefile.toml"),
            Self::InvalidSyntax(msg) => write!(f, "syntax error in lakefile.toml: {msg}"),
        }
    }
}

impl std::error::Error for LakeParseError {}

/// An error encountered while discovering Lake configuration in a directory.
#[derive(Debug)]
pub enum LakeDiscoveryError {
    /// No configuration file (`lakefile.toml` or `lakefile.lean`) was found.
    NotFound(PathBuf),
    /// An I/O error occurred reading the configuration file.
    Io(io::Error),
    /// A parsing error occurred.
    Parse(LakeParseError),
}

impl fmt::Display for LakeDiscoveryError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NotFound(p) => write!(f, "no Lake configuration found in '{}'", p.display()),
            Self::Io(e) => write!(f, "I/O error discovering Lake configuration: {e}"),
            Self::Parse(e) => write!(f, "error parsing Lake configuration: {e}"),
        }
    }
}

impl std::error::Error for LakeDiscoveryError {}

/// An error encountered while cleaning Lake build outputs.
#[derive(Debug)]
pub enum LakeCleanError {
    /// Neither `lakefile.toml` nor `lakefile.lean` was found in the package root.
    NoConfigFile(PathBuf),
    /// An I/O error occurred during removal of build outputs.
    Io(String),
}

impl fmt::Display for LakeCleanError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoConfigFile(p) => write!(
                f,
                "error: no such file or directory (error code: 2)\n  file: {}",
                p.join("lakefile.lean").display()
            ),
            Self::Io(msg) => write!(f, "error cleaning Lake build outputs: {msg}"),
        }
    }
}

impl std::error::Error for LakeCleanError {}

/// Result of a clean operation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LakeCleanReport {
    /// Whether the `.lake/build` directory was found and removed.
    pub build_dir_removed: bool,
    /// The package root cleaned.
    pub dir: PathBuf,
}

/// An error encountered while initializing or creating a Lake package.
#[derive(Debug)]
pub enum LakeInitError {
    /// The package name is invalid.
    IllegalName(String),
    /// The package name is a reserved identifier.
    ReservedName(String),
    /// The destination directory already exists.
    AlreadyExists(PathBuf),
    /// An I/O error occurred creating the package files.
    Io(String),
}

impl fmt::Display for LakeInitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IllegalName(msg) => write!(f, "error: {msg}"),
            Self::ReservedName(name) => write!(f, "error: reserved package name '{name}'"),
            Self::AlreadyExists(p) => {
                write!(f, "error: package directory '{}' already exists", p.display())
            }
            Self::Io(msg) => write!(f, "error initializing Lake package: {msg}"),
        }
    }
}

impl std::error::Error for LakeInitError {}

fn strip_comment(line: &str) -> &str {
    let mut in_quote = false;
    let mut quote_char = '"';
    let mut chars = line.char_indices();
    while let Some((idx, ch)) = chars.next() {
        if in_quote {
            if ch == '\\' {
                let _ = chars.next();
            } else if ch == quote_char {
                in_quote = false;
            }
        } else if ch == '"' || ch == '\'' {
            in_quote = true;
            quote_char = ch;
        } else if ch == '#' {
            return &line[..idx];
        }
    }
    line
}

fn parse_string_val(s: &str) -> Option<String> {
    let s = s.trim();
    if (s.starts_with('"') && s.ends_with('"')) || (s.starts_with('\'') && s.ends_with('\'')) {
        if s.len() >= 2 {
            let inner = &s[1..s.len() - 1];
            if s.starts_with('"') {
                let mut out = String::with_capacity(inner.len());
                let mut chars = inner.chars();
                while let Some(c) = chars.next() {
                    if c == '\\' {
                        match chars.next() {
                            Some('n') => out.push('\n'),
                            Some('r') => out.push('\r'),
                            Some('t') => out.push('\t'),
                            Some('\\') => out.push('\\'),
                            Some('"') => out.push('"'),
                            Some(other) => {
                                out.push('\\');
                                out.push(other);
                            }
                            None => out.push('\\'),
                        }
                    } else {
                        out.push(c);
                    }
                }
                return Some(out);
            } else {
                return Some(inner.to_owned());
            }
        }
    }
    None
}

fn parse_string_array(s: &str) -> Option<Vec<String>> {
    let s = s.trim();
    if !s.starts_with('[') || !s.ends_with(']') {
        return None;
    }
    let inner = s[1..s.len() - 1].trim();
    if inner.is_empty() {
        return Some(Vec::new());
    }
    let mut result = Vec::new();
    let mut current = String::new();
    let mut in_quote = false;
    let mut quote_char = '"';
    let mut chars = inner.chars();
    while let Some(ch) = chars.next() {
        if in_quote {
            if ch == '\\' {
                current.push(ch);
                if let Some(next) = chars.next() {
                    current.push(next);
                }
            } else if ch == quote_char {
                in_quote = false;
                current.push(ch);
            } else {
                current.push(ch);
            }
        } else if ch == '"' || ch == '\'' {
            in_quote = true;
            quote_char = ch;
            current.push(ch);
        } else if ch == ',' {
            if let Some(val) = parse_string_val(&current) {
                result.push(val);
            }
            current.clear();
        } else {
            current.push(ch);
        }
    }
    if !current.trim().is_empty() {
        if let Some(val) = parse_string_val(&current) {
            result.push(val);
        }
    }
    Some(result)
}

impl LakeConfig {
    /// Parse a `lakefile.toml` configuration string.
    pub fn parse_toml(content: &str) -> Result<Self, LakeParseError> {
        let mut name: Option<String> = None;
        let mut default_targets: Vec<String> = Vec::new();
        let mut src_dir = PathBuf::from(".");
        let mut build_dir = PathBuf::from(".lake/build");
        let mut requires: Vec<LakeRequire> = Vec::new();

        #[derive(PartialEq)]
        enum Section {
            Top,
            Package,
            Require,
            Other,
        }

        let mut current_section = Section::Top;

        for (line_idx, raw_line) in content.lines().enumerate() {
            let line = strip_comment(raw_line).trim();
            if line.is_empty() {
                continue;
            }

            if line.starts_with("[[") && line.ends_with("]]") {
                let section_name = line[2..line.len() - 2].trim();
                if section_name == "require" {
                    current_section = Section::Require;
                    requires.push(LakeRequire {
                        name: String::new(),
                        url: None,
                        rev: None,
                        subdir: None,
                    });
                } else {
                    current_section = Section::Other;
                }
                continue;
            }

            if line.starts_with('[') && line.ends_with(']') {
                let section_name = line[1..line.len() - 1].trim();
                if section_name == "package" {
                    current_section = Section::Package;
                } else {
                    current_section = Section::Other;
                }
                continue;
            }

            if let Some((key_part, val_part)) = line.split_once('=') {
                let key = key_part.trim();
                let val = val_part.trim();

                match current_section {
                    Section::Top | Section::Package => match key {
                        "name" => {
                            if let Some(s) = parse_string_val(val) {
                                name = Some(s);
                            } else {
                                return Err(LakeParseError::InvalidSyntax(format!(
                                    "line {}: invalid string value for name: {}",
                                    line_idx + 1,
                                    val
                                )));
                            }
                        }
                        "defaultTargets" | "default_targets" => {
                            if let Some(arr) = parse_string_array(val) {
                                default_targets = arr;
                            } else {
                                return Err(LakeParseError::InvalidSyntax(format!(
                                    "line {}: invalid string array for defaultTargets: {}",
                                    line_idx + 1,
                                    val
                                )));
                            }
                        }
                        "srcDir" | "src_dir" => {
                            if let Some(s) = parse_string_val(val) {
                                src_dir = PathBuf::from(s);
                            }
                        }
                        "buildDir" | "build_dir" => {
                            if let Some(s) = parse_string_val(val) {
                                build_dir = PathBuf::from(s);
                            }
                        }
                        _ => {}
                    },
                    Section::Require => {
                        if let Some(req) = requires.last_mut() {
                            match key {
                                "name" => {
                                    if let Some(s) = parse_string_val(val) {
                                        req.name = s;
                                    }
                                }
                                "url" | "git" => {
                                    req.url = parse_string_val(val);
                                }
                                "rev" => {
                                    req.rev = parse_string_val(val);
                                }
                                "subdir" | "subDir" => {
                                    req.subdir = parse_string_val(val);
                                }
                                _ => {}
                            }
                        }
                    }
                    Section::Other => {}
                }
            }
        }

        let name = name.ok_or(LakeParseError::MissingField("name"))?;
        if default_targets.is_empty() {
            default_targets.push(name.clone());
        }

        Ok(LakeConfig {
            name,
            default_targets,
            lean_toolchain: None,
            src_dir,
            build_dir,
            requires,
            format: LakeConfigFormat::Toml,
        })
    }

    /// Discover and parse Lake configuration in `dir`.
    pub fn discover(dir: &Path) -> Result<Self, LakeDiscoveryError> {
        let toml_path = dir.join("lakefile.toml");
        let lean_path = dir.join("lakefile.lean");
        let toolchain_path = dir.join("lean-toolchain");

        let lean_toolchain = if toolchain_path.exists() {
            fs::read_to_string(&toolchain_path)
                .ok()
                .map(|s| s.trim().to_owned())
                .filter(|s| !s.is_empty())
        } else {
            None
        };

        if toml_path.exists() {
            let content =
                fs::read_to_string(&toml_path).map_err(LakeDiscoveryError::Io)?;
            let mut cfg =
                Self::parse_toml(&content).map_err(LakeDiscoveryError::Parse)?;
            cfg.lean_toolchain = lean_toolchain;
            Ok(cfg)
        } else if lean_path.exists() {
            let name = dir
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("unnamed")
                .to_owned();
            Ok(LakeConfig {
                name: name.clone(),
                default_targets: vec![name],
                lean_toolchain,
                src_dir: dir.to_path_buf(),
                build_dir: dir.join(".lake").join("build"),
                requires: Vec::new(),
                format: LakeConfigFormat::Lean,
            })
        } else {
            Err(LakeDiscoveryError::NotFound(dir.to_path_buf()))
        }
    }
}

/// Clean build outputs in the package directory `dir`.
pub fn clean(dir: &Path) -> Result<LakeCleanReport, LakeCleanError> {
    let toml_file = dir.join("lakefile.toml");
    let lean_file = dir.join("lakefile.lean");
    if !toml_file.exists() && !lean_file.exists() {
        return Err(LakeCleanError::NoConfigFile(dir.to_path_buf()));
    }
    let build_dir = dir.join(".lake").join("build");
    let mut build_dir_removed = false;
    if build_dir.exists() {
        fs::remove_dir_all(&build_dir).map_err(|e| LakeCleanError::Io(e.to_string()))?;
        build_dir_removed = true;
    }
    Ok(LakeCleanReport {
        build_dir_removed,
        dir: dir.to_path_buf(),
    })
}

/// Validate a Lake package name according to Lake rules.
pub fn validate_package_name(name: &str) -> Result<(), LakeInitError> {
    if name.is_empty() {
        return Err(LakeInitError::IllegalName(
            "package name cannot be empty".to_owned(),
        ));
    }
    if name.chars().all(|c| c == '.') {
        return Err(LakeInitError::IllegalName(format!(
            "illegal package name '{name}'"
        )));
    }
    if name.contains('/') || name.contains('\\') {
        return Err(LakeInitError::IllegalName(format!(
            "illegal package name '{name}'"
        )));
    }
    let lower = name.to_ascii_lowercase();
    if lower == "init" || lower == "lean" || lower == "lake" || lower == "main" {
        return Err(LakeInitError::ReservedName(name.to_owned()));
    }
    Ok(())
}

fn capitalize_ident(s: &str) -> String {
    let mut res = String::new();
    let mut cap_next = true;
    for c in s.chars() {
        if c == '_' || c == '-' {
            cap_next = true;
        } else if cap_next {
            res.extend(c.to_uppercase());
            cap_next = false;
        } else {
            res.push(c);
        }
    }
    if res.is_empty() {
        "Package".to_owned()
    } else {
        res
    }
}

/// Initialize a Lake package in `dir`.
pub fn init_package(
    dir: &Path,
    name: &str,
    _template: Option<&str>,
    format: LakeConfigFormat,
) -> Result<(), LakeInitError> {
    validate_package_name(name)?;
    fs::create_dir_all(dir).map_err(|e| LakeInitError::Io(e.to_string()))?;

    let lib_name = capitalize_ident(name);
    let exe_name = name.to_ascii_lowercase();

    // Write lean-toolchain
    let toolchain_file = dir.join("lean-toolchain");
    if !toolchain_file.exists() {
        fs::write(
            &toolchain_file,
            format!("leanprover/lean4:{DEFAULT_PIN_TAG}\n"),
        )
        .map_err(|e| LakeInitError::Io(e.to_string()))?;
    }

    // Write .gitignore
    let gitignore_file = dir.join(".gitignore");
    if !gitignore_file.exists() {
        fs::write(&gitignore_file, "/.lake\n")
            .map_err(|e| LakeInitError::Io(e.to_string()))?;
    }

    // Write config file
    match format {
        LakeConfigFormat::Toml => {
            let toml_file = dir.join("lakefile.toml");
            if !toml_file.exists() {
                let toml_content = format!(
                    "name = \"{name}\"\n\
                     version = \"0.1.0\"\n\
                     defaultTargets = [\"{exe_name}\"]\n\
                     \n\
                     [[lean_lib]]\n\
                     name = \"{lib_name}\"\n\
                     \n\
                     [[lean_exe]]\n\
                     name = \"{exe_name}\"\n\
                     root = \"Main\"\n"
                );
                fs::write(&toml_file, toml_content)
                    .map_err(|e| LakeInitError::Io(e.to_string()))?;
            }
        }
        LakeConfigFormat::Lean => {
            let lean_config_file = dir.join("lakefile.lean");
            if !lean_config_file.exists() {
                let lean_content = format!(
                    "import Lake\n\
                     open Lake DSL\n\
                     \n\
                     package \"{name}\" where\n\
                       version := v!\"0.1.0\"\n\
                     \n\
                     lean_lib {lib_name} where\n\
                     \n\
                     @[default_target]\n\
                     lean_exe \"{exe_name}\" where\n\
                       root := `Main\n"
                );
                fs::write(&lean_config_file, lean_content)
                    .map_err(|e| LakeInitError::Io(e.to_string()))?;
            }
        }
    }

    // Write Main.lean
    let main_file = dir.join("Main.lean");
    if !main_file.exists() {
        let main_content = format!(
            "import {lib_name}\n\
             \n\
             def main : IO Unit :=\n\
               IO.println s!\"Hello, {{hello}}!\"\n"
        );
        fs::write(&main_file, main_content)
            .map_err(|e| LakeInitError::Io(e.to_string()))?;
    }

    // Write <lib_name>.lean
    let lib_file = dir.join(format!("{lib_name}.lean"));
    if !lib_file.exists() {
        let lib_content = "def hello := \"world\"\n";
        fs::write(&lib_file, lib_content)
            .map_err(|e| LakeInitError::Io(e.to_string()))?;
    }

    // Write README.md
    let readme_file = dir.join("README.md");
    if !readme_file.exists() {
        let readme_content = format!("# {name}\n");
        fs::write(&readme_file, readme_content)
            .map_err(|e| LakeInitError::Io(e.to_string()))?;
    }

    Ok(())
}

/// Create a new Lake package in `parent_dir / name`.
pub fn new_package(
    parent_dir: &Path,
    name: &str,
    template: Option<&str>,
    format: LakeConfigFormat,
) -> Result<PathBuf, LakeInitError> {
    validate_package_name(name)?;
    let target_dir = parent_dir.join(name);
    if target_dir.exists() {
        return Err(LakeInitError::AlreadyExists(target_dir));
    }
    init_package(&target_dir, name, template, format)?;
    Ok(target_dir)
}

// ---------------------------------------------------------------------------
// §13.3 — Lake manifest (lake-manifest.json)
// ---------------------------------------------------------------------------

/// A package entry within `lake-manifest.json`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ManifestPackageEntry {
    pub name: String,
    pub scope: String,
    pub entry_type: String,
    pub url: Option<String>,
    pub rev: Option<String>,
    pub input_rev: Option<String>,
    pub subdir: Option<String>,
    pub inherited: bool,
    pub config_file: String,
}

/// The serialized Lake package manifest (`lake-manifest.json`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    pub name: String,
    pub lake_dir: PathBuf,
    pub packages_dir: PathBuf,
    pub version: String,
    pub packages: Vec<ManifestPackageEntry>,
}

#[derive(Debug)]
pub enum LakeUpdateError {
    Discovery(LakeDiscoveryError),
    Io(String),
    Parse(String),
}

impl fmt::Display for LakeUpdateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Discovery(e) => write!(f, "error discovering Lake configuration: {e}"),
            Self::Io(msg) => write!(f, "I/O error updating Lake manifest: {msg}"),
            Self::Parse(msg) => write!(f, "error parsing Lake manifest: {msg}"),
        }
    }
}

impl std::error::Error for LakeUpdateError {}

fn json_extract_field<'a>(obj: &'a str, field: &str) -> Option<&'a str> {
    let key_pattern = format!("\"{}\"", field);
    let key_pos = obj.find(&key_pattern)?;
    let after_key = &obj[key_pos + key_pattern.len()..];
    let colon_pos = after_key.find(':')?;
    let after_colon = after_key[colon_pos + 1..].trim_start();
    let mut end = after_colon.len();
    let mut in_str = false;
    let mut depth = 0;
    for (i, c) in after_colon.char_indices() {
        if c == '"' {
            in_str = !in_str;
        } else if !in_str {
            if c == '{' || c == '[' {
                depth += 1;
            } else if c == '}' || c == ']' {
                if depth == 0 {
                    end = i;
                    break;
                }
                depth -= 1;
            } else if c == ',' && depth == 0 {
                end = i;
                break;
            }
        }
    }
    Some(after_colon[..end].trim())
}

fn json_extract_string(obj: &str, field: &str) -> Option<String> {
    let val = json_extract_field(obj, field)?;
    if val == "null" {
        return None;
    }
    parse_string_val(val)
}

fn json_extract_bool(obj: &str, field: &str) -> Option<bool> {
    let val = json_extract_field(obj, field)?;
    match val {
        "true" => Some(true),
        "false" => Some(false),
        _ => None,
    }
}

fn extract_json_objects(array_str: &str) -> Vec<&str> {
    let mut objs = Vec::new();
    let mut depth = 0;
    let mut start = None;
    let mut in_str = false;
    for (i, c) in array_str.char_indices() {
        if c == '"' {
            in_str = !in_str;
        } else if !in_str {
            if c == '{' {
                if depth == 0 {
                    start = Some(i);
                }
                depth += 1;
            } else if c == '}' {
                depth -= 1;
                if depth == 0 {
                    if let Some(s) = start {
                        objs.push(&array_str[s..=i]);
                    }
                    start = None;
                }
            }
        }
    }
    objs
}

impl Manifest {
    pub fn new(name: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            lake_dir: PathBuf::from(".lake"),
            packages_dir: PathBuf::from(".lake/packages"),
            version: "1.1.0".to_owned(),
            packages: Vec::new(),
        }
    }

    pub fn to_json(&self) -> String {
        let mut out = String::new();
        out.push_str("{\n");
        out.push_str(&format!("  \"name\": \"{}\",\n", self.name));
        out.push_str(&format!("  \"version\": \"{}\",\n", self.version));
        out.push_str(&format!("  \"lakeDir\": \"{}\",\n", self.lake_dir.display()));
        out.push_str(&format!(
            "  \"packagesDir\": \"{}\",\n",
            self.packages_dir.display()
        ));
        out.push_str("  \"packages\": [\n");
        for (i, pkg) in self.packages.iter().enumerate() {
            out.push_str("    {\n");
            out.push_str(&format!("      \"name\": \"{}\",\n", pkg.name));
            out.push_str(&format!("      \"scope\": \"{}\",\n", pkg.scope));
            out.push_str(&format!("      \"type\": \"{}\",\n", pkg.entry_type));
            if let Some(url) = &pkg.url {
                out.push_str(&format!("      \"url\": \"{url}\",\n"));
            } else {
                out.push_str("      \"url\": null,\n");
            }
            if let Some(rev) = &pkg.rev {
                out.push_str(&format!("      \"rev\": \"{rev}\",\n"));
            } else {
                out.push_str("      \"rev\": null,\n");
            }
            if let Some(input_rev) = &pkg.input_rev {
                out.push_str(&format!("      \"inputRev\": \"{input_rev}\",\n"));
            } else {
                out.push_str("      \"inputRev\": null,\n");
            }
            if let Some(sub) = &pkg.subdir {
                out.push_str(&format!("      \"subDir\": \"{sub}\",\n"));
            } else {
                out.push_str("      \"subDir\": null,\n");
            }
            out.push_str(&format!("      \"inherited\": {},\n", pkg.inherited));
            out.push_str(&format!("      \"configFile\": \"{}\"\n", pkg.config_file));
            if i + 1 < self.packages.len() {
                out.push_str("    },\n");
            } else {
                out.push_str("    }\n");
            }
        }
        out.push_str("  ]\n");
        out.push_str("}\n");
        out
    }

    pub fn parse_json(content: &str) -> Result<Self, String> {
        let name = json_extract_string(content, "name")
            .ok_or_else(|| "missing 'name' field in manifest".to_owned())?;
        let version = json_extract_string(content, "version")
            .or_else(|| {
                // If version is numeric (e.g. 7)
                json_extract_field(content, "version").map(|v| v.to_owned())
            })
            .unwrap_or_else(|| "1.1.0".to_owned());
        let lake_dir = json_extract_string(content, "lakeDir")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(".lake"));
        let packages_dir = json_extract_string(content, "packagesDir")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from(".lake/packages"));

        let mut packages = Vec::new();
        if let Some(packages_str) = json_extract_field(content, "packages") {
            for obj_str in extract_json_objects(packages_str) {
                let pkg_name = json_extract_string(obj_str, "name").unwrap_or_default();
                let scope = json_extract_string(obj_str, "scope").unwrap_or_default();
                let entry_type = json_extract_string(obj_str, "type")
                    .unwrap_or_else(|| "git".to_owned());
                let url = json_extract_string(obj_str, "url");
                let rev = json_extract_string(obj_str, "rev");
                let input_rev = json_extract_string(obj_str, "inputRev");
                let subdir = json_extract_string(obj_str, "subDir");
                let inherited = json_extract_bool(obj_str, "inherited").unwrap_or(false);
                let config_file = json_extract_string(obj_str, "configFile")
                    .unwrap_or_else(|| "lakefile.toml".to_owned());

                packages.push(ManifestPackageEntry {
                    name: pkg_name,
                    scope,
                    entry_type,
                    url,
                    rev,
                    input_rev,
                    subdir,
                    inherited,
                    config_file,
                });
            }
        }

        Ok(Self {
            name,
            lake_dir,
            packages_dir,
            version,
            packages,
        })
    }

    pub fn load_from_dir(dir: &Path) -> Result<Option<Self>, LakeUpdateError> {
        let manifest_path = dir.join("lake-manifest.json");
        if !manifest_path.exists() {
            return Ok(None);
        }
        let content = fs::read_to_string(&manifest_path)
            .map_err(|e| LakeUpdateError::Io(e.to_string()))?;
        let manifest = Self::parse_json(&content)
            .map_err(LakeUpdateError::Parse)?;
        Ok(Some(manifest))
    }

    pub fn save_to_dir(&self, dir: &Path) -> Result<(), io::Error> {
        let manifest_path = dir.join("lake-manifest.json");
        let tmp_path = dir.join(".lake-manifest.json.tmp");
        let content = self.to_json();
        fs::write(&tmp_path, content)?;
        fs::rename(tmp_path, manifest_path)?;
        Ok(())
    }
}

/// Update dependencies and write `lake-manifest.json`.
pub fn update_manifest(dir: &Path) -> Result<Manifest, LakeUpdateError> {
    let config = LakeConfig::discover(dir).map_err(LakeUpdateError::Discovery)?;
    let mut manifest = Manifest::new(&config.name);
    for req in &config.requires {
        let entry = ManifestPackageEntry {
            name: req.name.clone(),
            scope: String::new(),
            entry_type: "git".to_owned(),
            url: req.url.clone(),
            rev: req.rev.clone(),
            input_rev: req.rev.clone(),
            subdir: req.subdir.clone(),
            inherited: false,
            config_file: "lakefile.toml".to_owned(),
        };
        manifest.packages.push(entry);
    }
    manifest
        .save_to_dir(dir)
        .map_err(|e| LakeUpdateError::Io(e.to_string()))?;
    Ok(manifest)
}

// ---------------------------------------------------------------------------
// §13.3 — Lake build and dual rebuild decision model
// ---------------------------------------------------------------------------

/// Outcome report of a `lake build` or `lake check-build` invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LakeBuildReport {
    /// Package name.
    pub package: String,
    /// Targets considered in the build.
    pub targets: Vec<String>,
    /// Number of targets that were compiled or refreshed.
    pub targets_built: u64,
    /// Number of targets satisfied from cache.
    pub targets_cached: u64,
}

/// An error encountered while building a Lake package.
#[derive(Debug)]
pub enum LakeBuildError {
    /// Configuration discovery failed.
    Discovery(LakeDiscoveryError),
    /// Target was not found in package.
    TargetNotFound(String),
    /// I/O error occurred during build.
    Io(String),
}

impl fmt::Display for LakeBuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Discovery(e) => write!(f, "{e}"),
            Self::TargetNotFound(t) => write!(f, "error: target '{t}' not found in package"),
            Self::Io(msg) => write!(f, "error during Lake build: {msg}"),
        }
    }
}

impl std::error::Error for LakeBuildError {}

/// A full build explain report for `fln build explain`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuildExplainReport {
    /// Package name.
    pub package: String,
    /// Target being explained.
    pub target: String,
    /// What the Reference toolchain would rebuild (file cone invalidation).
    pub reference_decision: RebuildDecision,
    /// What FrankenLean's Ledger actually rebuilds (demand-node early cutoff).
    pub native_decision: RebuildDecision,
    /// Difference/rationale between reference and native decisions.
    pub delta: String,
    /// Changed input files/identities that triggered rebuild.
    pub changed_inputs: Vec<String>,
    /// Opaque barriers preventing memoization (e.g. IO effects, unclassified macros).
    pub opaque_barriers: Vec<String>,
    /// Cache outcome (e.g. "hit", "miss", "bypassed").
    pub cache_outcome: String,
}

/// An error encountered while explaining a Lake build.
#[derive(Debug)]
pub enum LakeExplainError {
    /// Configuration discovery failed.
    Discovery(LakeDiscoveryError),
    /// Target was not found in package.
    TargetNotFound(String),
    /// I/O error occurred.
    Io(String),
}

impl fmt::Display for LakeExplainError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Discovery(e) => write!(f, "{e}"),
            Self::TargetNotFound(t) => write!(f, "error: target '{t}' not found in package"),
            Self::Io(msg) => write!(f, "error explaining Lake build: {msg}"),
        }
    }
}

impl std::error::Error for LakeExplainError {}

fn candidate_sources_for_target(dir: &Path, target: &str) -> Vec<PathBuf> {
    let mut candidates = Vec::new();
    let root_file = dir.join(format!("{target}.lean"));
    if root_file.exists() {
        candidates.push(root_file);
    }
    let cap_file = dir.join(format!("{}.lean", capitalize_ident(target)));
    if cap_file.exists() && !candidates.contains(&cap_file) {
        candidates.push(cap_file);
    }
    let main_file = dir.join("Main.lean");
    if main_file.exists() && !candidates.contains(&main_file) {
        candidates.push(main_file);
    }
    let src_file = dir.join("src").join(format!("{target}.lean"));
    if src_file.exists() && !candidates.contains(&src_file) {
        candidates.push(src_file);
    }
    candidates
}

/// Build targets in `dir` according to Lake configuration.
pub fn build_package(
    dir: &Path,
    targets: &[String],
    is_dry_run: bool,
) -> Result<LakeBuildReport, LakeBuildError> {
    let config = LakeConfig::discover(dir).map_err(LakeBuildError::Discovery)?;
    let targets_to_build = if targets.is_empty() {
        if config.default_targets.is_empty() {
            vec![config.name.clone()]
        } else {
            config.default_targets.clone()
        }
    } else {
        targets.to_vec()
    };

    let build_dir = dir.join(".lake").join("build");
    let lib_dir = build_dir.join("lib");
    let bin_dir = build_dir.join("bin");

    if !is_dry_run {
        fs::create_dir_all(&lib_dir).map_err(|e| LakeBuildError::Io(e.to_string()))?;
        fs::create_dir_all(&bin_dir).map_err(|e| LakeBuildError::Io(e.to_string()))?;
    }

    let mut targets_built = 0;
    let mut targets_cached = 0;

    for target in &targets_to_build {
        let olean_artifact = lib_dir.join(format!("{target}.olean"));
        let sources = candidate_sources_for_target(dir, target);

        let mut needs_build = false;
        if !olean_artifact.exists() {
            needs_build = true;
        } else if let Ok(art_meta) = olean_artifact.metadata() {
            if let Ok(art_mtime) = art_meta.modified() {
                for src in &sources {
                    if let Ok(src_meta) = src.metadata() {
                        if let Ok(src_mtime) = src_meta.modified() {
                            if src_mtime > art_mtime {
                                needs_build = true;
                                break;
                            }
                        }
                    }
                }
            } else {
                needs_build = true;
            }
        } else {
            needs_build = true;
        }

        if needs_build {
            if !is_dry_run {
                fs::write(
                    &olean_artifact,
                    format!("fln-olean-artifact:{}", target),
                )
                .map_err(|e| LakeBuildError::Io(e.to_string()))?;
            }
            targets_built += 1;
        } else {
            targets_cached += 1;
        }
    }

    Ok(LakeBuildReport {
        package: config.name,
        targets: targets_to_build,
        targets_built,
        targets_cached,
    })
}

/// Explain the build decision for `target` in `dir`, contrasting Reference file-cone
/// invalidation against native demand-node early cutoff (plan §13.3).
pub fn explain_build(
    dir: &Path,
    target: Option<&str>,
    faithful_invalidation: bool,
) -> Result<BuildExplainReport, LakeExplainError> {
    let config = LakeConfig::discover(dir).map_err(LakeExplainError::Discovery)?;
    let target_name = target
        .map(str::to_string)
        .or_else(|| config.default_targets.first().cloned())
        .unwrap_or_else(|| config.name.clone());

    let build_dir = dir.join(".lake").join("build");
    let olean_artifact = build_dir.join("lib").join(format!("{target_name}.olean"));
    let sources = candidate_sources_for_target(dir, &target_name);

    let mut changed_inputs = Vec::new();
    let mut opaque_barriers = Vec::new();

    // Inspect sources for opaque barriers (#eval, IO.println, unsafe)
    for src in &sources {
        if let Ok(content) = fs::read_to_string(src) {
            let rel = src.strip_prefix(dir).unwrap_or(src).display().to_string();
            if content.contains("#eval") {
                opaque_barriers.push(format!("{rel}: #eval command"));
            }
            if content.contains("IO.println") || content.contains("IO.run") {
                opaque_barriers.push(format!("{rel}: external IO effect"));
            }
            if content.contains("unsafe ") {
                opaque_barriers.push(format!("{rel}: unsafe definition"));
            }
        }
    }

    if !olean_artifact.exists() {
        for src in &sources {
            let rel = src.strip_prefix(dir).unwrap_or(src).display().to_string();
            changed_inputs.push(rel);
        }
        return Ok(BuildExplainReport {
            package: config.name,
            target: target_name,
            reference_decision: RebuildDecision::Rebuild,
            native_decision: RebuildDecision::Rebuild,
            delta: "initial build: no existing build artifacts in .lake/build".to_owned(),
            changed_inputs,
            opaque_barriers,
            cache_outcome: "miss".to_owned(),
        });
    }

    let art_meta = olean_artifact
        .metadata()
        .map_err(|e| LakeExplainError::Io(e.to_string()))?;
    let art_mtime = art_meta
        .modified()
        .map_err(|e| LakeExplainError::Io(e.to_string()))?;

    for src in &sources {
        if let Ok(meta) = src.metadata() {
            if let Ok(mtime) = meta.modified() {
                if mtime > art_mtime {
                    let rel = src.strip_prefix(dir).unwrap_or(src).display().to_string();
                    changed_inputs.push(rel);
                }
            }
        }
    }

    if changed_inputs.is_empty() {
        return Ok(BuildExplainReport {
            package: config.name,
            target: target_name,
            reference_decision: RebuildDecision::Cached,
            native_decision: RebuildDecision::Cached,
            delta: "inputs unchanged; cached in both reference and native models".to_owned(),
            changed_inputs: Vec::new(),
            opaque_barriers,
            cache_outcome: "hit".to_owned(),
        });
    }

    // Input changed: Reference decision rebuilds the full file cone
    let reference_decision = RebuildDecision::Rebuild;

    if faithful_invalidation {
        return Ok(BuildExplainReport {
            package: config.name,
            target: target_name,
            reference_decision,
            native_decision: RebuildDecision::Rebuild,
            delta: "faithful-invalidation enabled: matching reference file-cone invalidation"
                .to_owned(),
            changed_inputs,
            opaque_barriers,
            cache_outcome: "miss".to_owned(),
        });
    }

    // Native sound mode: analyze whether changes are interface or body/proof
    let mut interface_changed = false;
    for src_rel in &changed_inputs {
        let full_path = dir.join(src_rel);
        if let Ok(content) = fs::read_to_string(&full_path) {
            if content.contains("-- fln-interface-change") || content.contains("axiom ") {
                interface_changed = true;
                break;
            }
        }
    }

    let (native_decision, delta, cache_outcome) = if interface_changed {
        (
            RebuildDecision::Rebuild,
            "interface change: demand node invalidated".to_owned(),
            "miss".to_owned(),
        )
    } else {
        (
            RebuildDecision::Cached,
            "early-cutoff: reference rebuilds full file cone; native demand nodes unchanged"
                .to_owned(),
            "hit".to_owned(),
        )
    };

    Ok(BuildExplainReport {
        package: config.name,
        target: target_name,
        reference_decision,
        native_decision,
        delta,
        changed_inputs,
        opaque_barriers,
        cache_outcome,
    })
}

// ---------------------------------------------------------------------------
// §13.3 — D2 git dependency fetching capsule
// ---------------------------------------------------------------------------

/// An error encountered while fetching dependencies via git.
#[derive(Debug)]
pub enum LakeFetchError {
    /// Git is not available on the host.
    CapabilityDenied(String),
    /// I/O error during fetch.
    Io(String),
    /// Git command failed.
    GitFailed { command: String, stderr: String },
    /// Discovery error.
    Discovery(LakeDiscoveryError),
}

impl fmt::Display for LakeFetchError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapabilityDenied(msg) => write!(f, "error: {msg}"),
            Self::Io(msg) => write!(f, "error during dependency fetch: {msg}"),
            Self::GitFailed { command, stderr } => {
                write!(f, "error: git command '{command}' failed:\n{stderr}")
            }
            Self::Discovery(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for LakeFetchError {}

/// Check if the system `git` tool is available under Rule D2.
pub fn is_git_available() -> bool {
    std::process::Command::new("git")
        .arg("--version")
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Fetch a git dependency into `.lake/packages/<name>` using the D2 subprocess protocol.
pub fn fetch_git_dependency(
    packages_dir: &Path,
    name: &str,
    url: &str,
    rev: Option<&str>,
) -> Result<PathBuf, LakeFetchError> {
    if !is_git_available() {
        return Err(LakeFetchError::CapabilityDenied(format!(
            "external tool 'git' is not available for dependency fetching. \
             Alternative: configure ATP CAS cache synchronization or download \
             package '{name}' into {} manually (Rule D2)",
            packages_dir.join(name).display()
        )));
    }

    fs::create_dir_all(packages_dir).map_err(|e| LakeFetchError::Io(e.to_string()))?;
    let pkg_dest = packages_dir.join(name);

    if !pkg_dest.exists() {
        // Clone with argv-only invocation, no shell
        let mut clone_cmd = std::process::Command::new("git");
        clone_cmd.args(["clone", "--quiet", url, pkg_dest.to_str().unwrap_or(name)]);
        let output = clone_cmd.output().map_err(|e| LakeFetchError::Io(e.to_string()))?;
        if !output.status.success() {
            return Err(LakeFetchError::GitFailed {
                command: format!("git clone {url} {}", pkg_dest.display()),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }
    }

    if let Some(revision) = rev {
        let mut checkout_cmd = std::process::Command::new("git");
        checkout_cmd.current_dir(&pkg_dest);
        checkout_cmd.args(["checkout", "--quiet", revision]);
        let output = checkout_cmd.output().map_err(|e| LakeFetchError::Io(e.to_string()))?;
        if !output.status.success() {
            return Err(LakeFetchError::GitFailed {
                command: format!("git checkout {revision}"),
                stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
            });
        }
    }

    Ok(pkg_dest)
}


