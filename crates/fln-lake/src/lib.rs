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

